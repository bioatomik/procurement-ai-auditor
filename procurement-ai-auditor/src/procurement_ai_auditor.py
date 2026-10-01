#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import sys
import os
import time
import logging
import threading
import shutil
import json
import hashlib
import random
import contextlib
import re
from datetime import datetime, date
from decimal import Decimal
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Dict, Any, Optional, Union
from dataclasses import dataclass, field
from enum import Enum
import queue

import requests
import urllib3


import pandas as pd
import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext, filedialog

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)


def json_serialize_fallback(obj: Any) -> Any:
    """Конвертер типов, которые стандартный json не умеет сериализовать."""
    if isinstance(obj, Decimal):
        return float(obj)
    if isinstance(obj, (datetime, date)):
        return obj.isoformat()
    try:
        if pd.isna(obj):
            return None
    except Exception:
        pass
    return str(obj)


def get_app_dir() -> str:
    """Каталог приложения без привязки к конкретному компьютеру/диску."""
    if getattr(sys, "frozen", False):
        return os.path.dirname(os.path.abspath(sys.executable))
    return os.path.dirname(os.path.abspath(__file__))


APP_DIR = get_app_dir()
SETTINGS_FILE = os.path.join(APP_DIR, "spp_audit_settings.json")
COLUMN_ALIASES_FILE = os.path.join(APP_DIR, "column_aliases.json")
REVIEW_SESSION_FILE = os.path.join(APP_DIR, "review_session.json")
WORK_CATEGORIES_FILE = os.path.join(APP_DIR, "work_categories.json")
WORK_GROUPS_FILE = os.path.join(APP_DIR, "work_group_rules.json")
CLASSIFICATION_MASTER_FILE = os.path.join(APP_DIR, "classification_master.json")

try:
    from pyrfc import Connection, RFCError
except ImportError:
    print("[CRITICAL ERROR] Не найдена библиотека pyrfc.")
    sys.exit(1)


class VerdictCategory(Enum):
    FAST_BUILD = "Быстрая стройка"
    FAST_BUILD_OS = "Быстрая стройка + ОС"
    EQUIPMENT = "Оборудование"
    REPAIR_OS = "Ремонт ОС"
    SKIP = "ПРОПУСК"
    UNKNOWN = "Не определено"

    @classmethod
    def from_string(cls, value: str):
        if value is None:
            return None
        cleaned = str(value).strip().strip("\"'")
        aliases = {
            "быстрая стройка": cls.FAST_BUILD,
            "быстрая стройка + ос": cls.FAST_BUILD_OS,
            "оборудование": cls.EQUIPMENT,
            "ремонт ос": cls.REPAIR_OS,
            "пропуск": cls.SKIP,
            "не определено": cls.UNKNOWN,
            "неопределено": cls.UNKNOWN,
        }
        return aliases.get(cleaned.lower())


# Счета учёта по классу закупки:
#   Оборудование              → 1031100
#   Быстрая стройка / Ремонт ОС → 1031200
#   Быстрая стройка + ОС      → оба (1031200 + 1031100)
ACCOUNT_EQUIPMENT = "1031100"
ACCOUNT_FAST_OR_REPAIR = "1031200"


def accounts_for_verdict(verdict: Optional[str]) -> list:
    """Возвращает список счетов для вердикта (может быть 0, 1 или 2)."""
    v = str(verdict or "").strip()
    if not v or v in ("Не определено", "ПРОПУСК"):
        return []
    if v == VerdictCategory.EQUIPMENT.value:
        return [ACCOUNT_EQUIPMENT]
    if v in (VerdictCategory.FAST_BUILD.value, VerdictCategory.REPAIR_OS.value):
        return [ACCOUNT_FAST_OR_REPAIR]
    if v == VerdictCategory.FAST_BUILD_OS.value:
        # «Быстрая стройка + ОС» — одновременно 12 и 11
        return [ACCOUNT_FAST_OR_REPAIR, ACCOUNT_EQUIPMENT]
    return []


def format_accounts(verdict: Optional[str]) -> str:
    """Строка для Excel/UI: один счёт или «1031200 + 1031100»."""
    accs = accounts_for_verdict(verdict)
    if not accs:
        return ""
    if len(accs) == 1:
        return accs[0]
    return " + ".join(accs)


def build_semantic_text(item_name: str = "", services: Optional[list] = None, max_len: int = 7000) -> str:
    """Единый билдер семантического текста позиции (без номеров заказа/СФ/МВЗ).

    Используется в pipeline, few-shot и review — один формат, без дублей логики.
    """
    parts = []
    name = str(item_name or "").strip()
    if name:
        parts.append(f"Название позиции SAP: {name}")
    names = []
    for x in services or []:
        if isinstance(x, dict):
            v = str(x.get("Наименование работ / материалов", "") or "").strip()
        else:
            v = str(x or "").strip()
        if v and v not in names:
            names.append(v)
    if names:
        parts.append("Работы / услуги / материалы: " + " ||| ".join(names))
    return " | ".join(parts)[:max_len]


def write_verdict_columns(df: Optional[pd.DataFrame], df_idx, record: dict) -> None:
    """Единая запись Вердикт / Счет / Источник / Проверено в review DataFrame."""
    if df is None or df_idx is None:
        return
    try:
        if df_idx not in df.index:
            return
    except Exception:
        return
    fv = record.get("final_verdict") or record.get("verdict") or None
    df.at[df_idx, "Вердикт ИИ"] = fv
    if "Счет" in df.columns or True:
        if "Счет" not in df.columns:
            df["Счет"] = None
        df.at[df_idx, "Счет"] = format_accounts(fv)
    if "Источник" in df.columns:
        df.at[df_idx, "Источник"] = record.get("source") or "unknown"
    if "Проверено" in df.columns:
        df.at[df_idx, "Проверено"] = record.get("checked", "Нет")
    if "Авто вердикт" in df.columns:
        df.at[df_idx, "Авто вердикт"] = record.get("auto_verdict") or None
    if "Основание решения" in df.columns:
        df.at[df_idx, "Основание решения"] = record.get("reason") or ""
    if "Категория работы" in df.columns and record.get("work_category") is not None:
        df.at[df_idx, "Категория работы"] = record.get("work_category") or ""


class Tooltip:
    """Небольшая подсказка при наведении на кнопку/контрол."""
    def __init__(self, widget, text, delay=500):
        self.widget = widget
        self.text = text
        self.delay = delay
        self.tip = None
        self.after_id = None
        widget.bind("<Enter>", self._enter, add="+")
        widget.bind("<Leave>", self._leave, add="+")
    def _enter(self, _=None):
        self.after_id = self.widget.after(self.delay, self._show)
    def _leave(self, _=None):
        if self.after_id:
            try: self.widget.after_cancel(self.after_id)
            except Exception: pass
            self.after_id = None
        self._hide()
    def _show(self):
        if self.tip or not self.text:
            return
        x = self.widget.winfo_rootx() + 12
        y = self.widget.winfo_rooty() + self.widget.winfo_height() + 4
        self.tip = tk.Toplevel(self.widget)
        self.tip.wm_overrideredirect(True)
        self.tip.wm_geometry(f"+{x}+{y}")
        tk.Label(self.tip, text=self.text, justify=tk.LEFT, bg="#111827", fg="white",
                 font=("Segoe UI", 9), padx=8, pady=5, relief="solid", bd=1).pack()
    def _hide(self):
        if self.tip:
            try: self.tip.destroy()
            except Exception: pass
            self.tip = None


# Зарезервированные аналитические группы (не итоговый вердикт аудита).
# НМА — только ярлык на будущее, без автоопределения.
# Стройка — группа работ (можно назначить вручную / слабым правилом ниже).
NMA_WORK_GROUP = "НМА"
STROYKA_WORK_GROUP = "Стройка"
RESERVED_WORK_GROUPS = (STROYKA_WORK_GROUP, NMA_WORK_GROUP)
# Пустые / «Без категории» / «Не определено» в UI показываем одним ярлыком:
UNKNOWN_WORK_CATEGORY = "Не определено"

WORK_CATEGORY_RULES = [
    (re.compile(r"\bконтроллер(?:ы|а|ов|ом|ами)?\b", re.I), "Контроллеры"),
    (re.compile(r"\bнасос(?:ы|а|ов|ом|ами)?\b", re.I), "Насосы"),
    (re.compile(r"\bкомпрессор(?:ы|а|ов|ом|ами)?\b", re.I), "Компрессоры"),
    (re.compile(r"\bдатчик(?:и|а|ов|ом|ами)?\b", re.I), "Датчики"),
    (re.compile(r"\bклапан(?:ы|а|ов|ом|ами)?\b|\bарматур(?:а|ы|ой|у)\b", re.I), "Клапаны и арматура"),
    (re.compile(r"\bмойк(?:а|и|у|ой|ами)\b.*\bнерж|\bнерж(?:аве?йка|аве?ющ)|\bнержавеющ", re.I), "Мойки из нержавеющей стали"),
    (re.compile(r"\bводонагревател(?:ь|и|я|ей|ем|ями)?\b", re.I), "Водонагреватели"),
    (re.compile(r"\bкофемашин(?:а|ы|у|ой|ами)\b", re.I), "Кофейное оборудование"),
    (re.compile(r"\bтестораскаточ(?:ная|ные|ную|ной|ных)\b", re.I), "Тестораскаточные машины"),
    (re.compile(r"\bхолодильн(?:ое|ая|ые|ую|ой|ых)\s+(?:оборудован|техник)", re.I), "Холодильное оборудование"),
    (re.compile(r"\bрозетк(?:а|и|у|ой|ами)\b", re.I), "Розетки и электрофурнитура"),
    (re.compile(r"\bкабел(?:ь|и|я|ем|ями)\b|\bпровод(?:а|ом|ами)?\b", re.I), "Кабели и проводка"),
    (re.compile(r"\bсветильник(?:и|а|ов|ом|ами)?\b|\bосвещен", re.I), "Освещение"),
    (re.compile(r"\bремонт\b.*\bоборудован|\bобслуживан\w*\b.*\bоборудован", re.I), "Ремонт и обслуживание оборудования"),
    # Аналитическая группа «Стройка» (не вердикт «Быстрая стройка»)
    (re.compile(r"\bстройк[а-яё]*\b|\bстроительн", re.I), STROYKA_WORK_GROUP),
    # НМА — без regex, только ручное назначение.
]


def deterministic_work_category(text):
    text = re.sub(r"\s+", " ", str(text or "").strip())
    if not text:
        return ""
    for pattern, category in WORK_CATEGORY_RULES:
        if pattern.search(text):
            return category
    return ""


def load_work_categories():
    if not os.path.exists(WORK_CATEGORIES_FILE):
        return {}
    try:
        with open(WORK_CATEGORIES_FILE, encoding="utf-8") as f:
            raw=json.load(f)
        return raw if isinstance(raw, dict) else {}
    except Exception as e:
        logger.warning(f"Не удалось загрузить work_categories.json: {e}")
        return {}


def save_work_categories(mapping):
    tmp=WORK_CATEGORIES_FILE+".tmp"
    try:
        with open(tmp,"w",encoding="utf-8") as f:
            json.dump(mapping,f,ensure_ascii=False,indent=2)
        os.replace(tmp,WORK_CATEGORIES_FILE)
    except Exception as e:
        logger.warning(f"Не удалось сохранить work_categories.json: {e}")


def load_work_groups():
    """Загружает пользовательские связи: родительская группа -> подгруппы -> основной классификатор."""
    if not os.path.exists(WORK_GROUPS_FILE):
        return {}
    try:
        with open(WORK_GROUPS_FILE, encoding="utf-8") as f:
            raw = json.load(f)
        if isinstance(raw, dict) and isinstance(raw.get("groups"), dict):
            return raw["groups"]
        if isinstance(raw, dict):
            return raw
    except Exception as e:
        logger.warning(f"Не удалось загрузить work_group_rules.json: {e}")
    return {}


def save_work_groups(groups):
    payload = {
        "version": 1,
        "description": "Пользовательские иерархические группы работ: родительская группа содержит подгруппы/категории и наследуемый основной классификатор.",
        "updated_at": datetime.now().isoformat(timespec="seconds"),
        "groups": groups,
    }
    tmp = WORK_GROUPS_FILE + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)
        os.replace(tmp, WORK_GROUPS_FILE)
    except Exception as e:
        logger.error(f"Не удалось сохранить work_group_rules.json: {e}")


def _group_tokens(text):
    raw = re.findall(r"[a-zа-яё0-9]+", str(text or "").lower().replace("ё", "е"))
    out = set()
    endings = (
        "иями", "ями", "ами", "ого", "ему", "ому", "ыми", "ими", "ией",
        "иям", "ием", "иях", "ов", "ев", "ей", "ам", "ям", "ах", "ях",
        "ом", "ем", "ым", "им", "ую", "юю", "ою", "ею", "ая", "яя",
        "ое", "ее", "ие", "ые", "ого", "ему", "а", "я", "ы", "и",
        "у", "ю", "о", "е", "э", "ь", "й"
    )
    stopwords = {"из", "на", "по", "для", "при", "и", "от", "до", "с", "со", "в", "во", "к", "у", "а", "о", "не", "же"}
    for token in raw:
        if token.isdigit() or len(token) < 2 or token in stopwords:
            continue
        for ending in endings:
            if token.endswith(ending) and len(token) - len(ending) >= 4:
                token = token[:-len(ending)]
                break
        if len(token) >= 2:
            out.add(token)
    return out


def resolve_work_group(text, work_category, groups=None):
    """Возвращает ручное родительское правило, если текст/категория входит в заданную группу."""
    groups = groups or {}
    current = str(text or "").strip().lower()
    category = str(work_category or "").strip().lower()
    current_tokens = _group_tokens(current + " " + category)
    if not current and not category:
        return None

    best = None
    for parent, raw_rule in groups.items():
        rule = raw_rule if isinstance(raw_rule, dict) else {}
        verdict = str(rule.get("verdict", "")).strip()
        if not verdict:
            continue
        children = [str(x).strip() for x in rule.get("children", []) if str(x).strip()]
        keywords = [str(x).strip() for x in rule.get("keywords", []) if str(x).strip()]
        candidates = children + keywords + [str(parent).strip()]
        for candidate in candidates:
            cand_norm = re.sub(r"\s+", " ", candidate.lower()).strip()
            if not cand_norm:
                continue
            # Точное совпадение с категорией/фразой — максимальный приоритет.
            if category and (category == cand_norm or cand_norm in category or category in cand_norm):
                return {"group": parent, "verdict": verdict, "matched": candidate, "score": 1.0}
            if cand_norm in current:
                return {"group": parent, "verdict": verdict, "matched": candidate, "score": 0.98}
            cand_tokens = _group_tokens(cand_norm)
            matched_pairs = set()
            for ct in current_tokens:
                for wt in cand_tokens:
                    common = 0
                    for idx in range(min(len(ct), len(wt))):
                        if ct[idx] != wt[idx]:
                            break
                        common += 1
                    if ct == wt or common >= 5:
                        matched_pairs.add((ct, wt))
            overlap = len({ct for ct, _ in matched_pairs})
            if overlap == 0:
                continue
            precision = overlap / max(1, len(cand_tokens))
            recall = overlap / max(1, len(current_tokens))
            f1 = 2 * precision * recall / max(0.0001, precision + recall)
            # Для ручных подгрупп допускаем сильное совпадение фразы, но не одиночные общие слова.
            strong_single = overlap == 1 and (
                any(len(ct) >= 8 or len(wt) >= 8 for ct, wt in matched_pairs)
                or (len(cand_tokens) == 1 and all(ct == wt or ct.startswith(wt[:4]) or wt.startswith(ct[:4]) for ct, wt in matched_pairs))
            )
            score = f1
            if strong_single:
                score = max(score, 0.86)
            if len(cand_tokens) >= 2 and overlap >= 2:
                score = max(score, 0.92)
            if score >= 0.82 and (best is None or score > best["score"]):
                best = {"group": parent, "verdict": verdict, "matched": candidate, "score": score}
    return best


def generate_timestamped_filename(source_path: str) -> str:
    """Создаёт имя результата рядом с выбранным входным Excel."""
    source = os.path.abspath(source_path)
    name, ext = os.path.splitext(os.path.basename(source))
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    return os.path.join(os.path.dirname(source), f"{name}_результат_{timestamp}{ext or '.xlsx'}")


def workbench_sidecar_path(excel_path: str) -> str:
    base, _ = os.path.splitext(os.path.abspath(excel_path))
    return base + ".workbench.json"


@dataclass
class AppConfig:
    sap_mshost: str = field(default_factory=lambda: os.getenv('SAP_MSHOST', ''))
    sap_msserv: str = field(default_factory=lambda: os.getenv('SAP_MSSERV', '3601'))
    sap_sysid: str = field(default_factory=lambda: os.getenv('SAP_SYSID', ''))
    sap_group: str = field(default_factory=lambda: os.getenv('SAP_GROUP', ''))
    sap_client: str = field(default_factory=lambda: os.getenv('SAP_CLIENT', ''))
    sap_user: str = field(default_factory=lambda: os.getenv('SAP_USER', ''))
    sap_snc_lib: str = field(default_factory=lambda: os.getenv(
        'SAP_SNC_LIB',
        r'C:\Program Files\SAP\FrontEnd\SecureLogin\lib\sapcrypto.dll'
    ))
    sap_snc_partner: str = field(default_factory=lambda: os.getenv('SAP_SNC_PARTNER', ''))

    ai_api_key: str = field(default_factory=lambda: os.getenv('AI_API_KEY', ''))
    ai_base_url: str = field(default_factory=lambda: os.getenv('AI_BASE_URL', ''))
    ai_model: str = field(default_factory=lambda: os.getenv('AI_MODEL', 'default-model'))
    # Эскалация: второй, более сильный AI вызывается только если первый
    # не дал валидного классификационного ответа. Выбора модели в UI нет.
    ai_escalation_model: str = field(default_factory=lambda: os.getenv('AI_ESCALATION_MODEL', 'advanced-model'))
    ai_rps_limit: int = 5
    ai_max_retries: int = 3
    ai_timeout: int = 60

    sap_pool_size: int = 3
    max_workers: int = 5
    batch_save_interval: int = 100

    # Файлы выбираются через UI и сохраняются в настройках.
    target_excel: str = ""
    base_file: str = ""
    spare_file: str = ""
    stroy_file: str = ""
    output_excel: str = ""
    cache_file: str = field(default_factory=lambda: os.path.join(APP_DIR, 'order_cache.json'))
    detailed_json_output: str = ""
    review_session_file: str = field(default_factory=lambda: REVIEW_SESSION_FILE)
    few_shot_file: str = field(default_factory=lambda: os.path.join(APP_DIR, 'few_shot_examples.json'))
    classification_master_file: str = field(default_factory=lambda: CLASSIFICATION_MASTER_FILE)
    settings_file: str = SETTINGS_FILE
    column_mapping: Dict[str, str] = field(default_factory=dict)

    def __post_init__(self):
        self._load_settings()
        if not os.path.exists(self.sap_snc_lib):
            alternatives = [
                r"C:\SAP\FrontEnd\SecureLogin\lib\sapcrypto.dll",
                r"/usr/lib/sapcrypto.so",
            ]
            for alt in alternatives:
                if os.path.exists(alt):
                    self.sap_snc_lib = alt
                    break

    def _load_settings(self):
        if not os.path.exists(self.settings_file):
            return
        try:
            with open(self.settings_file, encoding="utf-8") as f:
                data = json.load(f)
            if not isinstance(data, dict):
                return
            for name in ("target_excel", "base_file", "spare_file", "stroy_file", "output_excel", "detailed_json_output", "review_session_file", "few_shot_file", "classification_master_file", "cache_file"):
                value = data.get(name)
                if isinstance(value, str):
                    setattr(self, name, value)
            mapping = data.get("column_mapping")
            if isinstance(mapping, dict):
                self.column_mapping = {str(k): str(v) for k, v in mapping.items() if v}
        except Exception as e:
            logger.warning(f"Не удалось загрузить настройки: {e}")

    def save_settings(self):
        payload = {
            "target_excel": self.target_excel,
            "base_file": self.base_file,
            "spare_file": self.spare_file,
            "stroy_file": self.stroy_file,
            "output_excel": self.output_excel,
            "detailed_json_output": self.detailed_json_output,
            "review_session_file": self.review_session_file,
            "few_shot_file": self.few_shot_file,
            "classification_master_file": self.classification_master_file,
            "cache_file": self.cache_file,
            "column_mapping": self.column_mapping,
            "updated_at": datetime.now().isoformat(timespec="seconds"),
        }
        try:
            tmp = self.settings_file + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(payload, f, ensure_ascii=False, indent=2)
            os.replace(tmp, self.settings_file)
        except Exception as e:
            logger.warning(f"Не удалось сохранить настройки: {e}")

    @property
    def has_ai_config(self) -> bool:
        return bool(self.ai_api_key)

    @property
    def has_sap_config(self) -> bool:
        return bool(self.sap_user)

    def get_sap_params(self) -> dict:
        if not self.sap_user:
            raise ValueError("SAP_USER не задан")
        return {
            'mshost': self.sap_mshost,
            'msserv': self.sap_msserv,
            'sysid': self.sap_sysid,
            'group': self.sap_group,
            'client': self.sap_client,
            'user': self.sap_user,
            'snc_mode': '1',
            'snc_qop': '3',
            'snc_lib': self.sap_snc_lib,
            'snc_partnername': self.sap_snc_partner,
        }


class ColoredFormatter(logging.Formatter):
    COLORS = {
        'DEBUG': '\033[36m',
        'INFO': '\033[32m',
        'WARNING': '\033[33m',
        'ERROR': '\033[31m',
        'CRITICAL': '\033[35m',
    }
    RESET = '\033[0m'
    
    def format(self, record):
        log_color = self.COLORS.get(record.levelname, self.RESET)
        record.levelname = f"{log_color}{record.levelname}{self.RESET}"
        return super().format(record)


def setup_logging(level: str = "INFO") -> logging.Logger:
    logger = logging.getLogger("ProcurementAudit")
    logger.setLevel(getattr(logging, level.upper()))
    
    for h in logger.handlers[:]:
        logger.removeHandler(h)
    
    console = logging.StreamHandler()
    console.setFormatter(ColoredFormatter(
        "%(asctime)s [%(levelname)s] %(name)s: %(message)s",
        datefmt="%H:%M:%S"
    ))
    logger.addHandler(console)
    
    return logger


APP_VERSION = "5.4.16"
AI_QUEUE_VERSION = "global-rps-v1"
CLASSIFIER_VERSION = "5.4.20-ai-first"
# Жёсткие regex-правила (мойка/ремонт/капстрой) больше НЕ ставят вердикт сами.
# Классификацию делает AI (+ ручные группы, если пользователь их завёл).
HARD_RULES_ASSIGN_VERDICT = False
# Версия кэша отдельно: смена UI не должна сбрасывать order_cache.json
CACHE_VERSION = "5.4-pre-podrtext"

logger = setup_logging()


class AdaptiveRateLimiter:
    """Глобальный ограничитель AI-запросов.

    Один экземпляр передаётся всем AI worker'ам. Скорость не разгоняется
    выше заданного ai_rps_limit, а 429/5xx не создают лавину параллельных retry.
    """
    def __init__(self, initial_rate: float, min_rate: float = 0.5):
        self.rate = max(float(initial_rate), min_rate)
        self.max_rate = self.rate
        self.min_rate = min_rate
        self.min_interval = 1.0 / self.rate
        self.last_time = 0.0
        self.error_count = 0
        self._lock = threading.Lock()

    def acquire(self, blocking: bool = True, timeout: Optional[float] = None) -> bool:
        start = time.monotonic()
        while True:
            with self._lock:
                now = time.monotonic()
                wait_time = max(0.0, self.min_interval - (now - self.last_time))
                if wait_time <= 0:
                    self.last_time = now
                    return True
            if not blocking:
                return False
            if timeout is not None:
                remaining = timeout - (time.monotonic() - start)
                if remaining <= 0:
                    return False
                wait_time = min(wait_time, remaining)
            time.sleep(wait_time)

    def report_success(self):
        with self._lock:
            self.error_count = max(0, self.error_count - 1)
            # Не разгоняемся выше установленного пользователем лимита.
            self.rate = min(self.rate, self.max_rate)
            self.min_interval = 1.0 / self.rate

    def report_error(self):
        with self._lock:
            self.error_count += 1
            if self.error_count >= 3:
                self.rate = max(self.min_rate, self.rate * 0.7)
                self.min_interval = 1.0 / self.rate
                self.error_count = 0

    def report_429(self):
        with self._lock:
            self.rate = max(self.min_rate, self.rate * 0.7)
            self.min_interval = 1.0 / self.rate
            self.error_count = 0


class SAPConnectionPool:
    def __init__(self, config: AppConfig, size: int):
        self.config = config
        self.size = size
        self._pool: queue.Queue = queue.Queue(maxsize=size)
        self._lock = threading.Lock()
        self._active = True
        self._fill_pool()
    
    def _create_connection(self) -> Connection:
        params = self.config.get_sap_params()
        return Connection(**params)
    
    def _fill_pool(self):
        for i in range(self.size):
            try:
                conn = self._create_connection()
                self._pool.put(conn)
                logger.info(f"SAP connection {i+1}/{self.size} created")
            except Exception as e:
                logger.error(f"Failed to create SAP connection: {e}")
                if self._pool.empty():
                    raise RuntimeError("Cannot create SAP connection pool")
    
    @contextlib.contextmanager
    def acquire(self, timeout: float = 30.0):
        conn = None
        try:
            conn = self._pool.get(timeout=timeout)
            try:
                conn.call('RFC_PING')
            except Exception:
                logger.warning("SAP connection stale, reconnecting...")
                try:
                    conn.close()
                except Exception:
                    pass
                conn = self._create_connection()
            yield conn
        finally:
            if conn is not None and self._active:
                try:
                    self._pool.put(conn, block=False)
                except queue.Full:
                    conn.close()
    
    def close_all(self):
        self._active = False
        while not self._pool.empty():
            try:
                conn = self._pool.get_nowait()
                conn.close()
            except Exception:
                pass
    
    def __enter__(self):
        return self
    
    def __exit__(self, *args):
        self.close_all()


class AIAssistantClient:
    def __init__(self, config: AppConfig, rate_limiter: Optional[AdaptiveRateLimiter] = None):
        self.config = config
        if not config.has_ai_config:
            raise ValueError("AI API key не задан")
        
        self.base_url = config.ai_base_url.rstrip("/")
        self.verify_ssl = False
        self.headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {config.ai_api_key}"
        }
        self.rate_limiter = rate_limiter or AdaptiveRateLimiter(config.ai_rps_limit)
        self._http_local = threading.local()
        self._circuit_failures = 0
        self._circuit_open_until: Optional[float] = None
    
    def _is_circuit_open(self) -> bool:
        if self._circuit_open_until is None:
            return False
        if time.time() > self._circuit_open_until:
            self._circuit_open_until = None
            self._circuit_failures = 0
            return False
        return True
    
    def chat_completion(
        self,
        messages: List[Dict[str, str]],
        model: Optional[str] = None,
        temperature: float = 0.1,
        max_tokens: int = 150,
        timeout: Optional[int] = None
    ) -> Optional[str]:
        
        if self._is_circuit_open():
            logger.warning("Circuit breaker open, skipping AI call")
            return None
        
        url = f"{self.base_url}/chat/completions"
        target_model = model or self.config.ai_model
        timeout = timeout or self.config.ai_timeout
        
        payload = {
            "model": target_model,
            "messages": messages,
            "temperature": temperature,
            "max_tokens": max_tokens,
            "stream": False
        }

        session = getattr(self._http_local, "session", None)
        if session is None:
            session = requests.Session()
            self._http_local.session = session

        for attempt in range(1, self.config.ai_max_retries + 1):
            try:
                self.rate_limiter.acquire()
                response = session.post(
                    url, headers=self.headers, json=payload,
                    timeout=timeout, verify=self.verify_ssl
                )
                
                if response.status_code == 200:
                    self.rate_limiter.report_success()
                    self._circuit_failures = 0
                    return response.json()["choices"][0]["message"]["content"]
                
                elif response.status_code == 429:
                    self.rate_limiter.report_429()
                    retry_after = response.headers.get("Retry-After", "")
                    try:
                        wait = min(float(retry_after), 60.0) if retry_after else min(2 ** attempt + random.uniform(0, 1), 30)
                    except Exception:
                        wait = min(2 ** attempt + random.uniform(0, 1), 30)
                    logger.warning(f"AI 429: общая очередь снижает темп, повтор через {wait:.1f}s")
                    time.sleep(wait)
                    continue
                    
                elif response.status_code >= 500:
                    self.rate_limiter.report_error()
                    self._circuit_failures += 1
                    if self._circuit_failures >= 5:
                        self._circuit_open_until = time.time() + 30
                        logger.error("Circuit breaker opened")
                        return None
                
                response.raise_for_status()
                
            except requests.exceptions.Timeout:
                logger.warning(f"AI timeout (attempt {attempt})")
            except Exception as e:
                logger.warning(f"AI error (attempt {attempt}): {e}")
            
            if attempt < self.config.ai_max_retries:
                delay = min(2 ** attempt, 30)
                time.sleep(delay)
        
        self._circuit_failures += 1
        return None


class ClassificationMasterStore:
    """Постоянный эталон ручной классификации.

    Excel остаётся рабочим результатом для людей. Этот JSON — внутреннее хранилище
    классификации: содержит строки текущих запусков и ОДИН подтверждённый эталон на
    каждую уникальную семантическую позицию. Номера заказов/позиций не являются ключом.
    """
    VERSION = 1

    def __init__(self, filepath: str):
        self.filepath = filepath or CLASSIFICATION_MASTER_FILE
        self.data = {"version": self.VERSION, "updated_at": None,
                     "rows": [], "confirmed_examples": {}}
        self._load()

    @staticmethod
    def semantic_key(item_name="", services=None):
        parts = []
        name = re.sub(r"\s+", " ", str(item_name or "").strip().lower().replace("ё", "е"))
        if name:
            parts.append(name)
        vals = []
        for x in services or []:
            if isinstance(x, dict):
                v = x.get("Наименование работ / материалов", "")
            else:
                v = x
            v = re.sub(r"\s+", " ", str(v or "").strip().lower().replace("ё", "е"))
            if v and v not in vals:
                vals.append(v)
        if vals:
            parts.append(" ||| ".join(vals))
        return " | ".join(parts)

    @classmethod
    def record_key(cls, rec):
        return cls.semantic_key(rec.get("item_name", ""), rec.get("services_and_materials", rec.get("services", [])))

    def _load(self):
        if not os.path.exists(self.filepath):
            return
        try:
            with open(self.filepath, encoding="utf-8") as f:
                raw = json.load(f)
            if isinstance(raw, dict):
                self.data.update(raw)
                if not isinstance(self.data.get("rows"), list):
                    self.data["rows"] = []
                if not isinstance(self.data.get("confirmed_examples"), dict):
                    self.data["confirmed_examples"] = {}
            logger.info(f"Loaded classification master: {len(self.data['rows'])} rows, {len(self.data['confirmed_examples'])} confirmed semantic examples")
        except Exception as e:
            logger.warning(f"Classification master load failed: {e}")

    def save(self):
        os.makedirs(os.path.dirname(self.filepath) or ".", exist_ok=True)
        self.data["version"] = self.VERSION
        self.data["updated_at"] = datetime.now().isoformat(timespec="seconds")
        tmp = self.filepath + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(self.data, f, ensure_ascii=False, indent=2, default=json_serialize_fallback)
        os.replace(tmp, self.filepath)

    def merge_run_rows(self, rows):
        """Сохраняет все данные позиций, но не создаёт duplicate few-shot examples."""
        by_id = {}
        for r in self.data.get("rows", []):
            if not isinstance(r, dict):
                continue
            key = (str(r.get("order_number", "")), str(r.get("item_number", "")),
                   str(r.get("reference_document", "")), str(r.get("cost_center", "")))
            by_id[key] = r
        for r in rows or []:
            if not isinstance(r, dict):
                continue
            key = (str(r.get("order_number", "")), str(r.get("item_number", "")),
                   str(r.get("reference_document", "")), str(r.get("cost_center", "")))
            by_id[key] = dict(r)
        self.data["rows"] = list(by_id.values())

    def apply_confirmed(self, rows):
        """Применяет уже подтверждённый эталон ко всем точным семантическим дублям."""
        changed = 0
        examples = self.data.get("confirmed_examples", {})
        for r in rows or []:
            key = self.record_key(r)
            ex = examples.get(key) if key else None
            if not ex:
                continue
            verdict = str(ex.get("verdict", "Не определено"))
            r["auto_verdict"] = verdict
            r["final_verdict"] = verdict
            r["verdict"] = verdict
            r["source"] = "master"
            r["reason"] = "Подтверждённый эталон из classification_master.json"
            r["checked"] = "Да"
            r["review_status"] = "Подтверждено по эталону"
            changed += 1
        return changed

    def confirm(self, selected_record, group_records, verdict, source="manual"):
        """Создаёт/обновляет ровно ОДИН эталон для семантической группы."""
        key = self.record_key(selected_record)
        if not key:
            return False
        ex = {
            "semantic_key": key,
            "verdict": verdict,
            "source": source,
            "confirmed_at": datetime.now().isoformat(timespec="seconds"),
            "item_name": selected_record.get("item_name", ""),
            "services_and_materials": selected_record.get("services_and_materials", []),
        }
        self.data.setdefault("confirmed_examples", {})[key] = ex
        # Все строки группы получают эталон в полном master-хранилище.
        for r in group_records or []:
            rk = self.record_key(r)
            if rk == key:
                r["master_verdict"] = verdict
                r["master_source"] = source
                r["master_confirmed_at"] = ex["confirmed_at"]
        self.save()
        return True

    def confirmed_examples(self):
        return list(self.data.get("confirmed_examples", {}).values())

class FewShotManager:
    """Семантические экспертные примеры без номеров заказов/СФ."""
    def __init__(self, filepath: str, max_examples: int = 100):
        self.filepath, self.max_examples = filepath, max_examples
        self._examples, self._access_times = [], {}
        self._token_cache = {}
        self._load()
        if not self._examples and not os.path.exists(self.filepath):
            self._create_seed()

    def _load(self):
        if not os.path.exists(self.filepath): return
        try:
            with open(self.filepath, "r", encoding="utf-8") as f:
                raw = json.load(f)
            if isinstance(raw, dict) and isinstance(raw.get("examples"), list):
                self._examples = raw["examples"]
            elif isinstance(raw, list):
                self._examples = raw
            now = time.time()
            for ex in self._examples:
                key = str(ex.get("text", ""))
                if key:
                    self._access_times[key] = float(ex.get("last_used", now))
            logger.info(f"Loaded {len(self._examples)} few-shot examples")
        except Exception as e:
            logger.warning(f"Few-shot load failed: {e}")
            self._examples = []
        self._token_cache = {str(ex.get("text", "")): self._match_tokens(ex.get("text", "")) for ex in self._examples}

    def _create_seed(self):
        seeds = [
            {
                "text": "Название позиции SAP: Мойка нержавеющая двухсекционная | Состав позиции SAP: Мойка нержавеющая двухсекционная ||| Монтаж мойки ||| Подключение воды ||| Крепёж",
                "verdict": "Оборудование", "source": "seed_rule", "classifier_version": CLASSIFIER_VERSION, "last_used": time.time(), "active": True
            },
            {
                "text": "Название позиции SAP: Ремонт тестораскаточной машины | Состав позиции SAP: Диагностика ||| Замена детали ||| Настройка",
                "verdict": "Ремонт ОС", "source": "seed_rule", "classifier_version": CLASSIFIER_VERSION, "last_used": time.time(), "active": True
            }
        ]
        self._examples = seeds
        self._access_times = {str(x["text"]): float(x.get("last_used", time.time())) for x in seeds}
        self._token_cache = {str(x.get("text", "")): self._match_tokens(x.get("text", "")) for x in seeds}
        self.save()

    def save(self):
        payload={"version":2,"description":"Семантические экспертные примеры без идентификаторов заказов.","examples":self._examples}
        tmp=self.filepath+".tmp"
        try:
            with open(tmp,"w",encoding="utf-8") as f: json.dump(payload,f,ensure_ascii=False,indent=2,default=json_serialize_fallback)
            os.replace(tmp,self.filepath)
        except Exception as e: logger.error(f"Failed to save few-shot: {e}")

    def fingerprint(self) -> str:
        """Стабильный отпечаток содержимого Few-shot, влияющего на классификацию.

        Намеренно не учитывает last_used/source/classifier_version: служебные
        изменения не должны заставлять заново классифицировать весь файл.
        Учитываются текст, вердикт и active — то есть реальные изменения
        эталонных данных.
        """
        material = []
        for ex in self._examples:
            if not isinstance(ex, dict):
                continue
            material.append({
                "text": re.sub(r"\s+", " ", str(ex.get("text", "")).strip()),
                "verdict": str(ex.get("verdict", "")).strip(),
                "active": bool(ex.get("active", True)),
            })
        material.sort(key=lambda x: (x["text"].lower(), x["verdict"], x["active"]))
        raw = json.dumps(material, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        return hashlib.sha256(raw.encode("utf-8")).hexdigest()

    def add(self,text:str,verdict:str,source:str="manual_validation"):
        text=re.sub(r"\s+"," ",str(text).strip())
        if not text or not verdict: return
        now=time.time()
        idx=next((i for i,x in enumerate(self._examples) if str(x.get("text","")).lower()==text.lower()),None)
        rec={"text":text[:2000],"verdict":verdict,"source":source,"classifier_version":CLASSIFIER_VERSION,"last_used":now,"active":True}
        if idx is None: self._examples.append(rec)
        else: self._examples[idx]=rec
        self._access_times[text]=now
        self._token_cache[text] = self._match_tokens(text)
        if len(self._examples)>self.max_examples:
            self._examples.sort(key=lambda x:float(x.get("last_used",0)))
            self._examples=self._examples[-self.max_examples:]
            self._token_cache = {str(x.get("text", "")): self._token_cache.get(str(x.get("text", "")), self._match_tokens(x.get("text", ""))) for x in self._examples}
        self.save()

    _MATCH_STOPWORDS = {
        "название", "позиции", "позиция", "sap", "состав", "работы", "работа",
        "услуги", "услуга", "материалы", "материал", "ремонт", "замена",
        "монтаж", "подключение", "обслуживание", "обслуживанию", "диагностика",
        "настройка", "крепёж", "крепеж", "установка", "демонтаж", "проверка",
        "текущий", "техническое", "технический", "оборудование", "деталь",
        "детали", "шт", "мм", "см", "м", "м2", "м3", "руб", "россия",
    }

    @staticmethod
    def _stem_for_match(token: str) -> str:
        token = token.lower().replace("ё", "е")
        token = re.sub(r"[^a-zа-я0-9]+", "", token)
        if len(token) <= 4:
            return token
        endings = (
            "иями", "ями", "ами", "ого", "ему", "ому", "ыми", "ими", "ией",
            "иям", "ием", "иях", "ов", "ев", "ей", "ам", "ям", "ах", "ях",
            "ом", "ем", "ым", "им", "ую", "юю", "ою", "ею", "ая", "яя",
            "ое", "ее", "ие", "ые", "ого", "ему", "ами", "ями", "ов", "ев",
            "а", "я", "ы", "и", "у", "ю", "о", "е", "э", "ь", "й", "ом", "ем"
        )
        for ending in endings:
            if token.endswith(ending) and len(token) - len(ending) >= 4:
                return token[:-len(ending)]
        return token

    @classmethod
    def _match_tokens(cls, text: str):
        raw = re.findall(r"[a-zа-яё0-9]+", str(text or "").lower())
        out = set()
        for token in raw:
            stem = cls._stem_for_match(token)
            if len(stem) < 4 or stem in cls._MATCH_STOPWORDS:
                continue
            if stem.isdigit():
                continue
            out.add(stem)
        return out

    def best_semantic_match(self, text: str, min_score: float = 0.55):
        """Возвращает лучший Few-shot пример по содержанию, а не по заказу/позиции.

        Для коротких экспертных примеров допускается полное совпадение их ключевых слов,
        поэтому «контроллер», «контроллера», «контроллеры» считаются одной семантической группой.
        """
        current = self._match_tokens(text)
        if not current:
            return None
        best = None
        for ex in self._examples:
            if not bool(ex.get("active", True)):
                continue
            ex_text = str(ex.get("text", ""))
            ex_tokens = self._token_cache.get(ex_text)
            if ex_tokens is None:
                ex_tokens = self._match_tokens(ex_text)
                self._token_cache[ex_text] = ex_tokens
            if not ex_tokens:
                continue
            overlap = len(current & ex_tokens)
            if overlap == 0:
                continue
            recall = overlap / max(1, len(ex_tokens))
            precision = overlap / max(1, len(current))
            f1 = 2 * recall * precision / (recall + precision) if (recall + precision) else 0.0
            containment = overlap / max(1, min(len(ex_tokens), len(current)))
            # Для экспертного Few-shot важен объект работы: если все ключевые слова
            # короткого текущего описания входят в эталон («контроллер», «насос» и т.п.),
            # считаем это семантическим совпадением даже при более подробном тексте эталона.
            score = max(f1, containment * 0.95)
            # Для производных одного и того же объекта («контроллер», «контроллеры»,
            # «контроллера платы») достаточно одного сильного доменного ключа.
            if overlap >= 1 and any(len(tok) >= 7 for tok in (current & ex_tokens)):
                score = max(score, 0.85)
            if best is None or score > best["score"]:
                best = {"example": ex, "score": score, "overlap": sorted(current & ex_tokens)}
        if best and best["score"] >= min_score:
            return best
        return None

    def get_relevant_prompt_addon(self, text: str, count: int = 6) -> str:
        match = self.best_semantic_match(text, min_score=0.55)
        if not match:
            return ""
        ex = match["example"]
        self._access_times[str(ex.get("text", ""))] = time.time()
        body = (
            "\n\n=== РЕЛЕВАНТНЫЙ ПОДТВЕРЖДЁННЫЙ FEW-SHOT ===\n"
            f"Пример: {str(ex.get('text',''))[:2000]}\n"
            f"Вердикт примера: {ex.get('verdict','')}\n"
            "Используй этот пример как приоритетную аналогию по содержанию работ/материалов. "
            "Если текущая позиция действительно совпадает по смыслу, сохраняй тот же вердикт. "
            "Не учитывай номера заказа, позиции, СФ или МВЗ.\n"
            "=== КОНЕЦ РЕЛЕВАНТНОГО FEW-SHOT ===\n"
        )
        return body

    def load_confirmed_master(self, master_store):
        """Первичное заполнение Few-shot из classification_master.

        После появления few_shot_examples.json файл — единственный источник правды:
        даже пустой список (после «Сброс всех эталонов») НЕ восстанавливается из master.
        Master подмешивается только если файла ещё никогда не было.
        """
        if not master_store:
            return
        # Файл существует → пользователь/сброс уже управляет few-shot; master не трогаем.
        if os.path.exists(self.filepath):
            return
        confirmed = master_store.confirmed_examples()
        if not confirmed:
            return
        existing = {str(x.get("text", "")).lower(): x for x in self._examples}
        for ex in confirmed:
            item_name = str(ex.get("item_name", "") or "").strip()
            text = build_semantic_text(item_name, ex.get("services_and_materials") or [])
            if not text:
                continue
            key = text.lower()
            if key in existing:
                continue
            rec = {"text": text[:7000], "verdict": ex.get("verdict", "Не определено"),
                   "source": "classification_master", "classifier_version": CLASSIFIER_VERSION,
                   "last_used": time.time(), "active": True}
            self._examples.append(rec)
            existing[key] = rec
        self._token_cache = {str(x.get("text", "")): self._match_tokens(x.get("text", "")) for x in self._examples}
        if self._examples:
            self.save()

    def get_prompt_addon(self,count:int=25)->str:
        if not self._examples: return ""
        examples=sorted((x for x in self._examples if bool(x.get("active", True))),key=lambda x:float(x.get("last_used",0)),reverse=True)[:count]
        body="\n".join(f"- {str(x.get('text',''))[:600]} → {x.get('verdict','')}" for x in examples)
        return "\n\n=== ПОДТВЕРЖДЁННЫЕ ЭКСПЕРТОМ СЕМАНТИЧЕСКИЕ ПРИМЕРЫ ===\n"+body+"\nИспользуй их только как аналогию по содержанию работ/материалов.\n=== КОНЕЦ ПРИМЕРОВ ===\n"

    def get_stats(self)->Dict[str,int]:
        from collections import Counter
        counts = dict(Counter(x.get("verdict","Unknown") for x in self._examples))
        counts["Активные"] = sum(1 for x in self._examples if bool(x.get("active", True)))
        counts["Исключены"] = sum(1 for x in self._examples if not bool(x.get("active", True)))
        return counts


def load_excel_column_as_set(excel_path: str, possible_col_names: Optional[list] = None) -> set:
    if not os.path.exists(excel_path):
        logger.warning(f"File not found: {excel_path}")
        return set()
    try:
        df_base = pd.read_excel(excel_path)
        for col in possible_col_names or []:
            if col in df_base.columns:
                result = set(df_base[col].dropna().astype(str).str.strip().str.lower().tolist())
                logger.info(f"Loaded {len(result)} items from {excel_path}[{col}]")
                return result
        for col in df_base.columns:
            if df_base[col].dtype == 'object':
                result = set(df_base[col].dropna().astype(str).str.strip().str.lower().tolist())
                logger.info(f"Loaded {len(result)} items from {excel_path}[{col}] (fallback)")
                return result
    except Exception as e:
        logger.error(f"Ошибка загрузки справочника {excel_path}: {e}")
    return set()


def load_spare_parts_set(excel_path: str) -> set:
    if not os.path.exists(excel_path):
        logger.warning(f"File not found: {excel_path}")
        return set()
    try:
        xls = pd.ExcelFile(excel_path)
        items = set()
        for sheet in xls.sheet_names:
            df_sheet = pd.read_excel(excel_path, sheet_name=sheet)
            for col in df_sheet.columns:
                if df_sheet[col].dtype == 'object':
                    for val in df_sheet[col].dropna().astype(str):
                        cleaned = val.strip().lower()
                        if cleaned and not cleaned.startswith(('приложение', 'существенные', 'ос/зап', 'отклонить', 'наименование')):
                            items.add(cleaned)
        logger.info(f"Loaded {len(items)} items from spare parts workbook {excel_path}")
        return items
    except Exception as e:
        logger.error(f"Ошибка загрузки справочника запчастей {excel_path}: {e}")
        return set()


def load_stroy_equipment_set(excel_path: str) -> set:
    if not os.path.exists(excel_path):
        logger.warning(f"File not found: {excel_path}")
        return set()
    try:
        df = pd.read_excel(excel_path, header=None)
        items = set()
        if len(df) > 4:
            for val in df.iloc[4:, 0].dropna():
                cleaned = str(val).strip().replace('·', '').strip().lower()
                if cleaned and cleaned != 'название ос':
                    items.add(cleaned)
        logger.info(f"Loaded {len(items)} items from {excel_path} (строительное оборудование)")
        return items
    except Exception as e:
        logger.error(f"Ошибка загрузки справочника строй-оборудования {excel_path}: {e}")
        return set()


OS_PATTERNS = [
    re.compile(r"мойк[а-я]*\s+нерж", re.IGNORECASE),
    re.compile(r"розетк[а-я]*.*механическ[а-я]*\s+таймер", re.IGNORECASE),
    re.compile(r"водонагреват[а-я]*", re.IGNORECASE)
]
# Жёсткие правила: только однозначные случаи. Широкие слова («кофемашина»)
# без контекста ремонта больше НЕ дают вердикт — иначе уводят закупку в «Ремонт ОС».
EQUIPMENT_PATTERNS = [
    re.compile(r"\bмойк[а-яё]*\b.*\bнерж", re.IGNORECASE),
    re.compile(r"\bмойк[а-яё]*\b.*\bнержав", re.IGNORECASE),
    re.compile(r"\bнерж[а-яё.]*\b.*\bмойк[а-яё]*\b", re.IGNORECASE),
]
CAPITAL_PATTERNS = [
    re.compile(r"\bкапитальн[а-яё]*\s+строит", re.IGNORECASE),
    re.compile(r"\bреконструкц[а-яё]*\b", re.IGNORECASE),
]
# Объект ОС — только вместе с явным признаком ремонта/обслуживания.
_REPAIR_CONTEXT = re.compile(
    r"(?:\bремонт\b|\bобслуживан|\bТО\b|\bтех\.?\s*обслуж|\bдиагност|\bналадк|"
    r"\bзамен[а-яё]*\s+(?:детал|узл|комплект|плат|контроллер|двигател|насос))",
    re.IGNORECASE,
)
_REPAIR_OS_OBJECTS = [
    re.compile(r"тестораскат", re.IGNORECASE),
    re.compile(r"кофемашин", re.IGNORECASE),
    re.compile(r"холодильн[а-яё]*\s+оборуд", re.IGNORECASE),
    re.compile(r"\bпечь\b|\bпечи\b|\bшкаф\s+пекар", re.IGNORECASE),
]


def _report_text(report_df: pd.DataFrame) -> str:
    if report_df is None or report_df.empty:
        return ""
    cols = [c for c in ("Название позиции заказа", "Наименование работ / материалов") if c in report_df.columns]
    return " | ".join(str(v).strip() for c in cols for v in report_df[c].dropna().tolist()).lower()


def extract_rule_decision(report_df: pd.DataFrame):
    """Возвращает (вердикт, краткое основание) для детерминированного правила.

    Срабатывает только на узких, однозначных паттернах. Excel-справочники
    (стройка/запчасти/оборудование) здесь вердикт НЕ ставят — они только
    помечают строки в отчёте для AI/оператора.
    """
    text = _report_text(report_df)
    if not text:
        return None, None

    for p in CAPITAL_PATTERNS:
        m = p.search(text)
        if m:
            return (
                VerdictCategory.SKIP.value,
                f"Жёсткое правило: капитальное строительство / реконструкция («{m.group(0)}»)",
            )

    for p in EQUIPMENT_PATTERNS:
        m = p.search(text)
        if m:
            return (
                VerdictCategory.EQUIPMENT.value,
                f"Жёсткое правило: мойка из нержавеющей стали («{m.group(0)}»)",
            )

    # Ремонт ОС: нужен И объект, И контекст ремонта/обслуживания.
    has_repair_ctx = bool(_REPAIR_CONTEXT.search(text))
    if has_repair_ctx:
        for p in _REPAIR_OS_OBJECTS:
            m = p.search(text)
            if m:
                return (
                    VerdictCategory.REPAIR_OS.value,
                    f"Жёсткое правило: ремонт ОС — объект «{m.group(0)}» + контекст ремонта/ТО",
                )

    return None, None


def extract_rule_verdict(report_df: pd.DataFrame) -> Optional[str]:
    return extract_rule_decision(report_df)[0]



def ensure_output_columns(df: pd.DataFrame) -> pd.DataFrame:
    """Создаёт служебные поля, необходимые рабочему месту."""
    columns = {
        "Авто вердикт": None,
        "Вердикт ИИ": None,
        "Счет": None,
        "Источник": None,
        "Проверено": "Нет",
        "Название позиции SAP": None,
        "Состав позиции SAP": None,
        "Основание решения": None,
        "Категория работы": None,
    }
    for col, default in columns.items():
        if col not in df.columns:
            df[col] = default
    return df



def build_clean_service_report(
    data, 
    fast_build_set, 
    spare_parts_set, 
    stroy_equipment_set, 
    target_item: Optional[str] = None, 
    target_costcenter: Optional[str] = None
):
    items = data['items']
    services = data['services']
    srv_acc = data['srv_acc']
    po_account = data['po_account']

    if services.empty or items.empty:
        return pd.DataFrame()

    items['PO_ITEM'] = items['PO_ITEM'].astype(str).str.strip().str.zfill(5)
    item_names = items[['PO_ITEM', 'SHORT_TEXT']].rename(columns={'SHORT_TEXT': 'PO_NAME'})

    services['SHORT_TEXT'] = services['SHORT_TEXT'].str.strip()
    valid_srv = services[services['SHORT_TEXT'] != ''].copy()

    valid_srv['PCKG_NO'] = valid_srv['PCKG_NO'].astype(str).str.strip()
    valid_srv['LINE_NO'] = valid_srv['LINE_NO'].astype(str).str.strip()
    
    default_po_item = str(items['PO_ITEM'].iloc[0]).strip().zfill(5) if not items.empty else '00010'

    if 'PNT_LINE' in valid_srv.columns:
        valid_srv['PO_ITEM'] = valid_srv['PNT_LINE'].astype(str).str.strip().str.zfill(5)
    else:
        valid_srv['PO_ITEM'] = default_po_item
        
    valid_po_items = set(item_names['PO_ITEM'].values)
    valid_srv['PO_ITEM'] = valid_srv['PO_ITEM'].apply(
        lambda x: str(x).strip().zfill(5) if str(x).strip().zfill(5) in valid_po_items else default_po_item
    )

    if not srv_acc.empty:
        srv_acc['PCKG_NO'] = srv_acc['PCKG_NO'].astype(str).str.strip()
        srv_acc['LINE_NO'] = srv_acc['LINE_NO'].astype(str).str.strip()
        
        merged = pd.merge(
            valid_srv, srv_acc, on=['PCKG_NO', 'LINE_NO'],
            how='left', suffixes=('', '_acc')
        )
    else:
        merged = valid_srv.copy()
        if 'SERIAL_NO' not in merged.columns:
            merged['SERIAL_NO'] = '01'

    merged['SERIAL_NO'] = merged['SERIAL_NO'].astype(str).str.strip().str.zfill(2)

    if not po_account.empty:
        po_account['PO_ITEM'] = po_account['PO_ITEM'].astype(str).str.strip().str.zfill(5)
        po_account['SERIAL_NO'] = po_account['SERIAL_NO'].astype(str).str.strip().str.zfill(2)
        
        acc_subset = po_account.drop_duplicates()
        merged = pd.merge(
            merged, acc_subset, on=['PO_ITEM', 'SERIAL_NO'],
            how='left', suffixes=('', '_po_acc')
        )

    if target_costcenter:
        target_cc_str = str(target_costcenter).strip()
        cc_col = None
        for col in ['COSTCENTER', 'COST_CTR', 'MWSKZ', 'KOSTL']:
            if col in merged.columns:
                cc_col = col
                break
        if cc_col:
            merged[cc_col] = merged[cc_col].astype(str).str.strip().str.lstrip('0')
            target_cc_clean = target_cc_str.lstrip('0')
            merged = merged[merged[cc_col] == target_cc_clean]

    merged = pd.merge(merged, item_names, on='PO_ITEM', how='left')
    
    def classify_item(text):
        if pd.isna(text):
            return 'Нет', 'Нет'
        text_str = str(text).strip().lower()
        is_fast = text_str in fast_build_set
        is_os = any(pattern.search(text_str) for pattern in OS_PATTERNS)
        return 'Да' if is_fast else 'Нет', 'Да' if is_os else 'Нет'
    
    classifications = merged['SHORT_TEXT'].apply(classify_item)
    merged['IS_FAST_BUILD'] = [c[0] for c in classifications]
    merged['IS_OS_EQUIP'] = [c[1] for c in classifications]

    display_cols = [
        'PO_ITEM', 'PO_NAME', 'LINE_NO', 'SHORT_TEXT', 
        'QUANTITY', 'UOM_ISO', 'NET_VALUE', 'GL_ACCOUNT', 'WBS_ELEMENT', 
        'IS_FAST_BUILD', 'IS_OS_EQUIP'
    ]
    
    existing_cols = [c for c in display_cols if c in merged.columns]
    report_df = merged[existing_cols].copy()
    
    report_df.rename(columns={
        'PO_ITEM': 'Поз',
        'PO_NAME': 'Название позиции заказа',
        'LINE_NO': 'Стр',
        'SHORT_TEXT': 'Наименование работ / материалов',
        'QUANTITY': 'Кол-во',
        'UOM_ISO': 'Ед',
        'NET_VALUE': 'Сумма',
        'GL_ACCOUNT': 'Счет',
        'WBS_ELEMENT': 'СПП-элемент',
        'IS_FAST_BUILD': 'Быстрая стройка',
        'IS_OS_EQUIP': 'Оборудование ОС'
    }, inplace=True)

    if target_item:
        target_str = str(int(float(target_item))).strip().zfill(5) if pd.notna(target_item) else None
        if target_str and target_str in report_df['Поз'].values:
            report_df = report_df[report_df['Поз'] == target_str].copy()

    return report_df


def safe_save_excel(df: pd.DataFrame, target_path: str):
    dir_name=os.path.dirname(target_path) or "."
    base_name=os.path.basename(target_path)
    tmp_path=os.path.join(dir_name,f".~{base_name}.{os.getpid()}.{threading.get_ident()}.tmp.xlsx")
    backup_path=os.path.join(dir_name,f"~bak_{base_name}")
    try:
        df.to_excel(tmp_path,index=False,engine="openpyxl")
        if os.path.exists(target_path):
            if os.path.exists(backup_path): os.remove(backup_path)
            shutil.copy2(target_path,backup_path)
        os.replace(tmp_path,target_path)
        if os.path.exists(backup_path): os.remove(backup_path)
        logger.info(f"Saved {target_path} ({len(df)} rows)")
    except Exception as e:
        if os.path.exists(tmp_path):
            try: os.remove(tmp_path)
            except Exception: pass
        if os.path.exists(backup_path) and not os.path.exists(target_path):
            try: os.replace(backup_path,target_path)
            except Exception: pass
        raise RuntimeError(f"Failed to save {target_path}: {e}")


def load_column_aliases() -> dict:
    """Загружает пользовательские подсказки для автоматического определения колонок."""
    if not os.path.exists(COLUMN_ALIASES_FILE):
        try:
            with open(COLUMN_ALIASES_FILE, "w", encoding="utf-8") as f:
                json.dump({"order": [], "item": [], "ref": [], "mvz": []}, f, ensure_ascii=False, indent=2)
        except Exception:
            pass
        return {}
    try:
        with open(COLUMN_ALIASES_FILE, encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception as e:
        logger.warning(f"Не удалось загрузить column_aliases.json: {e}")
        return {}


class ColumnMappingDialog:
    ROLES = [
        ("order", "Заказ / документ закупки", True),
        ("item", "Позиция", True),
        ("ref", "СФ / ссылка", False),
        ("mvz", "МВЗ / центр затрат", False),
    ]

    def __init__(self, parent, columns, current_mapping):
        self.top = tk.Toplevel(parent)
        self.top.title("Настройка колонок Excel")
        self.top.geometry("620x300")
        self.top.transient(parent)
        self.top.grab_set()
        self.columns = list(columns)
        self.mapping = dict(current_mapping or {})
        self.result = None
        self.vars = {}
        self._build()
        self._suggest()
        self.top.protocol("WM_DELETE_WINDOW", self._cancel)

    def _build(self):
        tk.Label(self.top, text="Настройка структуры входного Excel", font=("Segoe UI", 13, "bold")).pack(anchor="w", padx=12, pady=10)
        tk.Label(self.top, text="Выбери колонки. Заказ и позиция обязательны; СФ и МВЗ можно оставить пустыми.", justify=tk.LEFT).pack(anchor="w", padx=12, pady=(0, 10))
        box = tk.Frame(self.top)
        box.pack(fill=tk.BOTH, expand=True, padx=12)
        for row, (key, label, required) in enumerate(self.ROLES):
            tk.Label(box, text=("* " if required else "  ") + label, width=28, anchor="w").grid(row=row, column=0, sticky="w", pady=5)
            var = tk.StringVar()
            self.vars[key] = var
            ttk.Combobox(box, textvariable=var, values=[""] + self.columns, state="readonly", width=48).grid(row=row, column=1, sticky="ew", pady=5)
        box.columnconfigure(1, weight=1)
        buttons = tk.Frame(self.top)
        buttons.pack(fill=tk.X, padx=12, pady=12)
        tk.Button(buttons, text="Сохранить", command=self._save, bg="#16a34a", fg="white", relief="flat", padx=14, pady=6).pack(side=tk.LEFT)
        tk.Button(buttons, text="Отмена", command=self._cancel, bg="#64748b", fg="white", relief="flat", padx=14, pady=6).pack(side=tk.RIGHT)

    def _suggest(self):
        aliases = load_column_aliases()
        lower_cols = {str(c).strip().lower(): c for c in self.columns}
        for key, _, _ in self.ROLES:
            current = self.mapping.get(key, "")
            if current in self.columns:
                self.vars[key].set(current)
                continue
            found = None
            for alias in aliases.get(key, []):
                found = next((original for low, original in lower_cols.items() if str(alias).lower() in low), None)
                if found is not None:
                    break
            self.vars[key].set(found or "")

    def _save(self):
        result = {key: self.vars[key].get().strip() for key, _, _ in self.ROLES}
        missing = [label for key, label, required in self.ROLES if required and not result.get(key)]
        if missing:
            messagebox.showwarning("Колонки", "Не выбраны обязательные колонки:\n\n" + "\n".join(missing), parent=self.top)
            return
        self.result = result
        self.top.destroy()

    def _cancel(self):
        self.result = None
        self.top.destroy()


class _LegacyClassificationReview:
    """Полноценное рабочее место ручной проверки автоматической классификации.

    Источник данных — review_session.json с SAP-детализацией текущего запуска.
    Результирующий Excel используется только для записи итогов, а не для наполнения карточки.
    """
    VERDICTS = [
        "Не определено", "Быстрая стройка", "Быстрая стройка + ОС",
        "Оборудование", "Ремонт ОС", "ПРОПУСК"
    ]
    VERDICT_KEYS = {
        "1": "Быстрая стройка",
        "2": "Быстрая стройка + ОС",
        "3": "Оборудование",
        "4": "Ремонт ОС",
        "5": "ПРОПУСК",
        "0": "Не определено",
    }

    def __init__(self, parent, app, records=None):
        """Базовая инициализация; UI строится через _build_ui() наследника."""
        self.parent = parent
        self.app = app
        self.config = app.config
        self.records = records if records is not None else list(getattr(app, "review_records", []))
        self.master = ClassificationMasterStore(self.config.classification_master_file)
        self.few_shot = FewShotManager(self.config.few_shot_file)
        try:
            self.few_shot.load_confirmed_master(self.master)
        except Exception:
            pass
        self.work_categories = load_work_categories()
        self.selected_idx = None
        self.ai_busy = False
        if not hasattr(self, "auto_next"):
            self.auto_next = tk.BooleanVar(value=True)
        self._fewshot_match_cache = getattr(self, "_fewshot_match_cache", {})
        self.top = tk.Toplevel(parent)
        self.top.title(f"Проверка классификации — Procurement AI Auditor {APP_VERSION}")
        self.top.geometry("1780x1000")
        self.top.minsize(1320, 820)
        self.top.bind("<Key>", self._on_key)
        self._build_ui()
        # Окно показываем сразу; тяжёлый refresh — idle, чтобы UI не «висел».
        if hasattr(self, "header_info"):
            try:
                self.header_info.config(text=f"Загрузка {len(self.records):,} позиций…".replace(",", " "))
            except Exception:
                pass
        self.top.after(20, self._deferred_first_refresh)

    def _deferred_first_refresh(self):
        try:
            self.top.config(cursor="watch")
        except Exception:
            pass
        try:
            self._refresh_all(keep_selection=False)
            try:
                self._focus_unchecked()
            except Exception:
                pass
        finally:
            try:
                self.top.config(cursor="")
            except Exception:
                pass

    # ---------------- shared helpers / few-shot ----------------
    def _build_fewshot_tab(self):
        top = tk.Frame(self.fewshot_tab, padx=10, pady=8)
        top.pack(fill=tk.X)
        tk.Label(top, text="Поиск: ").pack(side=tk.LEFT)
        self.fs_search = tk.StringVar()
        self.fs_search.trace_add("write", lambda *_: self._refresh_fewshot_list())
        tk.Entry(top, textvariable=self.fs_search, width=46).pack(side=tk.LEFT, padx=5)
        self.fs_stats = tk.Label(top, text="", fg="#475569")
        self.fs_stats.pack(side=tk.LEFT, padx=15)
        tk.Button(top, text="Новый пример", command=self._clear_fewshot_editor, bg="#2563eb", fg="white", relief="flat", padx=10, pady=5).pack(side=tk.RIGHT)

        main = ttk.PanedWindow(self.fewshot_tab, orient=tk.HORIZONTAL)
        main.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        left, right = ttk.Frame(main), ttk.Frame(main)
        main.add(left, weight=6)
        main.add(right, weight=5)
        self.fs_tree = ttk.Treeview(left, columns=("verdict", "source", "text"), show="headings", selectmode="browse")
        for c, t in (("verdict", "Вердикт"), ("source", "Источник"), ("text", "Семантический пример")):
            self.fs_tree.heading(c, text=t)
        self.fs_tree.column("verdict", width=190)
        self.fs_tree.column("source", width=130)
        self.fs_tree.column("text", width=700)
        sc = ttk.Scrollbar(left, orient=tk.VERTICAL, command=self.fs_tree.yview)
        self.fs_tree.configure(yscrollcommand=sc.set)
        self.fs_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sc.pack(side=tk.RIGHT, fill=tk.Y)
        self.fs_tree.bind("<<TreeviewSelect>>", self._on_fewshot_select)

        ed = ttk.LabelFrame(right, text="Пример", padding=8)
        ed.pack(fill=tk.BOTH, expand=True)
        tk.Label(ed, text="Содержание работ / услуг / материалов:", anchor="w").pack(fill=tk.X, pady=(0, 4))
        self.fs_text = scrolledtext.ScrolledText(ed, height=20, wrap=tk.WORD, font=("Consolas", 9))
        self.fs_text.pack(fill=tk.BOTH, expand=True)
        rr = tk.Frame(ed)
        rr.pack(fill=tk.X, pady=6)
        tk.Label(rr, text="Вердикт:").pack(side=tk.LEFT)
        self.fs_verdict = tk.StringVar()
        ttk.Combobox(rr, textvariable=self.fs_verdict, values=self.VERDICTS[1:], state="readonly", width=27).pack(side=tk.LEFT, padx=6)
        tk.Label(rr, text="Источник:").pack(side=tk.LEFT, padx=(10, 3))
        self.fs_source = tk.StringVar(value="manual")
        tk.Entry(rr, textvariable=self.fs_source, width=18).pack(side=tk.LEFT)
        self.fs_active = tk.BooleanVar(value=True)
        tk.Checkbutton(rr, text="Участвует в AI", variable=self.fs_active).pack(side=tk.LEFT, padx=10)
        br = tk.Frame(ed)
        br.pack(fill=tk.X)
        tk.Button(br, text="Сохранить пример", command=self._save_fewshot, bg="#16a34a", fg="white", relief="flat", padx=10, pady=5).pack(side=tk.LEFT, padx=2)
        tk.Button(br, text="Исключить / включить", command=self._toggle_fewshot, bg="#d97706", fg="white", relief="flat", padx=10, pady=5).pack(side=tk.LEFT, padx=2)
        tk.Button(br, text="Удалить", command=self._delete_fewshot, bg="#dc2626", fg="white", relief="flat", padx=10, pady=5).pack(side=tk.LEFT, padx=2)
        tk.Button(br, text="Очистить", command=self._clear_fewshot_editor, bg="#64748b", fg="white", relief="flat", padx=10, pady=5).pack(side=tk.LEFT, padx=2)
        self._refresh_fewshot_list()

    # ---------------- filtering / grouping ----------------
    @staticmethod
    def _norm(v):
        if v is None:
            return ""
        return str(v).strip()

    def _service_list(self, rec):
        if not isinstance(rec, dict):
            return []
        cached = rec.get("_svc_list")
        if isinstance(cached, list):
            return cached
        vals = []
        for item in rec.get("services_and_materials") or rec.get("services") or []:
            if isinstance(item, dict):
                val = item.get("Наименование работ / материалов") or item.get("SHORT_TEXT") or item.get("PO_NAME") or ""
            else:
                val = item
            val = self._norm(val)
            if val and val not in vals:
                vals.append(val)
        if not vals and self._norm(rec.get("item_name")):
            vals = [self._norm(rec.get("item_name"))]
        rec["_svc_list"] = vals
        return vals

    def _work_labels(self, rec):
        if not isinstance(rec, dict):
            return []
        cached = rec.get("_work_labels")
        if isinstance(cached, list):
            return cached
        labels = []
        for x in self._service_list(rec):
            if x and x not in labels:
                labels.append(x)
        item = self._norm(rec.get("item_name"))
        if item and item not in labels:
            labels.append(item)
        rec["_work_labels"] = labels
        return labels

    def _primary_work(self, rec):
        if not isinstance(rec, dict):
            return "Без работ / услуг"
        cached = rec.get("_primary_work")
        if isinstance(cached, str) and cached:
            return cached
        vals = self._work_labels(rec)
        val = vals[0] if vals else "Без работ / услуг"
        rec["_primary_work"] = val
        return val

    def _work_basis(self, rec):
        return " ||| ".join(self._work_labels(rec))

    def _normalized_work(self, rec):
        work = self._primary_work(rec)
        work = re.sub(r"\s+", " ", work).strip().lower()
        work = re.sub(r"[\"'`]+", "", work)
        return work

    def _title(self, rec):
        if not isinstance(rec, dict):
            return ""
        cached = rec.get("_title")
        if isinstance(cached, str) and cached:
            return cached
        val = self._norm(rec.get("item_name")) or self._primary_work(rec) or f"Позиция {rec.get('item_number', '') or ''}"
        rec["_title"] = val
        return val

    def _semantic_text(self, rec):
        if not isinstance(rec, dict):
            return ""
        cached = rec.get("_semantic_text")
        if isinstance(cached, str) and cached:
            return cached
        services = rec.get("services_and_materials") or rec.get("services")
        text = build_semantic_text(self._norm(rec.get("item_name")), services)
        rec["_semantic_text"] = text
        return text

    def _drop_record_derived_cache(self, rec):
        """Сброс локальных кэшей записи после смены состава/названия."""
        if not isinstance(rec, dict):
            return
        for k in ("_svc_list", "_work_labels", "_primary_work", "_title", "_semantic_text",
                  "_search_haystack", "_fs_trusted", "_group_trusted", "_group_key"):
            rec.pop(k, None)

    def _classification_group_key(self, rec):
        """Ключ одинаковой позиции для массового подтверждения классификации.

        В ключ намеренно НЕ входят заказ, номер позиции, СФ и МВЗ.
        Поэтому одна и та же семантическая позиция в разных заказах считается
        одной группой: ручное решение по одной строке распространяется на все
        идентичные позиции.
        """
        if not isinstance(rec, dict):
            return ""
        cached = rec.get("_group_key")
        if isinstance(cached, str) and cached:
            return cached
        key = self.master.record_key(rec) if hasattr(self, "master") else ""
        if not key:
            text = self._semantic_text(rec)
            if not text:
                rec["_group_key"] = ""
                return ""
            key = re.sub(r"\s+", " ", text.lower().replace("ё", "е")).strip()
        rec["_group_key"] = key
        return key

    def _classification_group_members(self, selected):
        key = self._classification_group_key(selected)
        if not key:
            return [self.selected_idx] if self.selected_idx is not None else []
        # Индекс групп строится лениво один раз на сессию review
        idx = getattr(self, "_group_members_index", None)
        if not isinstance(idx, dict) or not idx:
            idx = {}
            for i, rec in enumerate(self.records):
                k = self._classification_group_key(rec)
                if k:
                    idx.setdefault(k, []).append(i)
            self._group_members_index = idx
        members = idx.get(key) or []
        return list(members) if members else ([self.selected_idx] if self.selected_idx is not None else [])

    def _fewshot_match(self, rec):
        text = self._semantic_text(rec)
        if not text:
            return None
        cache_key = text
        cache = getattr(self, "_fewshot_match_cache", None)
        if cache is None:
            self._fewshot_match_cache = {}
            cache = self._fewshot_match_cache
        if cache_key in cache:
            return cache[cache_key]
        match = self.few_shot.best_semantic_match(text, min_score=0.55)
        cache[cache_key] = match
        return match

    def _fewshot_trusted(self, rec):
        """True, если текущая авто-классификация совпадает с уже подтверждённым Few-shot.

        Такие позиции не нужны оператору в очереди «На проверку»: они считаются
        уже закрытыми по существующему семантическому эталону.
        """
        auto = self._norm(rec.get("auto_verdict") or rec.get("verdict")) or "Не определено"
        if auto == "Не определено":
            return False
        match = self._fewshot_match(rec)
        if not match:
            return False
        expected = self._norm(match["example"].get("verdict"))
        return expected == auto

    def _fewshot_conflict(self, rec):
        """Возвращает совпавший Few-shot, если он требует ручной проверки."""
        auto = self._norm(rec.get("auto_verdict") or rec.get("verdict")) or "Не определено"
        match = self._fewshot_match(rec)
        if not match:
            return None
        expected = self._norm(match["example"].get("verdict"))
        if expected == auto:
            return None
        return match

    def _fewshot_hidden_count(self):
        # Только предвычисленные флаги — без повторного semantic match
        n = 0
        for r in self.records:
            if not isinstance(r, dict):
                continue
            if str(r.get("checked", "Нет")) == "Да":
                continue
            if r.get("_fs_trusted"):
                n += 1
        return n

    def _ensure_search_haystack(self, r):
        """Кеширует нормализованную строку поиска в записи (один раз до смены данных)."""
        if not isinstance(r, dict):
            return ""
        hay = r.get("_search_haystack")
        if isinstance(hay, str) and hay:
            return hay
        parts = [
            self._norm(r.get("item_name")),
            self._norm(r.get("work_category")),
            self._norm(r.get("order_number")),
            self._norm(r.get("item_number")),
            self._norm(r.get("reference_document")),
            self._norm(r.get("matched_work_group")),
            self._norm(r.get("cost_center")),
        ]
        try:
            for s in self._service_list(r):
                if s:
                    parts.append(s)
        except Exception:
            pass
        # semantic_text только если сервисов мало — иначе уже покрыто item_name + services
        if not any(parts[5:]):  # нет services / matched group
            try:
                st = self._semantic_text(r)
                if st:
                    parts.append(st)
            except Exception:
                pass
        hay = " ".join(p for p in parts if p).lower()
        r["_search_haystack"] = hay
        return hay

    def _set_groups_open(self, opened):
        for iid in self.tree.get_children():
            self.tree.item(iid, open=opened)

    # ---------------- work-category AI ----------------
    def _apply_cached_work_categories(self):
        mapping_changed = False
        for r in self.records:
            if not isinstance(r, dict):
                continue
            # Уже есть категория — не гоняем regex/справочник заново
            if self._norm(r.get("work_category")):
                continue
            chosen = ""
            for label in self._work_labels(r):
                key = re.sub(r"\s+", " ", label).strip().lower()
                if not key:
                    continue
                existing = self.work_categories.get(key, "")
                det = deterministic_work_category(label)
                category = existing or det
                if det and existing != det:
                    self.work_categories[key] = det
                    mapping_changed = True
                elif existing:
                    category = existing
                if category and not chosen:
                    chosen = category
            if not chosen:
                chosen = deterministic_work_category(self._work_basis(r))
            if chosen:
                r["work_category"] = chosen
                mapping_changed = True
        if mapping_changed:
            save_work_categories(self.work_categories)

    def _classify_work_categories(self):
        if self.ai_busy:
            return
        self._apply_cached_work_categories()
        unresolved = {}
        for r in self.records:
            for label in self._work_labels(r):
                key = re.sub(r"\s+", " ", label).strip().lower()
                if key and key not in self.work_categories and not deterministic_work_category(label):
                    unresolved.setdefault(key, label)
        if not unresolved:
            self._refresh_all()
            messagebox.showinfo("Категории работ", "Новые категории не требуются: работы уже сгруппированы правилами или сохранённым справочником.", parent=self.top)
            return
        self.ai_busy = True
        self.btn_cluster.config(state=tk.DISABLED, text="AI: классификация…")
        def worker():
            mapping={}
            try:
                client=AIAssistantClient(self.config, AdaptiveRateLimiter(self.config.ai_rps_limit))
                items=list(unresolved.items())
                for start in range(0,len(items),25):
                    batch=items[start:start+25]
                    payload={str(i): text[:300] for i,(key,text) in enumerate(batch)}
                    prompt=(
                        "Нормализуй названия отдельных работ/услуг в короткие семантические категории. "
                        "Нужно объединять одинаковый смысл в одну группу, а не классифицировать закупку. "
                        "Примеры: 'замена контроллера ХР', 'контроллер платы управления' -> 'Контроллеры'; "
                        "'замена насоса', 'ремонт насоса' -> 'Насосы'; 'замена компрессора' -> 'Компрессоры'. "
                        "Не используй номера заказов. Не создавай слишком уникальные категории. "
                        "Верни только JSON-объект вида {\"0\":\"Категория\",...}. Категория 1-4 слова.\n\n"
                        "Вход:\n" + json.dumps(payload,ensure_ascii=False)
                    )
                    resp=client.chat_completion([
                        {"role":"system","content":"Ты нормализуешь работы и услуги для аналитической группировки."},
                        {"role":"user","content":prompt}
                    ],temperature=0.0,max_tokens=900)
                    if not resp:
                        continue
                    text=resp.strip()
                    if text.startswith("```"):
                        text=re.sub(r"^```(?:json)?\s*|\s*```$","",text,flags=re.I|re.S).strip()
                    m=re.search(r"\{.*\}",text,re.S)
                    obj=json.loads(m.group(0) if m else text)
                    if not isinstance(obj,dict):
                        continue
                    for i,(key,_) in enumerate(batch):
                        cat=str(obj.get(str(i),"")).strip()
                        if cat and len(cat)<100:
                            mapping[key]=cat
            except Exception as e:
                logger.warning(f"AI-категоризация работ завершилась с ошибкой: {e}")
                self.top.after(0, lambda e=e: messagebox.showwarning("AI-категоризация", f"Не удалось полностью завершить группировку работ/услуг:\n{e}", parent=self.top))
            self.top.after(0, lambda: self._finish_work_categories(mapping))
        threading.Thread(target=worker, daemon=True).start()

    def _finish_work_categories(self, mapping):
        self.work_categories.update(mapping)
        for r in self.records:
            chosen = ""
            for label in self._work_labels(r):
                key=re.sub(r"\s+", " ", label).strip().lower()
                cat=self.work_categories.get(key) or deterministic_work_category(label)
                if cat and not chosen:
                    chosen=cat
            r["work_category"]=chosen or r.get("work_category") or ""
        save_work_categories(self.work_categories)
        try:
            self.app.review_records=list(self.records)
            if getattr(self.app, "review_df", None) is not None:
                if "Категория работы" not in self.app.review_df.columns:
                    self.app.review_df["Категория работы"] = ""
                for rec in self.records:
                    idx=rec.get("row_index")
                    if idx in self.app.review_df.index:
                        self.app.review_df.at[idx, "Категория работы"] = rec.get("work_category") or ""
                if self.app.config.output_excel:
                    self.app._save_export_excel()
            self.app._save_review_snapshot()
        except Exception as e:
            logger.warning(f"Не удалось сохранить категории в сеанс/Excel: {e}")
        self.ai_busy=False
        self.btn_cluster.config(state=tk.NORMAL, text="AI: сгруппировать работы")
        self._refresh_all()
        messagebox.showinfo("Категории работ", f"Готово. Категория назначена для {sum(1 for r in self.records if r.get('work_category'))} из {len(self.records)} позиций. Справочник сохранён в work_categories.json.", parent=self.top)

    def _show_help(self):
        messagebox.showinfo("Как работать с проверкой", (
            "1. «AI: сгруппировать работы» объединяет похожие названия работ/услуг в аналитические категории. "
            "Например, разные формулировки контроллеров попадут в «Контроллеры».\n\n"
            "2. Группировка «Категория работы» показывает крупные смысловые группы вместо тысяч отдельных формулировок.\n\n"
            "3. Справа всегда остаётся исходная SAP-детализация — она нужна для проверки.\n\n"
            "4. «Подтвердить авто» — сохранить автоматический вердикт. «Сохранить мой выбор» — выбрать другой классификатор. "
            "«Оставить неизвестной» — ничего не придумывать.\n\n"
            "5. «+ В Few-shot» сохраняет подтверждённую позицию как семантический пример для будущего AI.\n\n"
            "Категория работы и основной вердикт — разные вещи: категория помогает тебе быстро ориентироваться, а основной вердикт остаётся отдельным классификатором.\n\n"
            "6. Во вкладке «Группы» можно создать родительскую группу: например, «Рекламное оборудование» → подгруппы «Панели ПВХ», «Световые короба», «Баннеры». Для этой группы задаётся итоговый классификатор. После сохранения совпадения применяются к будущим позициям, а уже загруженные можно пересчитать кнопкой «Применить к позициям»."
        ), parent=self.top)

    # ---------------- decisions ----------------
    def _select_current(self):
        if self.selected_idx is None:
            return
        iid = f"r:{self.selected_idx}"
        if self.tree.exists(iid):
            self.tree.selection_set(iid)
            self.tree.see(iid)
            self._on_select()

    def _focus_unchecked(self):
        if not self.records:
            return
        for i, r in enumerate(self.records):
            if str(r.get("checked", "Нет")) != "Да":
                self._select_record_if_visible(i)
                return

    def _focus_unknown(self):
        for i, r in enumerate(self.records):
            if (self._norm(r.get("final_verdict") or r.get("verdict")) or "Не определено") == "Не определено":
                self._select_record_if_visible(i)
                return

    # ---------------- AI / few-shot ----------------
    def _set_advice_text(self, text: str):
        """Пишет AI-совет в Label (legacy) или Text/ScrolledText (v5.1+)."""
        widget = getattr(self, "advice_label", None)
        if widget is None:
            return
        try:
            if isinstance(widget, (tk.Text, scrolledtext.ScrolledText)):
                self._set_readonly_text(widget, text or "")
            else:
                widget.config(text=text or "")
        except Exception as e:
            logger.debug(f"_set_advice_text: {e}")

    def _ask_ai_advice(self):
        """Короткая помощь оператору по конкретной позиции. Не меняет классификацию."""
        if self.selected_idx is None or self.ai_busy:
            return
        try:
            r = self.records[self.selected_idx]
        except (IndexError, TypeError):
            return
        semantic = self._semantic_text(r)
        if not semantic:
            self._set_advice_text("Нет данных для AI-совета.")
            return
        auto = self._norm(r.get("auto_verdict") or r.get("verdict")) or "Не определено"
        selected = self._norm(self.selected_verdict.get()) or "Не определено"
        category = self._norm(r.get("work_category")) or "Не назначена"
        self.ai_busy = True
        try:
            if hasattr(self, "btn_ai_advice"):
                self.btn_ai_advice.config(state=tk.DISABLED)
        except Exception:
            pass
        self._set_advice_text("AI анализирует позицию…")

        def worker():
            out = "AI не вернул совет."
            try:
                client = AIAssistantClient(self.config, AdaptiveRateLimiter(self.config.ai_rps_limit))
                prompt = (
                    "Помоги оператору проверить классификацию одной позиции. "
                    "Не принимай решение за оператора и не меняй его выбор. "
                    "Не обсуждай номера заказа, позиции, СФ или МВЗ. "
                    "Сравни содержание работы/услуги с текущим автоматическим и выбранным решением. "
                    "Ответь строго в 3 коротких блоках:\n"
                    "ПОЧЕМУ — 1-2 предложения о главном признаке;\n"
                    "СОМНЕНИЕ — только если действительно есть неоднозначность, иначе напиши «Существенных сомнений нет»;\n"
                    "ЧТО ПРОВЕРИТЬ — один конкретный вопрос оператору.\n"
                    "Не придумывай отсутствующие в тексте факты. Не давай общих советов про коды, договоры и справочники, если их нет в исходных данных.\n\n"
                    f"Автоматический вердикт: {auto}\n"
                    f"Текущий выбор оператора: {selected}\n"
                    f"Категория работы: {category}\n\n"
                    f"{semantic}"
                )
                resp = client.chat_completion([
                    {"role": "system", "content": "Ты помощник аудитора закупок. Отвечай по-русски, конкретно и кратко. Максимум 6-8 строк."},
                    {"role": "user", "content": prompt}
                ], temperature=0.1, max_tokens=280)
                out = resp.strip() if resp else "AI не вернул совет."
            except Exception as e:
                out = f"Ошибка AI-совета: {e}"
            try:
                self.top.after(0, lambda t=out: self._finish_ai_advice(t))
            except Exception:
                self.ai_busy = False

        threading.Thread(target=worker, daemon=True).start()

    def _finish_ai_advice(self, text):
        self.ai_busy = False
        try:
            if hasattr(self, "btn_ai_advice"):
                self.btn_ai_advice.config(state=tk.NORMAL)
        except Exception:
            pass
        self._set_advice_text(text or "")

    def _clear_fewshot_editor(self):
        if hasattr(self, "fs_tree"):
            self.fs_tree.selection_remove(self.fs_tree.selection())
        self.fs_text.delete("1.0", tk.END)
        self.fs_verdict.set("")
        self.fs_source.set("manual")
        if hasattr(self, "fs_active"):
            self.fs_active.set(True)

    def _refresh_fewshot_list(self):
        if not hasattr(self, "fs_tree"):
            return
        for iid in self.fs_tree.get_children():
            self.fs_tree.delete(iid)
        q = self.fs_search.get().strip().lower() if hasattr(self, "fs_search") else ""
        count = 0
        for i, ex in enumerate(self.few_shot._examples):
            txt = str(ex.get("text", ""))
            hay = f"{txt} {ex.get('verdict','')} {ex.get('source','')}".lower()
            if q and q not in hay:
                continue
            status = "✓" if bool(ex.get("active", True)) else "⛔"
            self.fs_tree.insert("", "end", iid=str(i), values=(f"{status} {ex.get('verdict', '')}", ex.get("source", ""), txt[:500]))
            count += 1
        stats = self.few_shot.get_stats()
        self.fs_stats.config(text=f"Всего: {len(self.few_shot._examples)} • Показано: {count} • " + " | ".join(f"{k}: {v}" for k, v in stats.items()))

    def _on_fewshot_select(self, _event=None):
        sel = self.fs_tree.selection()
        if not sel:
            return
        i = int(sel[0])
        if i >= len(self.few_shot._examples):
            return
        ex = self.few_shot._examples[i]
        self.fs_text.delete("1.0", tk.END)
        self.fs_text.insert("1.0", ex.get("text", ""))
        self.fs_verdict.set(ex.get("verdict", ""))
        self.fs_source.set(ex.get("source", "manual"))
        if hasattr(self, "fs_active"):
            self.fs_active.set(bool(ex.get("active", True)))

    def _save_fewshot(self):
        text = re.sub(r"\s+", " ", self.fs_text.get("1.0", tk.END).strip())
        verdict = self.fs_verdict.get().strip()
        source = self.fs_source.get().strip() or "manual"
        if not text or verdict not in self.VERDICTS[1:]:
            messagebox.showwarning("Few-shot", "Укажи описание и вердикт.", parent=self.top)
            return
        active = bool(self.fs_active.get()) if hasattr(self, "fs_active") else True
        sel = self.fs_tree.selection()
        if sel:
            i = int(sel[0])
            if i < len(self.few_shot._examples):
                ex = self.few_shot._examples[i]
                ex.update({"text": text[:2000], "verdict": verdict, "source": source, "active": active, "classifier_version": CLASSIFIER_VERSION, "last_used": time.time()})
                self.few_shot._token_cache = {str(x.get("text", "")): self.few_shot._match_tokens(x.get("text", "")) for x in self.few_shot._examples}
                self.few_shot.save()
        else:
            self.few_shot.add(text, verdict, source=source)
            if self.few_shot._examples:
                self.few_shot._examples[-1]["active"] = active
                self.few_shot.save()
        self._invalidate_trust_flags()
        self._refresh_fewshot_list()
        self._refresh_header()

    def _toggle_fewshot(self):
        sel = self.fs_tree.selection()
        if not sel:
            return
        i = int(sel[0])
        if i >= len(self.few_shot._examples):
            return
        ex = self.few_shot._examples[i]
        ex["active"] = not bool(ex.get("active", True))
        self.few_shot.save()
        self.fs_active.set(bool(ex["active"]))
        self._invalidate_trust_flags()
        self._refresh_fewshot_list()
        self._refresh_header()

    def _delete_fewshot(self):
        sel = self.fs_tree.selection()
        if not sel:
            return
        i = int(sel[0])
        if i >= len(self.few_shot._examples):
            return
        if not messagebox.askyesno("Удаление", "Удалить выбранный Few-shot пример?", parent=self.top):
            return
        self.few_shot._examples.pop(i)
        self.few_shot.save()
        self._invalidate_trust_flags()
        self._clear_fewshot_editor()
        self._refresh_fewshot_list()
        self._refresh_header()

    def _reload_session(self):
        rows = self.app._load_review_rows_from_session(show_message=True)
        if rows:
            self.records = rows
            self.selected_idx = None
            self._refresh_all()
            self._focus_unchecked()


class ClassificationReview(_LegacyClassificationReview):
    """Упрощённое рабочее место v5.1.

    Принципы UX:
    - минимум постоянно видимых фильтров;
    - быстрые кнопки выбора класса НИЧЕГО не сохраняют сами;
    - решение сохраняется одной явной кнопкой;
    - после обновления сохраняются текущие фильтры и выбранная позиция;
    - у позиции явно виден статус проверки и статус Few-shot;
    - категорию работы можно вручную назначить отдельной кнопкой.
    """

    def __init__(self, parent, app, records=None):
        self._ux51_pending_selection = False
        self._fewshot_match_cache = {}
        self._search_after_id = None
        self._search_index = []
        self._group_members_index = None
        self.work_groups = load_work_groups()
        # Тяжёлая подготовка (normalize / search index / trust) — внутри
        # _deferred_first_refresh → _refresh_all, без дубля после super().
        super().__init__(parent, app, records)
        self.top.protocol("WM_DELETE_WINDOW", self._on_close_review)

    def _on_close_review(self):
        try:
            self.app.flush_pending_saves()
        except Exception:
            pass
        self.top.destroy()

    def _debounced_search(self):
        if self._search_after_id:
            try:
                self.top.after_cancel(self._search_after_id)
            except Exception:
                pass
        self._search_after_id = self.top.after(350, lambda: self._refresh_positions(keep_selection=True))

    def _work_category_label(self, rec):
        """Пусто / «Без категории» / «Не определено» → один ярлык."""
        cat = self._norm(rec.get("work_category"))
        if not cat:
            return UNKNOWN_WORK_CATEGORY
        low = cat.lower()
        if low in ("без категории", "не определено", "none", "-", "—", "н/д", "н/а"):
            return UNKNOWN_WORK_CATEGORY
        return cat

    def _rebuild_search_index(self):
        """Лёгкий индекс: пишем r['_search_haystack'] один раз, список — для совместимости."""
        idx = []
        for r in self.records:
            if not isinstance(r, dict):
                idx.append("")
                continue
            # Сброс устаревшего кеша только если явно пометили; иначе reuse.
            hay = r.get("_search_haystack")
            if not isinstance(hay, str) or not hay:
                hay = self._ensure_search_haystack(r)
            else:
                # Гарантируем наличие метода на legacy-пути
                r["_search_haystack"] = hay
            idx.append(hay)
        self._search_index = idx

    def _invalidate_search_haystack(self, records=None):
        """Сбрасывает кеш поиска после смены категории/состава работ."""
        for r in (records if records is not None else self.records):
            if isinstance(r, dict):
                r.pop("_search_haystack", None)
        self._search_index = []

    def _invalidate_trust_flags(self):
        """Сброс кэша few-shot match и trust-флагов после изменения эталонов."""
        self._fewshot_match_cache = {}
        for r in self.records:
            if isinstance(r, dict):
                r.pop("_fs_trusted", None)
                r.pop("_group_trusted", None)
        self._precompute_trust_flags(only_unchecked=True)

    def _precompute_trust_flags(self, only_unchecked: bool = True):
        """Считать Few-shot/группу один раз, а не на каждый refresh поиска.

        only_unchecked=True (по умолчанию): только непроверенные — они влияют
        на очередь «На проверку». Уже проверенные пропускаем (дорого и не нужно).
        """
        for r in self.records:
            if not isinstance(r, dict):
                continue
            if only_unchecked and str(r.get("checked", "Нет")) == "Да":
                r.setdefault("_fs_trusted", False)
                r.setdefault("_group_trusted", False)
                continue
            if "_fs_trusted" not in r:
                try:
                    r["_fs_trusted"] = bool(self._fewshot_trusted(r))
                except Exception:
                    r["_fs_trusted"] = False
            if "_group_trusted" not in r:
                try:
                    r["_group_trusted"] = bool(self._manual_group_trusted(r))
                except Exception:
                    r["_group_trusted"] = False

    def _normalize_review_state(self):
        for r in self.records:
            if not isinstance(r, dict):
                continue
            final = self._norm(r.get("final_verdict") or r.get("verdict")) or "Не определено"
            auto = self._norm(r.get("auto_verdict") or r.get("verdict")) or "Не определено"
            checked = str(r.get("checked", "Нет")) == "Да"
            source = self._norm(r.get("source"))
            if not r.get("review_status"):
                if not checked:
                    status = "Не проверено"
                elif final == "Не определено":
                    status = "Оставлено неизвестным"
                elif source == "confirmed" and final == auto:
                    status = "Подтверждено авто"
                elif source == "manual":
                    status = "Изменено вручную"
                else:
                    status = "Подтверждено"
                r["review_status"] = status
            if "fewshot_added" not in r:
                r["fewshot_added"] = False
            if "work_category_source" not in r:
                r["work_category_source"] = "ai" if r.get("work_category") else ""
            if "matched_work_group" not in r:
                r["matched_work_group"] = ""
            if "work_group_score" not in r:
                r["work_group_score"] = 0.0

    # ---------- компактный UI ----------
    def _build_ui(self):
        header = tk.Frame(self.top, bg="#14213d", padx=16, pady=10)
        header.pack(fill=tk.X)
        tk.Label(header, text="Проверка классификации",
                 font=("Segoe UI", 17, "bold"), fg="white", bg="#14213d").pack(side=tk.LEFT)
        self.header_info = tk.Label(header, text="", font=("Segoe UI", 10, "bold"),
                                    fg="#dbeafe", bg="#14213d")
        self.header_info.pack(side=tk.RIGHT)

        self._build_summary_cards()
        self._build_filter_bar()

        # Две рабочие вкладки: проверка позиций и управляемый Few-shot-эталон.
        self.notebook = ttk.Notebook(self.top)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 8))
        self.positions_tab = ttk.Frame(self.notebook)
        self.fewshot_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.positions_tab, text=" Проверка позиций ")
        self.notebook.add(self.fewshot_tab, text=" Few-shot ")
        self._build_positions_tab()
        self._build_fewshot_tab()

        footer = tk.Frame(self.top, bg="#f8fafc", padx=10, pady=5)
        footer.pack(fill=tk.X)
        tk.Label(footer,
                 text="1–5: класс  •  Enter: сохранить  •  ↑↓: позиция  •  мышь+Ctrl+C: копировать описание/заказ",
                 anchor="w", fg="#475569", bg="#f8fafc").pack(side=tk.LEFT)
        tk.Button(footer, text="Выгрузка классификатора", command=self._export_classifier_pending,
                  bg="#0f766e", fg="white", relief="flat", padx=10, pady=4).pack(side=tk.RIGHT, padx=(8, 0))
        self.footer_status = tk.Label(footer, text="Готово", anchor="e", fg="#64748b", bg="#f8fafc")
        self.footer_status.pack(side=tk.RIGHT)

    def _build_summary_cards(self):
        frame = tk.Frame(self.top, bg="#f8fafc", padx=10, pady=7)
        frame.pack(fill=tk.X)
        self.summary_cards = {}
        definitions = [
            ("На проверку", "unchecked", "#b45309"),
            ("Не определено", "unknown", "#b91c1c"),
            ("Проверено", "checked", "#15803d"),
            ("Эталонов", "fewshot", "#7c3aed"),
        ]
        for title, key, fg in definitions:
            card = tk.Frame(frame, bg="white", bd=1, relief="solid", padx=12, pady=6)
            card.pack(side=tk.LEFT, padx=4, fill=tk.X, expand=True)
            tk.Label(card, text=title, bg="white", fg="#475569", font=("Segoe UI", 9)).pack(anchor="w")
            value = tk.Label(card, text="—", bg="white", fg=fg, font=("Segoe UI", 15, "bold"))
            value.pack(anchor="w")
            self.summary_cards[key] = value

    def _build_filter_bar(self):
        outer = tk.Frame(self.top, bg="#f8fafc", padx=10, pady=6)
        outer.pack(fill=tk.X)
        row = tk.Frame(outer, bg="#f8fafc")
        row.pack(fill=tk.X)

        tk.Label(row, text="Поиск", bg="#f8fafc", fg="#334155", font=("Segoe UI", 9, "bold")).pack(side=tk.LEFT)
        self.search_var = tk.StringVar()
        ent = tk.Entry(row, textvariable=self.search_var, width=27, font=("Segoe UI", 9))
        ent.pack(side=tk.LEFT, padx=(5, 14))
        Tooltip(ent, "Ищет по названию SAP, работам, категории, заказу и СФ.")
        self.search_var.trace_add("write", lambda *_: self._debounced_search())

        tk.Label(row, text="Статус", bg="#f8fafc", fg="#334155", font=("Segoe UI", 9, "bold")).pack(side=tk.LEFT)
        self.mode_filter = tk.StringVar(value="На проверку")
        mode_cb = ttk.Combobox(row, textvariable=self.mode_filter,
            values=["На проверку", "Не определено", "Проверено", "Изменено вручную", "Подтверждено авто", "Все"],
            state="readonly", width=17)
        mode_cb.pack(side=tk.LEFT, padx=(5, 12))
        self.mode_filter.trace_add("write", lambda *_: self._refresh_positions(keep_selection=True))

        tk.Label(row, text="Группировка", bg="#f8fafc", fg="#334155", font=("Segoe UI", 9, "bold")).pack(side=tk.LEFT)
        self.group_by = tk.StringVar(value="Категория работы")
        group_cb = ttk.Combobox(row, textvariable=self.group_by,
            values=["Категория работы", "Работа / услуга", "Итоговый вердикт", "Без группировки"],
            state="readonly", width=18)
        group_cb.pack(side=tk.LEFT, padx=(5, 12))
        self.group_by.trace_add("write", lambda *_: self._refresh_positions(keep_selection=True))

        tk.Label(row, text="Сортировка", bg="#f8fafc", fg="#334155", font=("Segoe UI", 9, "bold")).pack(side=tk.LEFT)
        self.sort_mode = tk.StringVar(value="Количество ↓")
        sort_cb = ttk.Combobox(row, textvariable=self.sort_mode,
                               values=["Количество ↓", "Количество ↑", "A → Я", "Я → А"],
                               state="readonly", width=13)
        sort_cb.pack(side=tk.LEFT, padx=5)
        self.sort_mode.trace_add("write", lambda *_: self._refresh_positions(keep_selection=True))

        actions = tk.Frame(row, bg="#f8fafc")
        actions.pack(side=tk.RIGHT)
        self._top_action_buttons = {}
        b = tk.Button(actions, text="Обновить", command=lambda: self._refresh_all(keep_selection=True),
                       bg="#2563eb", fg="white", relief="flat", width=11, height=1,
                       cursor="hand2", font=("Segoe UI", 9, "bold"))
        b.pack(side=tk.LEFT, padx=2)
        Tooltip(b, "Обновить список с текущими фильтрами.")
        self._top_action_buttons["Обновить"] = b

        advanced = tk.Frame(outer, bg="#eef2f7", padx=8, pady=5)
        self.advanced_frame = advanced
        self.advanced_visible = False
        tk.Label(advanced, text="Дополнительные фильтры", bg="#eef2f7", fg="#475569", font=("Segoe UI", 9, "bold")).pack(side=tk.LEFT)
        self.source_filter = tk.StringVar(value="Все")
        ttk.Combobox(advanced, textvariable=self.source_filter,
                     values=["Все", "rule", "group", "ai", "cache", "confirmed", "manual", "unknown"],
                     state="readonly", width=12).pack(side=tk.LEFT, padx=6)
        self.sap_filter = tk.StringVar(value="Все")
        ttk.Combobox(advanced, textvariable=self.sap_filter,
                     values=["Все", "Есть данные", "Нет данных"], state="readonly", width=13).pack(side=tk.LEFT, padx=6)
        self.category_filter = tk.StringVar(value="Все")
        self.category_combo = ttk.Combobox(advanced, textvariable=self.category_filter,
                                           values=["Все"], state="readonly", width=26)
        self.category_combo.pack(side=tk.LEFT, padx=6)
        for var in (self.source_filter, self.sap_filter, self.category_filter):
            var.trace_add("write", lambda *_: self._refresh_positions(keep_selection=True))
        adv_btn = tk.Button(outer, text="Доп. фильтры ▾", command=self._toggle_advanced,
                            bg="#e2e8f0", fg="#334155", relief="flat", padx=10, pady=4,
                            font=("Segoe UI", 9, "bold"), cursor="hand2")
        adv_btn.pack(anchor="e", pady=(3, 0))
        self.advanced_button = adv_btn

    def _toggle_advanced(self):
        self.advanced_visible = not self.advanced_visible
        if self.advanced_visible:
            self.advanced_frame.pack(fill=tk.X, pady=(4, 0))
            self.advanced_button.config(text="Доп. фильтры ▴")
        else:
            self.advanced_frame.pack_forget()
            self.advanced_button.config(text="Доп. фильтры ▾")

    def _reset_view(self):
        self.search_var.set("")
        self.mode_filter.set("На проверку")
        self.group_by.set("Категория работы")
        self.sort_mode.set("Количество ↓")
        self.source_filter.set("Все")
        self.sap_filter.set("Все")
        self.category_filter.set("Все")
        self._refresh_positions(keep_selection=False)
        self._focus_unchecked()

    # ---------- hierarchical work groups ----------
    def _build_groups_tab(self):
        outer = tk.Frame(self.groups_tab, bg="#f8fafc", padx=10, pady=10)
        outer.pack(fill=tk.BOTH, expand=True)

        intro = tk.Frame(outer, bg="#eef2ff", padx=10, pady=8)
        intro.pack(fill=tk.X, pady=(0, 8))
        tk.Label(
            intro,
            text="Родительская группа → подгруппы → основной классификатор",
            bg="#eef2ff", fg="#312e81", font=("Segoe UI", 11, "bold")
        ).pack(anchor="w")
        tk.Label(
            intro,
            text="Например: Панели ПВХ + Световые короба + Баннерные конструкции → Рекламное оборудование → Оборудование. "
                 "Созданное правило применяется к существующим и будущим позициям.",
            bg="#eef2ff", fg="#4338ca", justify=tk.LEFT, wraplength=1200
        ).pack(anchor="w", pady=(3, 0))

        paned = ttk.PanedWindow(outer, orient=tk.HORIZONTAL)
        paned.pack(fill=tk.BOTH, expand=True)
        left = ttk.Frame(paned)
        right = ttk.Frame(paned)
        paned.add(left, weight=4)
        paned.add(right, weight=7)

        left_top = tk.Frame(left, pady=4)
        left_top.pack(fill=tk.X)
        tk.Button(left_top, text="+ Новая группа", command=self._new_work_group,
                  bg="#2563eb", fg="white", relief="flat", width=16,
                  font=("Segoe UI", 9, "bold")).pack(side=tk.LEFT)
        tk.Button(left_top, text="Обновить", command=self._refresh_group_tree,
                  bg="#64748b", fg="white", relief="flat", width=12).pack(side=tk.LEFT, padx=4)
        Tooltip(left_top.winfo_children()[0], "Создать новую родительскую группу, которая будет наследовать выбранный классификатор.")

        group_frame = ttk.Frame(left)
        group_frame.pack(fill=tk.BOTH, expand=True)
        self.group_tree = ttk.Treeview(group_frame, columns=("verdict", "children"), show="tree headings", selectmode="browse")
        self.group_tree.heading("#0", text="Родительская группа")
        self.group_tree.heading("verdict", text="Классификатор")
        self.group_tree.heading("children", text="Подгрупп")
        self.group_tree.column("#0", width=240, minwidth=160)
        self.group_tree.column("verdict", width=170, minwidth=130)
        self.group_tree.column("children", width=90, minwidth=70, anchor="center")
        gsc = ttk.Scrollbar(group_frame, orient=tk.VERTICAL, command=self.group_tree.yview)
        self.group_tree.configure(yscrollcommand=gsc.set)
        self.group_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        gsc.pack(side=tk.RIGHT, fill=tk.Y)
        self.group_tree.bind("<<TreeviewSelect>>", self._on_group_select)

        editor = ttk.LabelFrame(right, text="Родительская группа", padding=10)
        editor.pack(fill=tk.BOTH, expand=True)

        row = tk.Frame(editor)
        row.pack(fill=tk.X, pady=(0, 8))
        tk.Label(row, text="Название", width=12, anchor="w").pack(side=tk.LEFT)
        self.work_group_name = tk.StringVar()
        tk.Entry(row, textvariable=self.work_group_name, font=("Segoe UI", 10)).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=4)
        tk.Label(row, text="Классификатор", width=15, anchor="w").pack(side=tk.LEFT, padx=(12, 3))
        self.work_group_verdict = tk.StringVar(value="Оборудование")
        ttk.Combobox(row, textvariable=self.work_group_verdict, state="readonly", values=self.VERDICTS[1:], width=24).pack(side=tk.LEFT)

        btns = tk.Frame(editor)
        btns.pack(fill=tk.X, pady=(0, 8))
        tk.Button(btns, text="Сохранить группу", command=self._save_work_group,
                  bg="#16a34a", fg="white", relief="flat", width=18,
                  font=("Segoe UI", 9, "bold")).pack(side=tk.LEFT)
        tk.Button(btns, text="Удалить группу", command=self._delete_work_group,
                  bg="#dc2626", fg="white", relief="flat", width=15).pack(side=tk.LEFT, padx=5)
        tk.Button(btns, text="Применить к позициям", command=self._apply_all_work_groups,
                  bg="#7c3aed", fg="white", relief="flat", width=20,
                  font=("Segoe UI", 9, "bold")).pack(side=tk.LEFT, padx=5)
        Tooltip(btns.winfo_children()[0], "Сохранить название, классификатор и текущий состав подгрупп. После сохранения правило начинает работать для будущих позиций.")
        Tooltip(btns.winfo_children()[2], "Проверить уже загруженные позиции и применить новые родительские правила. Ручные подтверждения не перезаписываются.")

        lists = ttk.PanedWindow(editor, orient=tk.HORIZONTAL)
        lists.pack(fill=tk.BOTH, expand=True)
        child_box = ttk.LabelFrame(lists, text="Подгруппы / категории, уже входящие в группу", padding=6)
        available_box = ttk.LabelFrame(lists, text="Доступные категории работ", padding=6)
        lists.add(child_box, weight=1)
        lists.add(available_box, weight=1)

        self.group_children_list = tk.Listbox(child_box, selectmode=tk.EXTENDED, exportselection=False,
                                               font=("Segoe UI", 9), activestyle="dotbox")
        self.group_children_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        csc = ttk.Scrollbar(child_box, orient=tk.VERTICAL, command=self.group_children_list.yview)
        self.group_children_list.configure(yscrollcommand=csc.set)
        csc.pack(side=tk.RIGHT, fill=tk.Y)

        self.group_available_list = tk.Listbox(available_box, selectmode=tk.EXTENDED, exportselection=False,
                                               font=("Segoe UI", 9), activestyle="dotbox")
        self.group_available_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        asc = ttk.Scrollbar(available_box, orient=tk.VERTICAL, command=self.group_available_list.yview)
        self.group_available_list.configure(yscrollcommand=asc.set)
        asc.pack(side=tk.RIGHT, fill=tk.Y)

        cat_buttons = tk.Frame(editor)
        cat_buttons.pack(fill=tk.X, pady=(8, 4))
        tk.Button(cat_buttons, text="← Добавить выбранные подгруппы", command=self._add_selected_group_children,
                  bg="#0f766e", fg="white", relief="flat", width=28).pack(side=tk.LEFT)
        tk.Button(cat_buttons, text="Удалить выбранные подгруппы →", command=self._remove_selected_group_children,
                  bg="#64748b", fg="white", relief="flat", width=28).pack(side=tk.RIGHT)

        kwrow = tk.Frame(editor)
        kwrow.pack(fill=tk.X, pady=(4, 0))
        tk.Label(kwrow, text="Доп. ключевые фразы", width=20, anchor="w").pack(side=tk.LEFT)
        self.work_group_keywords = tk.StringVar()
        tk.Entry(kwrow, textvariable=self.work_group_keywords).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=4)
        tk.Label(kwrow, text="через ;", fg="#64748b").pack(side=tk.LEFT)
        tk.Button(kwrow, text="Сохранить фразы", command=self._save_work_group_keywords,
                  bg="#2563eb", fg="white", relief="flat", width=17).pack(side=tk.LEFT, padx=5)
        Tooltip(kwrow.winfo_children()[3], "Фразы, которые прямо должны вести в эту родительскую группу. Например: «панель пвх; световой короб; баннерная кассета».")

        self.group_status = tk.Label(editor, text="Выбери группу слева или создай новую.",
                                     anchor="w", fg="#64748b", justify=tk.LEFT)
        self.group_status.pack(fill=tk.X, pady=(8, 0))
        self._refresh_group_tree()
        self._refresh_group_available()

    def _refresh_group_tree(self):
        if not hasattr(self, "group_tree"):
            return
        for iid in self.group_tree.get_children():
            self.group_tree.delete(iid)
        for name in sorted(self.work_groups, key=lambda x: x.lower()):
            rule = self.work_groups.get(name, {}) if isinstance(self.work_groups.get(name, {}), dict) else {}
            children = [str(x) for x in rule.get("children", []) if str(x).strip()]
            verdict = str(rule.get("verdict", ""))
            self.group_tree.insert("", "end", iid=name, text=name,
                                   values=(verdict, len(children)))

    def _refresh_group_available(self):
        if not hasattr(self, "group_available_list"):
            return
        values = sorted({self._norm(r.get("work_category")) for r in self.records if self._norm(r.get("work_category"))})
        # Добавляем категории из сохранённого словаря/родительских правил, даже если текущая выборка их не содержит.
        for rule in self.work_groups.values():
            for child in rule.get("children", []) if isinstance(rule, dict) else []:
                if str(child).strip() and str(child).strip() not in values:
                    values.append(str(child).strip())
        values = sorted(set(values), key=lambda x: x.lower())
        current_children = set()
        name = self.work_group_name.get().strip()
        if name in self.work_groups:
            current_children = {str(x).strip() for x in self.work_groups.get(name, {}).get("children", [])}
        self.group_available_list.delete(0, tk.END)
        for value in values:
            if value not in current_children:
                self.group_available_list.insert(tk.END, value)

    def _on_group_select(self, _event=None):
        sel = self.group_tree.selection()
        if not sel:
            return
        name = sel[0]
        rule = self.work_groups.get(name, {}) if isinstance(self.work_groups.get(name, {}), dict) else {}
        self.work_group_name.set(name)
        self.work_group_verdict.set(str(rule.get("verdict", "Оборудование")))
        self.group_children_list.delete(0, tk.END)
        children = [str(x).strip() for x in rule.get("children", []) if str(x).strip()]
        for value in sorted(children, key=lambda x: x.lower()):
            self.group_children_list.insert(tk.END, value)
        self.work_group_keywords.set("; ".join(str(x) for x in rule.get("keywords", []) if str(x).strip()))
        self._refresh_group_available()
        self.group_status.config(text=f"Группа: {name} • классификатор: {rule.get('verdict', '—')} • подгрупп: {len(children)}")

    def _new_work_group(self):
        self.group_tree.selection_remove(self.group_tree.selection())
        self.work_group_name.set("")
        self.work_group_verdict.set("Оборудование")
        self.group_children_list.delete(0, tk.END)
        self.work_group_keywords.set("")
        self._refresh_group_available()
        self.group_status.config(text="Новая группа. Назови её, выбери классификатор и добавь подгруппы.")

    def _save_work_group(self):
        name = re.sub(r"\s+", " ", self.work_group_name.get().strip())
        verdict = self.work_group_verdict.get().strip()
        if not name or verdict not in self.VERDICTS[1:]:
            messagebox.showwarning("Группы", "Укажи название группы и основной классификатор.", parent=self.top)
            return
        selected_children = [self.group_children_list.get(i).strip() for i in range(self.group_children_list.size()) if self.group_children_list.get(i).strip()]
        if not selected_children and not self.work_group_keywords.get().strip():
            if not messagebox.askyesno("Группа без подгрупп", "В группе пока нет подгрупп/ключевых фраз. Всё равно сохранить?", parent=self.top):
                return
        old_sel = self.group_tree.selection()
        old_name = old_sel[0] if old_sel and old_sel[0] != name else None
        if old_name and old_name != name:
            self.work_groups.pop(old_name, None)
        keywords = [re.sub(r"\s+", " ", x.strip()) for x in self.work_group_keywords.get().split(";") if x.strip()]
        self.work_groups[name] = {
            "verdict": verdict,
            "children": sorted(set(selected_children), key=lambda x: x.lower()),
            "keywords": sorted(set(keywords), key=lambda x: x.lower()),
        }
        save_work_groups(self.work_groups)
        self._apply_all_work_groups(show_message=False)
        self._refresh_group_tree()
        if self.group_tree.exists(name):
            self.group_tree.selection_set(name)
            self.group_tree.see(name)
            self._on_group_select()
        self.group_status.config(text=f"Сохранено: {name} → {verdict}. Правило будет применяться и к новым позициям.")

    def _delete_work_group(self):
        name = self.work_group_name.get().strip()
        if not name or name not in self.work_groups:
            return
        if not messagebox.askyesno("Удаление группы", f"Удалить родительскую группу «{name}»?\nПодгруппы не удаляются из справочника работ.", parent=self.top):
            return
        self.work_groups.pop(name, None)
        save_work_groups(self.work_groups)
        self._refresh_group_tree()
        self._new_work_group()
        self._refresh_all()

    def _add_selected_group_children(self):
        selections = list(self.group_available_list.curselection())
        existing = {self.group_children_list.get(i) for i in range(self.group_children_list.size())}
        for idx in selections:
            value = self.group_available_list.get(idx)
            if value not in existing:
                self.group_children_list.insert(tk.END, value)
                existing.add(value)
        self._refresh_group_available()

    def _remove_selected_group_children(self):
        for idx in reversed(self.group_children_list.curselection()):
            self.group_children_list.delete(idx)
        self._refresh_group_available()

    def _save_work_group_keywords(self):
        name = self.work_group_name.get().strip()
        if not name or name not in self.work_groups:
            messagebox.showwarning("Группы", "Сначала создай или сохрани родительскую группу.", parent=self.top)
            return
        keywords = [re.sub(r"\s+", " ", x.strip()) for x in self.work_group_keywords.get().split(";") if x.strip()]
        self.work_groups[name]["keywords"] = sorted(set(keywords), key=lambda x: x.lower())
        save_work_groups(self.work_groups)
        self._apply_all_work_groups(show_message=False)
        self.group_status.config(text=f"Ключевые фразы сохранены для группы: {name}")

    def _manual_group_match(self, rec):
        return resolve_work_group(self._semantic_text(rec), self._norm(rec.get("work_category")), self.work_groups)

    def _manual_group_trusted(self, rec):
        auto = self._norm(rec.get("auto_verdict") or rec.get("verdict")) or "Не определено"
        match = self._manual_group_match(rec)
        if not match or auto == "Не определено":
            return False
        return match.get("verdict") == auto

    def _manual_group_conflict(self, rec):
        auto = self._norm(rec.get("auto_verdict") or rec.get("verdict")) or "Не определено"
        match = self._manual_group_match(rec)
        if match and match.get("verdict") != auto:
            return match
        return None

    def _apply_all_work_groups(self, show_message=True):
        self.work_groups = load_work_groups() if not self.work_groups else self.work_groups
        changed = 0
        for r in self.records:
            match = self._manual_group_match(r)
            if not match:
                continue
            verdict = match["verdict"]
            r["matched_work_group"] = match["group"]
            r["work_group_score"] = match.get("score", 0.0)
            # Пользовательские правила влияют на автоматический вердикт.
            # Ручное ранее подтверждённое решение не перезаписываем.
            if str(r.get("checked", "Нет")) == "Да" and self._current_status(r) in ("Изменено вручную", "Подтверждено", "Оставлено неизвестным"):
                continue
            auto = self._norm(r.get("auto_verdict") or r.get("verdict")) or "Не определено"
            if auto != verdict or self._norm(r.get("source")) != "group":
                r["auto_verdict"] = verdict
                r["final_verdict"] = verdict
                r["verdict"] = verdict
                r["source"] = "group"
                r["reason"] = f"Ручное правило группы «{match['group']}»: подгруппа «{match['matched']}» ({match.get('score',0.0):.0%})"
                r["checked"] = "Нет"
                r["review_status"] = "Не проверено"
                changed += 1
        self.app.review_records = list(self.records)
        save_work_groups(self.work_groups)
        try:
            self.app._save_review_snapshot()
            if getattr(self.app, "review_df", None) is not None:
                for rec in self.records:
                    idx = rec.get("row_index")
                    if idx in self.app.review_df.index:
                        fv = rec.get("final_verdict") or rec.get("verdict") or None
                        self.app.review_df.at[idx, "Авто вердикт"] = rec.get("auto_verdict") or None
                        self.app.review_df.at[idx, "Вердикт ИИ"] = fv
                        self.app.review_df.at[idx, "Счет"] = format_accounts(fv)
                        self.app.review_df.at[idx, "Источник"] = rec.get("source") or ""
                        self.app.review_df.at[idx, "Основание решения"] = rec.get("reason") or ""
                        self.app.review_df.at[idx, "Категория работы"] = rec.get("work_category") or ""
                if self.app.config.output_excel:
                    self.app._save_export_excel()
        except Exception as e:
            logger.warning(f"Не удалось записать родительские группы в результат: {e}")
        self._refresh_all(keep_selection=True)
        if show_message:
            messagebox.showinfo("Группы", f"Применено правил: {changed} позиций. Будущие совпадения будут получать тот же классификатор.", parent=self.top)
        return changed

    def _build_positions_tab(self):
        paned = ttk.PanedWindow(self.positions_tab, orient=tk.HORIZONTAL)
        paned.pack(fill=tk.BOTH, expand=True)
        left, right = ttk.Frame(paned), ttk.Frame(paned)
        paned.add(left, weight=9)
        paned.add(right, weight=6)

        top_left = tk.Frame(left, bg="#ffffff", padx=2, pady=3)
        top_left.pack(fill=tk.X)
        self.queue_info = tk.Label(top_left, text="", fg="#475569", anchor="w", bg="#ffffff",
                                   font=("Segoe UI", 9, "bold"))
        self.queue_info.pack(side=tk.LEFT)
        self.auto_next = tk.BooleanVar(value=False)
        tk.Checkbutton(top_left, text="После сохранения выбрать следующую", variable=self.auto_next,
                       bg="#ffffff", fg="#475569", activebackground="#ffffff").pack(side=tk.RIGHT)
        tk.Button(top_left, text="Следующая непроверенная", command=lambda: self._focus_next_unchecked(force=True),
                  bg="#334155", fg="white", relief="flat", padx=10, pady=4,
                  font=("Segoe UI", 9, "bold")).pack(side=tk.RIGHT, padx=6)

        frame = ttk.Frame(left)
        frame.pack(fill=tk.BOTH, expand=True)
        cols = ("work", "category", "auto", "final", "status", "fewshot")
        self.tree = ttk.Treeview(frame, columns=cols, show="tree headings", selectmode="browse")
        self.tree.heading("#0", text="Позиция")
        for c, t in (("work", "Работа / услуга"), ("category", "Группа"), ("auto", "Авто"),
                     ("final", "Итог"), ("status", "Статус"), ("fewshot", "Few-shot")):
            self.tree.heading(c, text=t)
        self.tree.column("#0", width=300, minwidth=180)
        self.tree.column("work", width=280, minwidth=160)
        self.tree.column("category", width=160, minwidth=110)
        self.tree.column("auto", width=130, minwidth=100)
        self.tree.column("final", width=140, minwidth=110)
        self.tree.column("status", width=140, minwidth=100)
        self.tree.column("fewshot", width=100, minwidth=80)
        sc_y = ttk.Scrollbar(frame, orient=tk.VERTICAL, command=self.tree.yview)
        sc_x = ttk.Scrollbar(frame, orient=tk.HORIZONTAL, command=self.tree.xview)
        self.tree.configure(yscrollcommand=sc_y.set, xscrollcommand=sc_x.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        sc_y.grid(row=0, column=1, sticky="ns")
        sc_x.grid(row=1, column=0, sticky="ew")
        frame.rowconfigure(0, weight=1)
        frame.columnconfigure(0, weight=1)
        self.tree.bind("<<TreeviewSelect>>", self._on_select)
        self.tree.tag_configure("group", font=("Segoe UI", 9, "bold"), background="#e2e8f0")
        self.tree.tag_configure("unknown", background="#fff1f2")
        self.tree.tag_configure("manual", background="#fff7ed")
        self.tree.tag_configure("confirmed", background="#f0fdf4")
        self.tree.tag_configure("rule", background="#ecfdf5")
        self.tree.tag_configure("ai", background="#eff6ff")
        self.tree.tag_configure("cache", background="#f8fafc")

        detail = ttk.LabelFrame(right, text="Позиция", padding=8)
        detail.pack(fill=tk.BOTH, expand=True)

        # Заголовок + метаданные — Text (readonly), чтобы копировать заказ/позицию/СФ
        title_row = tk.Frame(detail)
        title_row.pack(fill=tk.X, pady=(0, 2))
        self.detail_title = tk.Text(
            title_row, height=2, wrap=tk.WORD, font=("Segoe UI", 13, "bold"),
            relief="flat", bg="#f8fafc", fg="#0f172a", padx=2, pady=2,
            cursor="xterm", exportselection=True
        )
        self.detail_title.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self._make_text_selectable(self.detail_title)
        tk.Button(
            title_row, text="Копировать", command=self._copy_detail_all,
            bg="#e2e8f0", fg="#334155", relief="flat", padx=8, pady=2,
            font=("Segoe UI", 8, "bold"), cursor="hand2"
        ).pack(side=tk.RIGHT, padx=(4, 0))
        Tooltip(title_row.winfo_children()[-1], "Скопировать название, заказ, описание и AI-совет в буфер обмена (Ctrl+C тоже работает в полях).")

        self.detail_meta = tk.Text(
            detail, height=2, wrap=tk.WORD, font=("Segoe UI", 9),
            relief="flat", bg="#f1f5f9", fg="#475569", padx=4, pady=3,
            cursor="xterm", exportselection=True
        )
        self.detail_meta.pack(fill=tk.X, pady=(0, 4))
        self._make_text_selectable(self.detail_meta)

        # Описание работ — компактнее, со скроллом; можно выделять и копировать
        desc_frame = ttk.LabelFrame(detail, text="Описание (выделение мышью + Ctrl+C)", padding=3)
        desc_frame.pack(fill=tk.BOTH, expand=False, pady=(0, 4))
        self.detail_text = scrolledtext.ScrolledText(
            desc_frame, height=9, wrap=tk.WORD, font=("Consolas", 9),
            cursor="xterm", exportselection=True, undo=False
        )
        self.detail_text.pack(fill=tk.BOTH, expand=True)
        self._make_text_selectable(self.detail_text)

        cat_box = ttk.LabelFrame(detail, text="Категория работы — только для аналитики", padding=6)
        cat_box.pack(fill=tk.X, pady=(2, 4))
        cat_row = tk.Frame(cat_box)
        cat_row.pack(fill=tk.X)
        self.selected_category = tk.StringVar(value="")
        self.category_edit = ttk.Combobox(cat_row, textvariable=self.selected_category, state="normal", width=32)
        self.category_edit.pack(side=tk.LEFT, fill=tk.X, expand=True)
        tk.Button(cat_row, text="Сохранить категорию", command=self._save_category,
                  bg="#0f766e", fg="white", relief="flat", width=18, height=1,
                  font=("Segoe UI", 9, "bold")).pack(side=tk.LEFT, padx=(6, 0))
        tk.Label(cat_box, text="Не влияет на 5 классов классификации.", fg="#64748b", font=("Segoe UI", 8)).pack(anchor="w", pady=(2, 0))

        box = ttk.LabelFrame(detail, text="Классификация", padding=6)
        box.pack(fill=tk.X, pady=(0, 4))
        self.selected_verdict = tk.StringVar(value="Не определено")
        quick = tk.Frame(box)
        quick.pack(fill=tk.X)
        verdict_btns = [
            ("1", "Быстрая стройка"), ("2", "Быстрая стройка + ОС"),
            ("3", "Оборудование"), ("4", "Ремонт ОС"), ("5", "ПРОПУСК"),
        ]
        self._verdict_buttons = {}
        for key, verdict in verdict_btns:
            btn = tk.Button(quick, text=f"{key}. {verdict}", command=lambda v=verdict: self._quick_set(v),
                            bg="#f8fafc", fg="#0f172a", relief="ridge", height=2,
                            font=("Segoe UI", 8, "bold"), cursor="hand2")
            btn.pack(side=tk.LEFT, padx=2, fill=tk.X, expand=True)
            self._verdict_buttons[verdict] = btn

        self.selected_verdict_label = tk.Label(box, text="Выбрано: Не определено", anchor="w", fg="#475569", font=("Segoe UI", 9, "bold"))
        self.selected_verdict_label.pack(fill=tk.X, pady=(4, 3))

        actions = tk.Frame(box)
        actions.pack(fill=tk.X)
        self.btn_save_decision = tk.Button(actions, text="Сохранить решение", command=self._save_manual,
                                           bg="#2563eb", fg="white", relief="flat", height=2,
                                           font=("Segoe UI", 9, "bold"))
        self.btn_save_decision.pack(side=tk.LEFT, padx=2, fill=tk.X, expand=True)
        self.btn_confirm = tk.Button(actions, text="Подтвердить AI-решение", command=self._confirm_auto,
                                     bg="#16a34a", fg="white", relief="flat", height=2,
                                     font=("Segoe UI", 9, "bold"))
        self.btn_confirm.pack(side=tk.LEFT, padx=2, fill=tk.X, expand=True)
        self.btn_unknown = tk.Button(actions, text="Оставить неизвестным", command=self._mark_unknown,
                                     bg="#64748b", fg="white", relief="flat", height=2,
                                     font=("Segoe UI", 9, "bold"))
        self.btn_unknown.pack(side=tk.LEFT, padx=2, fill=tk.X, expand=True)
        tk.Label(box, text="Одно сохранение применяется ко всем одинаковым работам во всех заказах и создаёт один эталон для AI. Отдельно добавлять Few-shot не нужно.",
                 fg="#475569", wraplength=660, justify=tk.LEFT, font=("Segoe UI", 8)).pack(fill=tk.X, pady=(5, 0))

        fsrow = tk.Frame(box)
        fsrow.pack(fill=tk.X, pady=(5, 0))
        self.btn_ai_advice = tk.Button(fsrow, text="AI-совет по этой позиции", command=self._ask_ai_advice,
                  bg="#7c3aed", fg="white", relief="flat", width=24, height=1, font=("Segoe UI", 9, "bold"))
        self.btn_ai_advice.pack(side=tk.LEFT, padx=2)
        tk.Label(fsrow, text="AI-совет только помогает проверить выбор и ничего не сохраняет.",
                 fg="#64748b", font=("Segoe UI", 8)).pack(side=tk.LEFT, padx=8)

        # AI-совет — расширенная область со скроллом и возможностью копирования
        advice_box = ttk.LabelFrame(detail, text="AI-совет (выделение + Ctrl+C)", padding=3)
        advice_box.pack(fill=tk.BOTH, expand=True, pady=(4, 0))
        self.advice_label = scrolledtext.ScrolledText(
            advice_box, height=7, wrap=tk.WORD, font=("Segoe UI", 9),
            fg="#4c1d95", bg="#f5f3ff", cursor="xterm", exportselection=True, undo=False
        )
        self.advice_label.pack(fill=tk.BOTH, expand=True)
        self._make_text_selectable(self.advice_label)

    # ---------- state/filtering ----------
    def _current_status(self, r):
        status = self._norm(r.get("review_status"))
        if status:
            return status
        checked = str(r.get("checked", "Нет")) == "Да"
        final = self._norm(r.get("final_verdict") or r.get("verdict")) or "Не определено"
        auto = self._norm(r.get("auto_verdict") or r.get("verdict")) or "Не определено"
        src = self._norm(r.get("source"))
        if not checked:
            return "Не проверено"
        if final == "Не определено":
            return "Оставлено неизвестным"
        if src == "confirmed" and final == auto:
            return "Подтверждено авто"
        if src == "manual":
            return "Изменено вручную"
        return "Подтверждено"

    def _filtered(self):
        q = self.search_var.get().strip().lower()
        mode = self.mode_filter.get()
        source = self.source_filter.get()
        sapf = self.sap_filter.get()
        category = self.category_filter.get()
        # «Не определено» в фильтре категории = пустые + без категории
        category_is_unknown = category in (UNKNOWN_WORK_CATEGORY, "Без категории")
        if not self._search_index or len(self._search_index) != len(self.records):
            self._rebuild_search_index()
        out = []
        for i, r in enumerate(self.records):
            a = self._norm(r.get("auto_verdict") or r.get("verdict")) or "Не определено"
            f = self._norm(r.get("final_verdict") or r.get("verdict")) or "Не определено"
            src = self._norm(r.get("source")) or "unknown"
            status = self._current_status(r)
            cat = self._work_category_label(r)
            has_sap = bool(r.get("services_and_materials")) or bool(self._norm(r.get("item_name")))
            fs_added = bool(r.get("fewshot_added"))

            # Кеш в записи + индекс: без пересборки semantic_text на каждый символ
            if q:
                hay = r.get("_search_haystack") if isinstance(r, dict) else None
                if not isinstance(hay, str) or not hay:
                    hay = self._search_index[i] if i < len(self._search_index) else self._ensure_search_haystack(r)
                if q not in hay:
                    continue

            if mode == "На проверку":
                if status != "Не проверено":
                    continue
                # Предвычисленные флаги — без тяжёлого match на каждый refresh
                if r.get("_fs_trusted"):
                    continue
                if r.get("_group_trusted"):
                    continue
            if mode == "Few-shot требует проверки":
                if status != "Не проверено":
                    continue
                if r.get("_fs_trusted"):
                    continue
                match = self._fewshot_match(r)
                if match is None and f != "Не определено":
                    continue
            if mode == "Ручная группа требует проверки":
                if status != "Не проверено":
                    continue
                if self._manual_group_conflict(r) is None:
                    continue
            if mode == "Не определено" and f != "Не определено":
                continue
            if mode == "Проверено" and status == "Не проверено":
                continue
            if mode == "Изменено вручную" and status != "Изменено вручную":
                continue
            if mode == "Подтверждено авто" and status != "Подтверждено авто":
                continue
            if mode == "Few-shot добавлен" and not fs_added:
                continue
            if mode == "Few-shot не добавлен" and fs_added:
                continue
            if source != "Все" and src != source:
                continue
            if sapf == "Есть данные" and not has_sap:
                continue
            if sapf == "Нет данных" and has_sap:
                continue
            if category != "Все":
                if category_is_unknown:
                    if cat != UNKNOWN_WORK_CATEGORY:
                        continue
                elif cat != category:
                    continue
            out.append((i, r, a, f, src, status, self._primary_work(r), cat, fs_added))
        return out

    def _group_key(self, rec, a, f, src, work):
        mode = self.group_by.get()
        if mode == "Категория работы":
            return self._work_category_label(rec)
        if mode == "Работа / услуга":
            return self._primary_work(rec).strip()[:180]
        if mode == "Авто вердикт":
            return a or "Не определено"
        if mode == "Итоговый вердикт":
            return f or "Не определено"
        return "__flat__"

    # Мягкий лимит строк в Treeview: дальше Tk тормозит на вставке.
    MAX_TREE_ROWS = 2500

    def _refresh_positions(self, keep_selection=True, update_header: bool = True):
        if not hasattr(self, "tree"):
            return
        current = self.selected_idx if keep_selection else None
        try:
            self.tree.delete(*self.tree.get_children())
        except Exception:
            try:
                for iid in self.tree.get_children():
                    self.tree.delete(iid)
            except Exception:
                pass
        try:
            rows = self._filtered()
        except Exception as e:
            logger.warning(f"_filtered failed: {e}")
            rows = []
        self._last_visible_count = len(rows)
        truncated = False
        try:
            if self.group_by.get() == "Без группировки":
                seq = list(rows)
                reverse = self.sort_mode.get() == "Я → А"
                seq.sort(key=lambda x: self._title(x[1]).lower(), reverse=reverse)
                if len(seq) > self.MAX_TREE_ROWS:
                    seq = seq[: self.MAX_TREE_ROWS]
                    truncated = True
                for item in seq:
                    try:
                        self._insert_row("", *item)
                    except Exception:
                        continue
            else:
                groups = {}
                for item in rows:
                    try:
                        groups.setdefault(self._group_key(item[1], item[2], item[3], item[4], item[6]), []).append(item)
                    except Exception:
                        continue
                items = list(groups.items())
                sm = self.sort_mode.get()
                if sm == "A → Я":
                    items.sort(key=lambda x: str(x[0]).lower())
                elif sm == "Я → А":
                    items.sort(key=lambda x: str(x[0]).lower(), reverse=True)
                elif sm == "Количество ↑":
                    items.sort(key=lambda x: len(x[1]))
                else:
                    items.sort(key=lambda x: len(x[1]), reverse=True)
                inserted = 0
                for n, (g, group_rows) in enumerate(items):
                    if inserted >= self.MAX_TREE_ROWS:
                        truncated = True
                        break
                    gid = f"g:{n}"
                    try:
                        self.tree.insert("", "end", iid=gid, text=f"{g}  ({len(group_rows)})",
                                         values=("", g, "", "", "", ""), open=False, tags=("group",))
                        group_rows.sort(key=lambda x: self._title(x[1]).lower())
                        for item in group_rows:
                            if inserted >= self.MAX_TREE_ROWS:
                                truncated = True
                                break
                            try:
                                self._insert_row(gid, *item)
                                inserted += 1
                            except Exception:
                                continue
                    except Exception:
                        continue
        except Exception as e:
            logger.warning(f"_refresh_positions build failed: {e}")
        if truncated and hasattr(self, "queue_info"):
            try:
                self.queue_info.config(
                    text=f"Показано первые {self.MAX_TREE_ROWS:,} из {self._last_visible_count:,} "
                         f"(сузьте фильтр для полного списка)".replace(",", " ")
                )
            except Exception:
                pass
        if update_header:
            try:
                self._refresh_header(visible_count=getattr(self, "_last_visible_count", None))
            except Exception as e:
                logger.debug(f"_refresh_header: {e}")
        if current is not None:
            try:
                if self.tree.exists(f"r:{current}"):
                    self.tree.selection_set(f"r:{current}")
                    self.tree.see(f"r:{current}")
                    self._on_select()
            except Exception:
                pass

    def _insert_row(self, parent, i, r, a, f, src, status, work, cat, fs_added):
        tag = "unknown" if f == "Не определено" else ("manual" if status == "Изменено вручную" else ("confirmed" if status == "Подтверждено авто" else src))
        self.tree.insert(parent, "end", iid=f"r:{i}", text=self._title(r),
                         values=(work, cat, a, f, status, "✓ Да" if fs_added else "—"), tags=(tag,))

    def _refresh_header(self, visible_count=None):
        """Один проход по records для счётчиков — без повторного _filtered/_fewshot_match."""
        total = len(self.records)
        unchecked = unknown = manual = checked = 0
        cats = set()
        hidden_fs = 0
        hidden_group = 0
        for r in self.records:
            if not isinstance(r, dict):
                continue
            status = self._current_status(r)
            final = self._norm(r.get("final_verdict") or r.get("verdict")) or "Не определено"
            if status == "Не проверено":
                unchecked += 1
                if r.get("_fs_trusted"):
                    hidden_fs += 1
                if r.get("_group_trusted"):
                    hidden_group += 1
            elif status == "Изменено вручную":
                manual += 1
                checked += 1
            elif status in ("Подтверждено", "Подтверждено авто", "Оставлено неизвестным"):
                checked += 1
            if final == "Не определено":
                unknown += 1
            cats.add(self._work_category_label(r))
        try:
            fs_count = len(self.master.confirmed_examples())
        except Exception:
            fs_count = 0
        if hasattr(self, "header_info"):
            self.header_info.config(
                text=f"Позиции: {total:,} • Проверено: {checked:,} • Осталось: {unchecked:,}".replace(",", " ")
            )
        values = {"unchecked": unchecked, "unknown": unknown, "checked": checked, "fewshot": fs_count}
        for key, value in values.items():
            if hasattr(self, "summary_cards") and key in self.summary_cards:
                self.summary_cards[key].config(text=f"{value:,}".replace(",", " "))
        cat_list = sorted(cats)
        for g in RESERVED_WORK_GROUPS:
            if g not in cat_list:
                cat_list.append(g)
        if UNKNOWN_WORK_CATEGORY not in cat_list:
            cat_list.insert(0, UNKNOWN_WORK_CATEGORY)
        if hasattr(self, "category_combo"):
            self.category_combo["values"] = ["Все"] + cat_list
            if self.category_filter.get() not in ["Все"] + cat_list:
                self.category_filter.set("Все")
        if visible_count is None:
            visible_count = getattr(self, "_last_visible_count", total)
        if hasattr(self, "queue_info"):
            self.queue_info.config(text=(
                f"Показано {visible_count:,} из {total:,}  •  скрыто Few-shot: {hidden_fs:,}  "
                f"•  скрыто ручными группами: {hidden_group:,}"
            ).replace(",", " "))

    def _refresh_all(self, keep_selection=True):
        # Категории — только если ещё не проставлены (полный проход дорогой)
        need_cats = any(
            isinstance(r, dict) and not self._norm(r.get("work_category"))
            for r in self.records[:50]
        ) if self.records else False
        if need_cats or not any(isinstance(r, dict) and r.get("work_category") for r in self.records[:20]):
            self._apply_cached_work_categories()
        self._normalize_review_state()
        # Сброс индекса групп — ключи могли измениться
        self._group_members_index = None
        # Пересчёт trust только для записей без флагов (или после смены few-shot)
        for r in self.records:
            if isinstance(r, dict):
                r.pop("_fs_trusted", None)
                r.pop("_group_trusted", None)
        self._precompute_trust_flags(only_unchecked=True)
        if not getattr(self, "work_groups", None):
            self.work_groups = load_work_groups()
        self._refresh_positions(keep_selection=keep_selection, update_header=True)
        self._refresh_fewshot_list()
        if hasattr(self, "group_tree"):
            self._refresh_group_tree()
            self._refresh_group_available()
        if self.selected_idx is not None and self.tree.exists(f"r:{self.selected_idx}"):
            self.tree.selection_set(f"r:{self.selected_idx}")
            self.tree.see(f"r:{self.selected_idx}")

    def _summary_click(self, key):
        # Оставлено для совместимости, но карточки v5.1 не кликабельны.
        return

    def _show_unchecked(self):
        self.mode_filter.set("На проверку")
        self._refresh_positions(keep_selection=False)
        self._focus_unchecked()
        self.footer_status.config(text="На проверку: новые/конфликтные позиции. Совпавшие Few-shot автоматически скрыты.")

    def _show_unknown(self):
        self.mode_filter.set("Не определено")
        self._refresh_positions(keep_selection=False)
        self._focus_unknown()

    def _clear_filters(self):
        self._reset_view()

    def _select_record_if_visible(self, idx):
        self.selected_idx = idx
        iid = f"r:{idx}"
        if self.tree.exists(iid):
            self.tree.selection_set(iid)
            self.tree.see(iid)
            self._on_select()
            return True
        return False

    def _focus_next_unchecked(self, force=False):
        rows = [x[0] for x in self._filtered() if self._current_status(x[1]) == "Не проверено"]
        if not rows:
            if force:
                messagebox.showinfo("Очередь", "В текущем фильтре больше нет непроверенных позиций.", parent=self.top)
            return
        if self.selected_idx in rows:
            pos = rows.index(self.selected_idx)
            target = rows[(pos + 1) % len(rows)]
        else:
            target = rows[0]
        self._select_record_if_visible(target)

    def _set_readonly_text(self, widget, text: str):
        """Безопасно заполняет readonly Text/ScrolledText без потери возможности выделения."""
        if widget is None:
            return
        try:
            widget.configure(state=tk.NORMAL)
            widget.delete("1.0", tk.END)
            widget.insert("1.0", text or "")
            widget.configure(state=tk.NORMAL)  # оставляем NORMAL — правки блокирует _make_text_selectable
            widget.see("1.0")
        except Exception as e:
            logger.debug(f"_set_readonly_text: {e}")

    def _make_text_selectable(self, widget):
        """Readonly Text: мышь + Ctrl+C / Ctrl+A, без правки содержимого."""
        if widget is None or getattr(widget, "_selectable_bound", False):
            return

        nav_keys = {
            "Left", "Right", "Up", "Down", "Home", "End", "Prior", "Next",
            "Shift_L", "Shift_R", "Control_L", "Control_R", "Alt_L", "Alt_R",
            "Tab", "ISO_Left_Tab", "Escape", "Return", "KP_Enter",
        }
        allow_ctrl = {"c", "C", "a", "A", "Insert"}

        def _on_key(event):
            # Ctrl+C / Ctrl+A — разрешены
            if event.state & 0x4:  # Control
                if event.keysym in allow_ctrl:
                    return None
                return "break"
            if event.keysym in nav_keys:
                return None
            # Остальные клавиши (ввод текста) — блокируем
            return "break"

        def _block_edit(_event=None):
            return "break"

        widget.bind("<Key>", _on_key, add="+")
        widget.bind("<<Paste>>", _block_edit, add="+")
        widget.bind("<<Cut>>", _block_edit, add="+")
        # Колёсико мыши для скролла работает по умолчанию у ScrolledText
        widget._selectable_bound = True

    def _copy_detail_all(self):
        """Копирует карточку позиции целиком в буфер обмена."""
        try:
            parts = []
            for w in (getattr(self, "detail_title", None),
                      getattr(self, "detail_meta", None),
                      getattr(self, "detail_text", None),
                      getattr(self, "advice_label", None)):
                if w is None:
                    continue
                try:
                    t = w.get("1.0", "end-1c").strip()
                    if t:
                        parts.append(t)
                except Exception:
                    pass
            payload = "\n\n".join(parts).strip()
            if not payload:
                return
            self.top.clipboard_clear()
            self.top.clipboard_append(payload)
            self.top.update_idletasks()
            if hasattr(self, "footer_status"):
                self.footer_status.config(text="Скопировано в буфер обмена")
        except Exception as e:
            logger.warning(f"Копирование карточки: {e}")

    def _on_select(self, _event=None):
        sel = self.tree.selection()
        if not sel or not sel[0].startswith("r:"):
            return
        try:
            i = int(sel[0][2:])
        except (ValueError, TypeError):
            return
        if i < 0 or i >= len(self.records):
            return
        self.selected_idx = i
        r = self.records[i]
        if not isinstance(r, dict):
            return
        auto = self._norm(r.get("auto_verdict") or r.get("verdict")) or "Не определено"
        final = self._norm(r.get("final_verdict") or r.get("verdict")) or "Не определено"
        self.selected_verdict.set(final if final in self.VERDICTS else "Не определено")
        if hasattr(self, "selected_verdict_label"):
            self.selected_verdict_label.config(text=f"Выбрано: {final}")
        for name, btn in getattr(self, "_verdict_buttons", {}).items():
            try:
                btn.config(relief="sunken" if name == final else "ridge", bd=3 if name == final else 2)
            except Exception:
                pass
        self.selected_category.set(self._norm(r.get("work_category")))
        try:
            cats = sorted({self._norm(x.get("work_category")) for x in self.records if self._norm(x.get("work_category"))})
            extra = [g for g in RESERVED_WORK_GROUPS if g not in cats]
            if UNKNOWN_WORK_CATEGORY not in cats:
                extra = [UNKNOWN_WORK_CATEGORY] + extra
            self.category_edit["values"] = list(cats) + extra
        except Exception:
            pass
        services = self._service_list(r)
        service_text = "\n".join(f"• {x}" for x in services) if services else "Нет сохранённых работ/услуг из SAP."
        status = self._current_status(r)
        try:
            fs = "Эталон есть" if self._fewshot_trusted(r) else "Нового эталона нет"
        except Exception:
            fs = "—"
        fs_match = None
        try:
            fs_match = self._fewshot_match(r)
        except Exception:
            fs_match = None
        fs_note = ""
        if fs_match:
            ex = fs_match.get("example") or {}
            expected = self._norm(ex.get("verdict")) or "Не определено"
            score = fs_match.get("score", 0.0)
            if expected == auto:
                fs_note = f"  •  ✓ Few-shot совпадает: {expected} ({score:.0%})"
            else:
                fs_note = f"  •  ⚠ Few-shot ожидает: {expected} ({score:.0%})"
        self._set_readonly_text(self.detail_title, self._title(r))
        acc = format_accounts(final) or "—"
        self._set_readonly_text(self.detail_meta, (
            f"Заказ {self._norm(r.get('order_number')) or '—'}  •  Поз. {self._norm(r.get('item_number')) or '—'}  •  СФ {self._norm(r.get('reference_document')) or '—'}\n"
            f"Авто: {auto}  •  Итог: {final}  •  Счет: {acc}  •  Статус: {status}  •  Few-shot: {fs}{fs_note}"
        ))
        self._set_readonly_text(self.detail_text, (
            f"НАЗВАНИЕ SAP\n{self._norm(r.get('item_name')) or '—'}\n\n"
            f"РАБОТЫ / УСЛУГИ / МАТЕРИАЛЫ\n{service_text}\n\n"
            f"ОСНОВАНИЕ АВТОМАТИЧЕСКОГО РЕШЕНИЯ\n{self._norm(r.get('reason')) or '—'}\n\n"
            f"КАТЕГОРИЯ РАБОТЫ\n{self._norm(r.get('work_category')) or 'Не назначена'}\n\n"
            f"СЕМАНТИЧЕСКИЙ ТЕКСТ ДЛЯ FEW-SHOT\n{self._semantic_text(r) or '—'}"
        ))
        self._set_readonly_text(self.advice_label, "")
        self.footer_status.config(text=f"Выбрана позиция {i + 1} из {len(self.records)}")

    # ---------- explicit actions ----------
    def _quick_set(self, verdict):
        self.selected_verdict.set(verdict)
        self._ux51_pending_selection = True
        if hasattr(self, "selected_verdict_label"):
            self.selected_verdict_label.config(text=f"Выбрано: {verdict}")
        for name, btn in getattr(self, "_verdict_buttons", {}).items():
            btn.config(relief="sunken" if name == verdict else "ridge", bd=3 if name == verdict else 2)
        group_count = len(self._classification_group_members(self.records[self.selected_idx])) if self.selected_idx is not None else 1
        self.footer_status.config(text=f"Выбрано: {verdict}. После сохранения решение применится к {group_count} одинаковым позициям.")

    def _update_record(self, verdict, checked=True, source=None, reason=None, add_fs=False, bulk_update=True):
        """Применяет вердикт к семантической группе.

        bulk_update=True (по умолчанию): один проход по членам группы в памяти,
        один снимок review_session и один отложенный flush Excel — без записи
        JSON на каждую строку (критично при 5 000+ одинаковых позиций).
        """
        if self.selected_idx is None:
            return

        selected = self.records[self.selected_idx]
        members = self._classification_group_members(selected)
        group_count = len(members)
        bulk = bool(bulk_update) or group_count > 1

        # Одно ручное решение распространяется на все строки с тем же
        # семантическим описанием позиции, независимо от заказа/позиции/СФ/МВЗ.
        member_recs = []
        for member_idx in members:
            r = self.records[member_idx]
            auto = self._norm(r.get("auto_verdict") or r.get("verdict")) or "Не определено"
            r["final_verdict"] = verdict
            r["verdict"] = verdict
            r["checked"] = "Да" if checked else "Нет"
            if source:
                r["source"] = source
            if reason is not None:
                r["reason"] = reason
            if verdict == "Не определено":
                r["review_status"] = "Оставлено неизвестным"
            elif source == "confirmed" and verdict == auto:
                r["review_status"] = "Подтверждено авто"
            elif source == "manual":
                r["review_status"] = "Изменено вручную"
            else:
                r["review_status"] = "Подтверждено"
            # Статус/вердикт не меняют haystack поиска — кеш оставляем.

            # Инвалидируем только соответствующий старый cache-key; не пишем
            # отдельный JSON-снимок на каждую строку группы.
            if source in ("manual", "confirmed"):
                if not hasattr(self.app, "_pending_cache_invalidations"):
                    self.app._pending_cache_invalidations = set()
                order = str(r.get("order_number") or "")
                item = str(r.get("item_number") or "").zfill(5)
                ref = str(r.get("reference_document") or "NO_REF")
                mvz = str(r.get("cost_center") or "NO_MVZ")
                self.app._pending_cache_invalidations.add(f"{order}:{item}:{ref}:{mvz}")

            write_verdict_columns(self.app.review_df, r.get("row_index"), r)
            member_recs.append(r)

        # Без лишнего list()-копирования всего массива на каждую строку группы
        self.app.review_records = self.records

        # В master JSON — ОДИН эталон на семантическую группу (не N дублей).
        try:
            if verdict != "Не определено":
                self.master.confirm(selected, member_recs, verdict, source=source or "manual")
            # merge_run_rows тяжёлый на 5k+: при bulk достаточно confirm + отложенный merge
            if not bulk or group_count <= 50:
                self.master.merge_run_rows(self.records)
                self.master.save()
            else:
                # Крупная группа: confirm уже сохранил эталон; полный merge — в фоне/по закрытию
                try:
                    self.master.save()
                except Exception:
                    pass
        except Exception as master_err:
            logger.warning(f"Не удалось обновить classification master: {master_err}")

        # Один снимок сессии на всю группу (с debounce для больших файлов)
        try:
            if bulk and group_count >= 20:
                self.app._schedule_review_snapshot(delay_ms=800)
            else:
                self.app._save_review_snapshot()
        except Exception as e:
            logger.warning(f"Не удалось сохранить сеанс проверки: {e}")
        self.app._schedule_excel_flush(delay_ms=2500 if group_count < 100 else 4000)

        if add_fs and verdict != "Не определено":
            self._add_selected_to_fewshot(show_message=False)

        self._ux51_pending_selection = False
        self._refresh_all(keep_selection=True)
        self.footer_status.config(
            text=(f"Решение сохранено для {group_count} одинаковых позиций."
                  if group_count > 1 else "Решение сохранено.")
        )
        if self.auto_next.get():
            self._focus_next_unchecked()

    def _confirm_auto(self):
        if self.selected_idx is None:
            return
        r = self.records[self.selected_idx]
        auto = self._norm(r.get("auto_verdict") or r.get("verdict")) or "Не определено"
        if auto == "Не определено":
            messagebox.showwarning("Проверка", "Автоматическое решение не определено. Выбери классификатор вручную или оставь неизвестным.", parent=self.top)
            return
        self._update_record(auto, True, "confirmed", "Подтверждено пользователем без изменения автоматического решения.", True)

    def _save_manual(self):
        verdict = self.selected_verdict.get().strip() or "Не определено"
        if verdict == "Не определено":
            self._mark_unknown()
            return
        self._update_record(verdict, True, "manual", "Решение выбрано пользователем вручную.", False)

    def _mark_unknown(self):
        self.selected_verdict.set("Не определено")
        self._update_record("Не определено", True, "manual", "Пользователь оставил позицию без классификации.", False)

    def _export_classifier_pending(self):
        """Выгрузка Excel только по позициям, которые ещё нужно классифицировать.

        Исключаются: уже проверенные, доверенные Few-shot, доверенные ручные группы.
        В файл попадают исходные колонки + «Вердикт ИИ», «Счет», «Категория работы».
        """
        review_df = getattr(self.app, "review_df", None)
        if review_df is None or review_df.empty:
            messagebox.showwarning(
                "Выгрузка классификатора",
                "Нет данных для выгрузки. Сначала выполни прогон или загрузи сеанс проверки.",
                parent=self.top,
            )
            return

        # Флаги доверия могли не быть посчитаны — досчитаем.
        try:
            self._precompute_trust_flags()
        except Exception:
            pass

        pending_indices = []
        for r in self.records:
            if not isinstance(r, dict):
                continue
            if str(r.get("checked", "Нет")) == "Да":
                continue
            if r.get("_fs_trusted"):
                continue
            if r.get("_group_trusted"):
                continue
            # «На проверку» без авто-вердикта тоже включаем
            idx = r.get("row_index")
            if idx is None:
                continue
            if idx in review_df.index:
                pending_indices.append(idx)

        pending_indices = sorted(set(pending_indices))
        if not pending_indices:
            messagebox.showinfo(
                "Выгрузка классификатора",
                "Позиций для классификации нет — все закрыты, подтверждены Few-shot или ручными группами.",
                parent=self.top,
            )
            return

        try:
            full_export = self.app._prepare_export_df()
            if full_export is None or full_export.empty:
                messagebox.showwarning(
                    "Выгрузка классификатора",
                    "Не удалось подготовить таблицу для Excel.",
                    parent=self.top,
                )
                return
            # Индексы из review_records должны совпадать с index DataFrame
            available = [i for i in pending_indices if i in full_export.index]
            if not available:
                # fallback: по позиции в records (0..n-1) если row_index не совпал
                available = [i for i in pending_indices if i in review_df.index]
                if available:
                    full_export = self.app._prepare_export_df()
            if not available:
                messagebox.showwarning(
                    "Выгрузка классификатора",
                    "Индексы позиций не совпали с Excel-таблицей. Перезапусти прогон или обнови сеанс.",
                    parent=self.top,
                )
                return
            export_df = full_export.loc[available].copy()
        except Exception as e:
            logger.exception("Выгрузка классификатора: подготовка")
            messagebox.showerror("Выгрузка классификатора", f"Ошибка подготовки:\n{e}", parent=self.top)
            return

        out_path = getattr(self.app.config, "output_excel", "") or ""
        if out_path:
            base, ext = os.path.splitext(out_path)
            target = f"{base}_classification_pending{ext or '.xlsx'}"
        else:
            target = filedialog.asksaveasfilename(
                parent=self.top,
                title="Сохранить файл классификатора",
                defaultextension=".xlsx",
                filetypes=[("Excel", "*.xlsx"), ("Все файлы", "*.*")],
                initialfile="classification_pending.xlsx",
            )
            if not target:
                return

        try:
            safe_save_excel(export_df, target)
        except Exception as e:
            logger.exception("Выгрузка классификатора: запись Excel")
            messagebox.showerror("Выгрузка классификатора", f"Не удалось сохранить файл:\n{e}", parent=self.top)
            return

        if hasattr(self, "footer_status"):
            self.footer_status.config(text=f"Классификатор: {len(export_df)} позиций → {os.path.basename(target)}")
        messagebox.showinfo(
            "Выгрузка классификатора",
            f"Выгружено {len(export_df)} позиций для классификации.\n\n{target}",
            parent=self.top,
        )

    def _save_category(self):
        if self.selected_idx is None:
            return
        value = re.sub(r"\s+", " ", self.selected_category.get().strip())
        if not value:
            messagebox.showwarning("Группа работы", "Укажи название группы, например «Контроллеры».", parent=self.top)
            return
        r = self.records[self.selected_idx]
        r["work_category"] = value
        r["work_category_source"] = "manual"
        r.pop("_search_haystack", None)  # категория входит в поиск — сбросить кеш
        # Ручная категория становится устойчивым словарным правилом для будущих совпадений.
        for label in self._work_labels(r):
            key = re.sub(r"\s+", " ", str(label).strip()).lower()
            if key:
                self.work_categories[key] = value
        save_work_categories(self.work_categories)
        self.app._save_review_record(self.selected_idx, r)
        self.app.review_records = self.records
        try:
            self.app._schedule_review_snapshot(delay_ms=500)
        except Exception:
            try:
                self.app._save_review_snapshot()
            except Exception:
                pass
        self._rebuild_search_index()
        self._refresh_all(keep_selection=True)
        self.footer_status.config(text=f"Группа сохранена: {value}")

    def _add_selected_to_fewshot(self, show_message=True):
        """Добавляет только выбранную подтверждённую позицию в Few-shot.

        Это не массовое действие: семантическая группа уже получает итоговый
        вердикт в _update_record, а в Few-shot попадает ровно один
        представитель — выбранная пользователем позиция.
        """
        if self.selected_idx is None:
            return False
        r = self.records[self.selected_idx]
        verdict = self._norm(r.get("final_verdict") or r.get("verdict")) or "Не определено"
        if verdict == "Не определено":
            if show_message:
                messagebox.showwarning("Few-shot", "Сначала выбери классификатор.", parent=self.top)
            return False
        text = self._semantic_text(r)
        if not text:
            if show_message:
                messagebox.showwarning("Few-shot", "Нет семантического описания работ/материалов.", parent=self.top)
            return False

        norm_text = re.sub(r"\s+", " ", str(text).strip()).lower()
        existing = next((ex for ex in self.few_shot._examples
                         if re.sub(r"\s+", " ", str(ex.get("text", "")).strip()).lower() == norm_text), None)
        if existing is not None:
            # Не переактивируем намеренно исключённый пользователем пример.
            r["fewshot_added"] = True
            self._invalidate_trust_flags()
            self._refresh_fewshot_list()
            self._refresh_header()
            if show_message:
                state = "активен" if bool(existing.get("active", True)) else "исключён вручную"
                messagebox.showinfo("Few-shot", f"Позиция уже есть в Few-shot ({state}). Дубликат не создан.", parent=self.top)
            return False

        self.few_shot.add(text, verdict, source="confirmed_review")
        r["fewshot_added"] = True
        self._invalidate_trust_flags()
        self._refresh_fewshot_list()
        self._refresh_header()
        if show_message:
            messagebox.showinfo("Few-shot", "1 выбранная позиция добавлена в Few-shot. Похожие позиции будут скрыты из очереди, если их автоматический вердикт совпадает с эталоном.", parent=self.top)
        return True

    def _on_key(self, event):
        # Не перехватываем ввод/копирование в текстовых полях и combobox
        w = event.widget
        if isinstance(w, (tk.Entry, tk.Text, scrolledtext.ScrolledText, ttk.Entry, ttk.Combobox)):
            return
        # Также если focus внутри ScrolledText-фрейма
        try:
            cls_name = w.winfo_class()
            if cls_name in ("Text", "TEntry", "Entry", "TCombobox"):
                return
        except Exception:
            pass
        key = str(event.keysym)
        if key in self.VERDICT_KEYS:
            self._quick_set(self.VERDICT_KEYS[key])
            return "break"
        if key in ("Return", "KP_Enter"):
            self._save_manual()
            return "break"
        if key == "Down":
            self._focus_next_record(1)
            return "break"
        if key == "Up":
            self._focus_next_record(-1)
            return "break"

    def _focus_next_record(self, delta):
        rows = [x[0] for x in self._filtered()]
        if not rows:
            return
        if self.selected_idx in rows:
            pos = rows.index(self.selected_idx)
            idx = rows[(pos + delta) % len(rows)]
        else:
            idx = rows[0]
        self._select_record_if_visible(idx)



class AuditApp:
    def __init__(self, root: tk.Tk, config: AppConfig):
        self.root = root
        self.config = config
        self.root.title(f"Procurement AI Auditor v{APP_VERSION}")
        self.root.geometry("850x780")
        self.root.minsize(700, 600)
        
        self.is_paused = threading.Event()
        self.is_paused.set()
        self.stop_event = threading.Event()
        self.gui_queue: queue.Queue = queue.Queue()
        self.cache_lock = threading.Lock()
        
        self.session_stats = {
            'cache_hits': 0,
            'ai_calls': 0,
            'rule_hits': 0,
            'errors': 0,
            'start_time': None
        }
        self.review_records = []
        self.review_df = None
        
        self._build_ui()
        self._load_saved_review_snapshot()
        self._check_queue()
        self._validate_config()
    
    def _validate_config(self):
        issues = []
        
        if not self.config.has_sap_config:
            issues.append("SAP_USER не задан")
        if not self.config.has_ai_config:
            issues.append("AI API key не задан")
        
        if issues:
            msg = "Проблемы конфигурации:\n\n" + "\n".join(f"- {i}" for i in issues)
            msg += "\n\nПродолжить?"
            
            if not messagebox.askyesno("Предупреждение", msg):
                self.root.after(100, self.root.quit)

    def _build_ui(self):
        header = tk.Frame(self.root, bg="#1a237e", padx=15, pady=12)
        header.pack(fill=tk.X)
        
        tk.Label(
            header, text=f"Procurement AI Auditor v{APP_VERSION}",
            font=("Segoe UI", 16, "bold"), fg="white", bg="#1a237e"
        ).pack(side=tk.LEFT)
        
        self.status_label = tk.Label(
            header, text="Ожидание",
            font=("Consolas", 11), bg="#283593", fg="white",
            padx=15, pady=5
        )
        self.status_label.pack(side=tk.RIGHT)
        
        files_frame = tk.LabelFrame(
            self.root, text=" Конфигурация ",
            font=("Segoe UI", 10, "bold"), padx=10, pady=10
        )
        files_frame.pack(fill=tk.X, padx=10, pady=5)
        
        self.path_entries = {}
        configs = [
            ("Excel заказов:", "target_excel"),
            ("Справочник стройки:", "base_file"),
            ("Справочник запчастей:", "spare_file"),
            ("Справочник оборудования:", "stroy_file"),
            ("Файл результата:", "output_excel"),
        ]
        for label, attr in configs:
            self._build_file_row(files_frame, label, attr)
        
        tools = tk.Frame(files_frame)
        tools.pack(fill=tk.X, pady=(10, 0))
        
        tk.Button(
            tools, text="Очистить кэш", command=self._clear_cache,
            bg="#ff5722", fg="white", font=("Segoe UI", 9, "bold"),
            relief="flat", padx=8, pady=5
        ).pack(side=tk.LEFT, padx=3)
        tk.Button(
            tools, text="Кэш + Few-shot", command=self._clear_cache_and_fewshot,
            bg="#c62828", fg="white", font=("Segoe UI", 9, "bold"),
            relief="flat", padx=8, pady=5
        ).pack(side=tk.LEFT, padx=3)
        tk.Button(
            tools, text="Сброс всех эталонов", command=self._clear_all_etalons,
            bg="#4a148c", fg="white", font=("Segoe UI", 9, "bold"),
            relief="flat", padx=8, pady=5
        ).pack(side=tk.LEFT, padx=3)

        self.cache_info = tk.Label(
            tools, text=self._get_cache_info(),
            font=("Consolas", 9), fg="#757575"
        )
        self.cache_info.pack(side=tk.LEFT, padx=10)
        
        tk.Button(
            tools, text="Колонки", command=self._configure_input_columns,
            bg="#0f766e", fg="white", font=("Segoe UI", 9, "bold"),
            relief="flat", padx=10, pady=5
        ).pack(side=tk.RIGHT, padx=5)
        self.btn_review = tk.Button(
            tools, text="Проверка классификации", command=self._open_review,
            bg="#2563eb", fg="white", font=("Segoe UI", 9, "bold"),
            relief="flat", padx=10, pady=5, state=tk.DISABLED
        )
        self.btn_review.pack(side=tk.RIGHT, padx=5)
        
        prog_frame = tk.Frame(self.root, padx=10, pady=10)
        prog_frame.pack(fill=tk.X)
        
        self.progress_var = tk.DoubleVar()
        ttk.Progressbar(
            prog_frame, variable=self.progress_var, maximum=100,
            mode="determinate"
        ).pack(fill=tk.X)
        
        self.percent_label = tk.Label(
            prog_frame, text="0%", font=("Segoe UI", 14, "bold"),
            fg="#1976d2"
        )
        self.percent_label.pack(anchor="e")
        
        stats_frame = tk.Frame(self.root, bg="#f5f5f5", padx=10, pady=8)
        stats_frame.pack(fill=tk.X, padx=10, pady=5)
        
        self.stat_labels = {}
        for text, key, color in [
            ("Время", "time", "#5e35b1"),
            ("Кэш", "cache", "#2e7d32"),
            ("Правила", "rules", "#0f766e"),
            ("AI", "ai", "#1565c0"),
            ("Ошибки", "errors", "#c62828"),
        ]:
            frame = tk.Frame(stats_frame, bg="#f5f5f5")
            frame.pack(side=tk.LEFT, expand=True)
            tk.Label(frame, text=text, bg="#f5f5f5", font=("Segoe UI", 9)).pack()
            self.stat_labels[key] = tk.Label(
                frame, text="—", font=("Consolas", 12, "bold"),
                bg="#f5f5f5", fg=color
            )
            self.stat_labels[key].pack()
        
        log_frame = tk.LabelFrame(self.root, text=" Журнал ", font=("Segoe UI", 9))
        log_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        self.log_box = scrolledtext.ScrolledText(
            log_frame, font=("Consolas", 9), state=tk.DISABLED,
            bg="#fafafa", padx=5, pady=5
        )
        self.log_box.pack(fill=tk.BOTH, expand=True)
        
        controls = tk.Frame(self.root, padx=10, pady=10)
        controls.pack(fill=tk.X, side=tk.BOTTOM)
        
        self.btn_start = tk.Button(
            controls, text="СТАРТ", command=self.start_process,
            bg="#4caf50", fg="white", font=("Segoe UI", 11, "bold"),
            relief="flat", padx=25, pady=10, cursor="hand2"
        )
        self.btn_start.pack(side=tk.LEFT, padx=5)
        
        self.btn_pause = tk.Button(
            controls, text="ПАУЗА", command=self.pause_process,
            bg="#ff9800", fg="white", font=("Segoe UI", 11),
            relief="flat", padx=20, pady=10, cursor="hand2",
            state=tk.DISABLED
        )
        self.btn_pause.pack(side=tk.LEFT, padx=5)
        
        self.btn_resume = tk.Button(
            controls, text="Продолжить", command=self.resume_process,
            bg="#2196f3", fg="white", font=("Segoe UI", 11),
            relief="flat", padx=20, pady=10, cursor="hand2",
            state=tk.DISABLED
        )
        self.btn_resume.pack(side=tk.LEFT, padx=5)
        
        self.btn_stop = tk.Button(
            controls, text="СТОП", command=self.stop_process,
            bg="#f44336", fg="white", font=("Segoe UI", 11),
            relief="flat", padx=20, pady=10, cursor="hand2",
            state=tk.DISABLED
        )
        self.btn_stop.pack(side=tk.LEFT, padx=5)

    def _build_file_row(self, parent, icon, attr):
        row = tk.Frame(parent)
        row.pack(fill=tk.X, pady=3)
        
        tk.Label(row, text=icon, font=("Segoe UI", 11), width=18, anchor="w").pack(side=tk.LEFT)
        
        var = tk.StringVar(value=getattr(self.config, attr))
        self.path_entries[attr] = var
        
        tk.Entry(row, textvariable=var, font=("Consolas", 9)).pack(
            side=tk.LEFT, fill=tk.X, expand=True, padx=5
        )
        
        tk.Button(
            row, text="...", width=3,
            command=lambda a=attr, v=var: self._browse_file(a, v)
        ).pack(side=tk.RIGHT)

    def _browse_file(self, attr, var):
        f = filedialog.askopenfilename(
            title="Выберите файл",
            filetypes=[("Excel", "*.xlsx *.xls"), ("Все файлы", "*.*")]
        )
        if f:
            var.set(f)
            setattr(self.config, attr, f)
            if attr == "output_excel":
                self.config.detailed_json_output = workbench_sidecar_path(f)
            self.config.save_settings()

    @staticmethod
    def _safe_remove_file(path: str) -> bool:
        """Удаляет файл и .tmp рядом. True если файл был и удалён."""
        if not path:
            return False
        removed = False
        for p in (path, path + ".tmp"):
            if os.path.exists(p):
                os.remove(p)
                removed = True
        return removed

    @staticmethod
    def _write_empty_fewshot(path: str) -> None:
        """Пустой few-shot-файл: блокирует seed и восстановление из master."""
        payload = {
            "version": 2,
            "description": "Пустой few-shot после сброса эталонов. Не заполняется из master.",
            "intentionally_empty": True,
            "examples": [],
            "cleared_at": datetime.now().isoformat(timespec="seconds"),
        }
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)
        os.replace(tmp, path)

    def _clear_cache(self):
        path = self.config.cache_file
        if not os.path.exists(path):
            self.cache_info.config(text="Кэш пуст")
            self.log("Кэш уже пуст")
            return
        if not messagebox.askyesno("Подтверждение", "Удалить файл кэша заказов?\n(order_cache.json)"):
            return
        try:
            self._safe_remove_file(path)
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось удалить кэш:\n{e}")
            return
        self.cache_info.config(text="Кэш очищен")
        self.log("Кэш удалён")

    def _clear_cache_and_fewshot(self):
        """Удаляет order_cache и пишет пустой few-shot (без seed/master)."""
        cache_path = self.config.cache_file
        fs_path = self.config.few_shot_file
        msg = (
            "Удалить:\n"
            f"• кэш заказов: {os.path.basename(cache_path)}\n"
            f"• few-shot: {os.path.basename(fs_path)}\n\n"
            "Few-shot станет пустым (без seed и без восстановления из master).\n"
            "classification_master.json НЕ трогается — эталоны из него\n"
            "всё ещё применятся в конце прогона (apply_confirmed).\n\n"
            "Для полного сброса используй «Сброс всех эталонов»."
        )
        if not messagebox.askyesno("Подтверждение", msg):
            return
        removed = []
        try:
            if self._safe_remove_file(cache_path):
                removed.append("кэш")
            self._write_empty_fewshot(fs_path)
            removed.append("few-shot (пустой)")
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось очистить:\n{e}")
            return
        self.cache_info.config(text=self._get_cache_info())
        self.log("Очищено: " + ", ".join(removed))

    def _clear_all_etalons(self):
        """Полный сброс: кэш + few-shot + classification_master (+ опционально группы)."""
        cache_path = self.config.cache_file
        fs_path = self.config.few_shot_file
        master_path = self.config.classification_master_file or CLASSIFICATION_MASTER_FILE
        groups_path = WORK_GROUPS_FILE

        msg = (
            "ПОЛНЫЙ СБРОС ЭТАЛОНОВ\n\n"
            "Будет удалено:\n"
            f"• кэш заказов: {os.path.basename(cache_path)}\n"
            f"• few-shot: {os.path.basename(fs_path)} → пустой файл\n"
            f"• master: {os.path.basename(master_path)}\n\n"
            "Опционально можно сбросить и ручные группы (work_group_rules.json).\n\n"
            "После сброса классификация идёт только по:\n"
            "правилам Excel-справочников + AI (без few-shot) + system prompt.\n"
            "Seed-примеры и master НЕ восстановятся."
        )
        if not messagebox.askyesno("Сброс всех эталонов", msg):
            return

        clear_groups = messagebox.askyesno(
            "Ручные группы",
            "Также удалить work_group_rules.json (ручные группы вердиктов)?\n\n"
            "Нет — группы оставить.\nДа — сбросить и группы."
        )

        removed = []
        try:
            if self._safe_remove_file(cache_path):
                removed.append("order_cache")
            if self._safe_remove_file(master_path):
                removed.append("classification_master")
            self._write_empty_fewshot(fs_path)
            removed.append("few_shot (пустой)")
            if clear_groups and self._safe_remove_file(groups_path):
                removed.append("work_group_rules")
        except Exception as e:
            messagebox.showerror("Ошибка", f"Сброс прерван:\n{e}")
            return

        self.cache_info.config(text=self._get_cache_info())
        summary = ", ".join(removed) if removed else "уже было пусто"
        self.log(f"Сброс всех эталонов: {summary}", "success")
        messagebox.showinfo(
            "Готово",
            "Эталоны сброшены.\n\n"
            f"Удалено/обновлено: {summary}\n\n"
            "Запусти классификатор заново — без старых few-shot/master/кэша."
        )

    def _get_cache_info(self) -> str:
        parts = []
        if not os.path.exists(self.config.cache_file):
            parts.append("кэш: пуст")
        else:
            try:
                with open(self.config.cache_file, encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, dict) and "items" in data:
                    n = len(data.get("items") or {})
                    ver = data.get("version", "?")
                    parts.append(f"кэш: {n} • {ver}")
                else:
                    parts.append("кэш: старый")
            except Exception:
                parts.append("кэш: ошибка")
        fs = self.config.few_shot_file
        if os.path.exists(fs):
            try:
                with open(fs, encoding="utf-8") as f:
                    raw = json.load(f)
                n = len(raw.get("examples") or []) if isinstance(raw, dict) else (len(raw) if isinstance(raw, list) else 0)
                parts.append(f"fs: {n}")
            except Exception:
                parts.append("fs: ?")
        else:
            parts.append("fs: нет")
        master = self.config.classification_master_file or CLASSIFICATION_MASTER_FILE
        if os.path.exists(master):
            try:
                with open(master, encoding="utf-8") as f:
                    raw = json.load(f)
                n = len((raw or {}).get("confirmed_examples") or {})
                parts.append(f"master: {n}")
            except Exception:
                parts.append("master: ?")
        else:
            parts.append("master: нет")
        return " · ".join(parts)

    def _configure_input_columns(self):
        self._sync_paths()
        if not self.config.target_excel or not os.path.exists(self.config.target_excel):
            messagebox.showwarning("Колонки", "Сначала выбери Excel заказов.")
            return
        try:
            df = pd.read_excel(self.config.target_excel, nrows=5)
            dialog = ColumnMappingDialog(self.root, list(df.columns), self.config.column_mapping)
            self.root.wait_window(dialog.top)
            if dialog.result:
                self.config.column_mapping = dialog.result
                self.config.save_settings()
                self.log("Сопоставление колонок сохранено", "success")
        except Exception as e:
            messagebox.showerror("Колонки", f"Не удалось прочитать Excel:\n{e}")

    def _load_review_rows_from_session(self, show_message=False):
        """Загружает именно непустой снимок текущего рабочего набора.

        Важно: review_session.json — общий legacy-снимок и может существовать
        пустым/устаревшим. Раньше наличие такого файла блокировало переход к
        актуальному *.workbench.json, из-за чего окно «Проверка классификации»
        открывалось пустым. Теперь проверяем все кандидаты и берём первый
        пригодный снимок с реальными строками.
        """
        candidates = []
        if self.config.detailed_json_output:
            candidates.append(self.config.detailed_json_output)
        if self.config.output_excel:
            candidates.append(workbench_sidecar_path(self.config.output_excel))
        if getattr(self.config, "review_session_file", ""):
            candidates.append(self.config.review_session_file)

        # Убираем дубли, сохраняя приоритет: workbench текущего Excel -> session.
        paths = []
        seen = set()
        for x in candidates:
            if not x:
                continue
            x = os.path.abspath(str(x))
            if x not in seen:
                seen.add(x)
                paths.append(x)

        existing = [x for x in paths if os.path.exists(x)]
        if not existing:
            if show_message:
                messagebox.showinfo(
                    "Проверка классификации",
                    "Сохранённого сеанса классификации нет. Сначала запусти обработку SAP/AI.",
                    parent=self.root
                )
            return []

        errors = []
        for path in existing:
            try:
                with open(path, encoding="utf-8") as f:
                    raw = json.load(f)
                rows = raw.get("rows", []) if isinstance(raw, dict) else raw
                if not isinstance(rows, list):
                    rows = []
                rows = [
                    r for r in rows
                    if isinstance(r, dict) and (
                        "row_index" in r or "order_number" in r or "item_number" in r
                    )
                ]
                if rows:
                    if path.endswith(".workbench.json"):
                        self.config.detailed_json_output = path
                    logger.info(f"Загружен снимок проверки {path}: {len(rows)} позиций")
                    return rows
                logger.warning(f"Снимок проверки пустой, пробую следующий: {path}")
            except Exception as e:
                errors.append(f"{path}: {e}")
                logger.warning(f"Не удалось загрузить снимок проверки {path}: {e}")

        if show_message:
            detail = "\n".join(errors[-3:]) if errors else "Найденные JSON-файлы не содержат позиций."
            messagebox.showwarning(
                "Проверка классификации",
                "Не удалось найти непустой сеанс проверки.\n\n" + detail,
                parent=self.root
            )
        return []

    def _load_saved_review_snapshot(self):
        rows = self._load_review_rows_from_session(show_message=False)
        if rows:
            self.review_records = rows
            self.review_records = list(self.review_records)
            for rec in self.review_records:
                raw = " ".join([str(rec.get("item_name", "")), " ".join(str(x.get("Наименование работ / материалов", "")) for x in rec.get("services_and_materials", []) if isinstance(x, dict))])
                key = re.sub(r"\s+", " ", raw).strip().lower()
                rec["work_category"] = rec.get("work_category") or deterministic_work_category(raw) or load_work_categories().get(key, "")
            # review_df is optional for reviewing; if result exists, use it for saving.
            if self.config.output_excel and os.path.exists(self.config.output_excel):
                try:
                    self.review_df = ensure_output_columns(pd.read_excel(self.config.output_excel))
                except Exception:
                    self.review_df = None
            self.btn_review.config(state=tk.NORMAL)
            self.log(f"Загружен сеанс классификации: {len(rows)} позиций", "success")
            try:
                self.status_label.config(text=f"Сеанс: {len(rows)} позиций")
            except Exception:
                pass

    def _open_review(self):
        rows = self._load_review_rows_from_session(show_message=False)
        if rows:
            self.review_records = rows
        if not self.review_records:
            messagebox.showinfo(
                "Проверка классификации",
                "В сохранённом сеансе нет позиций. Сначала запусти обработку SAP/AI; данные проверки сохраняются отдельно от Excel.",
                parent=self.root
            )
            return
        ClassificationReview(self.root, self, list(self.review_records))

    def _save_review_record(self, idx, record):
        """Сеанс JSON — сразу; Excel — отложенно (не на каждый клик)."""
        if idx >= len(self.review_records):
            return
        self.review_records[idx] = record
        if record.get("source") in ("manual", "confirmed"):
            if not hasattr(self, "_pending_cache_invalidations"):
                self._pending_cache_invalidations = set()
            order = str(record.get("order_number") or "")
            item = str(record.get("item_number") or "").zfill(5)
            ref = str(record.get("reference_document") or "NO_REF")
            mvz = str(record.get("cost_center") or "NO_MVZ")
            self._pending_cache_invalidations.add(f"{order}:{item}:{ref}:{mvz}")
        try:
            self._save_review_snapshot()
        except Exception as e:
            logger.warning(f"Не удалось сохранить сеанс проверки: {e}")
        df_idx = record.get("row_index")
        if self.review_df is not None and df_idx in self.review_df.index:
            fv = record.get("final_verdict") or record.get("verdict") or None
            self.review_df.at[df_idx, "Вердикт ИИ"] = fv
            self.review_df.at[df_idx, "Счет"] = format_accounts(fv)
            self.review_df.at[df_idx, "Источник"] = record.get("source") or "unknown"
            self.review_df.at[df_idx, "Проверено"] = record.get("checked", "Нет")
            self.review_df.at[df_idx, "Авто вердикт"] = record.get("auto_verdict") or None
            self.review_df.at[df_idx, "Основание решения"] = record.get("reason") or ""
            if "Категория работы" not in self.review_df.columns:
                self.review_df["Категория работы"] = None
            self.review_df.at[df_idx, "Категория работы"] = record.get("work_category") or ""
            self.review_df.at[df_idx, "Название позиции SAP"] = record.get("item_name") or ""
            vals = []
            for x in record.get("services_and_materials", []) or []:
                val = x.get("Наименование работ / материалов") if isinstance(x, dict) else x
                val = str(val or "").strip()
                if val and val not in vals:
                    vals.append(val)
            self.review_df.at[df_idx, "Состав позиции SAP"] = " ||| ".join(vals)
            self._schedule_excel_flush()

    def _schedule_excel_flush(self, delay_ms: int = 2500):
        if not hasattr(self, "_excel_flush_after_id"):
            self._excel_flush_after_id = None
        if self._excel_flush_after_id is not None:
            try:
                self.root.after_cancel(self._excel_flush_after_id)
            except Exception:
                pass
        self._excel_flush_after_id = self.root.after(delay_ms, self._flush_excel_and_cache)

    def _prepare_export_df(self):
        """Готовит итоговый Excel: исходные колонки + «Вердикт ИИ», «Счет», «Категория работы».

        Служебные поля и технические SAP/AI-детали в итоговый Excel не попадают.
        """
        if self.review_df is None:
            return None
        # Подтянуть счёт из вердикта, если колонка пустая/устарела
        if "Вердикт ИИ" in self.review_df.columns:
            if "Счет" not in self.review_df.columns:
                self.review_df["Счет"] = None
            for idx in self.review_df.index:
                verdict = self.review_df.at[idx, "Вердикт ИИ"]
                self.review_df.at[idx, "Счет"] = format_accounts(verdict)
        source_cols = list(getattr(self, "_export_source_columns", []) or [])
        if not source_cols:
            source_cols = [c for c in self.review_df.columns if c not in {
                "Авто вердикт", "Вердикт ИИ", "Счет", "Источник", "Проверено",
                "Название позиции SAP", "Состав позиции SAP", "Основание решения",
                "Категория работы"
            }]
        hidden = {
            "Авто вердикт", "Источник", "Проверено",
            "Название позиции SAP", "Состав позиции SAP", "Основание решения"
        }
        cols = [c for c in source_cols if c in self.review_df.columns and c not in hidden]
        if "Вердикт ИИ" in self.review_df.columns:
            cols.append("Вердикт ИИ")
        if "Счет" in self.review_df.columns:
            cols.append("Счет")
        if "Категория работы" in self.review_df.columns:
            cols.append("Категория работы")
        return self.review_df.loc[:, list(dict.fromkeys(cols))].copy()

    def _save_export_excel(self):
        """Сохраняет только пользовательский набор колонок в итоговый Excel."""
        if self.review_df is None or not self.config.output_excel:
            return
        export_df = self._prepare_export_df()
        if export_df is not None:
            safe_save_excel(export_df, self.config.output_excel)

    def _flush_excel_and_cache(self):
        self._excel_flush_after_id = None
        pending = getattr(self, "_pending_cache_invalidations", None)
        if pending:
            try:
                cache = self._load_cache()
                changed = False
                for key in list(pending):
                    if key in cache:
                        cache.pop(key, None)
                        changed = True
                if changed:
                    self._save_cache(cache)
                pending.clear()
            except Exception as e:
                logger.warning(f"Не удалось обновить кэш: {e}")
        if self.review_df is None or not self.config.output_excel:
            return
        try:
            self._save_export_excel()
            logger.info(f"Excel обновлён (отложенная запись): {self.config.output_excel}")
        except Exception as e:
            logger.error(f"Не удалось сохранить Excel: {e}")

    def flush_pending_saves(self):
        if getattr(self, "_review_snap_after_id", None) is not None:
            try:
                self.root.after_cancel(self._review_snap_after_id)
            except Exception:
                pass
            self._review_snap_after_id = None
            try:
                self._save_review_snapshot()
            except Exception as e:
                logger.warning(f"flush review snapshot: {e}")
        if getattr(self, "_excel_flush_after_id", None) is not None:
            try:
                self.root.after_cancel(self._excel_flush_after_id)
            except Exception:
                pass
            self._excel_flush_after_id = None
        self._flush_excel_and_cache()

    def _schedule_review_snapshot(self, delay_ms: int = 800):
        """Отложенная запись review_session.json — схлопывает пачку быстрых сохранений."""
        if not hasattr(self, "_review_snap_after_id"):
            self._review_snap_after_id = None
        if self._review_snap_after_id is not None:
            try:
                self.root.after_cancel(self._review_snap_after_id)
            except Exception:
                pass
        self._review_snap_after_id = self.root.after(delay_ms, self._flush_review_snapshot)

    def _flush_review_snapshot(self):
        self._review_snap_after_id = None
        try:
            self._save_review_snapshot()
        except Exception as e:
            logger.warning(f"Отложенный снимок сессии: {e}")

    @staticmethod
    def _strip_runtime_fields(rows):
        """Убирает служебные runtime-поля из JSON, чтобы не раздувать файл."""
        skip = {"_search_haystack", "_fs_trusted", "_group_trusted"}
        out = []
        for r in rows or []:
            if not isinstance(r, dict):
                continue
            out.append({k: v for k, v in r.items() if k not in skip})
        return out

    def _save_review_snapshot(self):
        path = self.config.review_session_file or REVIEW_SESSION_FILE
        rows = self._strip_runtime_fields(self.review_records)
        payload = {
            "version": 3,
            "classifier_version": CLASSIFIER_VERSION,
            "source_excel": self.config.target_excel,
            "output_excel": self.config.output_excel,
            "column_mapping": self.config.column_mapping,
            "saved_at": datetime.now().isoformat(timespec="seconds"),
            "rows": rows,
        }
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            # Без indent — заметно быстрее и меньше на диске при 5k+ строк
            json.dump(payload, f, ensure_ascii=False, separators=(",", ":"), default=json_serialize_fallback)
        os.replace(tmp, path)

    def _sync_paths(self):
        for attr, var in self.path_entries.items():
            setattr(self.config, attr, var.get().strip())
        if self.config.output_excel:
            self.config.detailed_json_output = workbench_sidecar_path(self.config.output_excel)
        self.config.review_session_file = self.config.review_session_file or REVIEW_SESSION_FILE
        self.config.save_settings()

    def log(self, msg: str, level: str = "info"):
        self._queue('log', msg, level)

    def start_process(self):
        self._sync_paths()

        if not self.config.target_excel or not os.path.exists(self.config.target_excel):
            messagebox.showwarning("Файл заказов", "Сначала выбери Excel с заказами.")
            return

        # Проверяем структуру Excel до запуска фоновых потоков. При необходимости открываем мастер колонок.
        try:
            preview = pd.read_excel(self.config.target_excel, nrows=5)
            required = {"order", "item"}
            mapping_ok = all(self.config.column_mapping.get(k) in preview.columns for k in required)
            if not mapping_ok:
                dialog = ColumnMappingDialog(self.root, list(preview.columns), self.config.column_mapping)
                self.root.wait_window(dialog.top)
                if not dialog.result:
                    self.log("Запуск отменён: не настроены обязательные колонки.", "warning")
                    return
                self.config.column_mapping = dialog.result
                self.config.save_settings()
        except Exception as e:
            messagebox.showerror("Структура Excel", f"Не удалось проверить колонки:\n{e}")
            return
        new_output_name = generate_timestamped_filename(self.config.target_excel)
        self.config.output_excel = new_output_name
        self.config.detailed_json_output = workbench_sidecar_path(new_output_name)
        if 'output_excel' in self.path_entries:
            self.path_entries['output_excel'].set(new_output_name)
        self.config.save_settings()
            
        self.session_stats = {'cache_hits': 0, 'ai_calls': 0, 'rule_hits': 0, 'errors': 0, 'start_time': time.time()}
        self.review_records = []
        self.review_df = None
        self.btn_review.config(state=tk.DISABLED)
        
        self.btn_start.config(state=tk.DISABLED)
        self.btn_pause.config(state=tk.NORMAL)
        self.btn_stop.config(state=tk.NORMAL)
        self.stop_event.clear()
        self.is_paused.set()
        
        threading.Thread(target=self._run_pipeline, daemon=True).start()
        self._update_timer()

    def _update_timer(self):
        if self.stop_event.is_set():
            return
        elapsed = time.time() - self.session_stats['start_time']
        self.stat_labels['time'].config(text=f"{int(elapsed)//60:02d}:{int(elapsed)%60:02d}")
        self.root.after(1000, self._update_timer)

    def pause_process(self):
        self.is_paused.clear()
        self.btn_pause.config(state=tk.DISABLED)
        self.btn_resume.config(state=tk.NORMAL)
        self.status_label.config(text="Пауза", bg="#ef6c00")
        self.log("Пауза")

    def resume_process(self):
        self.is_paused.set()
        self.btn_resume.config(state=tk.DISABLED)
        self.btn_pause.config(state=tk.NORMAL)
        self.status_label.config(text="Выполняется", bg="#2e7d32")
        self.log("Продолжение")

    def stop_process(self):
        self.stop_event.set()
        self.is_paused.set()
        self.status_label.config(text="Остановка...", bg="#c62828")
        self.log("Остановка...")

    def _run_pipeline(self):
        try:
            cfg = self.config
            
            master = ClassificationMasterStore(cfg.classification_master_file)
            few_shot = FewShotManager(cfg.few_shot_file)
            # Любое реальное изменение Few-shot инвалидирует старые AI-результаты.
            # SAP-кэш при этом не трогаем: повторно забираем только классификацию,
            # используя уже сохранённые order/item/services данные при необходимости.
            few_shot_signature = few_shot.fingerprint()
            self._few_shot_cache_signature = few_shot_signature
            work_groups = load_work_groups()
            work_categories = load_work_categories()
            order_cache = self._load_cache(expected_few_shot_signature=few_shot_signature)
            
            self._queue('status', "Загрузка справочников...")
            fast_base = load_excel_column_as_set(cfg.base_file)
            spare_parts = load_spare_parts_set(cfg.spare_file)
            stroy_equip = load_stroy_equipment_set(cfg.stroy_file)
            
            file_to_read = cfg.target_excel
            if not os.path.exists(file_to_read):
                self._queue('error', f"Файл не найден: {file_to_read}")
                return

            df_orders = pd.read_excel(file_to_read)
            self._export_source_columns = list(df_orders.columns)
            total = len(df_orders)
            
            cols = self._resolve_columns(df_orders)
            
            df_orders = ensure_output_columns(df_orders)
            self.review_df = df_orders
            
            base_prompt = self._get_system_prompt()
            system_prompt = base_prompt + few_shot.get_prompt_addon(count=12)
            
            results = {}
            detailed = []
            cache_dirty = 0
            cache_save_interval = max(10, int(cfg.batch_save_interval or 100))
            sap_raw_cache = {}
            sap_cache_locks = {}
            sap_cache_locks_guard = threading.Lock()
            cache_write_lock = threading.Lock()
            
            ai_limiter = AdaptiveRateLimiter(cfg.ai_rps_limit)
            ai_client = AIAssistantClient(cfg, ai_limiter) if cfg.has_ai_config else None
            
            with SAPConnectionPool(cfg, cfg.sap_pool_size) as sap_pool:

                def fetch_sap_order(order_num):
                    """Fetch PO once and enrich it with service-entry-sheet long texts when available."""
                    with sap_cache_locks_guard:
                        lock = sap_cache_locks.setdefault(order_num, threading.Lock())
                    with lock:
                        if order_num in sap_raw_cache:
                            return sap_raw_cache[order_num]
                        res = {}
                        try:
                            with sap_pool.acquire() as conn:
                                res = conn.call(
                                    'BAPI_PO_GETDETAIL1',
                                    PURCHASEORDER=order_num.zfill(10),
                                    SERVICES='X',
                                    ACCOUNT_ASSIGNMENT='X'
                                )

                        except Exception as sap_err:
                            logger.warning(f"[{order_num}] BAPI call fail: {sap_err}")
                        sap_raw_cache[order_num] = res or {}
                        return sap_raw_cache[order_num]

                def process_row(idx, row):
                    nonlocal cache_dirty
                    if self.stop_event.is_set():
                        return None
                    self.is_paused.wait()
                    
                    order_col = cols.get('order')
                    if not order_col or order_col not in row or pd.isna(row[order_col]):
                        return None
                    
                    raw_order = row[order_col]
                    order_num = str(int(raw_order)) if isinstance(raw_order, (int, float)) else str(raw_order).strip()
                    
                    item_col = cols.get('item')
                    raw_item = row[item_col] if item_col and item_col in row else None
                    item_num = str(int(raw_item)).strip().zfill(5) if pd.notna(raw_item) else "00010"
                    
                    ref_col = cols.get('ref')
                    ref_num = str(row[ref_col]).strip() if ref_col and ref_col in row and pd.notna(row[ref_col]) else "NO_REF"
                    
                    mvz_col = cols.get('mvz')
                    target_cc = str(row[mvz_col]).strip() if mvz_col and mvz_col in row and pd.notna(row[mvz_col]) else "NO_MVZ"
                    
                    cache_key = f"{order_num}:{item_num}:{ref_num}:{target_cc}"

                    # --- Кэш: только из order_cache (config.cache_file), без сторонних источников ---
                    cached_hit = None
                    with self.cache_lock:
                        raw_cached = order_cache.get(cache_key)
                        if isinstance(raw_cached, dict) and raw_cached.get("verdict") and not raw_cached.get("needs_reclassify"):
                            cached_hit = raw_cached
                        elif not isinstance(raw_cached, dict) and raw_cached:
                            # legacy: просто строка-вердикт
                            cached_hit = {"verdict": raw_cached, "source": "cache", "reason": "", "item_name": "", "services": []}

                    if cached_hit is not None:
                        verdict = cached_hit.get("verdict")
                        source = cached_hit.get("source", "cache")
                        reason = cached_hit.get("reason", "")
                        item_name = cached_hit.get("item_name", "")
                        services_list = cached_hit.get("services") or []
                        semantic_cache_text = build_semantic_text(item_name, services_list)
                        group_match = resolve_work_group(semantic_cache_text, "", work_groups)
                        if group_match:
                            verdict = group_match["verdict"]
                            source = "group"
                            reason = (
                                f"Ручное правило группы «{group_match['group']}»: "
                                f"совпала подгруппа «{group_match['matched']}» ({group_match['score']:.0%})"
                            )
                        return {
                            "idx": idx, "verdict": verdict, "auto_verdict": verdict, "final_verdict": verdict,
                            "source": source, "cache_hit": True, "checked": "Нет",
                            "services": services_list, "item_name": item_name, "reason": reason,
                            "matched_work_group": (group_match.get("group", "") if group_match else ""),
                            "work_group_score": (group_match.get("score", 0.0) if group_match else 0.0),
                            "order_num": order_num, "item_num": item_num,
                            "ref_num": ref_num, "target_cc": target_cc,
                        }

                    # SAP-only запись после смены few-shot: берём item_name/services без повторного BAPI.
                    sap_only = None
                    with self.cache_lock:
                        raw = order_cache.get(cache_key)
                        if isinstance(raw, dict) and raw.get("needs_reclassify"):
                            sap_only = raw

                    try:
                        item_name = ""
                        services_list = []
                        df_report = pd.DataFrame()

                        if sap_only and (sap_only.get("item_name") or sap_only.get("services")):
                            item_name = str(sap_only.get("item_name") or "")
                            services_list = list(sap_only.get("services") or [])
                            if services_list:
                                df_report = pd.DataFrame(services_list)
                        else:
                            res = fetch_sap_order(order_num)
                            data = {
                                "items": pd.DataFrame(res.get("POITEM", [])),
                                "services": pd.DataFrame(res.get("POSERVICES", [])),
                                "srv_acc": pd.DataFrame(res.get("POSRVACCESSVALUES", [])),
                                "po_account": pd.DataFrame(res.get("POACCOUNT", [])),
                            }
                            df_report = build_clean_service_report(
                                data, fast_base, spare_parts, stroy_equip,
                                target_item=item_num,
                                target_costcenter=target_cc if target_cc != "NO_MVZ" else None,
                            )
                            if not data["items"].empty and "SHORT_TEXT" in data["items"].columns:
                                tmp_items = data["items"].copy()
                                tmp_items["PO_ITEM"] = tmp_items["PO_ITEM"].astype(str).str.strip().str.zfill(5)
                                target_rows = tmp_items[tmp_items["PO_ITEM"] == item_num]
                                if not target_rows.empty:
                                    item_name = str(target_rows.iloc[0].get("SHORT_TEXT", "") or "").strip()
                            services_list = df_report.to_dict(orient="records") if not df_report.empty else []
                            if not services_list and item_name:
                                services_list = [{
                                    "Поз": item_num,
                                    "Название позиции заказа": item_name,
                                    "Наименование работ / материалов": item_name,
                                }]

                        rule_df = df_report
                        if rule_df.empty and item_name:
                            rule_df = pd.DataFrame([{
                                "Поз": item_num,
                                "Название позиции заказа": item_name,
                                "Наименование работ / материалов": item_name,
                            }])
                        # AI-first: жёсткие regex НЕ назначают вердикт (HARD_RULES_ASSIGN_VERDICT=False).
                        # extract_rule_decision оставлен только как опциональный legacy-режим.
                        verdict, reason = (None, None)
                        source = None
                        if HARD_RULES_ASSIGN_VERDICT:
                            verdict, reason = extract_rule_decision(rule_df)
                            source = "rule" if verdict else None
                        group_match = None
                        semantic_for_fs = build_semantic_text(item_name, services_list)

                        # Ручные группы пользователя — единственный детерминированный приоритет над AI.
                        if source != "rule" or verdict != VerdictCategory.SKIP.value:
                            group_match = resolve_work_group(semantic_for_fs, "", work_groups)
                            if group_match:
                                verdict = group_match["verdict"]
                                source = "group"
                                reason = (
                                    f"Ручное правило группы «{group_match['group']}»: "
                                    f"совпала подгруппа «{group_match['matched']}» ({group_match['score']:.0%})"
                                )

                        if verdict is None and ai_client:
                            if not rule_df.empty:
                                table_text = rule_df.to_csv(index=False, sep='\t')
                                prompt_content = f"Семантическая спецификация текущей позиции (идентификаторы намеренно исключены):\n\n{table_text}"
                            else:
                                prompt_content = "Семантическая спецификация текущей позиции отсутствует: детализация из SAP не получена."

                            relevant_fs = few_shot.get_relevant_prompt_addon(semantic_for_fs, count=6)
                            messages = [
                                {"role": "system", "content": system_prompt + relevant_fs},
                                {"role": "user", "content": prompt_content}
                            ]
                            def _parse_ai_verdict(ai_response):
                                if not ai_response:
                                    return None, "AI не вернул решение"
                                cleaned = ai_response.strip().strip("\"\'")
                                matched = VerdictCategory.from_string(cleaned)
                                if matched:
                                    return matched.value, "AI классификация"
                                if cleaned.strip().lower() in {
                                    "не определено", "неопределено", "unknown", "none"
                                }:
                                    return "Не определено", "AI классификация"
                                return None, f"AI вернул неизвестный вердикт: {cleaned[:120]}"

                            # Этап 1: штатный default-model.
                            ai_response = ai_client.chat_completion(messages=messages)
                            verdict, ai_reason = _parse_ai_verdict(ai_response)
                            if verdict is not None:
                                source = "ai"
                                reason = ai_reason
                            else:
                                # Этап 2: эскалация. Используется только после
                                # отсутствия/некорректного ответа первого AI.
                                escalation_model = getattr(ai_client.config, "ai_escalation_model", "")
                                if escalation_model and escalation_model != ai_client.config.ai_model:
                                    logger.warning(
                                        f"AI escalation: первый ответ не принят ({ai_reason}); "
                                        f"повтор через {escalation_model}"
                                    )
                                    escalation_messages = [
                                        {
                                            "role": "system",
                                            "content": (
                                                system_prompt + relevant_fs +
                                                "\n\nЭСКАЛАЦИЯ. Верни РОВНО ОДНУ категорию из списка, без пояснений, Markdown и дополнительного текста."
                                            )
                                        },
                                        {"role": "user", "content": prompt_content}
                                    ]
                                    escalation_response = ai_client.chat_completion(
                                        messages=escalation_messages,
                                        model=escalation_model,
                                        temperature=0.0,
                                        max_tokens=80
                                    )
                                    verdict, escalation_reason = _parse_ai_verdict(escalation_response)
                                    if verdict is not None:
                                        source = "ai_escalation"
                                        reason = escalation_reason
                                    else:
                                        raise RuntimeError(
                                            f"AI escalation не дала валидного решения: {escalation_reason}"
                                        )
                        elif verdict is None:
                            source="no_ai"

                        # Ошибки/отсутствие AI не превращаем в «ПРОПУСК» и не кладём в кэш.
                        gm_name = group_match.get("group", "") if group_match else ""
                        gm_score = group_match.get("score", 0.0) if group_match else 0.0
                        if verdict is not None:
                            cache_record = {
                                "verdict": verdict,
                                "source": source or "unknown",
                                "reason": reason or ("AI классификация" if source == "ai" else ""),
                                "item_name": item_name,
                                "services": services_list,
                                "matched_work_group": gm_name,
                                "work_group_score": gm_score,
                                "classifier_version": CLASSIFIER_VERSION,
                                "updated_at": datetime.now().isoformat(timespec="seconds"),
                            }
                            should_flush_cache = False
                            with self.cache_lock:
                                order_cache[cache_key] = cache_record
                                cache_dirty += 1
                                should_flush_cache = cache_dirty >= cache_save_interval
                                if should_flush_cache:
                                    cache_dirty = 0
                            if should_flush_cache:
                                with cache_write_lock:
                                    try:
                                        with self.cache_lock:
                                            cache_snapshot = dict(order_cache)
                                        self._save_cache(cache_snapshot)
                                    except Exception as c_err:
                                        logger.error(f"Failed writing cache: {c_err}")

                        return {
                            "idx": idx, "verdict": verdict, "auto_verdict": verdict, "final_verdict": verdict,
                            "source": source or "unknown", "cache_hit": False, "checked": "Нет",
                            "services": services_list, "item_name": item_name,
                            "reason": reason or ("AI классификация" if source == "ai" else ""),
                            "key": cache_key,
                            "matched_work_group": gm_name, "work_group_score": gm_score,
                            "order_num": order_num, "item_num": item_num,
                            "ref_num": ref_num, "target_cc": target_cc,
                        }
                        
                    except Exception as e:
                        logger.error(f"Error processing {order_num}: {e}")
                        return {
                            'idx': idx, 'verdict': None, 'error': str(e),
                            'order_num': order_num, 'item_num': item_num,
                            'ref_num': ref_num, 'target_cc': target_cc
                        }
                
                with ThreadPoolExecutor(cfg.max_workers) as executor:
                    futures = [executor.submit(process_row, i, r) for i, r in df_orders.iterrows()]
                    
                    completed = 0
                    for future in as_completed(futures):
                        if self.stop_event.is_set():
                            break
                        
                        result = future.result()
                        if result:
                            final_verdict = result.get('verdict')
                            results[result['idx']] = final_verdict
                            df_orders.at[result['idx'], 'Авто вердикт'] = result.get('auto_verdict') or final_verdict
                            df_orders.at[result['idx'], 'Вердикт ИИ'] = final_verdict
                            df_orders.at[result['idx'], 'Счет'] = format_accounts(final_verdict)
                            df_orders.at[result['idx'], 'Источник'] = result.get('source')
                            df_orders.at[result['idx'], 'Проверено'] = 'Нет'
                            df_orders.at[result['idx'], 'Название позиции SAP'] = result.get('item_name', '')
                            services_names = []
                            for srv in result.get('services', []) or []:
                                val = str(srv.get('Наименование работ / материалов', '')).strip() if isinstance(srv, dict) else str(srv).strip()
                                if val and val not in services_names: services_names.append(val)
                            df_orders.at[result['idx'], 'Состав позиции SAP'] = ' ||| '.join(services_names)
                            df_orders.at[result['idx'], 'Основание решения'] = result.get('reason', '')
                            if result.get('cache_hit'):
                                self.session_stats['cache_hits'] += 1
                            elif result.get('source') == 'ai':
                                self.session_stats['ai_calls'] += 1
                            elif result.get('source') == 'rule':
                                self.session_stats['rule_hits'] += 1
                            if result.get('error'):
                                self.session_stats['errors'] += 1
                            if result.get('source') == 'rule':
                                self._queue('log', f"[{result.get('order_num','')}/{result.get('item_num','')}] Правило → {result.get('verdict')}", 'success')
                            elif result.get('source') == 'ai':
                                self._queue('log', f"[{result.get('order_num','')}/{result.get('item_num','')}] AI → {result.get('verdict')}", 'info')
                            elif result.get('error'):
                                self._queue('log', f"[{result.get('order_num','')}/{result.get('item_num','')}] Ошибка → {result.get('error')}", 'error')

                            detailed.append({
                                "row_index": result['idx'],
                                "order_number": result.get('order_num', ''),
                                "item_number": result.get('item_num', ''),
                                "reference_document": result.get('ref_num', ''),
                                "cost_center": result.get('target_cc', ''),
                                "auto_verdict": result.get('auto_verdict') or result.get('verdict'),
                                "final_verdict": result.get('final_verdict') or result.get('verdict'),
                                "checked": result.get('checked', 'Нет'),
                                "source": result.get('source', 'unknown'),
                                "item_name": result.get('item_name', ''),
                                "reason": result.get('reason', ''),
                                "error": result.get('error', ''),
                                "services_and_materials": result.get('services', []),
                                "matched_work_group": result.get('matched_work_group', ''),
                                "work_group_score": result.get('work_group_score', 0.0),
                            })
                        completed += 1
                        self.review_records = list(detailed)
                        if completed % max(1, cfg.batch_save_interval) == 0:
                            try:
                                self._save_review_snapshot()
                            except Exception as snap_err:
                                logger.warning(f"Не удалось сохранить промежуточный сеанс проверки: {snap_err}")
                            try:
                                master.merge_run_rows(detailed)
                                master.save()
                            except Exception as master_snap_err:
                                logger.warning(f"Не удалось сохранить промежуточный classification master: {master_snap_err}")
                        self._queue('progress', completed, total)
                        self._queue('stats')
                
                for idx, verdict in results.items():
                    df_orders.at[idx, 'Вердикт ИИ'] = verdict
                    df_orders.at[idx, 'Счет'] = format_accounts(verdict)
                for item in detailed:
                    idx = item.get('row_index')
                    if idx in df_orders.index:
                        df_orders.at[idx, 'Источник'] = item.get('source')
                        fv = item.get('final_verdict') or item.get('verdict')
                        item['accounts'] = format_accounts(fv)
                
                # Единый эталон ручной классификации: уже подтверждённые
                # семантические позиции закрываются автоматически без повторной проверки.
                master_hits = master.apply_confirmed(detailed)
                if master_hits:
                    for item in detailed:
                        idx = item.get("row_index")
                        if idx in df_orders.index and item.get("source") == "master":
                            fv = item.get("final_verdict") or item.get("verdict")
                            df_orders.at[idx, "Вердикт ИИ"] = fv
                            df_orders.at[idx, "Счет"] = format_accounts(fv)
                            df_orders.at[idx, "Авто вердикт"] = item.get("auto_verdict") or item.get("verdict")
                            df_orders.at[idx, "Источник"] = "master"
                            df_orders.at[idx, "Проверено"] = "Да"
                    logger.info(f"Classification master: автоматически применён эталон к {master_hits} позициям")

                # Короткая аналитическая категория работ.
                # В итоговый Excel попадает только эта колонка; подробные служебные
                # поля остаются во внутреннем review_session/workbench JSON.
                category_map = load_work_categories()
                category_requests = {}
                for item in detailed:
                    idx = item.get("row_index")
                    parts = []
                    item_name = str(item.get("item_name", "") or "").strip()
                    if item_name:
                        parts.append(item_name)
                    for srv in item.get("services_and_materials", []) or []:
                        if isinstance(srv, dict):
                            val = str(srv.get("Наименование работ / материалов", "") or "").strip()
                        else:
                            val = str(srv or "").strip()
                        if val and val not in parts:
                            parts.append(val)
                    basis = " ||| ".join(parts)
                    key = re.sub(r"\s+", " ", basis).strip().lower()
                    if not key:
                        continue
                    existing = str(category_map.get(key, "") or "").strip()
                    deterministic = deterministic_work_category(basis)
                    # Старые длинные/детализированные категории считаем устаревшими
                    # и отправляем на повторную нормализацию.
                    if existing and len(existing) <= 60 and " ||| " not in existing:
                        chosen = existing
                    elif deterministic:
                        chosen = deterministic
                    else:
                        chosen = ""
                    if chosen:
                        item["work_category"] = chosen
                    else:
                        category_requests[key] = basis[:1400]

                if category_requests and ai_client:
                    try:
                        items = list(category_requests.items())
                        for start in range(0, len(items), 25):
                            batch = items[start:start + 25]
                            payload = {str(i): text for i, (_, text) in enumerate(batch)}
                            prompt = (
                                "Нормализуй описание работ/услуг в ОДНУ короткую аналитическую категорию. "
                                "Категория должна описывать тип работ или комплекс работ, а не пересказывать исходный текст. "
                                "Объединяй связанные виды работ в одну категорию. "
                                "Например: 'Монтаж одной КСО ||| Монтаж одной точки СКС ||| работы с ИТ-оборудованием ||| настройка кассы' "
                                "→ 'КСО + СКС + ИТ'. "
                                "Не используй номера заказов, цены, сроки, договоры и длинные описания. "
                                "1-5 слов, желательно до 40 символов. "
                                "Верни ТОЛЬКО JSON-объект вида {\"0\":\"Категория\",...}.\n\n"
                                "Вход:\n" + json.dumps(payload, ensure_ascii=False)
                            )
                            resp = ai_client.chat_completion([
                                {"role": "system", "content": "Ты нормализуешь работы и услуги в короткие категории для Excel-аналитики."},
                                {"role": "user", "content": prompt}
                            ], temperature=0.0, max_tokens=900)
                            if not resp:
                                continue
                            text = resp.strip()
                            if text.startswith("```"):
                                text = re.sub(r"^```(?:json)?\s*|\s*```$", "", text, flags=re.I | re.S).strip()
                            m = re.search(r"\{.*\}", text, re.S)
                            obj = json.loads(m.group(0) if m else text)
                            if not isinstance(obj, dict):
                                continue
                            for i, (key, _) in enumerate(batch):
                                cat = re.sub(r"\s+", " ", str(obj.get(str(i), "") or "").strip())
                                if cat and len(cat) <= 60 and "|||" not in cat and "\n" not in cat:
                                    category_map[key] = cat
                        save_work_categories(category_map)
                    except Exception as cat_err:
                        logger.warning(f"AI-нормализация категорий не завершена: {cat_err}")

                # Записываем короткую категорию в рабочий DataFrame и review records.
                for item in detailed:
                    idx = item.get("row_index")
                    item_name = str(item.get("item_name", "") or "").strip()
                    parts = [item_name] if item_name else []
                    for srv in item.get("services_and_materials", []) or []:
                        val = str(srv.get("Наименование работ / материалов", "") or "").strip() if isinstance(srv, dict) else str(srv or "").strip()
                        if val and val not in parts:
                            parts.append(val)
                    basis = " ||| ".join(parts)
                    key = re.sub(r"\s+", " ", basis).strip().lower()
                    cat = item.get("work_category") or category_map.get(key) or deterministic_work_category(basis) or ""
                    item["work_category"] = cat
                    if idx in df_orders.index:
                        df_orders.at[idx, "Категория работы"] = cat

                if cache_dirty:
                    with cache_write_lock:
                        try:
                            self._save_cache(order_cache)
                        except Exception as c_err:
                            logger.error(f"Failed writing final cache: {c_err}")
                master.merge_run_rows(detailed)
                try:
                    master.save()
                except Exception as master_err:
                    logger.warning(f"Не удалось сохранить classification master: {master_err}")
                self._save_export_excel()
                
                detailed.sort(key=lambda x: x["row_index"])
                sidecar_path = cfg.detailed_json_output or workbench_sidecar_path(cfg.output_excel)
                payload = {
                    "version": 1,
                    "classifier_version": CLASSIFIER_VERSION,
                    "source_excel": cfg.target_excel,
                    "output_excel": cfg.output_excel,
                    "column_mapping": cols,
                    "rows": detailed
                }
                with open(sidecar_path, 'w', encoding='utf-8') as f:
                    json.dump(payload, f, ensure_ascii=False, indent=2, default=json_serialize_fallback)
                cfg.detailed_json_output = sidecar_path
                cfg.review_session_file = cfg.review_session_file or REVIEW_SESSION_FILE
                cfg.save_settings()
                self.review_records = sorted(detailed, key=lambda x: x['row_index'])
                self.review_df = df_orders
                self._save_review_snapshot()
                self._queue('review_ready', True)
                self._queue('done', True)
                
        except Exception as e:
            logger.exception("Pipeline failed")
            self._queue('error', str(e))

    def _load_cache(self, expected_few_shot_signature: str = "") -> dict:
        """Загружает order_cache.json только из config.cache_file.

        При смене few-shot signature сохраняем SAP-данные (item_name/services),
        но сбрасываем вердикт — классификация пересчитывается без повторного
        запроса в SAP. Чужие/старые форматы игнорируются.
        """
        if not os.path.exists(self.config.cache_file):
            return {}
        try:
            with open(self.config.cache_file, encoding="utf-8") as f:
                data = json.load(f)
            if not (isinstance(data, dict) and data.get("version") == CACHE_VERSION):
                logger.info("Старый/несовместимый кэш проигнорирован")
                return {}
            items = data.get("items") or {}
            if not isinstance(items, dict):
                return {}
            cached_fs = str(data.get("few_shot_signature", ""))
            if expected_few_shot_signature and cached_fs and cached_fs != expected_few_shot_signature:
                logger.info(
                    "Few-shot изменён: вердикты в кэше инвалидированы, SAP-данные сохранены "
                    f"(старый={cached_fs[:12]}, новый={expected_few_shot_signature[:12]})"
                )
                sanitized = {}
                for key, rec in items.items():
                    if not isinstance(rec, dict):
                        continue
                    # Оставляем только структурные поля для ускорения SAP; вердикт — нет.
                    payload = {
                        "item_name": rec.get("item_name", ""),
                        "services": rec.get("services") or [],
                        "verdict": None,
                        "source": "sap_only",
                        "reason": "",
                        "classifier_version": CLASSIFIER_VERSION,
                        "needs_reclassify": True,
                    }
                    if payload["item_name"] or payload["services"]:
                        sanitized[key] = payload
                return sanitized
            return items
        except Exception as e:
            logger.warning(f"Cache load failed: {e}")
            return {}

    def _save_cache(self, cache: dict, few_shot_signature: str = ""):
        signature = few_shot_signature or getattr(self, "_few_shot_cache_signature", "")
        # Не пишем записи без вердикта (sap_only / needs_reclassify) как финальные —
        # только полноценные классификации, чтобы не «замораживать» пустые вердикты.
        clean = {}
        for key, rec in (cache or {}).items():
            if not isinstance(rec, dict):
                continue
            if rec.get("needs_reclassify") or not rec.get("verdict"):
                continue
            clean[key] = rec
        payload = {
            "version": CACHE_VERSION,
            "classifier_version": CLASSIFIER_VERSION,
            "few_shot_signature": signature,
            "updated_at": datetime.now().isoformat(timespec="seconds"),
            "items": clean,
        }
        tmp = self.config.cache_file + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2, default=json_serialize_fallback)
        os.replace(tmp, self.config.cache_file)

    def _resolve_columns(self, df: pd.DataFrame) -> dict:
        mapping = dict(self.config.column_mapping or {})
        columns = set(df.columns)
        aliases = load_column_aliases()
        if mapping.get("order") not in columns or mapping.get("item") not in columns:
            low = {str(c).strip().lower(): c for c in df.columns}
            for role in ("order", "item", "ref", "mvz"):
                if mapping.get(role) in columns:
                    continue
                for alias in aliases.get(role, []):
                    found = next((orig for key, orig in low.items() if str(alias).lower() in key), None)
                    if found:
                        mapping[role] = found
                        break
        if not (mapping.get("order") in columns and mapping.get("item") in columns):
            raise ValueError("Не удалось определить колонки заказа и позиции. Нажми «Колонки» и выбери их вручную.")
        mapping = {k:v for k,v in mapping.items() if v in columns}
        self.config.column_mapping = mapping
        self.config.save_settings()
        return mapping

    def _find_col(self, cols_lower: dict, variants: list) -> Optional[str]:
        for v in variants:
            for col_key in cols_lower:
                if v in col_key:
                    return cols_lower[col_key]
        return None

    def _get_system_prompt(self) -> str:
        return """Ты — эксперт по квалификации закупок компании.
Классифицируй только по содержанию текущей позиции: названию SAP и фактическим работам/материалам.
Номера заказа, позиции, СФ и МВЗ не являются признаками классификации.

КЛАССИФИКАТОРЫ:
1. Быстрая стройка — стандартные материалы/работы быстрой стройки, электрика, сантехника, инженерные коммуникации.
2. Быстрая стройка + ОС — быстрая стройка с явным специфическим оборудованием ОС.
3. Оборудование — товарное оборудование, СКС, ИТС, ПНР, ИТ-оборудование, кассы, рекламное оборудование. Мойка из нержавеющей стали и её монтаж/подключение/крепёж в одной позиции → Оборудование.
4. Ремонт ОС — ремонт/обслуживание технологического оборудования: тестораскаточные, кофемашины, холодильное оборудование и т.п.
5. ПРОПУСК — капитальное строительство, фасадные работы, реконструкция.
6. Если данных недостаточно для обоснованного выбора — отвечай НЕ ОПРЕДЕЛЕНО. Не выдумывай отсутствующие работы/материалы.

Ответ только одним значением: Быстрая стройка | Быстрая стройка + ОС | Оборудование | Ремонт ОС | ПРОПУСК | Не определено."""

    def _update_stats(self):
        self.stat_labels['rules'].config(text=str(self.session_stats.get('rule_hits',0)))
        self.stat_labels['cache'].config(text=str(self.session_stats['cache_hits']))
        self.stat_labels['ai'].config(text=str(self.session_stats['ai_calls']))
        self.stat_labels['errors'].config(text=str(self.session_stats['errors']))

    def _check_queue(self):
        try:
            while True:
                cmd, args = self.gui_queue.get_nowait()
                
                if cmd == 'log':
                    self._do_log(*args)
                elif cmd == 'progress':
                    cur, tot = args
                    pct = int(cur * 100 / tot) if tot > 0 else 0
                    self.progress_var.set(pct)
                    self.percent_label.config(text=f"{pct}%")
                elif cmd == 'status':
                    self.status_label.config(text=args[0])
                elif cmd == 'review_ready':
                    self.btn_review.config(state=tk.NORMAL)
                elif cmd == 'stats':
                    self._update_stats()
                elif cmd == 'done':
                    self._on_finished()
                elif cmd == 'error':
                    self._on_error(args[0])
                    
        except queue.Empty:
            pass
        # 80 ms — меньше нагрузка на Tk при большом потоке логов/stats
        self.root.after(80, self._check_queue)

    def _queue(self, cmd, *args):
        self.gui_queue.put((cmd, args))

    def _do_log(self, msg, level="info"):
        colors = {
            'info': '#1565c0', 'success': '#2e7d32',
            'warning': '#ef6c00', 'error': '#c62828'
        }
        self.log_box.config(state=tk.NORMAL)
        self.log_box.insert(tk.END, f"{msg}\n", level)
        self.log_box.tag_config(level, foreground=colors.get(level, '#212121'))
        self.log_box.see(tk.END)
        self.log_box.config(state=tk.DISABLED)

    def _on_finished(self):
        for b in [self.btn_start, self.btn_pause, self.btn_resume, self.btn_stop]:
            b.config(state=tk.NORMAL if b == self.btn_start else tk.DISABLED)
        self.status_label.config(text="Готово — можно проверять классификацию", bg="#1565c0")
        self.cache_info.config(text=self._get_cache_info())
        self.btn_review.config(state=tk.NORMAL if self.review_records else tk.DISABLED)

    def _on_error(self, msg):
        self._on_finished()
        messagebox.showerror("Ошибка", msg)


if __name__ == '__main__':
    root = tk.Tk()
    config = AppConfig()
    app = AuditApp(root, config)
    root.mainloop()

[README.md](https://github.com/user-attachments/files/32888319/README.md)
# Procurement AI Auditor

Desktop-приложение на Python для автоматизации классификации закупочных позиций и последующей ручной проверки результатов.

Проект демонстрирует прикладную автоматизацию: обработку Excel, интеграцию с ERP через SAP RFC, REST API для AI-классификации, кэширование, few-shot примеры, многопоточную обработку, adaptive rate limiting, retry/circuit-breaker и GUI на Tkinter.


- Python 3
- Tkinter GUI
- Pandas / Excel
- SAP RFC integration
- REST API для AI-классификации
- ThreadPoolExecutor
- Adaptive rate limiter
- Retry + circuit breaker
- Кэширование результатов
- Few-shot / экспертные примеры
- Ручная проверка и экспорт результата

## Публичная версия

Исходная рабочая система может требовать корпоративные библиотеки, доступы и инфраструктуру, которых нет в публичном репозитории.

## Запуск

```bash
python -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
cp .env.example .env
python src/procurement_ai_auditor.py
```

#v2.0.0 (Turso edition — persistent DB across redeploys)
from aiogram import Router
import asyncio
import sqlite3
import threading
import os
import re
import math
try:
    import libsql
except ImportError:
    libsql = None
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo
from typing import Optional, Dict, Tuple, List, Any
from collections import defaultdict
import io
import json
from aiogram import F
from PIL import Image
from aiogram.filters import StateFilter

from aiogram import Bot, Dispatcher, F, Router
from aiogram.types import Message, CallbackQuery, InlineKeyboardMarkup, InlineKeyboardButton, FSInputFile, ReplyKeyboardMarkup, KeyboardButton
from aiogram.enums import ChatAction
from aiogram.filters import Command
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage

from apscheduler.schedulers.asyncio import AsyncIOScheduler
from apscheduler.triggers.cron import CronTrigger

import plotly.graph_objects as go
from plotly.subplots import make_subplots

import signal

from google import genai
from google.genai import types

# ============ СОСТОЯНИЯ ============
class RatingState(StatesGroup):
    waiting_for_rating = State()
    waiting_for_mood_text = State()

class WorkoutState(StatesGroup):
    waiting_for_goal = State()
    choosing_category = State()
    choosing_exercise = State()
    entering_reps = State()
    entering_weight = State()
    entering_distance = State()
    entering_duration = State()
    confirm_continue = State()
    creating_category = State()
    renaming_category = State()
    deleting_category_confirm = State()
    creating_exercise = State()
    renaming_exercise = State()
    deleting_exercise_confirm = State()
    setting_goal_type = State()
    setting_strength_goal = State()
    setting_weight_increment = State()
    setting_cardio_goal = State()
    current_cat_id = State()
    current_ex_id = State()

class AIAdvisorState(StatesGroup):
    waiting_for_question = State()

class TaskState(StatesGroup):
    entering_title = State()
    choosing_repeat = State()
    choosing_days = State()
    choosing_priority = State()
    choosing_deadline = State()
    entering_deadline = State()

class AIPlanState(StatesGroup):
    choosing_mode = State()       # ai или manual
    choosing_goal = State()       # цель тренировок
    choosing_level = State()      # уровень
    choosing_days_count = State() # дней в неделю
    reviewing_plan = State()      # просмотр сгенерированного плана
    editing_plan = State()        # редактирование через ИИ
    entering_manual_plan = State()# ввод ручного плана
    entering_extra_notes = State() # доп пожелания

class WorkoutSessionState(StatesGroup):
    viewing_plan = State()        # экран плана на сегодня
    in_exercise = State()         # идёт упражнение
    entering_result = State()     # ввод текста результата
    skipping_day = State()        # ввод причины пропуска дня
    monthly_review = State()      # месячный пересмотр упражнений

class DietState(StatesGroup):
    weight = State()
    height = State()
    age = State()
    gender = State()
    activity = State()
    goal = State()
    target_weight = State()
    target_days = State()
    confirm = State()
    meal_type = State()
    food_description = State()
    manual_calories = State()
    food_confirm = State()
    new_food_name = State()
    new_food_calories = State()
    log_weight = State()
    body_fat_measurements = State()

# ============ ОБРАБОТЧИКИ ============
router = Router()

# ============ КОНФИГУРАЦИЯ ============
BOT_TOKEN = os.getenv("BOT_TOKEN")
GOOGLE_API_KEY = os.getenv("GOOGLE_API_KEY")

# ============ ОБАЛЬНЫЕ ПЕРЕМЕННЫЕ ============
user_last_menu: Dict[int, int] = {}
user_temp_messages: Dict[int, Dict[str, int]] = {}
user_history_page: Dict[int, int] = {}
user_food_history_page: Dict[int, int] = {}
user_welcome_message: Dict[int, int] = {}
scheduler = None
bot_instance = None

# ============ РАНГИ И ИСКРЫ ============
RANKS = {
    1: {"name": "Первые Искры", "emoji": "✨", "sparks_needed": 1, "motivation": "Первый шаг сделан! Искра зажжена, путь начат!"},
    2: {"name": "Искрящийся", "emoji": "💥", "sparks_needed": 7, "motivation": "Ты искришься энергией! Каждый день делает тебя ярче!"},
    3: {"name": "Горящий Огнем", "emoji": "🔥", "sparks_needed": 14, "motivation": "Ты горишь огнём прогресса! Ничто не остановит твой настрой!"},
    4: {"name": "Восходящая звезда", "emoji": "💫", "sparks_needed": 31, "motivation": "Ты восходишь над горизонтом! Твой свет заметен всем!"},
    5: {"name": "Супер звезда", "emoji": "⭐️", "sparks_needed": 62, "motivation": "Супер звезда во всей красе! Твоя дисциплина вдохновляет!"},
    6: {"name": "Яркий", "emoji": "🌟", "sparks_needed": 93, "motivation": "Ты сияешь как никто другой! Яркость твоей дисциплины ослепляет!"},
    7: {"name": "Самый Яркий", "emoji": "☀️", "sparks_needed": 183, "motivation": "Ты — центр вселенной продуктивности! Самый яркий из всех!"},
    8: {"name": "Нейтронная Звезда", "emoji": "❤️‍🔥", "sparks_needed": 365, "motivation": "Невероятная плотность дисциплины! Ты — явление вселенского масштаба!"}
}

MAX_SPARKS_PER_DAY = 2
SPARK_FOR_CATEGORIES = 1
SPARK_FOR_WORKOUT = 1

# ============ БАЗА ДАННЫХ (Turso, с фолбэком на локальный SQLite) ============
# Путь к локальному файлу — используется только если Turso не настроен
# (например, при локальной разработке без облачной БД).
DB_PATH = os.environ.get('DB_PATH', 'tracker.db')

# Если заданы обе переменные — бот подключается напрямую к Turso по сети,
# без локального файла вообще, так что редеплой (даже на платформе с
# эфемерной файловой системой вроде Infrlo) базу не трогает.
TURSO_DATABASE_URL = os.environ.get('TURSO_DATABASE_URL')
TURSO_AUTH_TOKEN = os.environ.get('TURSO_AUTH_TOKEN')
USE_TURSO = bool(TURSO_DATABASE_URL and TURSO_AUTH_TOKEN and libsql is not None)

class _CompatRow:
    """Даёт результату из libsql тот же интерфейс, что и sqlite3.Row:
    доступ по индексу, по имени колонки, dict(row), .keys() — чтобы весь
    остальной код (написанный под sqlite3.Row) не пришлось переписывать."""
    __slots__ = ('_cols', '_data')

    def __init__(self, cols, values):
        self._cols = cols
        self._data = tuple(values)

    def __getitem__(self, key):
        if isinstance(key, str):
            return self._data[self._cols.index(key)]
        return self._data[key]

    def keys(self):
        return list(self._cols)

    def __iter__(self):
        return iter(self._data)

    def __len__(self):
        return len(self._data)

    def __repr__(self):
        return f"<Row {dict(zip(self._cols, self._data))}>"

class _CompatCursor:
    """Оборачивает курсор libsql так, чтобы fetchone()/fetchall() возвращали
    _CompatRow вместо голых кортежей (как sqlite3.Row делает для sqlite3)."""

    def __init__(self, raw_cursor):
        self._cur = raw_cursor

    def _cols(self):
        return [d[0] for d in (self._cur.description or [])]

    def fetchone(self):
        row = self._cur.fetchone()
        return None if row is None else _CompatRow(self._cols(), row)

    def fetchall(self):
        cols = self._cols()
        return [_CompatRow(cols, r) for r in self._cur.fetchall()]

    @property
    def lastrowid(self):
        return getattr(self._cur, 'lastrowid', None)

    @property
    def rowcount(self):
        return getattr(self._cur, 'rowcount', -1)

class Database:
    """
    Обёртка над одним постоянным соединением с базой данных.
    Режим 'turso': подключение напрямую к облачной Turso по сети, без
    локального файла - данные переживают любой редеплой.
    Режим 'sqlite': локальный файл, как раньше (фолбэк для локальной
    разработки без облачной БД).
    Оба режима дают одинаковый интерфейс execute()/commit()/close(), так что
    остальной код бота не завязан на то, какой режим сейчас активен.
    """
    _instance = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._init_connection()
        return cls._instance

    def _init_connection(self):
        self._lock = threading.RLock()
        if USE_TURSO:
            self._mode = 'turso'
            self._conn = libsql.connect(database=TURSO_DATABASE_URL, auth_token=TURSO_AUTH_TOKEN)
        else:
            self._mode = 'sqlite'
            self._conn = sqlite3.connect(DB_PATH, check_same_thread=False)
            self._conn.row_factory = sqlite3.Row
            self._conn.execute("PRAGMA foreign_keys = ON")

    def execute(self, query: str, params: tuple = ()):
        with self._lock:
            is_write = query.strip().upper().startswith(
                ('INSERT', 'UPDATE', 'DELETE', 'CREATE', 'DROP', 'ALTER', 'PRAGMA')
            )
            if self._mode == 'turso':
                cur = self._conn.execute(query, params)
                if is_write:
                    try:
                        self._conn.commit()
                    except Exception as e:
                        # Некоторые режимы Turso автокоммитят каждый запрос сами -
                        # тогда commit() может быть не нужен/не поддержан. Не роняем
                        # бота из-за этого, но логируем на случай если причина другая.
                        print(f"[DB-TURSO] commit() после записи: {e}")
                return _CompatCursor(cur)
            else:
                cur = self._conn.cursor()
                cur.execute(query, params)
                if is_write:
                    self._conn.commit()
                return cur

    def commit(self):
        with self._lock:
            self._conn.commit()

    def close(self):
        with self._lock:
            self._conn.close()

db = Database()


def log_db_persistence_diagnostics():
    """Печатает в лог, какой режим БД активен и куда фактически идут данные.
    Полезно для диагностики 'после редеплоя бот всё забыл'."""
    print(f"[DB] Режим: {'Turso (удалённая БД, без локального файла)' if USE_TURSO else 'локальный файл SQLite'}")
    if TURSO_DATABASE_URL and TURSO_AUTH_TOKEN and libsql is None:
        print("[DB] ⚠️ TURSO_DATABASE_URL и TURSO_AUTH_TOKEN заданы, но пакет libsql не установлен - "
              "добавь 'libsql' в requirements.txt. Пока используется локальный файл (не переживёт редеплой).")
    if USE_TURSO:
        print(f"[DB] TURSO_DATABASE_URL: {TURSO_DATABASE_URL}")
        try:
            tasks_count = db.execute("SELECT COUNT(*) FROM tasks").fetchone()[0]
            ratings_count = db.execute("SELECT COUNT(*) FROM ratings").fetchone()[0]
            print(f"[DB] Текущие данные в Turso: tasks={tasks_count}, ratings={ratings_count}")
        except Exception as e:
            print(f"[DB] Не удалось прочитать счётчики строк из Turso (возможно таблицы ещё не созданы): {e}")
        return
    abs_path = os.path.abspath(DB_PATH)
    existed_before = os.path.exists(abs_path)
    size = os.path.getsize(abs_path) if existed_before else 0
    print(f"[DB] DB_PATH env: {os.environ.get('DB_PATH', '<не задан, используется default tracker.db>')}")
    print(f"[DB] Абсолютный путь к файлу БД: {abs_path}")
    print(f"[DB] Файл существовал до старта: {existed_before} (размер: {size} байт)")
    print("[DB] ⚠️ Turso не настроен (нет TURSO_DATABASE_URL/TURSO_AUTH_TOKEN) - используется локальный "
          "файл. На большинстве хостингов с эфемерной файловой системой (в т.ч. Infrlo) он не "
          "переживёт редеплой. Задай TURSO_DATABASE_URL и TURSO_AUTH_TOKEN, чтобы данные хранились "
          "в облаке Turso и не терялись.")
    try:
        tasks_count = db.execute("SELECT COUNT(*) FROM tasks").fetchone()[0]
        ratings_count = db.execute("SELECT COUNT(*) FROM ratings").fetchone()[0]
        print(f"[DB] Текущие данные: tasks={tasks_count}, ratings={ratings_count}")
    except Exception as e:
        print(f"[DB] Не удалось прочитать счётчики строк (возможно таблицы ещё не созданы): {e}")

def log_ratings_ai_diagnostics():
    """Печатает при старте, настроен ли отдельный ключ для авто-оценки Еды/Активности/Настроя.
    Если ключа нет - sync_diet_rating_for_today/sync_activity_rating_for_today и мод-флоу
    молча ничего не делают (это осознанное поведение - чтобы не выдумывать оценку),
    поэтому по симптомам ('значения не обновляются', 'настрой всегда просит оценить вручную')
    это выглядит как баг, хотя на самом деле просто не задана переменная окружения."""
    key_present = bool(os.environ.get("GOOGLE_API_KEY_RATINGS") or os.environ.get("GEMINI_API_KEY_RATINGS"))
    print(f"[RATINGS-AI] GOOGLE_API_KEY_RATINGS настроен: {key_present}")
    if not key_present:
        print("[RATINGS-AI] ⚠️ Ключ не задан - авто-оценка 'еда'/'активность' и AI-оценка 'настроя' "
              "не будут работать (тихо ничего не делают), 'настрой' всегда будет уходить в ручной ввод. "
              "Задайте переменную окружения GOOGLE_API_KEY_RATINGS с ключом Google AI Studio.")

# ============ ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ ============
def get_current_rank(total_sparks: int) -> int:
    current_rank = 1
    for rank_id, rank_data in sorted(RANKS.items()):
        if total_sparks >= rank_data["sparks_needed"]:
            current_rank = rank_id
        else:
            break
    return current_rank

def get_sparks_for_next_rank(current_rank: int, total_sparks: int) -> Tuple[int, int]:
    if current_rank >= 8:
        return (0, 365)
    next_rank = current_rank + 1
    next_sparks_needed = RANKS[next_rank]["sparks_needed"]
    sparks_needed = next_sparks_needed - total_sparks
    return (sparks_needed, next_sparks_needed)

def get_rank_emoji(rank_id: int) -> str:
    return RANKS.get(rank_id, RANKS[1])["emoji"]

def get_rank_name(rank_id: int) -> str:
    return RANKS.get(rank_id, RANKS[1])["name"]

def get_rank_motivation(rank_id: int) -> str:
    return RANKS.get(rank_id, RANKS[1])["motivation"]

def get_time_greeting(name: str) -> str:
    hour = datetime.now().hour
    if 5 <= hour < 12:
        return f"Бодрячком, {name}! 🌅"
    elif 12 <= hour < 17:
        return f"Как погодка, {name} ?☀️"
    elif 17 <= hour < 22:
        return f"Доообрый Вечер, {name}! 🌆"
    else:
        return f"Не спится, {name}? 🌙"

def create_new_progress_bar(current: int, max_val: int = 10) -> str:
    filled = min(current, max_val)
    empty = max_val - filled
    return "🔳" * filled + "◼️" * empty

def create_short_progress_bar(rating: int, total: int = 5) -> str:
    filled = round(rating / 10 * total)
    filled = min(filled, total)
    empty = total - filled
    return "🔳" * filled + "◼️" * empty

def create_workout_progress_bar(current: int, goal: int) -> str:
    if goal == 0:
        return "◼️" * 12 + " 0%"
    percentage = min(current / goal, 1.0)
    filled = int(12 * percentage)
    empty = 12 - filled
    return "🔳" * filled + "◼️" * empty + f" {int(percentage * 100)}%"

async def delete_message_safe(bot: Bot, chat_id: int, message_id: Optional[int]):
    if message_id:
        try:
            await bot.delete_message(chat_id, message_id)
        except Exception as e:
            print(f"[BOT] Ошибка удаления сообщения {message_id}: {e}")

async def delete_message_after_delay(bot: Bot, chat_id: int, message_id: Optional[int], delay: int = 10):
    await asyncio.sleep(delay)
    await delete_message_safe(bot, chat_id, message_id)

async def delete_temp_messages(bot: Bot, user_id: int, chat_id: int, keep_ai: bool = True):
    """Удаляет все временные сообщения кроме явно сохранённых."""
    temps = user_temp_messages.get(user_id, {})
    if not temps:
        return
    # Ключи, которые НЕ удаляем: ИИ сообщения, фото анализа, замеры % жира
    keys_to_preserve = set()
    if keep_ai:
        keys_to_preserve.update({'ai_response', 'ai_advisor'})
    keys_to_preserve.update({'photo_analysis_result', 'photo_user', 'body_fat_measurements', 'body_fat_result'})

    keys_to_delete = []
    for key, msg_id in list(temps.items()):
        if key in keys_to_preserve:
            continue
        keys_to_delete.append(key)
        await delete_message_safe(bot, chat_id, msg_id)
    for key in keys_to_delete:
        del temps[key]

async def send_spark_animation(bot: Bot, chat_id: int, text: str):
    spark_msg = await bot.send_message(chat_id, "✨")
    text_msg = await bot.send_message(chat_id, text)
    await asyncio.sleep(3)
    await delete_message_safe(bot, chat_id, spark_msg.message_id)
    await delete_message_safe(bot, chat_id, text_msg.message_id)

async def send_temp_message(bot: Bot, chat_id: int, text: str, delay: int = 3):
    msg = await bot.send_message(chat_id, text)
    await asyncio.sleep(delay)
    await delete_message_safe(bot, chat_id, msg.message_id)

# ============ ФУНКЦИИ GEMINI ============
def strip_markdown(text: str) -> str:
    """Убирает markdown-разметку и лишние эмодзи из ответов ИИ."""
    import re, unicodedata
    # Убираем markdown
    text = re.sub(r'\*\*(.+?)\*\*', r'\1', text, flags=re.DOTALL)
    text = re.sub(r'\*(.+?)\*', r'\1', text, flags=re.DOTALL)
    text = re.sub(r'__(.+?)__', r'\1', text, flags=re.DOTALL)
    text = re.sub(r'_(.+?)_', r'\1', text, flags=re.DOTALL)
    text = re.sub(r'^#{1,6}\s+', '', text, flags=re.MULTILINE)
    # Ограничиваем количество эмодзи: оставляем максимум 1 эмодзи подряд
    def is_emoji(ch):
        cp = ord(ch)
        return (0x1F300 <= cp <= 0x1FAFF) or (0x2600 <= cp <= 0x27BF) or (0xFE00 <= cp <= 0xFE0F)
    result = []
    prev_emoji = False
    for ch in text:
        if is_emoji(ch):
            if not prev_emoji:
                result.append(ch)
            prev_emoji = True
        else:
            prev_emoji = False
            result.append(ch)
    # Убираем эмодзи в начале каждой строки (кроме первого)
    lines = ''.join(result).split('\n')
    cleaned = []
    for line in lines:
        stripped = line.lstrip()
        # Удаляем ведущие эмодзи-маркеры типа "🔸 текст" -> "текст"
        stripped = re.sub(r'^[\U0001F300-\U0001FAFF\U00002600-\U000027BF]+\s*', '', stripped)
        # Восстанавливаем отступ
        indent = len(line) - len(line.lstrip())
        cleaned.append(' ' * indent + stripped)
    return '\n'.join(cleaned)

def gemini_generate(prompt: str, max_tokens: int = 8192, raw: bool = False) -> str:
    """Синхронный вызов Gemini. raw=True — не применять strip_markdown (для JSON-ответов)."""
    api_key = os.environ.get("GOOGLE_API_KEY") or os.environ.get("GEMINI_API_KEY")
    if not api_key:
        return "❌ ИИ недоступен (нет API-ключа). Установи GOOGLE_API_KEY или GEMINI_API_KEY."
    try:
        client = genai.Client(api_key=api_key)
        response = client.models.generate_content(
            model='gemini-3.6-flash',
            contents=prompt,
            config=types.GenerateContentConfig(max_output_tokens=max_tokens)
        )
        text = getattr(response, 'text', None)
        if text:
            text = text.strip()
            if raw:
                print(f"[GEMINI] Raw response ({len(text)} chars): {repr(text[:200])}")
                return text
            return strip_markdown(text)
        if response.candidates and response.candidates[0].content.parts:
            t = response.candidates[0].content.parts[0].text.strip()
            if raw:
                print(f"[GEMINI] Raw response from candidates ({len(t)} chars): {repr(t[:200])}")
                return t
            return strip_markdown(t)
        return "❌ ИИ не вернул ответ (возможно, сработала фильтрация)."
    except Exception as e:
        import traceback
        print(f"[GEMINI] Ошибка: {e}")
        traceback.print_exc()
        return "❌ Ошибка при обращении к ИИ. Проверь GOOGLE_API_KEY и логи сервера."

def gemini_generate_json(prompt: str, max_tokens: int = 8192) -> str:
    """Вызов Gemini для JSON-ответов — thinking отключён, все токены идут в ответ."""
    api_key = os.environ.get("GOOGLE_API_KEY") or os.environ.get("GEMINI_API_KEY")
    if not api_key:
        return ""
    try:
        client = genai.Client(api_key=api_key)
        response = client.models.generate_content(
            model='gemini-3.6-flash',
            contents=prompt,
            config=types.GenerateContentConfig(
                max_output_tokens=max_tokens,
                thinking_config=types.ThinkingConfig(thinking_budget=0)
            )
        )
        text = getattr(response, 'text', None)
        if text:
            text = text.strip()
            print(f"[GEMINI_JSON] Response ({len(text)} chars): {repr(text[:200])}")
            return text
        if response.candidates and response.candidates[0].content.parts:
            t = response.candidates[0].content.parts[0].text.strip()
            print(f"[GEMINI_JSON] Response from candidates ({len(t)} chars): {repr(t[:200])}")
            return t
        return ""
    except Exception as e:
        import traceback
        print(f"[GEMINI_JSON] Ошибка: {e}")
        traceback.print_exc()
        return ""

def gemini_generate_rating(prompt: str, max_tokens: int = 1024) -> Optional[dict]:
    """Вызов Gemini через ОТДЕЛЬНЫЙ API-ключ (GOOGLE_API_KEY_RATINGS), используется
    только для авто-оценки категорий 'еда'/'активность'/'настрой'. Модель должна
    ответить JSON {"rating": 1-10, "comment"/"response": "..."}. Возвращает None если
    ключ не настроен или запрос не удался — вызывающий код должен в этом случае
    откатиться на ручной ввод оценки, а не выдумывать число."""
    api_key = os.environ.get("GOOGLE_API_KEY_RATINGS") or os.environ.get("GEMINI_API_KEY_RATINGS")
    if not api_key:
        return None
    text = None
    try:
        client = genai.Client(api_key=api_key)
        response = client.models.generate_content(
            model='gemini-3.6-flash',
            contents=prompt,
            config=types.GenerateContentConfig(
                max_output_tokens=max_tokens,
                thinking_config=types.ThinkingConfig(thinking_budget=0)
            )
        )
        text = getattr(response, 'text', None)
        if not text and response.candidates and response.candidates[0].content.parts:
            text = response.candidates[0].content.parts[0].text
        if not text:
            print(f"[GEMINI-RATINGS] Пустой ответ от модели. finish_reason: "
                  f"{getattr(response.candidates[0], 'finish_reason', '?') if response.candidates else '?'}")
            return None
        text = text.strip()
        text = re.sub(r'^```json\s*|\s*```$', '', text).strip()
        data = json.loads(text)
        rating = max(1, min(10, int(round(float(data.get('rating'))))))
        # разные промпты просят модель назвать поле по-разному ('comment' у Еды/Активности,
        # 'response' у Настроя) - читаем любое из них, чтобы текст не терялся
        comment = str(data.get('comment') or data.get('response') or '').strip()
        return {'rating': rating, 'comment': comment}
    except Exception as e:
        import traceback
        print(f"[GEMINI-RATINGS] Ошибка ({type(e).__name__}): {e}")
        if text is not None:
            print(f"[GEMINI-RATINGS] Ответ модели, который не удалось разобрать: {repr(text[:300])}")
        traceback.print_exc()
        return None

def analyze_food_photo(image_bytes: bytes, prompt: str) -> Optional[str]:
    """Распознавание блюда/калорий по фото. Возвращает None при ошибке,
    чтобы вызывающий код мог показать кнопку повтора."""
    api_key = os.environ.get("GOOGLE_API_KEY") or os.environ.get("GEMINI_API_KEY")
    if not api_key or not image_bytes:
        return None
    try:
        client = genai.Client(api_key=api_key)
        image_part = types.Part.from_bytes(data=image_bytes, mime_type='image/png')
        response = client.models.generate_content(
            model='gemini-3.6-flash',
            contents=[image_part, prompt],
            config=types.GenerateContentConfig(max_output_tokens=256)
        )
        text = (getattr(response, 'text', None) or "").strip()
        if not text and response.candidates and response.candidates[0].content.parts:
            text = response.candidates[0].content.parts[0].text.strip()
        return text or None
    except Exception as e:
        import traceback
        print(f"[FOOD PHOTO] Ошибка: {e}")
        traceback.print_exc()
        return None

def photo_analysis_cancel_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="❌ Отмена", callback_data="photo_analysis_cancel")]
    ])

def photo_analysis_back_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Назад в меню", callback_data="photo_analysis_back")]
    ])

@router.message(F.text == "🤳 Анализ фото")
async def handle_photo_analysis_start(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    await state.clear()
    await delete_temp_messages(bot, message.from_user.id, message.chat.id, keep_ai=True)
    intro_msg = await message.answer(
        "📸 Отправь фото для анализа телосложения.\n\nИли нажми «❌ Отмена».",
        reply_markup=photo_analysis_cancel_keyboard()
    )
    user_temp_messages.setdefault(message.from_user.id, {})['photo_intro'] = intro_msg.message_id
    await state.set_state("waiting_for_photo")

@router.message(F.photo, StateFilter("waiting_for_photo"))
async def analyze_photo(message: Message, bot: Bot, state: FSMContext):
    user_id = message.from_user.id
    chat_id = message.chat.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, chat_id, temps.get('photo_intro'))
    if 'photo_intro' in temps:
        del temps['photo_intro']
    # Сохраняем фото пользователя (не удаляем)
    temps['photo_user'] = message.message_id
    user_temp_messages[user_id] = temps

    status_msg = await message.answer("🔍 Загружаю фото...")
    statuses = ["🔍 Анализирую телосложение...", "💪 Оцениваю пропорции...", "📝 Готовлю разбор..."]
    for s in statuses:
        await asyncio.sleep(1)
        try:
            await status_msg.edit_text(s)
        except:
            pass

    photo = message.photo[-1]
    file = await bot.get_file(photo.file_id)
    buffer = await bot.download_file(file.file_path)
    if buffer is None or not hasattr(buffer, 'read'):
        await status_msg.edit_text("❌ Не удалось загрузить фото.")
        await state.clear()
        await show_workout_main_menu(user_id, chat_id, bot)
        return
    if hasattr(buffer, 'seek'):
        buffer.seek(0)
    image = Image.open(buffer)
    img_buffer = io.BytesIO()
    image.save(img_buffer, format='PNG')
    image_bytes = img_buffer.getvalue()

    prompt = """Кратко проанализируй телосложение на фото. Формат ответа:
• Сильные стороны (1-2 предложения)
• Слабые стороны (1-2 предложения)
• Рекомендации (2-3 конкретных совета)
Без воды, по делу, макс 150 слов."""
    await state.update_data(
        retry_photo_bytes=image_bytes,
        retry_photo_prompt=prompt,
        retry_action="photo_analysis"
    )
    api_key = os.environ.get("GOOGLE_API_KEY") or os.environ.get("GEMINI_API_KEY")
    if not api_key:
        analysis = "❌ ИИ недоступен (нет API-ключа)."
    else:
        try:
            client = genai.Client(api_key=api_key)
            image_part = types.Part.from_bytes(data=image_bytes, mime_type='image/png')
            response = await run_in_thread(
                client.models.generate_content,
                model='gemini-3.6-flash',
                contents=[prompt, image_part],
                config=types.GenerateContentConfig(max_output_tokens=2048)
            )
            text = getattr(response, 'text', None)
            analysis = text.strip() if text else (response.candidates[0].content.parts[0].text if response.candidates and response.candidates[0].content.parts else "❌ Нет ответа")
        except Exception as e:
            import traceback
            traceback.print_exc()
            analysis = f"❌ Ошибка: {str(e)[:100]}"

    await delete_message_safe(bot, chat_id, status_msg.message_id)
    if analysis.startswith("❌"):
        result_msg = await message.answer(
            analysis + "\n\n🔄 Нажми кнопку чтобы попробовать ещё раз.",
            reply_markup=retry_ai_keyboard("photo_analysis")
        )
        user_temp_messages.setdefault(user_id, {})['photo_analysis_result'] = result_msg.message_id
        await state.clear()
        return
    result_msg = await message.answer(analysis, reply_markup=photo_analysis_back_keyboard())
    user_temp_messages.setdefault(user_id, {})['photo_analysis_result'] = result_msg.message_id
    await state.clear()

@router.callback_query(F.data == "photo_analysis_cancel", StateFilter("waiting_for_photo"))
async def photo_analysis_cancel(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, callback.message.chat.id, temps.get('photo_intro'))
    # НЕ удаляем фото пользователя и анализ ИИ при отмене
    await state.clear()
    await show_workout_main_menu(user_id, callback.message.chat.id, bot)
    try:
        await callback.message.delete()
    except:
        pass
    await callback.answer()

@router.callback_query(F.data == "photo_analysis_back")
async def photo_analysis_back(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    await delete_temp_messages(bot, user_id, callback.message.chat.id, keep_ai=True)
    # Убираем инлайн кнопки у сохранённых сообщений (включая сам результат анализа)
    temps = user_temp_messages.get(user_id, {})
    for key in ['photo_analysis_result', 'photo_user', 'body_fat_measurements', 'body_fat_result']:
        if key in temps:
            try:
                await bot.edit_message_reply_markup(callback.message.chat.id, temps[key])
            except:
                pass
    await state.clear()
    await send_main_menu(bot, user_id, callback.message.chat.id)
    await callback.answer()

@router.message(StateFilter("waiting_for_photo"), F.text)
async def photo_timeout(message: Message, bot: Bot, state: FSMContext):
    await message.answer("Я ждал фото. Отмена.")
    await state.clear()
    await show_workout_main_menu(message.from_user.id, message.chat.id, bot)

# ============ БАЗОВЫЕ ФУНКЦИИ ПОЛЬЗОВАТЕЛЯ ============
def save_user_settings(user_id: int, username: str, first_name: str):
    # NOTE: last_active_date is intentionally NOT set/overwritten here.
    # It's owned by update_streak()/get_streak() below - if we stamp it with
    # today's date on every call (which used to happen right before
    # update_streak() ran), update_streak() would always see last_date ==
    # today already and could never tell "a new day has started", so the
    # streak would never increment.
    db.execute('''
        INSERT INTO user_settings (user_id, username, first_name, last_active_date)
        VALUES (?, ?, ?, NULL)
        ON CONFLICT(user_id) DO UPDATE SET 
            username = excluded.username,
            first_name = excluded.first_name
    ''', (user_id, username, first_name))
    db.commit()

def get_user_name(user_id: int, fallback: Optional[str] = None) -> str:
    cursor = db.execute('SELECT first_name FROM user_settings WHERE user_id = ?', (user_id,))
    row = cursor.fetchone()
    if row and row[0]:
        return row[0]
    return fallback or "друг"

# ---------- ЧАСОВЫЕ ПОЯСА ----------
DEFAULT_TIMEZONE = "Europe/Moscow"

# Несколько самых популярных часовых поясов России (для быстрого выбора кнопками)
RUSSIAN_TIMEZONES = [
    ("Калининград (UTC+2)", "Europe/Kaliningrad"),
    ("Москва (UTC+3)", "Europe/Moscow"),
    ("Самара (UTC+4)", "Europe/Samara"),
    ("Екатеринбург (UTC+5)", "Asia/Yekaterinburg"),
    ("Омск (UTC+6)", "Asia/Omsk"),
    ("Красноярск (UTC+7)", "Asia/Krasnoyarsk"),
    ("Иркутск (UTC+8)", "Asia/Irkutsk"),
    ("Владивосток (UTC+10)", "Asia/Vladivostok"),
]

def get_user_timezone(user_id: int) -> str:
    cursor = db.execute('SELECT timezone FROM user_settings WHERE user_id = ?', (user_id,))
    row = cursor.fetchone()
    if row and row[0]:
        return row[0]
    return DEFAULT_TIMEZONE

def set_user_timezone(user_id: int, tz_name: str):
    db.execute('''
        INSERT INTO user_settings (user_id, timezone) VALUES (?, ?)
        ON CONFLICT(user_id) DO UPDATE SET timezone = excluded.timezone
    ''', (user_id, tz_name))
    db.commit()

def _resolve_tz(tz_name: str) -> ZoneInfo:
    try:
        return ZoneInfo(tz_name)
    except Exception:
        return ZoneInfo(DEFAULT_TIMEZONE)

def user_now(user_id: int) -> datetime:
    """Текущее время в часовом поясе пользователя (а не сервера)."""
    return datetime.now(_resolve_tz(get_user_timezone(user_id)))

def user_today_str(user_id: int, fmt: str = '%Y-%m-%d') -> str:
    return user_now(user_id).strftime(fmt)

def user_today_date(user_id: int):
    return user_now(user_id).date()

def user_weekday(user_id: int) -> int:
    return user_now(user_id).weekday()

def timezone_picker_keyboard(context: str = "onboarding"):
    rows = [[InlineKeyboardButton(text=label, callback_data=f"tz:{tz}:{context}")] for label, tz in RUSSIAN_TIMEZONES]
    return InlineKeyboardMarkup(inline_keyboard=rows)

def update_streak(user_id: int):
    today = user_today_str(user_id)
    yesterday = (user_now(user_id) - timedelta(days=1)).strftime('%Y-%m-%d')
    cursor = db.execute('SELECT streak_days, last_active_date FROM user_settings WHERE user_id = ?', (user_id,))
    row = cursor.fetchone()
    if row:
        streak, last_date = row
        if last_date == yesterday:
            streak += 1
        elif last_date != today:
            streak = 1
        db.execute('''
            UPDATE user_settings SET streak_days = ?, last_active_date = ?
            WHERE user_id = ?
        ''', (streak, today, user_id))
        db.commit()

def get_streak(user_id: int) -> int:
    today = user_today_str(user_id)
    yesterday = (user_now(user_id) - timedelta(days=1)).strftime('%Y-%m-%d')
    cursor = db.execute('SELECT streak_days, last_active_date FROM user_settings WHERE user_id = ?', (user_id,))
    row = cursor.fetchone()
    if not row:
        return 0
    streak, last_date = row
    # Если последняя активность не сегодня и не вчера — стрик сброшен
    if last_date not in (today, yesterday):
        if last_date is not None:
            db.execute('UPDATE user_settings SET streak_days = 0 WHERE user_id = ?', (user_id,))
            db.commit()
        return 0
    return streak if streak else 0

# ============ ФУНКЦИИ ДЛЯ ОЦЕНОК ============
def save_rating(user_id: int, category: str, rating: int, date: str):
    db.execute('''
        INSERT INTO ratings (user_id, category, rating, day_date)
        VALUES (?, ?, ?, ?)
        ON CONFLICT(user_id, category, day_date) 
        DO UPDATE SET rating = excluded.rating
    ''', (user_id, category, rating, date))
    db.commit()

def get_ratings(user_id: int, days: int = 1) -> list:
    date_from = (user_now(user_id) - timedelta(days=days-1)).strftime('%Y-%m-%d')
    valid_categories = ('сон', 'еда', 'активность', 'зависание', 'настрой')
    cursor = db.execute('''
        SELECT category, AVG(rating) as avg_rating, COUNT(*) as count
        FROM ratings 
        WHERE user_id = ? AND day_date >= ? AND category IN {} 
        GROUP BY category
    '''.format(valid_categories), (user_id, date_from))
    return cursor.fetchall()

def get_daily_ratings(user_id: int, days: int = 7) -> list:
    date_from = (user_now(user_id) - timedelta(days=days-1)).strftime('%Y-%m-%d')
    valid_categories = ('сон', 'еда', 'активность', 'зависание', 'настрой')
    cursor = db.execute('''
        SELECT day_date, category, rating
        FROM ratings 
        WHERE user_id = ? AND day_date >= ? AND category IN {}
        ORDER BY day_date, category
    '''.format(valid_categories), (user_id, date_from))
    return cursor.fetchall()

def get_today_ratings(user_id: int) -> dict:
    today = user_today_str(user_id)
    cursor = db.execute('''
        SELECT category, rating FROM ratings 
        WHERE user_id = ? AND day_date = ?
    ''', (user_id, today))
    return {r[0]: r[1] for r in cursor.fetchall()}

def get_yesterday_ratings(user_id: int) -> dict:
    yesterday = (user_now(user_id) - timedelta(days=1)).strftime('%Y-%m-%d')
    cursor = db.execute('''
        SELECT category, rating FROM ratings 
        WHERE user_id = ? AND day_date = ?
    ''', (user_id, yesterday))
    return {r[0]: r[1] for r in cursor.fetchall()}

def get_user_stats_for_ai(user_id: int) -> dict:
    ratings_7d = get_ratings(user_id, days=7)
    ratings_30d = get_ratings(user_id, days=30)
    workout_data = get_or_create_workout_data(user_id)
    rank_data = get_or_create_rank_data(user_id)
    yesterday = get_yesterday_ratings(user_id)
    return {
        'today': get_today_ratings(user_id),
        'yesterday': yesterday,
        'week_avg': {cat: avg for cat, avg, _ in ratings_7d},
        'month_avg': {cat: avg for cat, avg, _ in ratings_30d},
        'workouts': workout_data,
        'rank': rank_data
    }

def get_full_context_for_ai(user_id: int) -> str:
    """Собирает свежую сводку по рефлексии, диете, тренировкам и задачам,
    чтобы ответы и советы ИИ были персонализированы под конкретного пользователя."""
    lines = []

    # --- Рефлексия ---
    stats = get_user_stats_for_ai(user_id)
    today_r = stats['today']
    yesterday_r = stats['yesterday']
    week_avg = stats['week_avg']
    if today_r:
        lines.append("Рефлексия сегодня: " + ", ".join(f"{cat} {val}/10" for cat, val in today_r.items()))
    else:
        lines.append("Рефлексия сегодня: ещё не заполнена.")
    if yesterday_r:
        lines.append("Рефлексия вчера: " + ", ".join(f"{cat} {val}/10" for cat, val in yesterday_r.items()))
    if week_avg:
        lines.append("Средние оценки за 7 дней: " + ", ".join(f"{cat} {val:.1f}" for cat, val in week_avg.items()))

    # --- Диета ---
    try:
        profile = get_diet_profile(user_id)
    except Exception:
        profile = None
    if profile:
        today_cal = get_today_calories(user_id)
        goal = profile.get('daily_calories') or 0
        lines.append(f"Диета: цель {int(goal)} ккал/день, съедено сегодня {int(today_cal)} ккал.")
        food_log = get_today_food_log(user_id)
        if food_log:
            food_items = "; ".join(f"{meal}: {desc} ({int(cal)} ккал)" for meal, desc, cal in food_log)
            lines.append(f"Еда сегодня: {food_items}")
        last_weight = get_last_weight(user_id)
        if last_weight:
            lines.append(f"Последний зафиксированный вес: {last_weight} кг")
    else:
        lines.append("Диета: профиль питания ещё не настроен.")

    # --- Тренировки ---
    workouts = stats['workouts'] or {}
    lines.append(
        f"Тренировки в этом месяце: {workouts.get('current_count', 0)}/{workouts.get('monthly_goal', 0)}"
    )
    try:
        cursor = db.execute("""
            SELECT date, status, skip_reason FROM ai_workout_sessions
            WHERE user_id = ? AND status != 'pending'
            ORDER BY date DESC LIMIT 5
        """, (user_id,))
        recent_sessions = cursor.fetchall()
    except Exception:
        recent_sessions = []
    if recent_sessions:
        sess_lines = []
        for date, status, skip_reason in recent_sessions:
            if status == 'done':
                sess_lines.append(f"{date}: выполнена")
            elif status == 'skipped':
                reason = f" ({skip_reason})" if skip_reason else ""
                sess_lines.append(f"{date}: пропущена{reason}")
            else:
                sess_lines.append(f"{date}: {status}")
        lines.append("Последние тренировки: " + "; ".join(sess_lines))

    # --- Задачи ---
    try:
        tasks = get_tasks_for_today(user_id)
    except Exception:
        tasks = []
    if tasks:
        task_lines = []
        for t in tasks:
            mark = "🔥" if t.get('is_priority') else "-"
            done = " ✅" if t.get('is_done') else ""
            task_lines.append(f"{mark} {t['title']}{done}")
        lines.append("Задачи на сегодня: " + "; ".join(task_lines))

    return "\n".join(lines)

# ============ АВТО-ОЦЕНКА ЕДЫ / АКТИВНОСТИ (через ИИ, отдельный ключ) ============
def sync_diet_rating_for_today(user_id: int):
    """Пересчитывает оценку категории 'еда' за сегодня на основе фактически
    залогированной еды. Вызывается после каждой новой записи о еде.
    Если GOOGLE_API_KEY_RATINGS не настроен - ничего не делает (не выдумывает оценку)."""
    food_log = get_today_food_log(user_id)
    if not food_log:
        return
    profile = get_diet_profile(user_id)
    goal = profile.get('daily_calories') if profile else None
    today_cal = get_today_calories(user_id)
    food_items = "; ".join(f"{meal}: {desc} ({int(cal)} ккал)" for meal, desc, cal in food_log)
    prompt = f"""Ты оцениваешь качество питания пользователя за сегодня по шкале от 1 до 10.
Дневная цель по калориям: {int(goal) if goal else 'не задана'} ккал.
Съедено сегодня: {int(today_cal)} ккал.
Приёмы пищи: {food_items}

10 — питание сбалансированное, разнообразное и укладывается в цель по калориям.
1 — питание явно вредное или сильно выходит за рамки цели.
Ответь СТРОГО в формате JSON без пояснений: {{"rating": <целое число 1-10>, "comment": "<одно короткое предложение по-русски>"}}"""
    result = gemini_generate_rating(prompt)
    if result:
        save_rating(user_id, 'еда', result['rating'], user_today_str(user_id))

def sync_activity_rating_for_today(user_id: int):
    """Пересчитывает оценку категории 'активность' за сегодня на основе фактически
    выполненной тренировки. Вызывается сразу после завершения тренировки."""
    session = get_today_session(user_id)
    if not session or session.get('status') != 'done':
        return
    logs = get_session_exercise_logs(session['id'])
    if logs:
        log_lines = []
        for log in logs:
            if log.get('status') == 'skipped':
                log_lines.append(f"{log['exercise_name']}: пропущено")
            else:
                result = log.get('result') or {}
                log_lines.append(f"{log['exercise_name']}: {result}")
        exercises_summary = "; ".join(log_lines)
    else:
        exercises_summary = "нет подробных данных, но сессия отмечена как выполненная"
    prompt = f"""Ты оцениваешь качество сегодняшней тренировки пользователя по шкале от 1 до 10
на основе того, что реально выполнено.
Упражнения: {exercises_summary}

10 — тренировка выполнена полностью и качественно.
Ниже — если многое пропущено, сделано не полностью или с явными трудностями.
Ответь СТРОГО в формате JSON без пояснений: {{"rating": <целое число 1-10>, "comment": "<одно короткое предложение по-русски>"}}"""
    result = gemini_generate_rating(prompt)
    if result:
        save_rating(user_id, 'активность', result['rating'], user_today_str(user_id))

async def finalize_daily_ratings_for_timezone(tz_name: str):
    """Раз в сутки (23:55 по местному времени каждого часового пояса): если 'еда' или
    'активность' за сегодня так и не были залогированы - проставляет 0, а для
    активности - 5, если по плану сегодня был день отдыха."""
    try:
        if tz_name == DEFAULT_TIMEZONE:
            cursor = db.execute("SELECT user_id FROM user_settings WHERE timezone = ? OR timezone IS NULL", (tz_name,))
        else:
            cursor = db.execute("SELECT user_id FROM user_settings WHERE timezone = ?", (tz_name,))
        user_ids = [r[0] for r in cursor.fetchall()]
        for user_id in user_ids:
            today = user_today_str(user_id)
            today_ratings = get_today_ratings(user_id)
            if 'еда' not in today_ratings:
                save_rating(user_id, 'еда', 0, today)
            if 'активность' not in today_ratings:
                plan_data = get_ai_plan(user_id)
                is_rest_day = bool(plan_data) and not get_today_plan(plan_data, user_id)
                save_rating(user_id, 'активность', 5 if is_rest_day else 0, today)
    except Exception as e:
        print(f"[FINALIZE RATINGS] Ошибка для {tz_name}: {e}")

# ============ ФУНКЦИИ РАНГОВ И ИСКР ============
def _fetch_rank_data(user_id: int) -> dict:
    cursor = db.execute('SELECT * FROM user_ranks WHERE user_id = ?', (user_id,))
    row = cursor.fetchone()
    today = user_today_str(user_id)
    if row:
        user_id, total_sparks, current_rank, last_spark_date, sparks_today, cat_completed, workout_completed = row
        if last_spark_date != today:
            sparks_today = 0
            cat_completed = 0
            workout_completed = 0
            db.execute('''
                UPDATE user_ranks 
                SET sparks_today = 0, categories_completed_today = 0, workout_completed_today = 0, last_spark_date = ?
                WHERE user_id = ?
            ''', (today, user_id))
            db.commit()
        actual_rank = get_current_rank(total_sparks)
        if actual_rank != current_rank:
            current_rank = actual_rank
            db.execute('UPDATE user_ranks SET current_rank = ? WHERE user_id = ?', (current_rank, user_id))
            db.commit()
        return {
            'user_id': user_id,
            'total_sparks': total_sparks,
            'current_rank': current_rank,
            'sparks_today': sparks_today,
            'categories_completed_today': cat_completed,
            'workout_completed_today': workout_completed
        }
    else:
        db.execute('''
            INSERT INTO user_ranks (user_id, total_sparks, current_rank, last_spark_date, sparks_today, categories_completed_today, workout_completed_today)
            VALUES (?, 0, 1, ?, 0, 0, 0)
        ''', (user_id, today))
        db.commit()
        return {
            'user_id': user_id,
            'total_sparks': 0,
            'current_rank': 1,
            'sparks_today': 0,
            'categories_completed_today': 0,
            'workout_completed_today': 0
        }

def get_or_create_rank_data(user_id: int) -> dict:
    return _fetch_rank_data(user_id)

def check_all_categories_completed(user_id: int) -> bool:
    today_ratings = get_today_ratings(user_id)
    required_categories = {'сон', 'еда', 'активность', 'зависание', 'настрой'}
    return required_categories.issubset(set(today_ratings.keys()))

def manual_categories_completed(user_id: int) -> bool:
    """'еда' и 'активность' теперь выставляются автоматически (после лога еды/тренировки
    или в конце дня), а не кнопками. Эта проверка - только по трём категориям, которые
    пользователь реально заполняет сам, чтобы не зацикливать его в меню рефлексии,
    ожидая недостижимых вручную оценок."""
    today_ratings = get_today_ratings(user_id)
    required_categories = {'сон', 'зависание', 'настрой'}
    return required_categories.issubset(set(today_ratings.keys()))

def _deduct_spark_for_skip(user_id: int):
    """Отнимает 1 искру за пропущенный тренировочный день."""
    cursor = db.execute('SELECT total_sparks, current_rank FROM user_ranks WHERE user_id = ?', (user_id,))
    row = cursor.fetchone()
    if not row:
        return
    total = row[0]
    new_total = max(0, total - 1)
    new_rank = get_current_rank(new_total)
    db.execute('UPDATE user_ranks SET total_sparks = ?, current_rank = ? WHERE user_id = ?',
               (new_total, new_rank, user_id))
    db.commit()

def add_spark(user_id: int, spark_type: str) -> Tuple[bool, int, bool, int, int]:
    data = get_or_create_rank_data(user_id)
    # bonus_high bypasses daily limit
    if spark_type != 'bonus_high' and data['sparks_today'] >= MAX_SPARKS_PER_DAY:
        return (False, data['sparks_today'], False, data['current_rank'], data['current_rank'])
    if spark_type == 'categories' and data['categories_completed_today']:
        return (False, data['sparks_today'], False, data['current_rank'], data['current_rank'])
    if spark_type == 'workout' and data['workout_completed_today']:
        return (False, data['sparks_today'], False, data['current_rank'], data['current_rank'])
    old_rank = data['current_rank']
    today = user_today_str(user_id)
    if spark_type == 'categories':
        db.execute('''
            UPDATE user_ranks 
            SET total_sparks = total_sparks + ?, sparks_today = sparks_today + ?, 
                categories_completed_today = 1, last_spark_date = ?
            WHERE user_id = ?
        ''', (SPARK_FOR_CATEGORIES, SPARK_FOR_CATEGORIES, today, user_id))
    else:
        db.execute('''
            UPDATE user_ranks 
            SET total_sparks = total_sparks + ?, sparks_today = sparks_today + ?, 
                workout_completed_today = 1, last_spark_date = ?
            WHERE user_id = ?
        ''', (SPARK_FOR_WORKOUT, SPARK_FOR_WORKOUT, today, user_id))
    db.commit()
    new_data = get_or_create_rank_data(user_id)
    new_rank = new_data['current_rank']
    rank_up = new_rank > old_rank
    return (True, new_data['sparks_today'], rank_up, old_rank, new_rank)

# ============ ФУНКЦИИ ТРЕНИРОВОК ============
def get_or_create_workout_data(user_id: int) -> dict:
    cursor = db.execute('SELECT * FROM workouts WHERE user_id = ?', (user_id,))
    row = cursor.fetchone()
    today = user_today_str(user_id)
    current_month = user_today_str(user_id, '%Y-%m')
    if row:
        user_id, goal, count, last_date, today_count = row
        if last_date:
            last_month = last_date[:7]
            if last_month != current_month:
                count = 0
                today_count = 0
                db.execute('''
                    UPDATE workouts 
                    SET current_count = 0, today_count = 0, last_workout_date = ?
                    WHERE user_id = ?
                ''', (today, user_id))
                db.commit()
        if last_date != today:
            today_count = 0
            db.execute('UPDATE workouts SET today_count = 0 WHERE user_id = ?', (user_id,))
            db.commit()
        return {
            'user_id': user_id,
            'monthly_goal': goal,
            'current_count': count,
            'last_workout_date': last_date,
            'today_count': today_count
        }
    else:
        db.execute('''
            INSERT INTO workouts (user_id, monthly_goal, current_count, last_workout_date, today_count)
            VALUES (?, 0, 0, ?, 0)
        ''', (user_id, today))
        db.commit()
        return {
            'user_id': user_id,
            'monthly_goal': 0,
            'current_count': 0,
            'last_workout_date': today,
            'today_count': 0
        }

def set_workout_goal(user_id: int, goal: int):
    db.execute('''
        INSERT INTO workouts (user_id, monthly_goal, current_count, last_workout_date, today_count)
        VALUES (?, ?, 0, ?, 0)
        ON CONFLICT(user_id) DO UPDATE SET monthly_goal = excluded.monthly_goal
    ''', (user_id, goal, user_today_str(user_id)))
    db.commit()

def add_workout(user_id: int) -> dict:
    today = user_today_str(user_id)
    db.execute('''
        UPDATE workouts 
        SET current_count = current_count + 1, today_count = today_count + 1, last_workout_date = ?
        WHERE user_id = ?
    ''', (today, user_id))
    db.commit()
    return get_or_create_workout_data(user_id)

def change_workout_goal(user_id: int, new_goal: int):
    db.execute('UPDATE workouts SET monthly_goal = ? WHERE user_id = ?', (new_goal, user_id))
    db.commit()

# ============ ФУНКЦИИ ДЛЯ ДИЕТЫ ============
def save_diet_profile(user_id: int, weight: float, height: float, age: int, gender: str,
                      activity_level: float, goal_type: str, target_weight_change: float,
                      target_days: int, daily_calories: float):
    today = user_today_str(user_id)
    db.execute('''
        INSERT INTO diet_profile (user_id, weight, height, age, gender, activity_level,
                                   goal_type, target_weight_change, target_days, daily_calories, last_update_date)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(user_id) DO UPDATE SET
            weight = excluded.weight,
            height = excluded.height,
            age = excluded.age,
            gender = excluded.gender,
            activity_level = excluded.activity_level,
            goal_type = excluded.goal_type,
            target_weight_change = excluded.target_weight_change,
            target_days = excluded.target_days,
            daily_calories = excluded.daily_calories,
            last_update_date = excluded.last_update_date
    ''', (user_id, weight, height, age, gender, activity_level, goal_type,
          target_weight_change, target_days, daily_calories, today))
    db.commit()

def get_diet_profile(user_id: int) -> Optional[dict]:
    cursor = db.execute('SELECT * FROM diet_profile WHERE user_id = ?', (user_id,))
    row = cursor.fetchone()
    if row:
        return dict(row)
    return None

def save_food_log(user_id: int, meal_type: str, description: str, calories: float):
    today = user_today_str(user_id)
    db.execute('''
        INSERT INTO diet_log (user_id, date, meal_type, food_description, calories)
        VALUES (?, ?, ?, ?, ?)
    ''', (user_id, today, meal_type, description, calories))
    db.commit()

def get_today_calories(user_id: int) -> float:
    today = user_today_str(user_id)
    cursor = db.execute('SELECT SUM(calories) FROM diet_log WHERE user_id = ? AND date = ?', (user_id, today))
    row = cursor.fetchone()
    return row[0] if row[0] else 0.0

def get_today_food_log(user_id: int) -> list:
    today = user_today_str(user_id)
    cursor = db.execute('''
        SELECT meal_type, food_description, calories FROM diet_log
        WHERE user_id = ? AND date = ?
        ORDER BY timestamp
    ''', (user_id, today))
    return cursor.fetchall()

def save_weight_log(user_id: int, weight: float):
    today = user_today_str(user_id)
    db.execute('INSERT INTO weight_log (user_id, date, weight) VALUES (?, ?, ?)', (user_id, today, weight))
    db.commit()

def get_last_weight(user_id: int) -> Optional[float]:
    cursor = db.execute('SELECT weight FROM weight_log WHERE user_id = ? ORDER BY date DESC LIMIT 1', (user_id,))
    row = cursor.fetchone()
    return row[0] if row else None

def save_body_fat(user_id: int, body_fat: float):
    today = user_today_str(user_id)
    db.execute('INSERT INTO body_fat_log (user_id, date, body_fat) VALUES (?, ?, ?)', (user_id, today, body_fat))
    db.commit()

def add_my_food(user_id: int, name: str, calories: float):
    try:
        db.execute('INSERT INTO my_foods (user_id, name, calories) VALUES (?, ?, ?)', (user_id, name, calories))
        db.commit()
    except sqlite3.IntegrityError:
        pass

def get_my_foods(user_id: int) -> List[Tuple[str, float]]:
    cursor = db.execute('SELECT name, calories FROM my_foods WHERE user_id = ? ORDER BY name', (user_id,))
    return cursor.fetchall()

def save_last_ai_answer(user_id: int, answer: str):
    db.execute('UPDATE user_settings SET last_ai_answer = ? WHERE user_id = ?', (answer, user_id))
    db.commit()

def get_last_ai_answer(user_id: int) -> Optional[str]:
    cursor = db.execute('SELECT last_ai_answer FROM user_settings WHERE user_id = ?', (user_id,))
    row = cursor.fetchone()
    return row[0] if row else None

def calculate_bmr(weight: float, height: float, age: int, gender: str) -> float:
    if gender == 'мужской':
        return 10 * weight + 6.25 * height - 5 * age + 5
    else:
        return 10 * weight + 6.25 * height - 5 * age - 161

def calculate_tdee(bmr: float, activity_level: float) -> float:
    return bmr * activity_level

def calculate_daily_calories(tdee: float, goal_type: str, target_weight_change: float, target_days: int, gender: str) -> Tuple[float, str]:
    if goal_type == 'maintain':
        return tdee, "ok"
    total_energy = abs(target_weight_change) * 7700
    daily_adjustment = total_energy / target_days
    max_adjustment = 1000
    warning = "ok"
    if daily_adjustment > max_adjustment:
        daily_adjustment = max_adjustment
        warning = f"⚠️ Цель слишком амбициозна. Дефицит ограничен {max_adjustment} ккал/день. Для достижения цели потребуется больше времени."
    if goal_type == 'loss':
        calories = tdee - daily_adjustment
    else:
        calories = tdee + daily_adjustment
    min_calories = 1200 if gender == 'женский' else 1500
    if calories < min_calories:
        calories = min_calories
        warning = f"⚠️ Рассчитанная норма слишком низкая. Установлен безопасный минимум {min_calories} ккал/день. Рекомендуется пересмотреть цель."
    return calories, warning

# ============ ФУНКЦИИ ДЛЯ ЦЕЛЕЙ УПРАЖНЕНИЙ ============
def parse_reps_input(reps_input: str) -> Tuple[int, List[int]]:
    reps_input = reps_input.strip()
    if 'x' in reps_input.lower():
        parts = reps_input.lower().split('x')
        if len(parts) == 2:
            try:
                sets = int(parts[0])
                reps_per_set = int(parts[1])
                return sets, [reps_per_set] * sets
            except ValueError:
                pass
    if ' ' in reps_input:
        parts = reps_input.split()
        try:
            reps_list = [int(p) for p in parts]
            return len(reps_list), reps_list
        except ValueError:
            pass
    if ',' in reps_input:
        parts = reps_input.split(',')
        try:
            reps_list = [int(p.strip()) for p in parts]
            return len(reps_list), reps_list
        except ValueError:
            pass
    try:
        reps = int(reps_input)
        return 1, [reps]
    except ValueError:
        pass
    raise ValueError("Неверный формат")

def format_goal_button_text(exercise: dict) -> str:
    if exercise.get('ex_type') == 'strength':
        target_sets = exercise.get('target_sets')
        target_reps = exercise.get('target_reps')
        target_weight = exercise.get('target_weight')
        if target_sets and target_reps:
            return f"🎯 Цель достигнута ({target_sets}х{target_reps}{f' +{target_weight}кг' if target_weight else ''})"
    else:
        target_distance = exercise.get('target_distance')
        target_duration = exercise.get('target_duration')
        if target_distance and target_duration:
            return f"🎯 Цель достигнута ({target_distance}км / {target_duration}мин)"
    return None


# ============ ФУНКЦИИ ДЛЯ ЗАДАЧ ============
def get_tasks_for_today(user_id: int) -> list:
    today = user_today_str(user_id)
    today_wd = str(user_weekday(user_id))
    cursor = db.execute("""
        SELECT id, title, is_priority, deadline, repeat_days, is_done, done_date
        FROM tasks WHERE user_id = ?
    """, (user_id,))
    rows = cursor.fetchall()
    result = []
    for row in rows:
        task_id, title, is_priority, deadline, repeat_days, is_done, done_date = row
        if repeat_days:
            # Повторяющаяся: показываем если сегодня нужный день и не выполнена сегодня
            days = repeat_days.split(',')
            if today_wd not in days:
                continue
            if done_date == today:
                continue
        else:
            # Разовая: пропускаем если уже выполнена
            if is_done:
                continue
        result.append({
            'id': task_id, 'title': title, 'is_priority': bool(is_priority),
            'deadline': deadline, 'repeat_days': repeat_days,
            'is_done': bool(is_done), 'done_date': done_date
        })
    return result

def get_all_active_tasks(user_id: int) -> list:
    today = user_today_str(user_id)
    today_wd = str(user_weekday(user_id))
    cursor = db.execute("""
        SELECT id, title, is_priority, deadline, repeat_days, is_done, done_date
        FROM tasks WHERE user_id = ? ORDER BY is_priority DESC, deadline ASC NULLS LAST, id ASC
    """, (user_id,))
    rows = cursor.fetchall()
    result = []
    for row in rows:
        task_id, title, is_priority, deadline, repeat_days, is_done, done_date = row
        if repeat_days:
            days = repeat_days.split(',')
            done_today = (done_date == today)
            result.append({
                'id': task_id, 'title': title, 'is_priority': bool(is_priority),
                'deadline': deadline, 'repeat_days': repeat_days,
                'is_done': done_today, 'done_date': done_date
            })
        else:
            if is_done:
                continue
            result.append({
                'id': task_id, 'title': title, 'is_priority': bool(is_priority),
                'deadline': deadline, 'repeat_days': repeat_days,
                'is_done': False, 'done_date': done_date
            })
    return result

def get_urgent_tasks_for_menu(user_id: int) -> list:
    """Задачи для главного меню: приоритетные + дедлайн <= 3 дней."""
    today = user_today_date(user_id)
    tasks = get_tasks_for_today(user_id)
    urgent = []
    for t in tasks:
        days_left = None
        if t['deadline']:
            try:
                dl = datetime.strptime(t['deadline'], '%Y-%m-%d').date()
                days_left = (dl - today).days
            except:
                pass
        show = t['is_priority'] or (days_left is not None and days_left <= 3)
        if show:
            t['days_left'] = days_left
            urgent.append(t)
    return urgent[:5]

def complete_task(task_id: int, user_id: int):
    today = user_today_str(user_id)
    cursor = db.execute('SELECT repeat_days FROM tasks WHERE id = ? AND user_id = ?', (task_id, user_id))
    row = cursor.fetchone()
    if not row:
        return
    repeat_days = row[0]
    if repeat_days:
        db.execute('UPDATE tasks SET done_date = ? WHERE id = ? AND user_id = ?', (today, task_id, user_id))
    else:
        db.execute('UPDATE tasks SET is_done = 1, done_date = ? WHERE id = ? AND user_id = ?', (today, task_id, user_id))
    db.commit()

def delete_task(task_id: int, user_id: int):
    db.execute('DELETE FROM tasks WHERE id = ? AND user_id = ?', (task_id, user_id))
    db.commit()

def add_task(user_id: int, title: str, is_priority: bool, deadline: Optional[str], repeat_days: Optional[str]):
    db.execute("""
        INSERT INTO tasks (user_id, title, is_priority, deadline, repeat_days)
        VALUES (?, ?, ?, ?, ?)
    """, (user_id, title, int(is_priority), deadline, repeat_days))
    db.commit()

def days_left_str(deadline: str, user_id: Optional[int] = None) -> str:
    try:
        dl = datetime.strptime(deadline, '%Y-%m-%d').date()
        today = user_today_date(user_id) if user_id is not None else datetime.now().date()
        diff = (dl - today).days
        if diff < 0:
            return "просрочена!"
        elif diff == 0:
            return "сегодня!"
        elif diff == 1:
            return "завтра"
        else:
            return f"{diff} дн."
    except:
        return ""

WEEKDAY_NAMES = {0: "Пн", 1: "Вт", 2: "Ср", 3: "Чт", 4: "Пт", 5: "Сб", 6: "Вс"}

def format_repeat_days(repeat_days: str) -> str:
    try:
        days = [WEEKDAY_NAMES[int(d)] for d in repeat_days.split(',') if d.strip().isdigit()]
        return ", ".join(days)
    except:
        return ""


# ============ ФУНКЦИИ ДЛЯ ИИ-ПЛАНА ТРЕНИРОВОК ============
import json

WEEKDAY_RU = {0: "Понедельник", 1: "Вторник", 2: "Среда",
              3: "Четверг", 4: "Пятница", 5: "Суббота", 6: "Воскресенье"}
WEEKDAY_SHORT = {0: "Пн", 1: "Вт", 2: "Ср", 3: "Чт", 4: "Пт", 5: "Сб", 6: "Вс"}
WEEKDAY_KEY = {0: "monday", 1: "tuesday", 2: "wednesday",
               3: "thursday", 4: "friday", 5: "saturday", 6: "sunday"}
WEEKDAY_FROM_KEY = {v: k for k, v in WEEKDAY_KEY.items()}

def get_ai_plan(user_id: int) -> Optional[dict]:
    cursor = db.execute("SELECT * FROM ai_workout_plan WHERE user_id = ?", (user_id,))
    row = cursor.fetchone()
    if not row:
        return None
    plan = dict(row)
    plan["plan"] = json.loads(plan["plan_json"])
    return plan

def save_ai_plan(user_id: int, mode: str, goal: str, level: str,
                 days_per_week: int, plan: dict, cycle_weeks: int = 1):
    today = user_today_str(user_id)
    plan_json = json.dumps(plan, ensure_ascii=False)
    db.execute("""
        INSERT INTO ai_workout_plan (user_id, mode, goal, level, days_per_week, plan_json, cycle_weeks, start_date, last_monthly_review)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(user_id) DO UPDATE SET
            mode=excluded.mode, goal=excluded.goal, level=excluded.level,
            days_per_week=excluded.days_per_week, plan_json=excluded.plan_json,
            cycle_weeks=excluded.cycle_weeks,
            start_date=CASE WHEN ai_workout_plan.start_date IS NULL THEN excluded.start_date ELSE ai_workout_plan.start_date END
    """, (user_id, mode, goal, level, days_per_week, plan_json, cycle_weeks, today, today))
    db.commit()

def delete_all_workout_data(user_id: int):
    """Сбрасывает все данные тренировок пользователя."""
    db.execute("DELETE FROM ai_workout_plan WHERE user_id = ?", (user_id,))
    db.execute("DELETE FROM ai_workout_sessions WHERE user_id = ?", (user_id,))
    db.execute("DELETE FROM ai_exercise_logs WHERE user_id = ?", (user_id,))
    db.execute("DELETE FROM workout_log WHERE user_id = ?", (user_id,))
    db.execute("DELETE FROM exercises WHERE user_id = ?", (user_id,))
    db.execute("DELETE FROM exercise_categories WHERE user_id = ?", (user_id,))
    db.execute("UPDATE workouts SET current_count=0, today_count=0, last_workout_date=NULL WHERE user_id = ?", (user_id,))
    db.commit()

def get_current_week_session_key(plan_data: dict, start_date: str, user_id: Optional[int] = None) -> str:
    """Определяет какую неделю цикла использовать сегодня."""
    now_date = user_today_date(user_id) if user_id is not None else datetime.now().date()
    try:
        start = datetime.strptime(start_date, "%Y-%m-%d").date()
    except Exception:
        start = now_date
    today = now_date
    weeks_passed = max(0, (today - start).days // 7)
    # cycle_weeks может быть в plan_data или в вложенном plan
    plan = plan_data.get("plan", plan_data)
    cycle_weeks = plan_data.get("cycle_weeks", plan.get("cycle_weeks", 1)) or 1
    week_idx = (weeks_passed % cycle_weeks) + 1
    return f"week_{week_idx}"

def get_today_plan(plan_data: dict, user_id: Optional[int] = None) -> Optional[list]:
    """Возвращает список упражнений на сегодня (по времени пользователя) или None если день отдыха."""
    if not plan_data:
        return None
    plan = plan_data.get("plan")
    if not plan:
        return None
    now = user_now(user_id) if user_id is not None else datetime.now()
    start_date = plan_data.get("start_date") or now.strftime("%Y-%m-%d")
    week_key = get_current_week_session_key(plan_data, start_date, user_id)
    today_key = WEEKDAY_KEY[now.weekday()]
    week = plan.get(week_key) or plan.get("week_1") or {}
    exercises = week.get(today_key)
    if not exercises:
        return None
    if not isinstance(exercises, list) or len(exercises) == 0:
        return None
    return exercises

def get_today_session(user_id: int) -> Optional[dict]:
    today = user_today_str(user_id)
    cursor = db.execute(
        "SELECT * FROM ai_workout_sessions WHERE user_id = ? AND date = ?",
        (user_id, today)
    )
    row = cursor.fetchone()
    if not row:
        return None
    s = dict(row)
    s["plan"] = json.loads(s["plan_json"])
    return s

def create_today_session(user_id: int, plan_data: dict) -> Optional[dict]:
    """Создаёт сессию на сегодня если её нет."""
    existing = get_today_session(user_id)
    if existing:
        return existing
    today_exercises = get_today_plan(plan_data, user_id)
    if not today_exercises:
        return None
    today = user_today_str(user_id)
    weekday = user_weekday(user_id)
    start_date = plan_data.get("start_date") or today
    week_key = get_current_week_session_key(plan_data, start_date, user_id)
    today_key = WEEKDAY_KEY[weekday]
    session_key = f"{week_key}_{today_key}"
    plan_json = json.dumps(today_exercises, ensure_ascii=False)
    try:
        db.execute("""
            INSERT INTO ai_workout_sessions (user_id, date, weekday, session_key, plan_json, status)
            VALUES (?, ?, ?, ?, ?, 'pending')
        """, (user_id, today, weekday, session_key, plan_json))
        db.commit()
    except Exception as e:
        print(f"[SESSION] Insert error: {e}")
    return get_today_session(user_id)

def get_session_exercise_logs(session_id: int) -> list:
    cursor = db.execute(
        "SELECT * FROM ai_exercise_logs WHERE session_id = ? ORDER BY id",
        (session_id,)
    )
    rows = cursor.fetchall()
    result = []
    for row in rows:
        d = dict(row)
        if d.get("planned_json"):
            d["planned"] = json.loads(d["planned_json"])
        if d.get("result_json"):
            d["result"] = json.loads(d["result_json"])
        result.append(d)
    return result

def get_previous_same_session(user_id: int, session_key: str, exclude_date: str) -> Optional[dict]:
    """Возвращает предыдущую сессию того же типа (прошлая неделя, месяц назад, первая)."""
    cursor = db.execute("""
        SELECT * FROM ai_workout_sessions
        WHERE user_id = ? AND session_key LIKE ? AND date != ? AND status = 'done'
        ORDER BY date DESC LIMIT 3
    """, (user_id, f"%{session_key.split('_', 2)[-1]}", exclude_date))
    rows = cursor.fetchall()
    if not rows:
        return None
    sessions = []
    for row in rows:
        s = dict(row)
        s["plan"] = json.loads(s["plan_json"])
        s["logs"] = get_session_exercise_logs(s["id"])
        sessions.append(s)
    return sessions

def format_plan_for_display(exercises: list, prev_logs: list = None) -> str:
    """Форматирует план упражнений для показа пользователю."""
    lines = []
    prev_map = {}
    if prev_logs:
        for log in prev_logs:
            if log.get("result"):
                prev_map[log["exercise_name"]] = log["result"]

    for i, ex in enumerate(exercises, 1):
        name = ex.get("exercise", ex.get("name", "?"))
        sets = ex.get("sets", "?")
        reps = ex.get("reps", "?")
        weight = ex.get("weight")
        line = f"{i}. {name}  {sets}×{reps}"
        if weight:
            line += f" @ {weight}кг"
        lines.append(line)

    text = "\n".join(lines)

    # Прошлый раз — только важное
    if prev_logs:
        important = []
        for log in prev_logs:
            if log["status"] == "skipped":
                important.append(f"⏭ {log['exercise_name']} — пропущено")
            elif log.get("result") and log["result"].get("note"):
                important.append(f"⚠️ {log['exercise_name']} — {log['result']['note']}")
        if important:
            text += "\n\nПрошлый раз:\n" + "\n".join(important)

    return text

def format_exercise_card(exercise: dict, index: int, total: int, prev_result: dict = None) -> str:
    """Форматирует карточку одного упражнения."""
    name = exercise.get("exercise", exercise.get("name", "?"))
    sets = exercise.get("sets", "?")
    reps = exercise.get("reps", "?")
    weight = exercise.get("weight")

    text = f"Упражнение {index} из {total}\n\n"
    text += f"{name}\n"
    text += f"Цель: {sets} подхода × {reps} повторений"
    if weight:
        text += f" @ {weight} кг"

    if prev_result:
        text += "\n\nПрошлый раз: "
        if prev_result.get("sets_done"):
            text += f"{prev_result['sets_done']}×{prev_result.get('reps_done','?')}"
        if prev_result.get("weight_done"):
            text += f" @ {prev_result['weight_done']} кг"
        if prev_result.get("note"):
            text += f" ({prev_result['note']})"

    text += "\n\nНапиши что сделал или нажми кнопку:"
    return text


async def run_in_thread(func, *args, **kwargs):
    """Запускает синхронную функцию в пуле потоков, не блокируя event loop."""
    loop = asyncio.get_event_loop()
    import functools
    return await loop.run_in_executor(None, functools.partial(func, *args, **kwargs))

def _parse_json_response(text: str) -> Optional[dict]:
    """Надёжно извлекает JSON из ответа Gemini."""
    if not text:
        return None

    # Проверяем на явные ошибки
    if text.startswith("❌") or text.startswith("Error"):
        print(f"[JSON] Explicit error in response: {repr(text[:100])}")
        return None

    clean = text.strip()

    # Сначала пробуем найти JSON в markdown code block
    if "```" in clean:
        # Ищем блок ```json ... ``` или ``` ... ```
        match = re.search(r'```\s*(?:json)?\s*\n?(.*?)```', clean, re.DOTALL)
        if match:
            clean = match.group(1).strip()
        else:
            # Если не нашли парный блок, просто убираем все ```
            clean = clean.replace("```", "").strip()

    # Берём от первой { до последней } - это надёжный способ вырезать JSON
    start = clean.find("{")
    end = clean.rfind("}")
    if start == -1 or end == -1:
        print(f"[JSON] No braces found in: {repr(clean[:200])}")
        return None

    # Проверяем что { идёт перед }
    if start > end:
        print(f"[JSON] Invalid brace order: start={start}, end={end}")
        return None

    clean = clean[start:end+1]

    # Если JSON пустой или слишком короткий
    if len(clean) < 2:
        print(f"[JSON] Too short: {repr(clean)}")
        return None

    # Пытаемся распарсить
    try:
        return json.loads(clean)
    except json.JSONDecodeError as e:
        print(f"[JSON] Parse error: {e} | text: {repr(clean[:300])}")
        
        # Пробуем исправить частые проблемы
        # 1. Удаляем trailing commas
        clean_fixed = re.sub(r',\s*}', '}', clean)
        clean_fixed = re.sub(r',\s*]', ']', clean_fixed)
        try:
            result = json.loads(clean_fixed)
            print(f"[JSON] Fixed with trailing comma removal")
            return result
        except:
            pass
        
        # 2. Пробуем заменить одинарные кавычки на двойные
        try:
            clean_fixed = clean.replace("'", '"')
            result = json.loads(clean_fixed)
            print(f"[JSON] Fixed with single quote replacement")
            return result
        except:
            pass
        
        return None

def gemini_generate_plan(goal: str, level: str, days_per_week: int, notes: str = '') -> Optional[dict]:
    """Генерирует план тренировок через Gemini, возвращает dict."""
    day_keys = ["monday","tuesday","wednesday","thursday","friday","saturday","sunday"]
    # Выбираем нужные дни равномерно
    selected = day_keys[:days_per_week]
    days_example = {}
    for d in selected:
        days_example[d] = [
            {"exercise": "Упражнение 1", "sets": 3, "reps": "10", "weight": 50},
            {"exercise": "Упражнение 2", "sets": 3, "reps": "12", "weight": None}
        ]
    example = json.dumps({"cycle_weeks": 1, "week_1": days_example}, ensure_ascii=False, indent=2)

    prompt = (
        f"Ты фитнес-тренер. Создай план тренировок.\n"
        f"Цель: {goal}\nУровень: {level}\nТренировок в неделю: {days_per_week}\n\n"
        f"Верни ТОЛЬКО валидный JSON строго в этом формате (замени упражнения на реальные):\n"
        f"{example}\n\n"
        f"Правила:\n"
        f"- Используй ровно {days_per_week} дней из: monday tuesday wednesday thursday friday saturday sunday\n"
        f"- sets — целое число, reps — строка, weight — число или null\n"
        f"- Если нужны чередующиеся недели добавь week_2 и обнови cycle_weeks\n"
        f"- ТОЛЬКО JSON, никакого текста до или после\n"
        + (f"- Учти пожелания пользователя: {notes}\n" if notes else "")
    )

    result = gemini_generate_json(prompt, max_tokens=8192)
    print(f"[AI PLAN] Raw ({len(result)} chars): {repr(result[:300])}")
    return _parse_json_response(result)

def _fallback_parse_plan(raw_text: str) -> Optional[dict]:
    """Запасной разбор плана — максимально либеральный."""
    print(f"[FALLBACK] Parsing: {repr(raw_text[:200])}")
    prompt = (
        "Разбери этот план тренировок в JSON. Даже если формат нестандартный — сделай максимум.\n\n"
        "Структура: {\"cycle_weeks\": N, \"week_1\": {\"monday\": [...], ...}}\n"
        "Каждое упражнение: {\"exercise\": \"название\", \"sets\": 3, \"reps\": \"10\", \"weight\": 80}\n\n"
        "Правила:\n"
        "- Блоки 'Неделя 1/2/3' внутри дня → разные week_1/week_2/week_3, cycle_weeks = макс номер\n"
        "- '/' на отдельной строке = граница между неделями в рамках одного дня\n"
        "- Упражнения без метки недели → дублируй во все недели\n"
        "- МАХ(20кг) → максимальный вес на 1 повторение: sets:1, reps:'1', weight:20\n"
        "- '50 повторений' → sets:1, reps:'50', weight:null\n"
        "- '40 минут' → sets:1, reps:'40 мин', weight:null\n"
        "- Дроп-сет '2x(60-40)' → sets:2, reps:'до отказа', weight:60\n"
        "Только JSON:\n\n"
        f"{raw_text}"
    )
    result = gemini_generate_json(prompt, max_tokens=8192)
    print(f"[FALLBACK] Raw response: {repr(result[:500])}")
    parsed = _parse_json_response(result)
    if parsed:
        print(f"[FALLBACK] Success: cycle_weeks={parsed.get('cycle_weeks')}")
    else:
        print(f"[FALLBACK] Failed to parse")
    return parsed

def gemini_parse_manual_plan(raw_text: str) -> Optional[dict]:
    """Парсит ручной план пользователя через Gemini."""
    prompt = (
        "Ты — парсер планов тренировок. Разбери текст и верни ТОЛЬКО валидный JSON, без пояснений.\n\n"

        "=== СТРУКТУРА ВЫВОДА ===\n"
        "{\n"
        '  "cycle_weeks": N,\n'
        '  "week_1": { "monday": [...], "wednesday": [...], ... },\n'
        '  "week_2": { ... },\n'
        '  "week_3": { ... }\n'
        "}\n\n"
        "Каждое упражнение:\n"
        '{ "exercise": "название", "sets": 3, "reps": "5", "weight": 100 }\n\n'

        "=== ПРАВИЛА ЧЕРЕДОВАНИЯ ===\n"
        "Если внутри одного дня есть строки вида 'Неделя 1 - ...', 'Неделя 2 - ...' — это чередование.\n"
        "Каждый блок 'Неделя N' относится только к week_N этого дня.\n"
        "Строки БЕЗ метки 'Неделя N' (до первого блока или после последнего) — дублируй во ВСЕ недели этого дня.\n"
        "cycle_weeks = максимальный номер недели в тексте. Если меток нет — cycle_weeks:1.\n\n"

        "=== ФОРМАТЫ УПРАЖНЕНИЙ ===\n"
        "3x5(110кг)           → sets:3, reps:'5', weight:110\n"
        "3х11(90кг)           → sets:3, reps:'11', weight:90  (х — русская буква, то же что x)\n"
        "МАХ(120кг)           → sets:1, reps:'1', weight:120  (максимальный вес на 1 повторение)\n"
        "МАХ повторений(20кг) → sets:1, reps:'MAX', weight:20\n"
        "50 повторений        → sets:1, reps:'50', weight:null\n"
        "2x(от 60кг к 50кг)  → sets:2, reps:'до отказа', weight:60\n"
        "40 минут             → sets:1, reps:'40 мин', weight:null\n"
        "BIU / навык / skill  → sets:1, reps:'1', weight:null\n"
        "Без веса             → weight:null\n\n"

        "=== ДНИ НЕДЕЛИ ===\n"
        "Понедельник→monday, Вторник→tuesday, Среда→wednesday, Четверг→thursday,\n"
        "Пятница→friday, Суббота→saturday, Воскресенье→sunday\n"
        "Пометки типа 'PUSH', 'PULL', 'LEG' после названия дня — игнорируй.\n\n"

        "=== ПРИМЕР (3-недельный цикл) ===\n"
        "Вход:\n"
        "Понедельник:\n"
        "Неделя 1 - Жим лёжа - МАХ(120кг)\n"
        "Неделя 2 - Жим лёжа - 3x5(110кг)\n"
        "Неделя 3 - Жим на наклонной - 3x11(90кг)\n"
        "Разгибания трицепса - 3x12(40кг)\n\n"
        "→ 'Разгибания трицепса' идёт без метки недели — дублируется в week_1, week_2, week_3.\n\n"
        "Выход:\n"
        "{\n"
        '  "cycle_weeks": 3,\n'
        '  "week_1": {"monday": [\n'
        '    {"exercise": "Жим лёжа", "sets": 1, "reps": "1", "weight": 120},\n'
        '    {"exercise": "Разгибания трицепса", "sets": 3, "reps": "12", "weight": 40}\n'
        '  ]},\n'
        '  "week_2": {"monday": [\n'
        '    {"exercise": "Жим лёжа", "sets": 3, "reps": "5", "weight": 110},\n'
        '    {"exercise": "Разгибания трицепса", "sets": 3, "reps": "12", "weight": 40}\n'
        '  ]},\n'
        '  "week_3": {"monday": [\n'
        '    {"exercise": "Жим на наклонной", "sets": 3, "reps": "11", "weight": 90},\n'
        '    {"exercise": "Разгибания трицепса", "sets": 3, "reps": "12", "weight": 40}\n'
        '  ]}\n'
        "}\n\n"

        "=== ТЕКСТ ПОЛЬЗОВАТЕЛЯ ===\n"
        f"{raw_text}\n\n"
        "Верни ТОЛЬКО JSON:"
    )

    result = gemini_generate_json(prompt, max_tokens=8192)
    print(f"[MANUAL PLAN] Raw ({len(result)} chars): {repr(result[:500])}")
    parsed = _parse_json_response(result)
    if parsed:
        print(f"[MANUAL PLAN] Parsed OK: cycle_weeks={parsed.get('cycle_weeks')}, weeks={[k for k in parsed if k.startswith('week')]}")
        if 'week_1' not in parsed:
            print(f"[MANUAL PLAN] WARNING: No week_1 found in parsed result!")
    else:
        print(f"[MANUAL PLAN] Parse FAILED - Raw full: {repr(result)}")
    return parsed

def gemini_edit_plan(current_plan: dict, edit_request: str) -> Optional[dict]:
    """Редактирует план через Gemini по запросу пользователя."""
    prompt = (
        f"Текущий план тренировок (JSON):\n{json.dumps(current_plan, ensure_ascii=False)}\n\n"
        f"Запрос пользователя: {edit_request}\n\n"
        f"Внеси изменения и верни ТОЛЬКО обновлённый JSON без markdown и пояснений."
    )
    result = gemini_generate_json(prompt, max_tokens=8192)
    return _parse_json_response(result)

def gemini_parse_exercise_result(exercise: dict, raw_text: str) -> dict:
    """Разбирает текстовый ответ пользователя по одному упражнению."""
    name = exercise.get("exercise", exercise.get("name", "упражнение"))
    prompt = f"""Упражнение: {name}
План: {exercise.get("sets")} подходов × {exercise.get("reps")} повторений, вес {exercise.get("weight")} кг

Пользователь написал: "{raw_text}"

Верни ТОЛЬКО JSON:
{{
  "sets_done": 3,
  "reps_done": "10",
  "weight_done": 60,
  "completed": true,
  "note": "не добил последний подход"
}}

Правила:
- completed: true если выполнил хотя бы частично
- note: короткая заметка только если есть что-то важное, иначе null
- Только JSON"""

    result = gemini_generate(prompt, max_tokens=256, raw=True)
    try:
        clean = result.strip()
        if clean.startswith("```"):
            clean = re.sub(r"```[a-z]*\n?", "", clean).replace("```", "").strip()
        if not clean.startswith(("{","[")) and ("{" in clean or "[" in clean):
            for start in ("{","["):
                if start in clean:
                    end = "}" if start == "{" else "]"
                    if end in clean:
                        clean = clean[clean.index(start):clean.rindex(end)+1]
                        break
        return json.loads(clean)
    except:
        return {"sets_done": None, "reps_done": None, "weight_done": None,
                "completed": True, "note": raw_text[:100]}

def gemini_session_feedback(session_logs: list, plan_exercises: list) -> str:
    """Генерирует краткий фидбек по завершённой тренировке."""
    done = [l for l in session_logs if l["status"] == "done"]
    skipped = [l for l in session_logs if l["status"] == "skipped"]
    done_results = [l.get("result") if isinstance(l, dict) else None for l in done]
    skipped_names = [l["exercise_name"] for l in skipped]
    plan_json = json.dumps(plan_exercises, ensure_ascii=False)
    done_json = json.dumps(done_results, ensure_ascii=False)
    skipped_str = str(skipped_names)
    prompt = (
        "Пользователь завершил тренировку.\n"
        f"План: {plan_json}\n"
        f"Выполнено: {done_json}\n"
        f"Пропущено: {skipped_str}\n\n"
        "Напиши КРАТКИЙ фидбек (2-3 предложения). "
        "Только если есть прогресс — отметь. Если что-то пропущено — упомяни. Без воды."
    )
    return gemini_generate(prompt, max_tokens=300)

def gemini_adapt_next_session(plan_exercises: list, session_logs: list,
                               prev_sessions: list) -> list:
    """Адаптирует план следующей такой же тренировки на основе результатов."""
    logs_summary = [
        {
            "exercise": l["exercise_name"],
            "result": l.get("result"),
            "status": l["status"]
        }
        for l in session_logs
    ]
    plan_json = json.dumps(plan_exercises, ensure_ascii=False)
    logs_json = json.dumps(logs_summary, ensure_ascii=False)
    prompt = (
        "Ты тренер. Адаптируй план следующей тренировки на основе результатов.\n\n"
        f"Текущий план:\n{plan_json}\n\n"
        f"Результаты сегодня:\n{logs_json}\n\n"
        "Верни ТОЛЬКО JSON — обновлённый список упражнений (та же структура).\n"
        "Меняй только sets/reps/weight. Упражнения не меняй. Только JSON."
    )
    result = gemini_generate(prompt, max_tokens=1024, raw=True)
    parsed = _parse_json_response(result)
    if isinstance(parsed, list):
        return parsed
    # Если вернул dict с вложенным списком
    if isinstance(parsed, dict):
        for v in parsed.values():
            if isinstance(v, list):
                return v
    return plan_exercises

def gemini_monthly_review(plan: dict, recent_sessions: list) -> Optional[dict]:
    """Предлагает замену упражнений раз в месяц."""
    prompt = f"""Ты тренер. Проанализируй план тренировок и последние результаты.

Текущий план:
{json.dumps(plan, ensure_ascii=False)}

Последние тренировки (краткие результаты):
{json.dumps(recent_sessions[:10], ensure_ascii=False)}

Предложи замены упражнений если нужно. Верни ТОЛЬКО JSON:
{{
  "changes": [
    {{"day": "monday", "week": "week_1", "old_exercise": "Жим лёжа", "new_exercise": "Жим гантелей", "reason": "для разнообразия и проработки стабилизаторов"}},
  ],
  "no_changes_needed": false
}}

Если менять ничего не нужно — верни {{"changes": [], "no_changes_needed": true}}.
Только JSON."""

    result = gemini_generate(prompt, max_tokens=1024)
    try:
        clean = result.strip()
        if clean.startswith("```"):
            clean = re.sub(r"```[a-z]*\n?", "", clean).replace("```", "").strip()
        return json.loads(clean)
    except:
        return None

def apply_monthly_changes(user_id: int, plan_data: dict, accepted_indices: list, changes: list) -> dict:
    """Применяет принятые изменения к плану."""
    plan = plan_data["plan"].copy()
    for i in accepted_indices:
        if i >= len(changes):
            continue
        ch = changes[i]
        week = plan.get(ch["week"], {})
        day = week.get(ch["day"], [])
        for ex in day:
            if ex.get("exercise") == ch["old_exercise"]:
                ex["exercise"] = ch["new_exercise"]
    return plan

def update_plan_json(user_id: int, new_plan: dict):
    plan_json = json.dumps(new_plan, ensure_ascii=False)
    db.execute("UPDATE ai_workout_plan SET plan_json = ? WHERE user_id = ?",
               (plan_json, user_id))
    db.commit()

def update_session_exercise_plan(user_id: int, session_id: int,
                                  session_key: str, new_exercises: list):
    """Обновляет план упражнений в текущей и будущей сессии."""
    plan_json = json.dumps(new_exercises, ensure_ascii=False)
    db.execute("UPDATE ai_workout_sessions SET plan_json = ? WHERE id = ?",
               (plan_json, session_id))
    # Обновляем и в основном плане для будущих сессий
    plan_data = get_ai_plan(user_id)
    if plan_data:
        plan = plan_data["plan"]
        parts = session_key.split("_", 2)  # week_1_monday
        if len(parts) >= 3:
            week_key = f"{parts[0]}_{parts[1]}"
            day_key = parts[2]
            if week_key in plan and day_key in plan[week_key]:
                plan[week_key][day_key] = new_exercises
                update_plan_json(user_id, plan)
    db.commit()

def get_next_training_day(plan_data: dict, user_id: Optional[int] = None) -> Optional[str]:
    """Возвращает дату и название следующей тренировки."""
    plan = plan_data["plan"]
    start_date = plan_data["start_date"]
    today = user_today_date(user_id) if user_id is not None else datetime.now().date()
    today_weekday = today.weekday()

    for offset in range(1, 8):
        check_date = today + timedelta(days=offset)
        check_weekday = check_date.weekday()
        check_wd_key = WEEKDAY_KEY[check_weekday]
        weeks_passed = (check_date - datetime.strptime(start_date, "%Y-%m-%d").date()).days // 7
        cycle_weeks = plan_data.get("cycle_weeks", 1)
        week_idx = (weeks_passed % cycle_weeks) + 1
        week_key = f"week_{week_idx}"
        week = plan.get(week_key, plan.get("week_1", {}))
        if week.get(check_wd_key):
            return check_date.strftime("%d.%m"), WEEKDAY_RU[check_weekday]
    return None, None

def get_weekly_workout_progress(user_id: int) -> tuple:
    """Возвращает (выполнено, план) тренировок за текущую неделю."""
    plan_data = get_ai_plan(user_id)
    days_per_week = plan_data['days_per_week'] if plan_data else 0
    # Считаем начало недели (понедельник)
    today = user_today_date(user_id)
    week_start = today - timedelta(days=today.weekday())
    week_start_str = week_start.strftime('%Y-%m-%d')
    cursor = db.execute(
        "SELECT COUNT(*) FROM ai_workout_sessions WHERE user_id = ? AND date >= ? AND status = 'done'",
        (user_id, week_start_str)
    )
    row = cursor.fetchone()
    done = row[0] if row else 0
    return done, days_per_week

# ============ ИНИЦИАЛИЗАЦИЯ БАЗЫ ДАННЫХ ============
def init_db():
    db.execute('''
        CREATE TABLE IF NOT EXISTS ratings (
            user_id INTEGER,
            category TEXT,
            rating INTEGER,
            day_date TEXT,
            PRIMARY KEY (user_id, category, day_date)
        )
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS workouts (
            user_id INTEGER PRIMARY KEY,
            monthly_goal INTEGER DEFAULT 0,
            current_count INTEGER DEFAULT 0,
            last_workout_date TEXT,
            today_count INTEGER DEFAULT 0
        )
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS user_ranks (
            user_id INTEGER PRIMARY KEY,
            total_sparks INTEGER DEFAULT 0,
            current_rank INTEGER DEFAULT 1,
            last_spark_date TEXT,
            sparks_today INTEGER DEFAULT 0,
            categories_completed_today INTEGER DEFAULT 0,
            workout_completed_today INTEGER DEFAULT 0
        )
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS user_settings (
            user_id INTEGER PRIMARY KEY,
            username TEXT,
            first_name TEXT,
            notification_enabled INTEGER DEFAULT 1,
            streak_days INTEGER DEFAULT 0,
            last_active_date TEXT,
            last_ai_answer TEXT DEFAULT NULL,
            timezone TEXT DEFAULT NULL
        )
    ''')
    cursor = db.execute("PRAGMA table_info(user_settings)")
    columns = [col[1] for col in cursor.fetchall()]
    if 'last_ai_answer' not in columns:
        db.execute("ALTER TABLE user_settings ADD COLUMN last_ai_answer TEXT DEFAULT NULL")
    if 'timezone' not in columns:
        db.execute("ALTER TABLE user_settings ADD COLUMN timezone TEXT DEFAULT NULL")
    db.execute("UPDATE user_settings SET notification_enabled = 1 WHERE notification_enabled IS NULL")
    db.execute('''
        CREATE TABLE IF NOT EXISTS diet_profile (
            user_id INTEGER PRIMARY KEY,
            weight REAL,
            height REAL,
            age INTEGER,
            gender TEXT,
            activity_level REAL,
            goal_type TEXT,
            target_weight_change REAL,
            target_days INTEGER,
            daily_calories REAL,
            last_update_date TEXT
        )
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS diet_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER,
            date TEXT,
            meal_type TEXT,
            food_description TEXT,
            calories REAL,
            timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
        )
    ''')
    cursor = db.execute("PRAGMA table_info(diet_log)")
    columns = [col[1] for col in cursor.fetchall()]
    if 'meal_type' not in columns:
        db.execute("ALTER TABLE diet_log ADD COLUMN meal_type TEXT DEFAULT 'Еда'")
    db.execute('''
        CREATE TABLE IF NOT EXISTS exercise_categories (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            name TEXT NOT NULL,
            ex_type TEXT NOT NULL DEFAULT 'strength',
            UNIQUE(user_id, name)
        )
    ''')
    cursor = db.execute("PRAGMA table_info(exercise_categories)")
    columns = [col[1] for col in cursor.fetchall()]
    if 'ex_type' not in columns:
        db.execute("ALTER TABLE exercise_categories ADD COLUMN ex_type TEXT NOT NULL DEFAULT 'strength'")
    db.execute('''
        CREATE TABLE IF NOT EXISTS exercises (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            category_id INTEGER NOT NULL,
            name TEXT NOT NULL,
            target_sets INTEGER,
            target_reps TEXT,
            target_weight REAL,
            target_distance REAL,
            target_duration INTEGER,
            weight_increment REAL,
            last_achieved_date TEXT,
            FOREIGN KEY(category_id) REFERENCES exercise_categories(id) ON DELETE CASCADE,
            UNIQUE(user_id, category_id, name)
        )
    ''')
    cursor = db.execute("PRAGMA table_info(exercises)")
    existing_columns = [col[1] for col in cursor.fetchall()]
    columns_to_add = [
        ('target_sets', 'INTEGER'),
        ('target_reps', 'TEXT'),
        ('target_weight', 'REAL'),
        ('target_distance', 'REAL'),
        ('target_duration', 'INTEGER'),
        ('weight_increment', 'REAL'),
        ('last_achieved_date', 'TEXT')
    ]
    for col_name, col_type in columns_to_add:
        if col_name not in existing_columns:
            db.execute(f"ALTER TABLE exercises ADD COLUMN {col_name} {col_type}")
    db.execute('''
        CREATE TABLE IF NOT EXISTS workout_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            date TEXT NOT NULL,
            category_id INTEGER,
            exercise_name TEXT NOT NULL,
            sets INTEGER,
            reps TEXT,
            weight REAL,
            distance REAL,
            duration INTEGER,
            FOREIGN KEY(category_id) REFERENCES exercise_categories(id) ON DELETE SET NULL
        )
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS weight_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            date TEXT NOT NULL,
            weight REAL NOT NULL
        )
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS body_fat_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            date TEXT NOT NULL,
            body_fat REAL NOT NULL
        )
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS my_foods (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            name TEXT NOT NULL,
            calories REAL NOT NULL,
            UNIQUE(user_id, name)
        )
    ''')
    # Таблицы для умных напоминаний
    db.execute('''
        CREATE TABLE IF NOT EXISTS reminders (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            text TEXT NOT NULL,
            remind_time TEXT NOT NULL,
            recurring TEXT,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        )
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS workout_plans (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            name TEXT NOT NULL,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        )
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS plan_exercises (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            plan_id INTEGER NOT NULL,
            exercise_id INTEGER NOT NULL,
            sets INTEGER,
            reps TEXT,
            weight REAL,
            distance REAL,
            duration INTEGER,
            day_of_week INTEGER,
            FOREIGN KEY(plan_id) REFERENCES workout_plans(id) ON DELETE CASCADE,
            FOREIGN KEY(exercise_id) REFERENCES exercises(id) ON DELETE CASCADE
        )
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS tasks (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            title TEXT NOT NULL,
            is_priority INTEGER DEFAULT 0,
            deadline TEXT,
            repeat_days TEXT,
            is_done INTEGER DEFAULT 0,
            done_date TEXT,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        )
    ''')
    # Таблицы для новой системы тренировок с ИИ
    db.execute('''
        CREATE TABLE IF NOT EXISTS ai_workout_plan (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL UNIQUE,
            mode TEXT NOT NULL DEFAULT 'ai',
            goal TEXT,
            level TEXT,
            days_per_week INTEGER,
            plan_json TEXT NOT NULL,
            cycle_weeks INTEGER DEFAULT 1,
            start_date TEXT,
            last_monthly_review TEXT,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        )
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS ai_workout_sessions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL,
            date TEXT NOT NULL,
            weekday INTEGER NOT NULL,
            session_key TEXT NOT NULL,
            plan_json TEXT NOT NULL,
            status TEXT DEFAULT 'pending',
            skip_reason TEXT,
            feedback TEXT,
            completed_at TEXT
        )
    ''')
    db.execute('''
        CREATE TABLE IF NOT EXISTS ai_exercise_logs (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            session_id INTEGER NOT NULL,
            user_id INTEGER NOT NULL,
            exercise_name TEXT NOT NULL,
            planned_json TEXT,
            raw_input TEXT,
            result_json TEXT,
            status TEXT DEFAULT 'pending',
            FOREIGN KEY(session_id) REFERENCES ai_workout_sessions(id) ON DELETE CASCADE
        )
    ''')
    db.commit()
    
# ============ КЛАВИАТУРЫ ============
def main_menu_keyboard():
    keyboard = ReplyKeyboardMarkup(
        keyboard=[
            [KeyboardButton(text="📒 Рефлексия"), KeyboardButton(text="⭐ Ранг")],
            [KeyboardButton(text="🏋️ Тренировки"), KeyboardButton(text="Check AI")],
            [KeyboardButton(text="🍽 Диета"), KeyboardButton(text="📝 Задачи")]
        ],
        resize_keyboard=True,
        one_time_keyboard=False
    )
    return keyboard
    
def reflection_keyboard():
    keyboard = ReplyKeyboardMarkup(
        keyboard=[
            [KeyboardButton(text="😴 Сон"), KeyboardButton(text="🎮 Зависание")],
            [KeyboardButton(text="🎯 Настрой")],
            [KeyboardButton(text="🔙 Назад")]
        ],
        resize_keyboard=True,
        one_time_keyboard=False
    )
    return keyboard

def rating_keyboard():
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=str(i), callback_data=f"rate:{i}") for i in range(1, 6)],
        [InlineKeyboardButton(text=str(i), callback_data=f"rate:{i}") for i in range(6, 11)]
    ])
    return keyboard

def ai_reply_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💡 Дай мне совет", callback_data="ai_advice")],
        [InlineKeyboardButton(text="🔙 Назад в меню", callback_data="back_to_main")]
    ])

def low_rating_keyboard(category: str):
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🤖 Разобрать с ИИ", callback_data=f"analyze_low:{category}")],
        [InlineKeyboardButton(text="🔙 Пропустить", callback_data="skip_analysis")]
    ])
    return keyboard

def retry_ai_keyboard(action: str):
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔄 Попробовать еще раз", callback_data=f"retry_ai:{action}")]
    ])

@router.callback_query(F.data.startswith("retry_ai:"))
async def retry_ai_action(callback: CallbackQuery, bot: Bot, state: FSMContext):
    action = callback.data.split(":", 1)[1]
    data = await state.get_data()
    if action == "mood":
        await state.set_state(RatingState.waiting_for_mood_text)
        await _retry_mood_rating(callback, bot, state)
    elif action == "ai_advice":
        await _retry_ai_advice(callback, bot, state)
    elif action == "ai_question":
        await _retry_ai_question(callback, bot, state)
    elif action == "generate_plan":
        await _retry_generate_plan(callback, bot, state)
    elif action == "low_rating":
        await _retry_low_rating(callback, bot, state)
    elif action == "food_calories":
        await _retry_food_calories(callback, bot, state)
    elif action == "food_photo":
        await _retry_food_photo(callback, bot, state)
    elif action == "photo_analysis":
        await _retry_photo_analysis(callback, bot, state)
    elif action == "manual_plan":
        await _retry_manual_plan(callback, bot, state)
    elif action == "monthly_review":
        await _retry_monthly_review(callback, bot, state)
    elif action == "session_feedback":
        await _retry_session_feedback(callback, bot, state)
    await callback.answer()

async def _retry_mood_rating(callback, bot, state):
    data = await state.get_data()
    description = data.get("retry_mood_description", "")
    user_id = callback.from_user.id
    name = get_user_name(user_id, callback.from_user.first_name)
    full_context = get_full_context_for_ai(user_id)
    prompt = f"""Ты — заботливый персональный трекер-ассистент. Пользователя зовут {name}.
Он(а) описал(а) свой сегодняшний день и настроение так: "{description}"

Вот что ты ещё знаешь о нём(ней) за последнее время:
{full_context}

Оцени его(её) настроение сегодня по шкале от 1 до 10 (10 — отличное настроение, 1 — очень плохое).
Затем напиши короткий (2-4 предложения) тёплый отклик по-русски, обращаясь по имени:
- если настроение хорошее — искренне порадуйся вместе с ним(ней);
- если настроение так себе или плохое — мягко поддержи и дай 1-2 конкретных совета,
  как можно улучшить состояние или разобраться с тяжёлыми эмоциями, учитывая контекст выше.
Ответь СТРОГО в формате JSON без пояснений и без markdown:
{{"rating": <целое число 1-10>, "response": "<текст отклика>"}}"""
    result = await run_in_thread(gemini_generate_rating, prompt)
    if not result:
        await callback.message.edit_text(
            "❌ ИИ не ответил. Попробуй ещё раз.",
            reply_markup=retry_ai_keyboard("mood")
        )
        return
    today = user_today_str(user_id)
    rating = result['rating']
    save_rating(user_id, 'настрой', rating, today)
    reply_text = f"🎯 Настрой: {rating}/10\n\n{result.get('response') or result.get('comment', '')}"
    await callback.message.edit_text(reply_text, reply_markup=reflection_keyboard())
    await state.clear()
    all_completed = check_all_categories_completed(user_id)
    if all_completed:
        success, sparks_today, rank_up, old_rank, new_rank = add_spark(user_id, 'categories')
        update_streak(user_id)
        await send_main_menu(bot, callback.from_user.id, callback.message.chat.id)
    else:
        await show_reflection_menu(user_id, callback.message.chat.id, bot, state, callback.from_user.first_name)

async def _retry_ai_advice(callback, bot, state):
    data = await state.get_data()
    user_id = callback.from_user.id
    name = get_user_name(user_id, callback.from_user.first_name)
    full_context = get_full_context_for_ai(user_id)
    prompt = data.get("retry_ai_prompt", "")
    try:
        answer = await run_in_thread(gemini_generate, prompt, 8192)
    except:
        answer = "❌ Ошибка ИИ."
    if answer.startswith("❌"):
        await callback.message.edit_text(
            f"❌ ИИ не ответил. Попробуй ещё раз.",
            reply_markup=retry_ai_keyboard("ai_advice")
        )
        return
    await callback.message.edit_text(
        f"💡 <b>Совет:</b>\n\n{answer}",
        parse_mode="HTML", reply_markup=ai_reply_keyboard()
    )
    save_last_ai_answer(user_id, answer)

async def _retry_ai_question(callback, bot, state):
    data = await state.get_data()
    user_id = callback.from_user.id
    name = get_user_name(user_id, callback.from_user.first_name)
    full_context = get_full_context_for_ai(user_id)
    question = data.get("retry_ai_question", "")
    prompt = f"""Ты — персональный трекер-ассистент. Пользователь {name}.

Вот свежие данные пользователя:
{full_context}

Вопрос: {question}
Ответь кратко, конкретно, с эмодзи, обращайся по имени."""
    try:
        answer = await run_in_thread(gemini_generate, prompt, 8192)
    except:
        answer = "❌ Ошибка ИИ."
    if answer.startswith("❌"):
        await callback.message.edit_text(
            f"❌ ИИ не ответил. Попробуй ещё раз.",
            reply_markup=retry_ai_keyboard("ai_question")
        )
        return
    await callback.message.edit_text(
        f"🤖 <b>Check AI:</b>\n\n{answer}",
        parse_mode="HTML", reply_markup=ai_reply_keyboard()
    )
    save_last_ai_answer(user_id, answer)

async def _retry_generate_plan(callback, bot, state):
    data = await state.get_data()
    user_id = callback.from_user.id
    goal = data.get("wp_goal", "Общая форма")
    level = data.get("wp_level", "Средний")
    days = data.get("wp_days", 3)
    notes = data.get("wp_notes", "")
    await state.set_state(AIPlanState.reviewing_plan)
    phrases = ["Анализирую...", "Ищу пишущую ручку...", "Составляю программу...",
               "Подбираю упражнения...", "Рассчитываю нагрузку...", "Финальные штрихи..."]
    temps = user_temp_messages.get(user_id, {})
    msg_id = temps.get("workout_menu")
    stop_animation = asyncio.Event()
    async def animate():
        i = 0
        while not stop_animation.is_set():
            try:
                await bot.edit_message_text(phrases[i % len(phrases)],
                                             callback.message.chat.id, msg_id)
            except:
                pass
            await asyncio.sleep(2)
            i += 1
    anim_task = asyncio.create_task(animate())
    try:
        plan = await run_in_thread(gemini_generate_plan, goal, level, days, notes)
    finally:
        stop_animation.set()
        anim_task.cancel()
        try:
            await anim_task
        except asyncio.CancelledError:
            pass
    if not plan:
        await callback.message.edit_text(
            "Не удалось сгенерировать план. Попробуй ещё раз.",
            reply_markup=retry_ai_keyboard("generate_plan")
        )
        return
    await state.update_data(wp_plan=plan)
    text = _format_full_plan(plan, goal, level, days)
    await callback.message.edit_text(text, reply_markup=wp_plan_review_keyboard())

async def _retry_low_rating(callback, bot, state):
    data = await state.get_data()
    category = data.get("retry_low_rating_category", "")
    rating = data.get("retry_low_rating_value", 0)
    user_id = callback.from_user.id
    await bot.send_chat_action(callback.message.chat.id, action=ChatAction.TYPING)
    analysis = await run_in_thread(analyze_low_rating, user_id, category, rating)
    if analysis.startswith("❌"):
        # ИИ снова не ответил — оставляем ту же кнопку повтора
        await callback.message.edit_text(
            "❌ ИИ не ответил. Нажми кнопку чтобы попробовать ещё раз.",
            reply_markup=retry_ai_keyboard("low_rating")
        )
        return
    msg = await callback.message.answer(f"🤖 {analysis}", reply_markup=ai_reply_keyboard())
    save_last_ai_answer(user_id, analysis)

async def _retry_food_calories(callback, bot, state):
    data = await state.get_data()
    description = data.get("retry_food_description", "")
    user_id = callback.from_user.id
    prompt = f"""Ты — точный счётчик калорий. Пользователь описывает что он съел (на русском или английском языке).

Твоя задача: посчитать ОБЩЕЕ количество ккал во всём описанном количестве еды.

ПРАВИЛА:
- Если указано количество (2 бургера, 3 яйца, 200г) — умножай соответственно
- Если количество не указано — считай стандартную порцию (тарелка супа ~300мл, второе блюдо ~300-400г, бутерброд ~150г)
- Учитывай ВСЕ компоненты: хлеб, масло, соусы, напитки, гарнир
- Не занижай: реальная еда жирнее и калорийнее чем кажется
- Минимум для полноценного приёма пищи (обед/ужин): 350 ккал
- Перекус может быть 100-300 ккал

Ориентиры (на порцию):
гречка с курицей = 450, паста карбонара = 680, бургер = 550, пицца (2 куска) = 600,
борщ = 300, салат цезарь с курицей = 520, омлет 2 яйца = 200, овсянка на молоке = 280,
рис с мясом = 500, шаурма = 650, хинкали 5шт = 400, суши-сет 8шт = 480,
протеиновый коктейль = 150, кофе с молоком = 60, яблоко = 80, банан = 100

Еда: {description}

Ответь СТРОГО одним целым числом — суммарные килокалории. Никаких слов, никаких единиц:"""
    await bot.send_chat_action(callback.message.chat.id, action=ChatAction.TYPING)
    response = await run_in_thread(gemini_generate, prompt, 100, True)
    try:
        numbers = re.findall(r"\b(\d{2,5})\b", response)
        numbers = [float(n) for n in numbers if 50 <= float(n) <= 9999]
        calories = numbers[-1] if numbers else None
    except:
        calories = None
    if calories is None or calories <= 0:
        # ИИ снова не смог — оставляем кнопку повтора, не заставляя вводить руками
        await callback.message.edit_text(
            f"❌ Не удалось определить калории для «{description}». "
            "Нажми кнопку чтобы попробовать ещё раз.",
            reply_markup=retry_ai_keyboard("food_calories")
        )
        return
    await state.update_data(food_description=description, food_calories=calories)
    await state.set_state(DietState.food_confirm)
    await callback.message.edit_text(
        f"🍽 Ты съел: {description}\n🔢 Калории: {int(calories)} ккал\n\nВсё верно?",
        reply_markup=diet_confirm_food_keyboard()
    )

async def _retry_photo_analysis(callback, bot, state):
    data = await state.get_data()
    user_id = callback.from_user.id
    chat_id = callback.message.chat.id
    image_bytes = data.get("retry_photo_bytes")
    prompt = data.get("retry_photo_prompt", """Кратко проанализируй телосложение на фото. Формат ответа:
• Сильные стороны (1-2 предложения)
• Слабые стороны (1-2 предложения)
• Рекомендации (2-3 конкретных совета)
Без воды, по делу, макс 150 слов.""")
    image_part = types.Part.from_bytes(data=image_bytes, mime_type='image/png')
    try:
        client = genai.Client(api_key=os.environ.get("GOOGLE_API_KEY") or os.environ.get("GEMINI_API_KEY"))
        response = await run_in_thread(
            client.models.generate_content,
            model='gemini-3.6-flash',
            contents=[prompt, image_part],
            config=types.GenerateContentConfig(max_output_tokens=2048)
        )
        text = getattr(response, 'text', None)
        analysis = text.strip() if text else (response.candidates[0].content.parts[0].text if response.candidates and response.candidates[0].content.parts else "❌ Нет ответа")
    except Exception as e:
        analysis = f"❌ Ошибка: {str(e)[:100]}"
    if analysis.startswith("❌"):
        await callback.message.edit_text(
            analysis + "\n\n🔄 Нажми кнопку чтобы попробовать ещё раз.",
            reply_markup=retry_ai_keyboard("photo_analysis")
        )
        return
    await callback.message.edit_text(analysis, reply_markup=photo_analysis_back_keyboard())
    temps = user_temp_messages.get(user_id, {})
    temps['photo_analysis_result'] = callback.message.message_id
    user_temp_messages[user_id] = temps
    await state.clear()

async def _retry_food_photo(callback, bot, state):
    """Повторный анализ того же фото блюда без повторной загрузки."""
    data = await state.get_data()
    user_id = callback.from_user.id
    image_bytes = data.get("retry_food_photo_bytes")
    prompt = data.get("retry_food_photo_prompt")
    if not image_bytes or not prompt:
        await callback.message.edit_text(
            "❌ Фото больше не доступно. Отправь его заново."
        )
        return
    await bot.send_chat_action(callback.message.chat.id, action=ChatAction.TYPING)
    text = await run_in_thread(analyze_food_photo, image_bytes, prompt)
    if text is None:
        await callback.message.edit_text(
            "❌ Ошибка анализа фото.\n\n🔄 Нажми кнопку чтобы попробовать ещё раз.",
            reply_markup=retry_ai_keyboard("food_photo")
        )
        return
    description = "Блюдо на фото"
    calories = None
    nums = re.findall(r"\b(\d{2,5})\b", text)
    valid_nums = [float(n) for n in nums if 50 <= float(n) <= 9999]
    if valid_nums:
        calories = valid_nums[-1]
    match = re.search(r"^([^0-9]+?)(?:\s*\d|$)", text)
    if match:
        desc = match.group(1).strip(" .,;:-")
        if 2 <= len(desc) <= 50:
            description = desc
    if calories is None or calories <= 0 or calories > 5000:
        await callback.message.edit_text(
            f"🍽 Определено: {description}\n"
            "❌ Не удалось оценить калории.\n\n"
            "🔄 Нажми кнопку чтобы попробовать ещё раз.",
            reply_markup=retry_ai_keyboard("food_photo")
        )
        return
    await state.update_data(food_description=description, food_calories=calories)
    await state.set_state(DietState.food_confirm)
    await callback.message.edit_text(
        f"🍽 Ты съел: {description}\n🔢 Калории: ~{int(calories)} ккал\n\nВсё верно?",
        reply_markup=diet_confirm_food_keyboard()
    )

async def _retry_manual_plan(callback, bot, state):
    """Повторный разбор того же текста плана без повторного ввода."""
    data = await state.get_data()
    user_id = callback.from_user.id
    raw_text = data.get("retry_manual_plan_text", "")
    if not raw_text:
        await callback.message.edit_text(
            "❌ Текст плана не сохранился. Введи его заново.",
            reply_markup=wp_edit_keyboard()
        )
        return
    await state.set_state(AIPlanState.reviewing_plan)
    temps = user_temp_messages.get(user_id, {})
    # Кнопка повтора живёт на сообщении об ошибке — его и редактируем
    msg_id = callback.message.message_id
    temps['workout_menu'] = msg_id
    user_temp_messages[user_id] = temps
    stop_anim = asyncio.Event()
    phrases_m = ["Читаю план...", "Разбираю структуру...", "Определяю дни...",
                 "Считаю подходы...", "Почти готово..."]

    async def animate_m():
        i = 0
        while not stop_anim.is_set():
            try:
                await bot.edit_message_text(phrases_m[i % len(phrases_m)],
                                            callback.message.chat.id, msg_id)
            except:
                pass
            await asyncio.sleep(2)
            i += 1
    anim_m = asyncio.create_task(animate_m())
    try:
        plan = await run_in_thread(gemini_parse_manual_plan, raw_text)
    finally:
        stop_anim.set()
        anim_m.cancel()
        try:
            await anim_m
        except asyncio.CancelledError:
            pass
    if not plan:
        plan = await run_in_thread(_fallback_parse_plan, raw_text)
    if not plan:
        # Возвращаемся в режим ввода — можно и нажать повторно, и переописать план
        await state.set_state(AIPlanState.entering_manual_plan)
        await callback.message.edit_text(
            "❌ Не смог разобрать план.\n\n🔄 Нажми кнопку чтобы попробовать ещё раз.",
            reply_markup=retry_ai_keyboard("manual_plan")
        )
        return
    await state.update_data(wp_plan=plan, wp_mode="manual",
                            wp_goal="", wp_level="", wp_days=0)
    text = _format_full_plan(plan, "", "", 0)
    try:
        await bot.edit_message_text(text, callback.message.chat.id, msg_id,
                                    reply_markup=wp_plan_review_keyboard_manual())
    except:
        new_msg = await callback.message.answer(text,
                                                reply_markup=wp_plan_review_keyboard_manual())
        temps['workout_menu'] = new_msg.message_id
        user_temp_messages[user_id] = temps

async def _retry_monthly_review(callback, bot, state):
    """Повторный запуск месячного пересмотра упражнений."""
    user_id = callback.from_user.id
    plan_data = get_ai_plan(user_id)
    if not plan_data:
        await callback.answer("Нет плана", show_alert=True)
        return
    await bot.send_chat_action(callback.message.chat.id, action=ChatAction.TYPING)
    await callback.message.edit_text("Анализирую прогресс...")
    cursor = db.execute("""
        SELECT date, plan_json, status FROM ai_workout_sessions
        WHERE user_id = ? ORDER BY date DESC LIMIT 20
    """, (user_id,))
    recent = [{"date": row[0], "status": row[2]} for row in cursor.fetchall()]
    changes = await run_in_thread(gemini_monthly_review, plan_data["plan"], recent)
    if not changes:
        await callback.message.edit_text(
            "❌ Не удалось проанализировать прогресс.\n\n"
            "🔄 Нажми кнопку чтобы попробовать ещё раз.",
            reply_markup=retry_ai_keyboard("monthly_review")
        )
        return
    if changes.get("no_changes_needed") or not changes.get("changes"):
        await callback.message.edit_text(
            "Менять ничего не нужно — план хорошо сбалансирован.",
            reply_markup=wp_settings_keyboard()
        )
        return
    chg = changes["changes"]
    await state.set_state(WorkoutSessionState.monthly_review)
    await state.update_data(review_changes=chg)
    lines = ["Предлагаю заменить упражнения:\n"]
    for i, ch in enumerate(chg, 1):
        lines.append(f"{i}. {ch['old_exercise']} → {ch['new_exercise']}\n   {ch['reason']}")
    lines.append("\nНапиши номера изменений которые принять (например: 1 3) или «нет» чтобы отклонить всё:")
    await callback.message.edit_text("\n".join(lines),
                                      reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                                          [InlineKeyboardButton(text="🔙 Назад",
                                                                 callback_data="wp_review_decline")]
                                      ]))

def workout_main_reply_keyboard():
    return ReplyKeyboardMarkup(
        keyboard=[
            [KeyboardButton(text="🏋️ Добавить выполнение"), KeyboardButton(text="🤳 Анализ фото")],
            [KeyboardButton(text="📋 Управление"), KeyboardButton(text="📊 История")],
            [KeyboardButton(text="🔙 Назад в меню")]
        ],
        resize_keyboard=True, one_time_keyboard=False
    )

def workout_manage_reply_keyboard(mode: str = "ai"):
    """Клавиатура управления планом."""
    if mode == "ai":
        return ReplyKeyboardMarkup(
            keyboard=[
                [KeyboardButton(text="🆕 Новый план (ИИ)"), KeyboardButton(text="✏️ Редактировать план (ИИ)")],
                [KeyboardButton(text="📝 Загрузить свой план")],
                [KeyboardButton(text="🔙 Назад к тренировкам")]
            ],
            resize_keyboard=True, one_time_keyboard=False
        )
    # manual mode
    return ReplyKeyboardMarkup(
        keyboard=[
            [KeyboardButton(text="🆕 Новый план (ИИ)"), KeyboardButton(text="📝 Загрузить свой план")],
            [KeyboardButton(text="🔙 Назад к тренировкам")]
        ],
        resize_keyboard=True, one_time_keyboard=False
    )

def workout_main_keyboard():
    return workout_main_reply_keyboard()

def workout_categories_keyboard(categories: List[Tuple[int, str]], action: str = "add"):
    buttons = []
    row = []
    for i, (cat_id, cat_name) in enumerate(categories):
        if action == "add":
            callback = f"w_add_cat_{cat_id}"
        else:
            callback = f"w_manage_cat_{cat_id}"
        row.append(InlineKeyboardButton(text=cat_name, callback_data=callback))
        if len(row) == 2 or i == len(categories)-1:
            buttons.append(row)
            row = []
    if action == "manage":
        buttons.append([InlineKeyboardButton(text="➕ Создать категорию", callback_data="w_cat_new")])
    buttons.append([InlineKeyboardButton(text="🔙 Назад", callback_data="workout_main")])
    return InlineKeyboardMarkup(inline_keyboard=buttons)

def workout_category_actions_keyboard(cat_id: int):
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📋 Упражнения", callback_data=f"w_manage_exercises_{cat_id}")],
        [InlineKeyboardButton(text="✏️ Переименовать", callback_data=f"w_cat_rename_{cat_id}"),
         InlineKeyboardButton(text="❌ Удалить", callback_data=f"w_cat_delete_{cat_id}")],
        [InlineKeyboardButton(text="🔙 К списку категорий", callback_data="workout_manage")]
    ])
    return keyboard

def workout_exercises_keyboard(exercises: List[Tuple[int, str]], cat_id: int, action: str = "add"):
    buttons = []
    row = []
    for i, (ex_id, ex_name) in enumerate(exercises):
        if action == "add":
            callback = f"w_add_ex_{ex_id}"
        else:
            callback = f"w_manage_ex_{ex_id}"
        row.append(InlineKeyboardButton(text=ex_name, callback_data=callback))
        if len(row) == 2 or i == len(exercises)-1:
            buttons.append(row)
            row = []
    if action == "manage":
        buttons.append([InlineKeyboardButton(text="➕ Создать упражнение", callback_data=f"w_ex_new_{cat_id}")])
    buttons.append([InlineKeyboardButton(text="🔙 К категориям", callback_data="w_back_to_cats_from_ex")])
    return InlineKeyboardMarkup(inline_keyboard=buttons)

def workout_exercise_actions_keyboard(ex_id: int):
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✏️ Переименовать", callback_data=f"w_ex_rename_{ex_id}"),
         InlineKeyboardButton(text="❌ Удалить", callback_data=f"w_ex_delete_{ex_id}")],
        [InlineKeyboardButton(text="🎯 Установить цель", callback_data=f"w_ex_set_goal_{ex_id}")],
        [InlineKeyboardButton(text="🔙 К списку упражнений", callback_data="w_back_to_ex_from_actions")]
    ])
    return keyboard

def workout_continue_keyboard():
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Добавить ещё", callback_data="w_continue_yes")],
        [InlineKeyboardButton(text="❌ Закончить", callback_data="workout_main")]
    ])
    return keyboard

def workout_exercise_goal_keyboard():
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎯 Силовое", callback_data="goal_strength")],
        [InlineKeyboardButton(text="🚴 Кардио", callback_data="goal_cardio")],
        [InlineKeyboardButton(text="🔙 Назад", callback_data="w_back_to_ex_from_actions")]
    ])
    return keyboard

def workout_action_choice_keyboard(ex_id: int):
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📝 Ввести вручную", callback_data=f"w_manual_{ex_id}")],
        [InlineKeyboardButton(text="🎯 Цель достигнута", callback_data=f"w_achieve_goal_{ex_id}")],
        [InlineKeyboardButton(text="🔙 Назад", callback_data="w_back_to_main_from_add")]
    ])
    return keyboard

def stats_keyboard():
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📆 Неделя", callback_data="stats:week"),
         InlineKeyboardButton(text="🗓 Месяц", callback_data="stats:month")],
        [InlineKeyboardButton(text="📈 График неделя", callback_data="stats:chart_week"),
         InlineKeyboardButton(text="📈 График месяц", callback_data="stats:chart_month")],
        [InlineKeyboardButton(text="🔙 Назад в меню", callback_data="back_to_main")]
    ])
    return keyboard

def rank_back_keyboard():
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Назад в меню", callback_data="back_to_main")]
    ])
    return keyboard

def diet_menu_reply_keyboard():
    keyboard = ReplyKeyboardMarkup(
        keyboard=[
            [KeyboardButton(text="🍎 Записать еду"), KeyboardButton(text="⚖️ Записать вес")],
            [KeyboardButton(text="🧮 Рассчитать % жира"), KeyboardButton(text="📖 История еды")],
            [KeyboardButton(text="📈 Графики веса и % жира"), KeyboardButton(text="⚙️ Изменить цель")],
            [KeyboardButton(text="🔙 Назад")]
        ],
        resize_keyboard=True,
        one_time_keyboard=False
    )
    return keyboard

def meal_type_keyboard():
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🍳 Завтрак", callback_data="meal_type:Завтрак"),
         InlineKeyboardButton(text="🥗 Обед", callback_data="meal_type:Обед")],
        [InlineKeyboardButton(text="🍽 Ужин", callback_data="meal_type:Ужин"),
         InlineKeyboardButton(text="🍪 Перекус", callback_data="meal_type:Перекус")],
        [InlineKeyboardButton(text="🔙 Отмена", callback_data="meal_entry_cancel")]
    ])
    return keyboard

def meal_chosen_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✏️ Записать калории вручную", callback_data="meal_entry_manual")],
        [InlineKeyboardButton(text="❌ Отмена", callback_data="meal_entry_cancel")]
    ])

def save_food_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💾 Сохранить в «Мои блюда»", callback_data="save_food_yes")],
        [InlineKeyboardButton(text="➡️ Пропустить", callback_data="save_food_skip")]
    ])

def my_foods_keyboard(foods: List[Tuple[str, float]]):
    buttons = []
    for name, calories in foods:
        buttons.append([InlineKeyboardButton(text=f"{name} ({int(calories)} ккал)", callback_data=f"food_choose_{name}")])
    buttons.append([InlineKeyboardButton(text="➕ Создать новое блюдо", callback_data="food_create_new")])
    buttons.append([InlineKeyboardButton(text="🔙 Отмена", callback_data="food_cancel")])
    return InlineKeyboardMarkup(inline_keyboard=buttons)

def gender_keyboard():
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🚹 Мужской", callback_data="gender_male"),
         InlineKeyboardButton(text="🚺 Женский", callback_data="gender_female")]
    ])
    return keyboard

def activity_keyboard():
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="1️⃣ Сидячий (нет тренировок)", callback_data="activity_1.2")],
        [InlineKeyboardButton(text="2️⃣ Лёгкий (1-3 раза/нед)", callback_data="activity_1.375")],
        [InlineKeyboardButton(text="3️⃣ Умеренный (3-5 раз/нед)", callback_data="activity_1.55")],
        [InlineKeyboardButton(text="4️⃣ Высокий (6-7 раз/нед)", callback_data="activity_1.725")],
        [InlineKeyboardButton(text="5️⃣ Очень высокий (физ. работа + спорт)", callback_data="activity_1.9")]
    ])
    return keyboard

def goal_keyboard():
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔻 Снизить вес", callback_data="goal_loss")],
        [InlineKeyboardButton(text="🔹 Поддерживать вес", callback_data="goal_maintain")],
        [InlineKeyboardButton(text="🔺 Набрать вес", callback_data="goal_gain")]
    ])
    return keyboard

def diet_confirm_keyboard():
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Подтвердить", callback_data="diet_confirm")],
        [InlineKeyboardButton(text="🔄 Заново", callback_data="diet_restart")]
    ])
    return keyboard

def diet_confirm_food_keyboard():
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Да, верно", callback_data="food_confirm_yes")],
        [InlineKeyboardButton(text="🔄 Ввести заново", callback_data="food_confirm_redo")],
        [InlineKeyboardButton(text="✏️ Ввести калории вручную", callback_data="food_confirm_manual")],
        [InlineKeyboardButton(text="❌ Отмена", callback_data="food_cancel")]
    ])
    return keyboard

def back_keyboard():
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Назад", callback_data="back_to_main")]
    ])
    return keyboard

def food_add_more_keyboard():
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Да, добавить ещё", callback_data="food_add_more_yes")],
        [InlineKeyboardButton(text="❌ Нет, в меню", callback_data="back_to_main")]
    ])
    return keyboard

def food_cancel_keyboard():
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="❌ Отмена", callback_data="food_cancel")]
    ])
    return keyboard
    


# ============ КЛАВИАТУРЫ ДЛЯ ЗАДАЧ ============
def tasks_menu_keyboard(tasks: list, user_id: Optional[int] = None) -> InlineKeyboardMarkup:
    buttons = []
    for t in tasks:
        prefix = "🔥 " if t['is_priority'] else ""
        title = t['title']
        if len(title) > 28:
            title = title[:25] + "..."
        suffix = ""
        if t['deadline']:
            suffix = f" ⏰{days_left_str(t['deadline'], user_id)}"
        if t.get('repeat_days'):
            suffix += f" 🔁"
        label = f"{'✅ ' if t['is_done'] else ''}{prefix}{title}{suffix}"
        if not t['is_done']:
            buttons.append([
                InlineKeyboardButton(text=label, callback_data=f"task_done_{t['id']}"),
                InlineKeyboardButton(text="🗑", callback_data=f"task_del_{t['id']}")
            ])
        else:
            buttons.append([
                InlineKeyboardButton(text=label, callback_data="task_noop"),
                InlineKeyboardButton(text="🗑", callback_data=f"task_del_{t['id']}")
            ])
    buttons.append([InlineKeyboardButton(text="➕ Новая задача", callback_data="task_new")])
    buttons.append([InlineKeyboardButton(text="🔙 Главное меню", callback_data="back_to_main")])
    return InlineKeyboardMarkup(inline_keyboard=buttons)

def tasks_confirm_keyboard(task_id: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Да, выполнена", callback_data=f"task_confirm_{task_id}"),
         InlineKeyboardButton(text="❌ Нет", callback_data="back_to_main")]
    ])

def task_repeat_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="1️⃣ Разовая", callback_data="task_type_once")],
        [InlineKeyboardButton(text="🔁 Повторяющаяся", callback_data="task_type_repeat")]
    ])

def task_days_keyboard(selected: list) -> InlineKeyboardMarkup:
    days = [(0,"Пн"),(1,"Вт"),(2,"Ср"),(3,"Чт"),(4,"Пт"),(5,"Сб"),(6,"Вс")]
    row = []
    buttons = []
    for num, name in days:
        mark = "✅" if str(num) in selected else ""
        row.append(InlineKeyboardButton(text=f"{mark}{name}", callback_data=f"task_day_{num}"))
    buttons.append(row)
    buttons.append([InlineKeyboardButton(text="✔️ Готово", callback_data="task_days_done")])
    return InlineKeyboardMarkup(inline_keyboard=buttons)

def task_priority_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔥 Да, важная", callback_data="task_priority_yes"),
         InlineKeyboardButton(text="Нет", callback_data="task_priority_no")]
    ])

def task_deadline_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📅 Добавить дедлайн", callback_data="task_deadline_yes"),
         InlineKeyboardButton(text="Пропустить", callback_data="task_deadline_no")]
    ])

def urgent_tasks_keyboard(tasks: list, user_id: Optional[int] = None) -> Optional[InlineKeyboardMarkup]:
    """Инлайн-кнопки срочных задач для главного меню."""
    if not tasks:
        return None
    buttons = []
    for t in tasks:
        label = ("🔥 " if t['is_priority'] else "⏰ ") + t['title']
        if len(label) > 32:
            label = label[:29] + "..."
        if t.get('days_left') is not None:
            label += f" – {days_left_str(t['deadline'], user_id)}"
        buttons.append([InlineKeyboardButton(text=label, callback_data=f"task_done_{t['id']}")])
    return InlineKeyboardMarkup(inline_keyboard=buttons)


# ============ КЛАВИАТУРЫ ДЛЯ ИИ-ПЛАНА ============
def wp_mode_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🤖 Создать план с ИИ", callback_data="wp_mode_ai")],
        [InlineKeyboardButton(text="📝 Ввести свой план", callback_data="wp_mode_manual")],
        [InlineKeyboardButton(text="🔙 Назад", callback_data="back_to_main")]
    ])

def wp_goal_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💪 Набор массы", callback_data="wp_goal_mass")],
        [InlineKeyboardButton(text="🔥 Похудение", callback_data="wp_goal_loss")],
        [InlineKeyboardButton(text="⚡ Сила", callback_data="wp_goal_strength")],
        [InlineKeyboardButton(text="🎯 Общая форма", callback_data="wp_goal_fitness")],
        [InlineKeyboardButton(text="🔙 Назад", callback_data="wp_back_to_mode")]
    ])

def wp_level_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🌱 Новичок", callback_data="wp_level_beginner")],
        [InlineKeyboardButton(text="📈 Средний", callback_data="wp_level_intermediate")],
        [InlineKeyboardButton(text="🏆 Продвинутый", callback_data="wp_level_advanced")],
        [InlineKeyboardButton(text="🔙 Назад", callback_data="wp_back_to_goal")]
    ])

def wp_days_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="2", callback_data="wp_days_2"),
         InlineKeyboardButton(text="3", callback_data="wp_days_3"),
         InlineKeyboardButton(text="4", callback_data="wp_days_4"),
         InlineKeyboardButton(text="5", callback_data="wp_days_5")],
        [InlineKeyboardButton(text="🔙 Назад", callback_data="wp_back_to_level")]
    ])

def wp_plan_review_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Принять план", callback_data="wp_plan_accept")],
        [InlineKeyboardButton(text="✏️ Редактировать", callback_data="wp_plan_edit")],
        [InlineKeyboardButton(text="🔄 Сгенерировать заново", callback_data="wp_plan_regenerate")],
        [InlineKeyboardButton(text="🔙 Назад", callback_data="wp_back_to_days")]
    ])

def wp_plan_review_keyboard_manual():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Принять план", callback_data="wp_plan_accept")],
        [InlineKeyboardButton(text="✏️ Редактировать", callback_data="wp_plan_edit")],
        [InlineKeyboardButton(text="🔄 Ввести заново", callback_data="wp_mode_manual")],
        [InlineKeyboardButton(text="🔙 Назад", callback_data="wp_back_to_mode")]
    ])

def wp_edit_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Назад к плану", callback_data="wp_back_to_review")]
    ])

def ws_today_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="ПОГНАЛИ 💪", callback_data="ws_start")],
        [InlineKeyboardButton(text="Пропустил день", callback_data="ws_skip_day")],
        [InlineKeyboardButton(text="🔙 Назад", callback_data="back_to_main")]
    ])

def ws_exercise_keyboard(is_first: bool = True):
    buttons = [
        [InlineKeyboardButton(text="✅ Цель выполнена", callback_data="ws_ex_done")],
        [InlineKeyboardButton(text="⏭ Пропустить", callback_data="ws_ex_skip")]
    ]
    if not is_first:
        buttons.append([InlineKeyboardButton(text="↩️ Назад", callback_data="ws_ex_prev")])
    return InlineKeyboardMarkup(inline_keyboard=buttons)

def ws_skip_day_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Назад", callback_data="ws_back_to_today")]
    ])

def ws_rest_day_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Назад в меню тренировок", callback_data="back_to_workout_main")]
    ])

def wp_settings_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔄 Обновить план", callback_data="wp_reset")],
        [InlineKeyboardButton(text="📋 Пересмотр упражнений", callback_data="wp_monthly_review")],
        [InlineKeyboardButton(text="🔙 Назад", callback_data="workout_main_ai")]
    ])

def wp_monthly_review_keyboard(changes: list):
    buttons = []
    for i, ch in enumerate(changes):
        buttons.append([InlineKeyboardButton(
            text=f"{i+1}. {ch['old_exercise']} → {ch['new_exercise']}",
            callback_data=f"wp_review_noop"
        )])
    buttons.append([InlineKeyboardButton(text="✅ Принять выбранные", callback_data="wp_review_accept")])
    buttons.append([InlineKeyboardButton(text="❌ Отклонить всё", callback_data="wp_review_decline")])
    buttons.append([InlineKeyboardButton(text="🔙 Назад", callback_data="workout_main_ai")])
    return InlineKeyboardMarkup(inline_keyboard=buttons)

def workout_ai_main_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📋 Настройки плана", callback_data="wp_settings")],
        [InlineKeyboardButton(text="🔙 Главное меню", callback_data="back_to_main")]
    ])

# ============ ФОРМИРОВАНИЕ МЕНЮ ============
def format_main_menu(user_id: int) -> str:
    today_ratings = get_today_ratings(user_id)
    workout_data = get_or_create_workout_data(user_id)
    rank_data = get_or_create_rank_data(user_id)
    streak = get_streak(user_id)
    profile = get_diet_profile(user_id)
    if profile:
        today_cal = get_today_calories(user_id)
        daily_goal = profile['daily_calories']
        percent = (today_cal / daily_goal * 100) if daily_goal > 0 else 0
        calories_line = f"🍽 Калории: {int(today_cal)}/{int(daily_goal)} ({int(percent)}%)"
    else:
        calories_line = "🍽 Диета не настроена"

    categories = {
        'сон': '😴',
        'еда': '🍽',
        'активность': '💪',
        'зависание': '🎮',
        'настрой': '🎯'
    }

    rank_id = rank_data['current_rank']
    rank_name = get_rank_name(rank_id)
    rank_emoji = get_rank_emoji(rank_id)

    lines = [f"┌─ TrackCheck "]
    lines.append("│")
    lines.append(f"│ <i>{rank_emoji} {rank_name} {rank_emoji}</i>")
    lines.append("│")

    for cat_key, emoji in categories.items():
        rating = today_ratings.get(cat_key)
        if rating:
            bar = create_new_progress_bar(rating)
            lines.append(f"│ {emoji} {bar}")
        else:
            lines.append(f"│ {emoji} {create_new_progress_bar(0)}")

    lines.append("│")

    total_sparks = rank_data['total_sparks']
    sparks_needed, next_total = get_sparks_for_next_rank(rank_id, total_sparks)

    lines.append(f"│ 🏋️ {workout_data['current_count']}/{workout_data['monthly_goal']} | ✨ {total_sparks}/{next_total} искр")
    lines.append(f"│ {calories_line}")
    lines.append(f"│ 🔥 Стрик: {streak} дней")
    lines.append("└─────────────────────")

    return "\n".join(lines)

async def send_main_menu(bot: Bot, user_id: int, chat_id: int):
    try:
        text = format_main_menu(user_id)
        old_menu = user_last_menu.get(user_id)
        if old_menu:
            try:
                await bot.delete_message(chat_id, old_menu)
            except Exception as e:
                print(f"[BOT] Не удалось удалить старое меню: {e}")
        # Удаляем временные сообщения, сохраняя важные (фото, ИИ, замеры)
        await delete_temp_messages(bot, user_id, chat_id, keep_ai=True)
        msg = await bot.send_message(chat_id, text, reply_markup=main_menu_keyboard(), parse_mode="HTML")
        user_last_menu[user_id] = msg.message_id
        # Отправляем срочные задачи отдельным сообщением если есть
        urgent = get_urgent_tasks_for_menu(user_id)
        if urgent:
            kb = urgent_tasks_keyboard(urgent, user_id)
            tasks_msg = await bot.send_message(chat_id, "⚡ Срочные задачи:", reply_markup=kb)
            user_temp_messages.setdefault(user_id, {})['urgent_tasks'] = tasks_msg.message_id
        else:
            user_temp_messages.setdefault(user_id, {}).pop('urgent_tasks', None)
    except Exception as e:
        print(f"[BOT] ОШИБКА в send_main_menu: {e}")
        try:
            msg = await bot.send_message(chat_id, "Меню (режим восстановления)", reply_markup=main_menu_keyboard())
            user_last_menu[user_id] = msg.message_id
        except Exception as e2:
            print(f"[BOT] Критическая ошибка: {e2}")

# ---------- СТАРТ ----------
@router.message(Command("start"))
async def cmd_start(message: Message, bot: Bot):
    try:
        await message.delete()
    except:
        pass
    user_id = message.from_user.id
    cursor = db.execute('SELECT first_name FROM user_settings WHERE user_id = ?', (user_id,))
    row = cursor.fetchone()
    if not row:
        welcome_text = """
🌟 *Добро пожаловать в TrackCheck!* 🌟

Я помогу тебе отслеживать ключевые сферы жизни и развивать дисциплину.

📒 *Рефлексия* – оценивай сон, еду, активность, зависание и настрой.
⭐ *Ранги и искры* – за выполнение всех категорий или тренировку.
🏋️ *Тренировки* – создавай категории и упражнения, ставь цели.
🤖 *ИИ-советчик* – задавай вопросы, получай разбор оценок.
🍽 *Диета* – рассчитывай норму калорий, записывай еду, вес, % жира.
📊 *Статистика* – графики и динамика.
🤳 *Анализ фото* – в разделе Тренировки, разбор сильных и слабых сторон телосложения.

👇 Нажми кнопку **«ПОГНАЛИ 💪»**, чтобы начать!
        """
        markup = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="ПОГНАЛИ 💪", callback_data="ws_start")]
        ])
        msg = await bot.send_message(message.chat.id, welcome_text, parse_mode="Markdown", reply_markup=markup)
        user_welcome_message[user_id] = msg.message_id
        asyncio.create_task(delete_welcome_after_delay(user_id, bot, msg.message_id))
        return
    save_user_settings(user_id, message.from_user.username, message.from_user.first_name)
    update_streak(user_id)
    await send_main_menu(bot, user_id, message.chat.id)

async def delete_welcome_after_delay(user_id: int, bot: Bot, msg_id: int):
    await asyncio.sleep(600)
    await delete_message_safe(bot, user_id, msg_id)
    if user_id in user_welcome_message:
        del user_welcome_message[user_id]

@router.callback_query(F.data == "ws_start")
async def handle_start_button(callback: CallbackQuery, bot: Bot, state: FSMContext):
    # Одна кнопка «ПОГНАЛИ» работает и на приветственном экране (онбординг),
    # и на экране плана тренировки (просмотр плана → старт сессии).
    current_state = await state.get_state()
    if current_state == WorkoutSessionState.viewing_plan:
        await _ws_start_workout(callback, bot, state)
    else:
        await _start_onboarding(callback, bot, state)
    await callback.answer()

async def _start_onboarding(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    await state.clear()
    # удаляем приветственное сообщение с кнопкой ПОГНАЛИ
    try:
        await callback.message.delete()
    except:
        pass
    if user_id in user_welcome_message:
        del user_welcome_message[user_id]
    save_user_settings(user_id, callback.from_user.username, callback.from_user.first_name)
    update_streak(user_id)
    cursor = db.execute('SELECT timezone FROM user_settings WHERE user_id = ?', (user_id,))
    row = cursor.fetchone()
    if not row or not row[0]:
        msg = await bot.send_message(
            callback.message.chat.id,
            "🕒 Для начала выбери свой часовой пояс — так все даты, стрики и напоминания "
            "будут работать по твоему времени, а не по серверному.\n\n"
            "Позже его можно поменять командой /timezone.",
            reply_markup=timezone_picker_keyboard("onboarding")
        )
        user_temp_messages.setdefault(user_id, {})['timezone_picker'] = msg.message_id
        return
    await send_main_menu(bot, user_id, callback.message.chat.id)

@router.callback_query(F.data.startswith("tz:"))
async def handle_timezone_choice(callback: CallbackQuery, bot: Bot):
    user_id = callback.from_user.id
    _, tz_name, context = callback.data.split(":")
    set_user_timezone(user_id, tz_name)
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, callback.message.chat.id, temps.pop('timezone_picker', None))
    user_temp_messages[user_id] = temps
    label = next((l for l, tz in RUSSIAN_TIMEZONES if tz == tz_name), tz_name)
    await callback.answer(f"Часовой пояс: {label} ✅")
    if context == "onboarding":
        await send_main_menu(bot, user_id, callback.message.chat.id)
    else:
        confirm_msg = await bot.send_message(callback.message.chat.id, f"🕒 Часовой пояс изменён на: {label}")
        asyncio.create_task(delete_message_after_delay(bot, callback.message.chat.id, confirm_msg.message_id, delay=4))

@router.message(Command("timezone"))
async def cmd_timezone(message: Message, bot: Bot):
    try:
        await message.delete()
    except:
        pass
    user_id = message.from_user.id
    current = get_user_timezone(user_id)
    current_label = next((label for label, tz in RUSSIAN_TIMEZONES if tz == current), current)
    msg = await message.answer(
        f"🕒 Текущий часовой пояс: {current_label}\n\nВыбери новый:",
        reply_markup=timezone_picker_keyboard("change")
    )
    user_temp_messages.setdefault(user_id, {})['timezone_picker'] = msg.message_id

# ---------- РЕФЛЕКСИЯ ----------
async def show_reflection_menu(user_id: int, chat_id: int, bot: Bot, state: FSMContext, fallback_name: Optional[str] = None):
    await state.clear()
    name = get_user_name(user_id, fallback_name)
    old_menu = user_last_menu.get(user_id)
    if old_menu:
        await delete_message_safe(bot, chat_id, old_menu)
        user_last_menu[user_id] = None
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, chat_id, temps.pop('reflection', None))
    await delete_message_safe(bot, chat_id, temps.pop('tasks_menu', None))
    # Проверяем, заполнены ли все категории — если да, запоминаем для последующего возврата в меню
    if check_all_categories_completed(user_id):
        temps['all_categories_filled'] = True
    else:
        temps.pop('all_categories_filled', None)
    user_temp_messages[user_id] = temps
    # Еда и активность теперь считаются автоматически (после лога еды/тренировки, либо в
    # конце дня) - если пользователь уже заполнил всё, что доступно ему вручную, незачем
    # бесконечно звать его обратно в "что оценим?" в ожидании авто-категорий.
    if manual_categories_completed(user_id):
        update_streak(user_id)
        await bot.send_message(
            chat_id,
            f"{name}, на сегодня с рефлексией всё! 🎉\n"
            "Еда и активность посчитаются сами, как только ты их залогируешь.",
        )
        await delete_temp_messages(bot, user_id, chat_id, keep_ai=True)
        await send_main_menu(bot, user_id, chat_id)
        return
    msg = await bot.send_message(chat_id, f"{name}, что оценим?", reply_markup=reflection_keyboard())
    user_temp_messages[user_id]['reflection'] = msg.message_id

@router.message(F.text == "📒 Рефлексия")
async def handle_reflection(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    await show_reflection_menu(message.from_user.id, message.chat.id, bot, state, message.from_user.first_name)


@router.message(F.text.in_(["😴 Сон", "🎮 Зависание"]))
async def handle_category(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    text_to_category = {
        "😴 Сон": "сон",
        "🎮 Зависание": "зависание",
    }
    category = text_to_category.get(message.text)
    if not category:
        return
    temps = user_temp_messages.get(message.from_user.id, {})
    await delete_message_safe(bot, message.chat.id, temps.get('reflection'))
    await state.update_data(category=category)
    await state.set_state(RatingState.waiting_for_rating)
    msg = await message.answer(f"📝 Оцени {category.upper()} за сегодня:", reply_markup=rating_keyboard())
    temps['rating'] = msg.message_id
    # Сохраняем флаг all_categories_filled для последующей проверки в process_rating
    user_temp_messages[message.from_user.id] = temps

@router.message(F.text == "🎯 Настрой")
async def handle_mood_category(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    user_id = message.from_user.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, temps.get('reflection'))
    await state.set_state(RatingState.waiting_for_mood_text)
    msg = await message.answer(
        "🎯 Опиши в паре предложений, как прошёл твой день и что ты сегодня чувствовал(а):",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="🔙 Назад", callback_data="mood_back")]
        ])
    )
    temps['rating'] = msg.message_id
    user_temp_messages[user_id] = temps

@router.callback_query(RatingState.waiting_for_mood_text, F.data == "mood_back")
async def mood_back(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, callback.message.chat.id, temps.get('rating'))
    await show_reflection_menu(user_id, callback.message.chat.id, bot, state, callback.from_user.first_name)
    await callback.answer()

@router.message(RatingState.waiting_for_mood_text)
async def process_mood_text(message: Message, bot: Bot, state: FSMContext):
    # На случай, если пользователь нажмёт reply-кнопку «🔙 Назад» меню рефлексии
    if message.text == "🔙 Назад":
        try:
            await message.delete()
        except:
            pass
        await show_reflection_menu(message.from_user.id, message.chat.id, bot, state, message.from_user.first_name)
        return
    description = (message.text or "").strip()
    if len(description) < 3:
        await message.answer("Напиши чуть подробнее, как прошёл день 🙂")
        return
    user_id = message.from_user.id
    try:
        await message.delete()
    except:
        pass
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, temps.get('rating'))
    await bot.send_chat_action(message.chat.id, action=ChatAction.TYPING)
    thinking_msg = await message.answer("Думаю...")
    temps['rating'] = thinking_msg.message_id
    user_temp_messages[user_id] = temps

    name = get_user_name(user_id, message.from_user.first_name)
    full_context = get_full_context_for_ai(user_id)
    prompt = f"""Ты — заботливый персональный трекер-ассистент. Пользователя зовут {name}.
Он(а) описал(а) свой сегодняшний день и настроение так: "{description}"

Вот что ты ещё знаешь о нём(ней) за последнее время:
{full_context}

Оцени его(её) настроение сегодня по шкале от 1 до 10 (10 — отличное настроение, 1 — очень плохое).
Затем напиши короткий (2-4 предложения) тёплый отклик по-русски, обращаясь по имени:
- если настроение хорошее — искренне порадуйся вместе с ним(ней);
- если настроение так себе или плохое — мягко поддержи и дай 1-2 конкретных совета,
  как можно улучшить состояние или разобраться с тяжёлыми эмоциями, учитывая контекст выше.
Ответь СТРОГО в формате JSON без пояснений и без markdown:
{{"rating": <целое число 1-10>, "response": "<текст отклика>"}}"""

    await state.update_data(
        retry_mood_description=description,
        retry_action="mood"
    )
    result = await run_in_thread(gemini_generate_rating, prompt)
    if not result:
        await delete_message_safe(bot, message.chat.id, temps.get('rating'))
        await message.answer(
            "❌ ИИ не ответил.",
            reply_markup=retry_ai_keyboard("mood")
        )
        return

    today = user_today_str(user_id)
    rating = result['rating']
    save_rating(user_id, 'настрой', rating, today)
    reply_text = f"🎯 Настрой: {rating}/10\n\n{result.get('response') or result.get('comment', '')}"
    await state.clear()
    await delete_message_safe(bot, message.chat.id, temps.get('rating'))

    all_completed = check_all_categories_completed(user_id)
    if all_completed:
        success, sparks_today, rank_up, old_rank, new_rank = add_spark(user_id, 'categories')
        update_streak(user_id)
        await message.answer(reply_text)
        await delete_temp_messages(bot, user_id, message.chat.id, keep_ai=True)
        await send_main_menu(bot, user_id, message.chat.id)
    else:
        msg = await message.answer(reply_text, reply_markup=reflection_keyboard())
        temps = user_temp_messages.get(user_id, {})
        temps['rating'] = msg.message_id
        user_temp_messages[user_id] = temps
        await show_reflection_menu(user_id, message.chat.id, bot, state, message.from_user.first_name)

@router.message(F.text == "🔙 Назад в меню")
async def back_to_main_msg(message: Message, bot: Bot, state: FSMContext):
    user_id = message.from_user.id
    # Удаляем временные сообщения, сохраняя важные
    await delete_temp_messages(bot, user_id, message.chat.id, keep_ai=True)
    # Убираем инлайн кнопки у сохранённых сообщений
    temps = user_temp_messages.get(user_id, {})
    for key in ['photo_analysis_result', 'photo_user', 'body_fat_measurements', 'body_fat_result']:
        if key in temps:
            try:
                await bot.edit_message_reply_markup(message.chat.id, temps[key])
            except:
                pass
    try:
        await message.delete()
    except:
        pass
    await state.clear()
    await send_main_menu(bot, user_id, message.chat.id)

@router.callback_query(F.data == "back_to_main")
@router.callback_query(F.data == "back_to_main_from_ai")
async def back_to_main_callback(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    await state.clear()
    try:
        await callback.message.delete()
    except:
        pass
    # Удаляем временные сообщения, сохраняя важные
    await delete_temp_messages(bot, user_id, callback.message.chat.id, keep_ai=True)
    # Убираем инлайн кнопки у сохранённых сообщений
    temps = user_temp_messages.get(user_id, {})
    for key in ['photo_analysis_result', 'photo_user', 'body_fat_measurements', 'body_fat_result']:
        if key in temps:
            try:
                await bot.edit_message_reply_markup(callback.message.chat.id, temps[key])
            except:
                pass
    await send_main_menu(bot, user_id, callback.message.chat.id)
    await callback.answer()

@router.message(F.text == "🔙 Назад")
async def back_from_reflection(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    await state.clear()
    user_id = message.from_user.id
    # Удаляем временные сообщения, сохраняя важные
    await delete_temp_messages(bot, user_id, message.chat.id, keep_ai=True)
    # Убираем инлайн кнопки у сохранённых сообщений
    temps = user_temp_messages.get(user_id, {})
    for key in ['photo_analysis_result', 'photo_user', 'body_fat_measurements', 'body_fat_result']:
        if key in temps:
            try:
                await bot.edit_message_reply_markup(message.chat.id, temps[key])
            except:
                pass
    await send_main_menu(bot, user_id, message.chat.id)

@router.callback_query(F.data.startswith("rate:"))
async def process_rating(callback: CallbackQuery, bot: Bot, state: FSMContext):
    temps = user_temp_messages.get(callback.from_user.id, {})
    await delete_message_safe(bot, callback.message.chat.id, temps.get('reflection'))
    data = await state.get_data()
    category = data.get("category")
    rating = int(callback.data.split(":")[1])
    today = user_today_str(callback.from_user.id)
    save_rating(callback.from_user.id, category, rating, today)
    await state.clear()
    temps = user_temp_messages.get(callback.from_user.id, {})
    await delete_message_safe(bot, callback.message.chat.id, temps.get('rating'))
    name = get_user_name(callback.from_user.id, callback.from_user.first_name)

    # Проверяем, заполнены ли все 5 категорий
    all_completed = check_all_categories_completed(callback.from_user.id)
    # Также проверяем флаг из temp messages (если пользователь зашел повторно при заполненных категориях)
    all_filled_flag = temps.get('all_categories_filled', False)

    if rating <= 3:
        # Если все категории заполнены — спрашиваем про ИИ анализ, но сохраняем флаг
        msg = await callback.message.answer(
            f"{name}, низкая оценка {category} ({rating}/10). Разобрать с ИИ почему так?",
            reply_markup=low_rating_keyboard(category)
        )
        temps['low_rating'] = msg.message_id
        if all_completed or all_filled_flag:
            temps['all_categories_filled'] = True
        user_temp_messages[callback.from_user.id] = temps
        await show_reflection_menu(callback.from_user.id, callback.message.chat.id, bot, state, callback.from_user.first_name)
    else:
        if all_completed:
            success, sparks_today, rank_up, old_rank, new_rank = add_spark(callback.from_user.id, 'categories')
            update_streak(callback.from_user.id)
            if success:
                # Бонусная искра если все категории >= 8
                today_ratings = get_today_ratings(callback.from_user.id)
                all_high = len(today_ratings) == 5 and all(v >= 8 for v in today_ratings.values())
                if all_high:
                    add_spark(callback.from_user.id, 'bonus_high')
                    await callback.answer("✨ Искра + бонус за отличный день!", show_alert=False)
                elif rank_up:
                    await callback.answer(f"✨ Новый ранг: {get_rank_name(new_rank)}!", show_alert=False)
                else:
                    await callback.answer("✨ Искра зачислена.", show_alert=False)
            # Все категории заполнены и оценка высокая — сразу в главное меню
            await delete_message_safe(bot, callback.message.chat.id, callback.message.message_id)
            await delete_temp_messages(bot, callback.from_user.id, callback.message.chat.id, keep_ai=True)
            await send_main_menu(bot, callback.from_user.id, callback.message.chat.id)
        else:
            # Не все категории заполнены — показываем рефлексию снова
            await delete_message_safe(bot, callback.message.chat.id, callback.message.message_id)
            await show_reflection_menu(callback.from_user.id, callback.message.chat.id, bot, state, callback.from_user.first_name)
    await callback.answer("✅ Сохранено!")

@router.callback_query(F.data.startswith("analyze_low:"))
async def analyze_low_rating_handler(callback: CallbackQuery, bot: Bot, state: FSMContext):
    category = callback.data.split(":")[1]
    today_ratings = get_today_ratings(callback.from_user.id)
    rating = today_ratings.get(category, 0)
    temps = user_temp_messages.get(callback.from_user.id, {})
    await delete_message_safe(bot, callback.message.chat.id, temps.get('low_rating'))
    all_filled_flag = temps.get('all_categories_filled', False)
    await bot.send_chat_action(callback.message.chat.id, action=ChatAction.TYPING)
    await asyncio.sleep(1)
    analysis = analyze_low_rating(callback.from_user.id, category, rating)
    if analysis.startswith("❌"):
        await state.update_data(
            retry_low_rating_category=category,
            retry_low_rating_value=rating,
            retry_action="low_rating"
        )
        await callback.message.answer(
            "❌ ИИ не ответил.",
            reply_markup=retry_ai_keyboard("low_rating")
        )
        if all_filled_flag:
            temps['all_categories_filled'] = True
        user_temp_messages[callback.from_user.id] = temps
        await callback.answer()
        return
    msg = await callback.message.answer(f"🤖 {analysis}", reply_markup=ai_reply_keyboard())
    temps['ai_response'] = msg.message_id
    if all_filled_flag:
        temps['all_categories_filled'] = True
    user_temp_messages[callback.from_user.id] = temps
    save_last_ai_answer(callback.from_user.id, analysis)
    await callback.answer()

@router.callback_query(F.data == "skip_analysis")
async def skip_analysis(callback: CallbackQuery, bot: Bot, state: FSMContext):
    temps = user_temp_messages.get(callback.from_user.id, {})
    await delete_message_safe(bot, callback.message.chat.id, temps.get('low_rating'))
    # Если все категории заполнены — сразу в главное меню
    if temps.get('all_categories_filled'):
        await delete_temp_messages(bot, callback.from_user.id, callback.message.chat.id, keep_ai=True)
        await send_main_menu(bot, callback.from_user.id, callback.message.chat.id)
    else:
        await show_reflection_menu(callback.from_user.id, callback.message.chat.id, bot, state, callback.from_user.first_name)
    await callback.answer()

# ---------- ИИ-СОВЕТЧИК ----------
@router.message(F.text == "Check AI")
async def handle_ai(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    user_id = message.from_user.id
    await state.clear()
    old_menu = user_last_menu.get(user_id)
    if old_menu:
        await delete_message_safe(bot, message.chat.id, old_menu)
        user_last_menu[user_id] = None
    # Удаляем оставшиеся временные сообщения других разделов (фото/замеры/ИИ сохраняются)
    await delete_temp_messages(bot, user_id, message.chat.id, keep_ai=True)
    temps = user_temp_messages.setdefault(user_id, {})
    # Заготовленное сообщение с reply кнопкой
    msg = await message.answer("🤖 CheckAI тут, чем помочь?", reply_markup=ai_reply_keyboard())
    temps['ai_advisor'] = msg.message_id
    await state.set_state(AIAdvisorState.waiting_for_question)


@router.callback_query(F.data == "wp_edit_retry")
async def wp_edit_retry(callback: CallbackQuery, bot: Bot, state: FSMContext):
    data = await state.get_data()
    plan = data.get("wp_plan") or (get_ai_plan(callback.from_user.id) or {}).get("plan")
    await state.set_state(AIPlanState.editing_plan)
    await state.update_data(wp_plan=plan)
    await callback.message.edit_text(
        "Что хочешь изменить в плане?\n\nНапиши например:\n«убери приседания, замени на жим ногами»",
        reply_markup=wp_edit_keyboard()
    )
    await callback.answer()

@router.callback_query(F.data == "ai_advice")
async def handle_ai_advice(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    temps = user_temp_messages.get(user_id, {})
    # Удаляем вступительное сообщение бота (если ещё не удалено)
    await delete_message_safe(bot, callback.message.chat.id, temps.get('ai_advisor'))
    await bot.send_chat_action(callback.message.chat.id, action=ChatAction.TYPING)
    name = get_user_name(user_id, callback.from_user.first_name)
    full_context = get_full_context_for_ai(user_id)
    prompt = f"""Ты — персональный трекер-ассистент. Пользователь {name}.

Вот свежие данные пользователя:
{full_context}

Дай короткий персональный совет (3-5 предложений): что идёт хорошо, на что обратить внимание, и один конкретный шаг на сегодня/завтра.
Обращайся по имени, используй эмодзи, пиши по-русски."""
    await state.update_data(retry_ai_prompt=prompt, retry_action="ai_advice")
    # Animation while generating
    phrases_ai = ["Думаю.", "Думаю..", "Думаю...", "Анализирую.", "Анализирую..", "Анализирую..."]
    stop_ai = asyncio.Event()
    tmp = await callback.message.answer("Думаю...")
    ai_msg_id = tmp.message_id
    temps['ai_advisor'] = ai_msg_id
    user_temp_messages[user_id] = temps

    async def animate_ai():
        i = 0
        while not stop_ai.is_set():
            try:
                await bot.edit_message_text(phrases_ai[i % len(phrases_ai)],
                                             callback.message.chat.id, ai_msg_id)
            except:
                pass
            await asyncio.sleep(1)
            i += 1
    anim = asyncio.create_task(animate_ai())
    try:
        answer = await run_in_thread(gemini_generate, prompt, 8192)
    finally:
        stop_ai.set()
        anim.cancel()
        try:
            await anim
        except asyncio.CancelledError:
            pass
    if answer.startswith("❌"):
        try:
            await bot.edit_message_text("❌ ИИ не ответил.", callback.message.chat.id, ai_msg_id)
        except:
            pass
        await callback.message.answer(
            "❌ ИИ не ответил. Нажми кнопку чтобы попробовать ещё раз.",
            reply_markup=retry_ai_keyboard("ai_advice")
        )
        await state.set_state(AIAdvisorState.waiting_for_question)
        await callback.answer()
        return
    try:
        await bot.edit_message_text(
            f"💡 <b>Совет:</b>\n\n{answer}",
            callback.message.chat.id, ai_msg_id,
            parse_mode="HTML", reply_markup=ai_reply_keyboard()
        )
    except Exception:
        await delete_message_safe(bot, callback.message.chat.id, ai_msg_id)
        msg = await callback.message.answer(f"💡 <b>Совет:</b>\n\n{answer}",
                                            parse_mode="HTML", reply_markup=ai_reply_keyboard())
        ai_msg_id = msg.message_id
    temps['ai_response'] = ai_msg_id
    user_temp_messages[user_id] = temps
    save_last_ai_answer(user_id, answer)
    await state.set_state(AIAdvisorState.waiting_for_question)
    await callback.answer()

@router.message(AIAdvisorState.waiting_for_question)
async def process_ai_question(message: Message, bot: Bot, state: FSMContext):
    question = message.text.strip()
    if len(question) < 3:
        await message.answer("❌ Вопрос слишком короткий. Опиши подробнее!", reply_markup=ai_reply_keyboard())
        return
    user_id = message.from_user.id
    temps = user_temp_messages.get(user_id, {})
    # Удаляем вступительное сообщение бота (НЕ вопрос пользователя!)
    await delete_message_safe(bot, message.chat.id, temps.get('ai_advisor'))
    await bot.send_chat_action(message.chat.id, action=ChatAction.TYPING)
    name = get_user_name(user_id, message.from_user.first_name)
    full_context = get_full_context_for_ai(user_id)
    await state.update_data(retry_ai_question=question, retry_action="ai_question")
    context = f"""Ты — персональный трекер-ассистент. Пользователь {name}.

Вот свежие данные пользователя:
{full_context}

Вопрос: {question}
Ответь кратко, конкретно, с эмодзи, обращайся по имени."""
    # Animation while generating
    phrases_ai = ["Думаю.", "Думаю..", "Думаю...", "Анализирую.", "Анализирую..", "Анализирую..."]
    stop_ai = asyncio.Event()
    # Отправляем сообщение для анимации
    tmp = await message.answer("Думаю...")
    ai_msg_id = tmp.message_id
    temps['ai_advisor'] = ai_msg_id
    user_temp_messages[user_id] = temps

    async def animate_ai():
        i = 0
        while not stop_ai.is_set():
            try:
                await bot.edit_message_text(phrases_ai[i % len(phrases_ai)],
                                             message.chat.id, ai_msg_id)
            except:
                pass
            await asyncio.sleep(1)
            i += 1
    anim = asyncio.create_task(animate_ai())
    try:
        answer = await run_in_thread(gemini_generate, context, 8192)
    finally:
        stop_ai.set()
        anim.cancel()
        try:
            await anim
        except asyncio.CancelledError:
            pass
    if answer.startswith("❌"):
        try:
            await bot.edit_message_text("❌ ИИ не ответил.", message.chat.id, ai_msg_id)
        except:
            pass
        await message.answer(
            "❌ ИИ не ответил. Нажми кнопку чтобы попробовать ещё раз.",
            reply_markup=retry_ai_keyboard("ai_question")
        )
        await state.set_state(AIAdvisorState.waiting_for_question)
        return
    # Ответ ИИ с reply кнопкой - редактируем то же сообщение (не отправляем новое)
    try:
        await bot.edit_message_text(
            f"🤖 <b>Check AI:</b>\n\n{answer}",
            message.chat.id, ai_msg_id,
            parse_mode="HTML", reply_markup=ai_reply_keyboard()
        )
    except Exception as e:
        # Если редактирование не удалось - удаляем старое и отправляем новое
        await delete_message_safe(bot, message.chat.id, ai_msg_id)
        msg = await message.answer(f"🤖 <b>Check AI:</b>\n\n{answer}",
                                    parse_mode="HTML", reply_markup=ai_reply_keyboard())
        ai_msg_id = msg.message_id
    temps['ai_response'] = ai_msg_id
    user_temp_messages[user_id] = temps
    save_last_ai_answer(user_id, answer)

@router.callback_query(F.data == "show_last_ai")
async def show_last_ai(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    last_answer = get_last_ai_answer(user_id)
    if last_answer:
        await callback.message.answer(f"🤖 <b>Последний ответ ИИ:</b>\n\n{last_answer}", parse_mode="HTML", reply_markup=ai_reply_keyboard())
    else:
        await callback.answer("Нет сохранённого ответа", show_alert=True)
    await callback.answer()
    
# ---------- ТРЕНИРОВКИ ----------
async def show_workout_main_menu(user_id: int, chat_id: int, bot: Bot):
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, chat_id, temps.pop('workout_menu', None))
    await delete_message_safe(bot, chat_id, temps.pop('tasks_menu', None))
    user_temp_messages[user_id] = temps

    done_week, plan_week = get_weekly_workout_progress(user_id)
    week_bar = create_workout_progress_bar(done_week, plan_week if plan_week else 1)
    today_wd = WEEKDAY_RU[user_weekday(user_id)]
    date_str = user_today_str(user_id, '%d.%m.%Y')

    # Show today's completed exercises
    today_str = ""
    today_session = get_today_session(user_id)
    if today_session and today_session.get("status") == "done":
        logs = get_session_exercise_logs(today_session["id"])
        if logs:
            lines = []
            for log in logs:
                icon = "✅" if log["status"] == "done" else "⏭"
                name = log["exercise_name"]
                res = log.get("result")
                if res and isinstance(res, dict):
                    s = res.get("sets_done","?")
                    r = res.get("reps_done","?")
                    w = res.get("weight_done")
                    detail = f"{s}×{r}" + (f" @ {w}кг" if w else "")
                    lines.append(f"{icon} {name} — {detail}")
                else:
                    lines.append(f"{icon} {name}")
            today_str = "\nСегодня:\n" + "\n".join(lines)

    text = (
        f"🏋️ Тренировки\n\n"
        f"{today_wd}, {date_str}\n\n"
        f"Неделя: {week_bar}"
        + today_str
    )
    msg = await bot.send_message(chat_id, text, reply_markup=workout_main_keyboard())
    temps = user_temp_messages.get(user_id, {})
    temps['workout_menu'] = msg.message_id
    user_temp_messages[user_id] = temps

@router.message(F.text == "🏋️ Тренировки")
async def handle_workouts(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    user_id = message.from_user.id
    await state.clear()
    old_menu = user_last_menu.get(user_id)
    if old_menu:
        await delete_message_safe(bot, message.chat.id, old_menu)
        user_last_menu[user_id] = None
    # Sweep any leftover temp messages from an interrupted flow (add-workout,
    # AI plan wizard, skip-reason prompt, calorie entry, etc.) — every other
    # section entry point (handle_diet, back_to_main_msg, ...) already does this.
    await delete_temp_messages(bot, user_id, message.chat.id, keep_ai=True)
    await show_workout_main_menu(user_id, message.chat.id, bot)

@router.message(WorkoutState.waiting_for_goal)
async def process_workout_goal(message: Message, bot: Bot, state: FSMContext):
    try:
        goal = int(message.text.strip())
        if not 1 <= goal <= 31:
            raise ValueError
    except ValueError:
        await message.answer("❌ Введи число от 1 до 31!")
        return
    set_workout_goal(message.from_user.id, goal)
    await state.clear()
    try:
        await message.delete()
    except:
        pass
    temps = user_temp_messages.get(message.from_user.id, {})
    await delete_message_safe(bot, message.chat.id, temps.get('workout_setup'))
    await send_main_menu(bot, message.from_user.id, message.chat.id)

async def _do_workout_add(user_id: int, chat_id: int, bot: Bot, state: FSMContext):
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, chat_id, temps.pop('workout_menu', None))
    await delete_message_safe(bot, chat_id, temps.pop('tasks_menu', None))
    cursor = db.execute('SELECT id, name FROM exercise_categories WHERE user_id = ? ORDER BY name', (user_id,))
    categories = cursor.fetchall()
    await state.set_state(WorkoutState.choosing_category)
    msg = await bot.send_message(chat_id, "Выбери категорию упражнения:", reply_markup=workout_categories_keyboard(categories, action="add"))
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id

@router.message(F.text == "🏋️ Добавить выполнение")
async def workout_add_msg(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    user_id = message.from_user.id
    await state.clear()
    plan_data = get_ai_plan(user_id)
    if not plan_data:
        name = get_user_name(user_id, message.from_user.first_name)
        msg = await message.answer(
            f"{name}, план тренировок не настроен.\n\nСоздать план с ИИ или введёшь свой?",
            reply_markup=wp_mode_keyboard()
        )
        user_temp_messages.setdefault(user_id, {})['workout_menu'] = msg.message_id
    else:
        await show_ai_workout_today(user_id, message.chat.id, bot, state)

@router.callback_query(F.data == "workout_add")
async def workout_add_start(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    await callback.message.delete()
    await _do_workout_add(user_id, callback.message.chat.id, bot, state)
    await callback.answer()

@router.callback_query(F.data == "w_back_to_main_from_add")
async def workout_back_to_main(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    await callback.message.delete()
    await state.clear()
    # Отправляем в главное меню (не в меню тренировок!)
    await send_main_menu(bot, user_id, callback.message.chat.id)
    await callback.answer()

@router.callback_query(WorkoutState.choosing_category, F.data.startswith("w_add_cat_"))
async def workout_add_choose_category(callback: CallbackQuery, bot: Bot, state: FSMContext):
    data = await state.get_data()
    if data.get('workout_charts_mode'):
        await workout_charts_choose_category(callback, bot, state)
        return
    cat_id = int(callback.data.split("_")[3])
    user_id = callback.from_user.id
    await callback.message.delete()
    cursor = db.execute('SELECT id, name FROM exercises WHERE user_id = ? AND category_id = ? ORDER BY name', (user_id, cat_id))
    exercises = cursor.fetchall()
    await state.update_data(category_id=cat_id)
    await state.set_state(WorkoutState.choosing_exercise)
    msg = await callback.message.answer("Выбери упражнение:", reply_markup=workout_exercises_keyboard(exercises, cat_id, action="add"))
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.callback_query(WorkoutState.choosing_exercise, F.data.startswith("w_add_ex_"))
async def workout_add_choose_exercise(callback: CallbackQuery, bot: Bot, state: FSMContext):
    data = await state.get_data()
    if data.get('workout_charts_mode'):
        await workout_charts_generate(callback, bot, state)
        return
    ex_id = int(callback.data.split("_")[3])
    user_id = callback.from_user.id
    await callback.message.delete()
    cursor = db.execute('SELECT name, category_id, target_sets, target_reps, target_weight, target_distance, target_duration, weight_increment FROM exercises WHERE id = ?', (ex_id,))
    row = cursor.fetchone()
    if not row:
        await callback.message.answer("❌ Упражнение не найдено.")
        await workout_add_start(callback, bot, state)
        await callback.answer()
        return
    ex_name, cat_id, t_sets, t_reps, t_weight, t_dist, t_dur, inc = row
    type_cursor = db.execute('SELECT ex_type FROM exercise_categories WHERE id = ?', (cat_id,))
    type_row = type_cursor.fetchone()
    ex_type = type_row[0] if type_row else 'strength'

    target_info = ""
    last_info = ""
    if ex_type == 'strength' and t_sets and t_reps:
        target_info = f"\n🎯 Текущая цель: {t_sets}х{t_reps}"
        if t_weight:
            target_info += f" с весом {t_weight} кг"
        if inc:
            target_info += f" (шаг +{inc} кг)"
    elif ex_type == 'cardio' and t_dist and t_dur:
        target_info = f"\n🎯 Текущая цель: {t_dist} км за {t_dur} мин"

    last_cursor = db.execute('''
        SELECT sets, reps, weight, distance, duration, date
        FROM workout_log
        WHERE user_id = ? AND exercise_name = ? AND category_id = ?
        ORDER BY date DESC LIMIT 1
    ''', (user_id, ex_name, cat_id))
    last_row = last_cursor.fetchone()
    if last_row:
        last_sets, last_reps, last_weight, last_dist, last_dur, last_date = last_row
        last_date_formatted = datetime.strptime(last_date, '%Y-%m-%d').strftime('%d.%m')
        if ex_type == 'strength' and last_sets is not None:
            last_info = f"\n📊 Прошлый раз: {last_sets}х{last_reps}"
            if last_weight:
                last_info += f" ({last_weight} кг)"
            last_info += f" ({last_date_formatted})"
        elif ex_type == 'cardio' and last_dist is not None:
            last_info = f"\n📊 Прошлый раз: {last_dist} км / {last_dur} мин ({last_date_formatted})"

    await state.update_data(
        exercise_id=ex_id, exercise_name=ex_name, category_id=cat_id, ex_type=ex_type,
        target_sets=t_sets, target_reps=t_reps, target_weight=t_weight,
        target_distance=t_dist, target_duration=t_dur, weight_increment=inc
    )

    text = f"Упражнение: {ex_name}" + target_info + last_info + "\n\nВыбери действие:"
    msg = await callback.message.answer(text, reply_markup=workout_action_choice_keyboard(ex_id))
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.callback_query(F.data.startswith("w_manual_"))
async def workout_manual_enter(callback: CallbackQuery, bot: Bot, state: FSMContext):
    ex_id = int(callback.data.split("_")[2])
    user_id = callback.from_user.id
    data = await state.get_data()
    ex_type = data.get('ex_type', 'strength')
    await callback.message.delete()
    if ex_type == 'cardio':
        await state.set_state(WorkoutState.entering_distance)
        msg = await callback.message.answer("Введи дистанцию в км (или отправь '-', если не хочешь указывать):")
    else:
        await state.set_state(WorkoutState.entering_reps)
        msg = await callback.message.answer("Введи повторения.\nПримеры: 10, 10,8,6 или 3x10")
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.message(WorkoutState.entering_reps)
async def workout_enter_reps(message: Message, bot: Bot, state: FSMContext):
    reps_input = message.text.strip()
    user_id = message.from_user.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, message.message_id)
    await delete_message_safe(bot, message.chat.id, temps.get('workout_temp'))

    data = await state.get_data()
    ex_type = data.get('ex_type', 'strength')

    if ex_type == 'strength':
        try:
            sets, reps_list = parse_reps_input(reps_input)
            reps_str = ','.join(str(r) for r in reps_list)
            await state.update_data(sets=sets, reps=reps_str)
            await state.set_state(WorkoutState.entering_weight)
            msg = await message.answer("Введи вес в кг (или отправь '-', если не хочешь указывать):")
        except ValueError:
            msg = await message.answer("❌ Неверный формат. Попробуй ещё раз (например, 10, 10,8,6 или 3x10):")
    else:
        try:
            parts = reps_input.split()
            if len(parts) == 2:
                distance = float(parts[0].replace(',', '.'))
                duration = int(parts[1])
                await state.update_data(distance=distance, duration=duration)
                await save_workout_and_continue(message, bot, state, user_id)
                return
        except:
            pass
        await state.update_data(distance=None, duration=None)
        await state.set_state(WorkoutState.entering_distance)
        msg = await message.answer("Введи дистанцию в км (или отправь '-', если не хочешь указывать):")

    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id

async def save_workout_and_continue(message: Message, bot: Bot, state: FSMContext, user_id: int):
    data = await state.get_data()
    ex_name = data['exercise_name']
    ex_type = data.get('ex_type', 'strength')
    today = user_today_str(user_id)

    if ex_type == 'strength':
        sets = data['sets']
        reps = data['reps']
        weight = data.get('weight')
        db.execute('''
            INSERT INTO workout_log (user_id, date, category_id, exercise_name, sets, reps, weight)
            VALUES (?, ?, ?, ?, ?, ?, ?)
        ''', (user_id, today, data.get('category_id'), ex_name, sets, reps, weight))
        result_text = f"Сохранено: {ex_name} – {sets}х{reps}" + (f" ({weight} кг)" if weight else "")
    else:
        distance = data.get('distance')
        duration = data.get('duration')
        db.execute('''
            INSERT INTO workout_log (user_id, date, category_id, exercise_name, distance, duration)
            VALUES (?, ?, ?, ?, ?, ?)
        ''', (user_id, today, data.get('category_id'), ex_name, distance, duration))
        parts = []
        if distance:
            parts.append(f"{distance} км")
        if duration:
            parts.append(f"{duration} мин")
        result_text = f"Сохранено: {ex_name}" + (" – " + " / ".join(parts) if parts else "")
    db.commit()

    cursor = db.execute('SELECT COUNT(*) FROM workout_log WHERE user_id = ? AND date = ?', (user_id, today))
    count = cursor.fetchone()[0]

    spark_awarded = False
    if count == 1:
        add_workout(user_id)
        success, _, rank_up, old_rank, new_rank = add_spark(user_id, 'workout')
        if success:
            spark_awarded = True
            update_streak(user_id)
            if rank_up:
                await send_temp_message(bot, message.chat.id, f"✨ Новый ранг: {get_rank_name(new_rank)}!", delay=3)

    if spark_awarded:
        result_text += "\n✨ Искра за тренировку зачислена!"

    target_btn = None
    if data.get('target_sets') and data.get('target_reps'):
        target_sets = data['target_sets']
        target_reps = data['target_reps']
        target_weight = data.get('target_weight')
        sets = data.get('sets')
        reps = data.get('reps')
        if sets == target_sets and reps == target_reps:
            pass
        else:
            target_btn = InlineKeyboardButton(
                text=f"🎯 Цель: {target_sets}х{target_reps}" + (f" +{target_weight}кг" if target_weight else ""),
                callback_data=f"w_show_goal_{data['exercise_id']}"
            )
    elif data.get('target_distance') and data.get('target_duration'):
        target_dist = data['target_distance']
        target_dur = data['target_duration']
        distance = data.get('distance')
        duration = data.get('duration')
        if distance == target_dist and duration == target_dur:
            pass
        else:
            target_btn = InlineKeyboardButton(
                text=f"🎯 Цель: {target_dist}км / {target_dur}мин",
                callback_data=f"w_show_goal_{data['exercise_id']}"
            )

    markup = workout_continue_keyboard()
    if target_btn:
        markup.inline_keyboard.insert(0, [target_btn])

    await state.set_state(WorkoutState.confirm_continue)
    await message.answer(result_text, reply_markup=markup)

@router.message(WorkoutState.entering_weight)
async def workout_enter_weight(message: Message, bot: Bot, state: FSMContext):
    weight_str = message.text.strip()
    weight = None
    if weight_str != '-':
        try:
            weight = float(weight_str.replace(',', '.'))
        except ValueError:
            await message.answer("❌ Введи число или '-'.")
            return
    user_id = message.from_user.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, message.message_id)
    await delete_message_safe(bot, message.chat.id, temps.get('workout_temp'))
    await state.update_data(weight=weight)
    await save_workout_and_continue(message, bot, state, user_id)

@router.message(WorkoutState.entering_distance)
async def workout_enter_distance(message: Message, bot: Bot, state: FSMContext):
    dist_str = message.text.strip()
    distance = None
    if dist_str != '-':
        try:
            distance = float(dist_str.replace(',', '.'))
        except ValueError:
            await message.answer("❌ Введи число или '-'.")
            return
    user_id = message.from_user.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, message.message_id)
    await delete_message_safe(bot, message.chat.id, temps.get('workout_temp'))
    await state.update_data(distance=distance)
    await state.set_state(WorkoutState.entering_duration)
    msg = await message.answer("Введи время в минутах (или отправь '-', если не хочешь указывать):")
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id

@router.message(WorkoutState.entering_duration)
async def workout_enter_duration(message: Message, bot: Bot, state: FSMContext):
    dur_str = message.text.strip()
    duration = None
    if dur_str != '-':
        try:
            duration = int(dur_str)
            if duration <= 0:
                raise ValueError
        except ValueError:
            await message.answer("❌ Введи положительное число или '-'.")
            return
    user_id = message.from_user.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, message.message_id)
    await delete_message_safe(bot, message.chat.id, temps.get('workout_temp'))
    await state.update_data(duration=duration)
    await save_workout_and_continue(message, bot, state, user_id)

@router.callback_query(F.data == "w_continue_yes", WorkoutState.confirm_continue)
async def workout_continue_yes(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    await callback.message.delete()
    await state.update_data(sets=None, reps=None, weight=None, distance=None, duration=None)
    cursor = db.execute('SELECT id, name FROM exercise_categories WHERE user_id = ? ORDER BY name', (user_id,))
    categories = cursor.fetchall()
    await state.set_state(WorkoutState.choosing_category)
    msg = await callback.message.answer("Выбери категорию упражнения:", reply_markup=workout_categories_keyboard(categories, action="add"))
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.callback_query(F.data.startswith("w_achieve_goal_"))
async def workout_achieve_goal(callback: CallbackQuery, bot: Bot, state: FSMContext):
    ex_id = int(callback.data.split("_")[3])
    user_id = callback.from_user.id
    cursor = db.execute('''
        SELECT e.name, e.category_id, e.target_sets, e.target_reps, e.target_weight, e.weight_increment,
               e.target_distance, e.target_duration, c.ex_type
        FROM exercises e
        LEFT JOIN exercise_categories c ON e.category_id = c.id
        WHERE e.id = ? AND e.user_id = ?
    ''', (ex_id, user_id))
    row = cursor.fetchone()
    if not row:
        await callback.answer("❌ Упражнение не найдено", show_alert=True)
        return
    ex_name, cat_id, target_sets, target_reps, target_weight, inc, target_distance, target_duration, ex_type = row
    today = user_today_str(user_id)

    # Проверяем ДО вставки для определения первой тренировки дня
    cursor = db.execute('SELECT COUNT(*) FROM workout_log WHERE user_id = ? AND date = ?', (user_id, today))
    count_before = cursor.fetchone()[0]

    # Сохраняем в workout_log
    if ex_type == 'strength':
        db.execute('''
            INSERT INTO workout_log (user_id, date, category_id, exercise_name, sets, reps, weight)
            VALUES (?, ?, ?, ?, ?, ?, ?)
        ''', (user_id, today, cat_id, ex_name, target_sets, target_reps, target_weight))
        result_text = f"Сохранено: {ex_name} – {target_sets}х{target_reps}" + (f" ({target_weight} кг)" if target_weight else "")
    else:
        db.execute('''
            INSERT INTO workout_log (user_id, date, category_id, exercise_name, distance, duration)
            VALUES (?, ?, ?, ?, ?, ?)
        ''', (user_id, today, cat_id, ex_name, target_distance, target_duration))
        parts_list = []
        if target_distance:
            parts_list.append(f"{target_distance} км")
        if target_duration:
            parts_list.append(f"{target_duration} мин")
        result_text = f"Сохранено: {ex_name}" + (" – " + " / ".join(parts_list) if parts_list else "")
    db.commit()

    if count_before == 0:
        add_workout(user_id)
        success, _, rank_up, old_rank, new_rank = add_spark(user_id, 'workout')
        if success and rank_up:
            result_text += f"\n✨ Новый ранг: {get_rank_name(new_rank)}!"
        elif success:
            result_text += "\n✨ Искра за тренировку зачислена!"
    await callback.message.delete()
    markup = workout_continue_keyboard()
    await callback.message.answer(result_text, reply_markup=markup)
    await state.set_state(WorkoutState.confirm_continue)
    await state.update_data(sets=None, reps=None, weight=None, distance=None, duration=None)
    await callback.answer()


# ============ ИИ-ПЛАН ТРЕНИРОВОК — ОНБОРДИНГ ============

async def show_ai_workout_today(user_id: int, chat_id: int, bot: Bot, state: FSMContext):
    """Главный экран — план на сегодня или день отдыха."""
    try:
        await _show_ai_workout_today_inner(user_id, chat_id, bot, state)
    except Exception as e:
        import traceback
        print(f"[WORKOUT TODAY] Error: {e}")
        traceback.print_exc()
        temps = user_temp_messages.get(user_id, {})
        await delete_message_safe(bot, chat_id, temps.get('workout_menu'))
        msg = await bot.send_message(chat_id, "Произошла ошибка при загрузке плана. Попробуй ещё раз.",
                                      reply_markup=ws_rest_day_keyboard())
        user_temp_messages.setdefault(user_id, {})['workout_menu'] = msg.message_id

async def _show_ai_workout_today_inner(user_id: int, chat_id: int, bot: Bot, state: FSMContext):
    plan_data = get_ai_plan(user_id)
    if not plan_data:
        return

    today_exercises = get_today_plan(plan_data, user_id)
    temps = user_temp_messages.get(user_id, {})

    if not today_exercises:
        # День отдыха
        # Удаляем предыдущее сообщение workout_menu
        await delete_message_safe(bot, chat_id, temps.get('workout_menu'))
        
        next_date, next_day = get_next_training_day(plan_data, user_id)
        text = "Сегодня день отдыха."
        if next_date and next_day:
            text += f"\nСледующая тренировка: {next_day}, {next_date}"
        msg = await bot.send_message(chat_id, text, reply_markup=ws_rest_day_keyboard())
        temps['workout_menu'] = msg.message_id
        user_temp_messages[user_id] = temps
        return

    # Создаём сессию если нет
    session = create_today_session(user_id, plan_data)
    if session and session["status"] in ("done", "skipped"):
        # Уже завершили сегодня
        # Удаляем предыдущее сообщение workout_menu
        await delete_message_safe(bot, chat_id, temps.get('workout_menu'))
        
        text = "Сегодняшняя тренировка уже записана."
        next_date, next_day = get_next_training_day(plan_data, user_id)
        if next_date:
            text += f"\nСледующая: {next_day}, {next_date}"
        msg = await bot.send_message(chat_id, text, reply_markup=ws_rest_day_keyboard())
        temps['workout_menu'] = msg.message_id
        user_temp_messages[user_id] = temps
        return

    # Получаем историю прошлого раза
    weekday = user_weekday(user_id)
    today_key = WEEKDAY_KEY[weekday]
    week_key = get_current_week_session_key(plan_data, plan_data["start_date"], user_id)
    session_key = f"{week_key}_{today_key}"
    today_str = user_today_str(user_id)
    prev_sessions = get_previous_same_session(user_id, session_key, today_str)

    # Строим текст плана
    plan_name = f"Тренировка — {WEEKDAY_RU[weekday]}"
    date_str = user_today_str(user_id, '%d.%m.%Y')
    lines = [f"{plan_name}", f"{date_str}", ""]
    for i, ex in enumerate(today_exercises, 1):
        name = ex.get("exercise", ex.get("name", "?"))
        sets = ex.get("sets", "?")
        reps = ex.get("reps", "?")
        weight = ex.get("weight")
        line = f"{i}. {name}  {sets}×{reps}"
        if weight:
            line += f" @ {weight}кг"
        lines.append(line)

    # Добавляем важное из прошлого раза
    if prev_sessions:
        last = prev_sessions[0]
        last_logs = last.get("logs", [])
        last_date = datetime.strptime(last["date"], "%Y-%m-%d").strftime("%d.%m")
        important = []
        for log in last_logs:
            if log["status"] == "skipped":
                important.append(f"⏭ {log['exercise_name']} — пропущено")
            elif log.get("result") and log["result"].get("note"):
                important.append(f"⚠️ {log['exercise_name']} — {log['result']['note']}")
        if important:
            lines.append(f"\nПрошлый раз ({last_date}):")
            lines.extend(important)

    text = "\n".join(lines)
    await state.set_state(WorkoutSessionState.viewing_plan)
    await state.update_data(session_id=session["id"] if session else None,
                            exercise_index=0, prev_sessions=prev_sessions or [])
    msg = await bot.send_message(chat_id, text, reply_markup=ws_today_keyboard())
    temps['workout_menu'] = msg.message_id
    user_temp_messages[user_id] = temps


# --- Выбор режима ---
@router.callback_query(F.data == "wp_mode_ai")
async def wp_choose_ai(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.set_state(AIPlanState.choosing_goal)
    await callback.message.edit_text(
        "Создание плана тренировок\n\nШаг 1 из 3\nКакая твоя цель?",
        reply_markup=wp_goal_keyboard()
    )
    await callback.answer()

@router.callback_query(F.data == "wp_mode_manual")
async def wp_choose_manual(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.set_state(AIPlanState.entering_manual_plan)
    await callback.message.edit_text(
        "Отправь план одним сообщением в таком формате:\n\n"
        "День недели:\n"
        "Название упражнения - СетыxПовторения(Вес)\n\n"
        "Примеры строк:\n"
        "Жим лёжа - 3x5(110кг)\n"
        "Подтягивания - 3x10(+20кг)\n"
        "Становая тяга - МАХ(120кг)\n"
        "Отжимания - МАХ повторений(20кг)\n"
        "Присед - 2x(от 80кг к 60кг)\n"
        "Тренировка навыков - 40 минут\n\n"
        "Если в один день разные упражнения по неделям:\n"
        "Понедельник:\n"
        "Неделя 1 - Жим лёжа - МАХ(120кг)\n"
        "Неделя 2 - Жим лёжа - 3x5(110кг)\n"
        "Неделя 3 - Жим на наклонной - 3x11(90кг)\n"
        "Разгибания трицепса - 3x12(40кг)\n\n"
        "Упражнения без метки «Неделя N» дублируются во все недели.\n\n"
        "⚠️ Чем точнее формат — тем лучше ИИ разберёт план.",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="🔙 Назад", callback_data="wp_back_to_mode")]
        ])
    )
    await callback.answer()

@router.callback_query(F.data == "wp_back_to_mode")
async def wp_back_to_mode(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.set_state(AIPlanState.choosing_mode)
    name = get_user_name(callback.from_user.id, callback.from_user.first_name)
    await callback.message.edit_text(
        f"{name}, давай настроим тренировки!\n\nСоздать план с ИИ или введёшь свой?",
        reply_markup=wp_mode_keyboard()
    )
    await callback.answer()

# --- Онбординг ИИ ---
@router.callback_query(AIPlanState.choosing_goal, F.data.startswith("wp_goal_"))
async def wp_choose_goal(callback: CallbackQuery, bot: Bot, state: FSMContext):
    goal_map = {"wp_goal_mass": "Набор массы", "wp_goal_loss": "Похудение",
                "wp_goal_strength": "Сила", "wp_goal_fitness": "Общая форма"}
    goal = goal_map.get(callback.data, "Общая форма")
    await state.update_data(wp_goal=goal)
    await state.set_state(AIPlanState.choosing_level)
    await callback.message.edit_text(
        f"Создание плана тренировок\n\nШаг 2 из 3\nТвой уровень подготовки?",
        reply_markup=wp_level_keyboard()
    )
    await callback.answer()

@router.callback_query(F.data == "wp_back_to_goal")
async def wp_back_to_goal(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.set_state(AIPlanState.choosing_goal)
    await callback.message.edit_text(
        "Создание плана тренировок\n\nШаг 1 из 3\nКакая твоя цель?",
        reply_markup=wp_goal_keyboard()
    )
    await callback.answer()

@router.callback_query(AIPlanState.choosing_level, F.data.startswith("wp_level_"))
async def wp_choose_level(callback: CallbackQuery, bot: Bot, state: FSMContext):
    level_map = {"wp_level_beginner": "Новичок", "wp_level_intermediate": "Средний",
                 "wp_level_advanced": "Продвинутый"}
    level = level_map.get(callback.data, "Средний")
    await state.update_data(wp_level=level)
    await state.set_state(AIPlanState.choosing_days_count)
    await callback.message.edit_text(
        "Создание плана тренировок\n\nШаг 3 из 3\nСколько тренировок в неделю готов делать?",
        reply_markup=wp_days_keyboard()
    )
    await callback.answer()

@router.callback_query(F.data == "wp_back_to_level")
async def wp_back_to_level(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.set_state(AIPlanState.choosing_level)
    await callback.message.edit_text(
        "Создание плана тренировок\n\nШаг 2 из 3\nТвой уровень подготовки?",
        reply_markup=wp_level_keyboard()
    )
    await callback.answer()

@router.callback_query(AIPlanState.choosing_days_count, F.data.startswith("wp_days_"))
async def wp_choose_days(callback: CallbackQuery, bot: Bot, state: FSMContext):
    days = int(callback.data.split("_")[2])
    data = await state.get_data()
    goal = data.get("wp_goal", "Общая форма")
    level = data.get("wp_level", "Средний")
    await state.update_data(wp_days=days)
    await state.set_state(AIPlanState.entering_extra_notes)
    await callback.message.edit_text(
        "Есть пожелания или особенности?\n\n"
        "Например: «травма колена», «нет штанги», «только утром»\n"
        "Или нажми Пропустить:",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="Пропустить →", callback_data="wp_notes_skip")],
            [InlineKeyboardButton(text="🔙 Назад", callback_data="wp_back_to_days")]
        ])
    )
    await callback.answer()

@router.callback_query(AIPlanState.entering_extra_notes, F.data == "wp_notes_skip")
async def wp_notes_skip(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.update_data(wp_notes="")
    await _generate_and_show_plan(callback, bot, state)
    await callback.answer()

@router.message(AIPlanState.entering_extra_notes)
async def wp_notes_input(message: Message, bot: Bot, state: FSMContext):
    user_id = message.from_user.id
    try:
        await message.delete()
    except:
        pass
    await state.update_data(wp_notes=message.text.strip())
    temps = user_temp_messages.get(user_id, {})
    msg_id = temps.get("workout_menu")
    class FakeCB:
        def __init__(self):
            self.from_user = message.from_user
            self.message = type("M", (), {
                "chat": message.chat,
                "message_id": msg_id,
                "edit_text": lambda text, **kw: bot.edit_message_text(text, message.chat.id, msg_id, **kw),
            })()
        async def answer(self): pass
    await _generate_and_show_plan(FakeCB(), bot, state)

async def _generate_and_show_plan(callback, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    data = await state.get_data()
    goal = data.get("wp_goal", "Общая форма")
    level = data.get("wp_level", "Средний")
    days = data.get("wp_days", 3)
    notes = data.get("wp_notes", "")
    await state.set_state(AIPlanState.reviewing_plan)
    # Start animation
    phrases = ["Анализирую...", "Ищу пишущую ручку...", "Составляю программу...",
               "Подбираю упражнения...", "Рассчитываю нагрузку...", "Финальные штрихи..."]
    temps = user_temp_messages.get(user_id, {})
    msg_id = temps.get("workout_menu")
    stop_animation = asyncio.Event()
    async def animate():
        i = 0
        while not stop_animation.is_set():
            try:
                await bot.edit_message_text(phrases[i % len(phrases)],
                                             callback.message.chat.id, msg_id)
            except:
                pass
            await asyncio.sleep(2)
            i += 1
    anim_task = asyncio.create_task(animate())
    try:
        plan = await run_in_thread(gemini_generate_plan, goal, level, days, notes)
    finally:
        stop_animation.set()
        anim_task.cancel()
        try:
            await anim_task
        except asyncio.CancelledError:
            pass
    if not plan:
        try:
            await bot.edit_message_text(
                "Не удалось сгенерировать план. Попробуй ещё раз.",
                callback.message.chat.id, msg_id,
                reply_markup=retry_ai_keyboard("generate_plan")
            )
        except:
            pass
        return
    await state.update_data(wp_plan=plan, retry_action="generate_plan")
    text = _format_full_plan(plan, goal, level, days)
    try:
        await bot.edit_message_text(text, callback.message.chat.id, msg_id,
                                     reply_markup=wp_plan_review_keyboard())
    except:
        msg = await bot.send_message(callback.message.chat.id, text,
                                      reply_markup=wp_plan_review_keyboard())
        user_temp_messages.setdefault(user_id, {})['workout_menu'] = msg.message_id

@router.callback_query(F.data == "wp_back_to_days")
async def wp_back_to_days(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.set_state(AIPlanState.choosing_days_count)
    await callback.message.edit_text(
        "Создание плана тренировок\n\nШаг 3 из 3\nСколько тренировок в неделю?",
        reply_markup=wp_days_keyboard()
    )
    await callback.answer()

@router.callback_query(F.data == "wp_plan_regenerate")
async def wp_regenerate(callback: CallbackQuery, bot: Bot, state: FSMContext):
    data = await state.get_data()
    goal = data.get("wp_goal", "Общая форма")
    level = data.get("wp_level", "Средний")
    days = data.get("wp_days", 3)
    await _generate_and_show_plan(callback, bot, state)
    await callback.answer()

@router.callback_query(F.data == "wp_plan_edit")
async def wp_plan_edit_start(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.set_state(AIPlanState.editing_plan)
    await callback.message.edit_text(
        "Что хочешь изменить в плане?\n\nНапиши например:\n"
        "«убери приседания, замени на жим ногами»\n"
        "«добавь кардио в пятницу»",
        reply_markup=wp_edit_keyboard()
    )
    await callback.answer()

@router.callback_query(F.data == "wp_back_to_review")
async def wp_back_to_review(callback: CallbackQuery, bot: Bot, state: FSMContext):
    data = await state.get_data()
    plan = data.get("wp_plan")
    goal = data.get("wp_goal", "")
    level = data.get("wp_level", "")
    days = data.get("wp_days", 3)
    if not plan:
        await callback.answer("Нет плана", show_alert=True)
        return
    await state.set_state(AIPlanState.reviewing_plan)
    text = _format_full_plan(plan, goal, level, days)
    await callback.message.edit_text(text, reply_markup=wp_plan_review_keyboard())
    await callback.answer()

async def _handle_exercise_replace(message: Message, bot: Bot, state: FSMContext):
    user_id = message.from_user.id
    try:
        await message.delete()
    except:
        pass
    data = await state.get_data()
    ex_idx = data.get("wp_edit_ex_idx", 0)
    day_key = data.get("wp_edit_day", "monday")
    old_name = data.get("wp_edit_ex_name", "?")
    new_name = message.text.strip()
    plan_data = get_ai_plan(user_id)
    if not plan_data:
        return
    plan = plan_data.get("plan", {})
    cycle = plan_data.get("cycle_weeks", 1)
    # Replace in all weeks that have this day
    for w in range(1, cycle + 1):
        week_key = f"week_{w}"
        if week_key in plan and day_key in plan[week_key]:
            exs = plan[week_key][day_key]
            if ex_idx < len(exs):
                exs[ex_idx]["exercise"] = new_name
    update_plan_json(user_id, plan)
    await state.clear()
    temps = user_temp_messages.get(user_id, {})
    msg_id = temps.get("workout_menu")
    confirm = f"Заменено: «{old_name}» → «{new_name}»"
    if msg_id:
        try:
            await bot.edit_message_text(confirm, message.chat.id, msg_id,
                                         reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                                             [InlineKeyboardButton(text="🔙 Назад", callback_data="workout_manage_back")]
                                         ]))
            return
        except:
            pass
    msg = await message.answer(confirm, reply_markup=InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Назад", callback_data="workout_manage_back")]
    ]))
    user_temp_messages.setdefault(user_id, {})['workout_menu'] = msg.message_id

@router.message(AIPlanState.editing_plan)
async def wp_plan_edit_input(message: Message, bot: Bot, state: FSMContext):
    data = await state.get_data()
    # Route based on edit mode
    if data.get("wp_edit_mode") == "exercise_replace":
        await _handle_exercise_replace(message, bot, state)
        return
    # Original plan editing logic below

    user_id = message.from_user.id
    try:
        await message.delete()
    except:
        pass
    data = await state.get_data()
    current_plan = data.get("wp_plan")
    temps = user_temp_messages.get(user_id, {})
    edit_msg_id = temps.get("workout_menu")
    stop_upd = asyncio.Event()
    async def animate_upd():
        dots = ["Обновляю план.", "Обновляю план..", "Обновляю план..."]
        i = 0
        while not stop_upd.is_set():
            if edit_msg_id:
                try:
                    await bot.edit_message_text(dots[i % 3], message.chat.id, edit_msg_id)
                except:
                    pass
            await asyncio.sleep(0.8)
            i += 1
    anim_upd = asyncio.create_task(animate_upd())
    try:
        new_plan = await run_in_thread(gemini_edit_plan, current_plan, message.text.strip())
    finally:
        stop_upd.set()
        anim_upd.cancel()
        try:
            await anim_upd
        except asyncio.CancelledError:
            pass
    if not new_plan:
        back_to_workout_kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="🔄 Попробовать снова", callback_data="wp_edit_retry")],
            [InlineKeyboardButton(text="🔙 К тренировкам", callback_data="workout_manage_back")]
        ])
        try:
            await bot.edit_message_text(
                "Не удалось применить изменения. Попробуй сформулировать иначе.",
                message.chat.id, edit_msg_id, reply_markup=back_to_workout_kb
            )
        except:
            pass
        return
    await state.update_data(wp_plan=new_plan)
    await state.set_state(AIPlanState.reviewing_plan)
    goal = data.get("wp_goal", "")
    level = data.get("wp_level", "")
    days = data.get("wp_days", 3)
    text = _format_full_plan(new_plan, goal, level, days)
    try:
        await bot.edit_message_text(text, message.chat.id, edit_msg_id,
                                     reply_markup=wp_plan_review_keyboard())
    except:
        pass

@router.callback_query(F.data == "wp_plan_accept")
async def wp_plan_accept(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    data = await state.get_data()
    plan = data.get("wp_plan")
    if not plan:
        await callback.answer("План не найден. Попробуй сгенерировать заново.", show_alert=True)
        return
    mode = data.get("wp_mode", "ai" if data.get("wp_goal") else "manual")
    goal = data.get("wp_goal", "")
    level = data.get("wp_level", "")
    days = data.get("wp_days", 3)
    cycle_weeks = plan.get("cycle_weeks", 1) if isinstance(plan, dict) else 1
    # Удаляем все старые данные
    delete_all_workout_data(user_id)
    save_ai_plan(user_id, mode, goal, level, days, plan, cycle_weeks)
    await state.clear()
    # Показываем сообщение о сохранении и удаляем его через 2 секунды
    await callback.message.edit_text("✅ План сохранён! Возвращайся когда будешь готов тренироваться.")
    await asyncio.sleep(2)
    await callback.message.delete()
    await show_ai_workout_today(user_id, callback.message.chat.id, bot, state)
    await callback.answer()

# --- Ручной план ---
@router.message(AIPlanState.entering_manual_plan)
async def wp_manual_input(message: Message, bot: Bot, state: FSMContext):
    user_id = message.from_user.id
    raw_text = message.text.strip()
    print(f"[MANUAL INPUT] User {user_id} sent plan: {repr(raw_text[:200])}")
    try:
        await message.delete()
    except:
        pass
    # Сохраняем текст для повтора по кнопке
    await state.update_data(retry_manual_plan_text=raw_text, retry_action="manual_plan")
    temps = user_temp_messages.get(user_id, {})
    msg_id = temps.get("workout_menu")
    print(f"[MANUAL INPUT] msg_id={msg_id}")
    stop_anim = asyncio.Event()
    phrases_m = ["Читаю план...", "Разбираю структуру...", "Определяю дни...",
                 "Считаю подходы...", "Почти готово..."]
    async def animate_m():
        i = 0
        while not stop_anim.is_set():
            if msg_id:
                try:
                    await bot.edit_message_text(phrases_m[i % len(phrases_m)], message.chat.id, msg_id)
                except:
                    pass
            await asyncio.sleep(2)
            i += 1
    anim_m = asyncio.create_task(animate_m())
    try:
        plan = await run_in_thread(gemini_parse_manual_plan, raw_text)
    finally:
        stop_anim.set()
        anim_m.cancel()
        try:
            await anim_m
        except asyncio.CancelledError:
            pass
    
    print(f"[MANUAL INPUT] Parsing result: {'OK' if plan else 'FAILED'}")
    
    if not plan:
        print(f"[MANUAL INPUT] Trying fallback parser...")
        # Always try to generate something - ask ИИ to do best effort
        plan = await run_in_thread(_fallback_parse_plan, raw_text)
        print(f"[MANUAL INPUT] Fallback result: {'OK' if plan else 'FAILED'}")
    
    if not plan:
        print(f"[MANUAL INPUT] Both parsers failed, showing error to user")
        # Удаляем анимационное сообщение
        if msg_id:
            await delete_message_safe(bot, message.chat.id, msg_id)
        try:
            err_msg = await message.answer(
                "❌ Не смог разобрать план. Можно скинуть тот же текст — я попробую снова.",
                reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                    [InlineKeyboardButton(text="🔄 Попробовать снова",
                                          callback_data="retry_ai:manual_plan")],
                    [InlineKeyboardButton(text="🔙 Назад", callback_data="workout_manage_back")]
                ])
            )
            user_temp_messages.setdefault(user_id, {})['workout_error'] = err_msg.message_id
        except Exception as e:
            print(f"[MANUAL INPUT] Error sending error message: {e}")
        return
    
    print(f"[MANUAL INPUT] Plan parsed successfully, cycle_weeks={plan.get('cycle_weeks')}")
    await state.update_data(wp_plan=plan, wp_mode="manual",
                            wp_goal="", wp_level="", wp_days=0)
    await state.set_state(AIPlanState.reviewing_plan)
    text = _format_full_plan(plan, "", "", 0)
    print(f"[MANUAL INPUT] Formatted plan text ({len(text)} chars): {text[:500]}")
    
    # Пробуем отредактировать существующее сообщение или отправить новое
    if msg_id:
        try:
            await bot.edit_message_text(text, message.chat.id, msg_id,
                                         reply_markup=wp_plan_review_keyboard_manual())
            print(f"[MANUAL INPUT] Successfully edited message {msg_id}")
        except Exception as e:
            print(f"[MANUAL INPUT] Edit failed ({type(e).__name__}: {e}), sending new message")
            # Если не удалось отредактировать - отправляем новое сообщение
            new_msg = await message.answer(text, reply_markup=wp_plan_review_keyboard_manual())
            # Обновляем msg_id в temp messages
            temps['workout_menu'] = new_msg.message_id
            user_temp_messages[user_id] = temps
    else:
        print(f"[MANUAL INPUT] No msg_id, sending new message")
        new_msg = await message.answer(text, reply_markup=wp_plan_review_keyboard_manual())
        temps = user_temp_messages.setdefault(user_id, {})
        temps['workout_menu'] = new_msg.message_id

# ============ ТРЕНИРОВКА — ФЛОУ ============

@router.callback_query(F.data == "workout_main_ai")
async def workout_main_ai_callback(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    await state.clear()
    try:
        await callback.message.delete()
    except:
        pass
    await show_ai_workout_today(user_id, callback.message.chat.id, bot, state)
    await callback.answer()

@router.callback_query(F.data == "back_to_workout_main")
async def back_to_workout_main_callback(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    await state.clear()
    try:
        await callback.message.delete()
    except:
        pass
    await show_workout_main_menu(user_id, callback.message.chat.id, bot)
    await callback.answer()

async def _ws_start_workout(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    data = await state.get_data()
    session_id = data.get("session_id")
    plan_data = get_ai_plan(user_id)
    session = get_today_session(user_id)
    if not session:
        try:
            await callback.answer("Сессия не найдена", show_alert=True)
        except:
            pass
        return
    exercises = session["plan"]
    if isinstance(exercises, dict):
        exercises = list(exercises.values())
    await state.update_data(exercises=exercises, exercise_index=0,
                            session_id=session["id"])
    await state.set_state(WorkoutSessionState.in_exercise)
    await _show_exercise(callback.message, bot, state, user_id, 0, exercises)

async def _show_exercise(message, bot: Bot, state: FSMContext,
                          user_id: int, index: int, exercises: list):
    """Редактирует сообщение показывая текущее упражнение."""
    ex = exercises[index]
    total = len(exercises)
    name = ex.get("exercise", ex.get("name", "?"))
    sets = ex.get("sets", "?")
    reps = ex.get("reps", "?")
    weight = ex.get("weight")

    # Ищем результат предыдущего раза
    data = await state.get_data()
    prev_sessions = data.get("prev_sessions", [])
    prev_result = None
    if prev_sessions:
        last_logs = prev_sessions[0].get("logs", [])
        for log in last_logs:
            if log.get("exercise_name") == name and log.get("result"):
                prev_result = log["result"]
                break

    text = f"Упражнение {index + 1} из {total}\n\n"
    text += f"{name}\n"
    text += f"Цель: {sets} подхода × {reps} повторений"
    if weight:
        text += f" @ {weight} кг"
    if prev_result:
        text += "\n\nПрошлый раз: "
        if prev_result.get("sets_done"):
            text += f"{prev_result['sets_done']}×{prev_result.get('reps_done','?')}"
        if prev_result.get("weight_done"):
            text += f" @ {prev_result['weight_done']} кг"
        if prev_result.get("note"):
            text += f" ({prev_result['note']})"
    text += "\n\nНапиши что сделал или нажми кнопку:"

    await state.set_state(WorkoutSessionState.in_exercise)
    temps = user_temp_messages.get(user_id, {})
    msg_id = temps.get("workout_menu")
    if msg_id:
        try:
            await bot.edit_message_text(text, message.chat.id, msg_id,
                                         reply_markup=ws_exercise_keyboard(is_first=(index == 0)))
            return
        except:
            pass
    msg = await message.answer(text, reply_markup=ws_exercise_keyboard(is_first=(index == 0)))
    temps["workout_menu"] = msg.message_id
    user_temp_messages[user_id] = temps

@router.callback_query(WorkoutSessionState.in_exercise, F.data == "ws_ex_done")
async def ws_exercise_done(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    data = await state.get_data()
    exercises = data.get("exercises", [])
    index = data.get("exercise_index", 0)
    session_id = data.get("session_id")
    ex = exercises[index]
    # Записываем как выполнено по плану
    result = {"sets_done": ex.get("sets"), "reps_done": ex.get("reps"),
               "weight_done": ex.get("weight"), "completed": True, "note": None}
    db.execute("""
        INSERT INTO ai_exercise_logs (session_id, user_id, exercise_name, planned_json, result_json, status)
        VALUES (?, ?, ?, ?, ?, 'done')
    """, (session_id, user_id, ex.get("exercise", ex.get("name")),
           json.dumps(ex, ensure_ascii=False), json.dumps(result, ensure_ascii=False)))
    db.commit()
    await state.update_data(exercise_index=index + 1)
    await _next_exercise_or_finish(callback, bot, state, user_id)
    await callback.answer()

@router.callback_query(WorkoutSessionState.in_exercise, F.data == "ws_ex_skip")
async def ws_exercise_skip(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    data = await state.get_data()
    exercises = data.get("exercises", [])
    index = data.get("exercise_index", 0)
    session_id = data.get("session_id")
    ex = exercises[index]
    db.execute("""
        INSERT INTO ai_exercise_logs (session_id, user_id, exercise_name, planned_json, status)
        VALUES (?, ?, ?, ?, 'skipped')
    """, (session_id, user_id, ex.get("exercise", ex.get("name")),
           json.dumps(ex, ensure_ascii=False)))
    db.commit()
    await state.update_data(exercise_index=index + 1)
    await _next_exercise_or_finish(callback, bot, state, user_id)
    await callback.answer()

@router.callback_query(WorkoutSessionState.in_exercise, F.data == "ws_ex_prev")
async def ws_exercise_prev(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    data = await state.get_data()
    index = data.get("exercise_index", 0)
    session_id = data.get("session_id")
    if index <= 0:
        await callback.answer("Это первое упражнение", show_alert=True)
        return
    # Удаляем последний лог
    db.execute("""
        DELETE FROM ai_exercise_logs WHERE session_id = ? AND user_id = ?
        AND id = (SELECT MAX(id) FROM ai_exercise_logs WHERE session_id = ? AND user_id = ?)
    """, (session_id, user_id, session_id, user_id))
    db.commit()
    new_index = index - 1
    await state.update_data(exercise_index=new_index)
    exercises = data.get("exercises", [])
    await _show_exercise(callback.message, bot, state, user_id, new_index, exercises)
    await callback.answer()

@router.message(WorkoutSessionState.in_exercise)
async def ws_exercise_text_input(message: Message, bot: Bot, state: FSMContext):
    user_id = message.from_user.id
    try:
        await message.delete()
    except:
        pass
    data = await state.get_data()
    exercises = data.get("exercises", [])
    index = data.get("exercise_index", 0)
    session_id = data.get("session_id")
    ex = exercises[index]
    temps = user_temp_messages.get(user_id, {})
    msg_id = temps.get("workout_menu")
    if msg_id:
        try:
            await bot.edit_message_text("Записываю...", message.chat.id, msg_id)
        except:
            pass
    result = await run_in_thread(gemini_parse_exercise_result, ex, message.text.strip())
    db.execute("""
        INSERT INTO ai_exercise_logs
        (session_id, user_id, exercise_name, planned_json, raw_input, result_json, status)
        VALUES (?, ?, ?, ?, ?, ?, 'done')
    """, (session_id, user_id, ex.get("exercise", ex.get("name")),
           json.dumps(ex, ensure_ascii=False), message.text.strip(),
           json.dumps(result, ensure_ascii=False)))
    db.commit()
    await state.update_data(exercise_index=index + 1)
    # Передаём message для edit через фейк
    class FakeCallback:
        def __init__(self, msg, uid):
            self.message = msg
            self.from_user = type("U", (), {"id": uid})()
        async def answer(self): pass
    fake = FakeCallback(message, user_id)
    await _next_exercise_or_finish(fake, bot, state, user_id)

async def _next_exercise_or_finish(callback, bot: Bot, state: FSMContext, user_id: int):
    data = await state.get_data()
    exercises = data.get("exercises", [])
    index = data.get("exercise_index", 0)
    if index < len(exercises):
        await _show_exercise(callback.message, bot, state, user_id, index, exercises)
    else:
        await _finish_workout(callback.message, bot, state, user_id)

async def _finish_workout(message, bot: Bot, state: FSMContext, user_id: int):
    data = await state.get_data()
    session_id = data.get("session_id")
    exercises = data.get("exercises", [])
    today = user_today_str(user_id)

    # Помечаем сессию как выполненную
    db.execute("UPDATE ai_workout_sessions SET status='done', completed_at=? WHERE id=?",
               (today, session_id))
    db.commit()

    logs = get_session_exercise_logs(session_id)
    done = [l for l in logs if l["status"] == "done"]
    skipped = [l for l in logs if l["status"] == "skipped"]

    # Фидбек от ИИ
    feedback = await run_in_thread(gemini_session_feedback, logs, exercises)

    # Адаптируем план
    prev_sessions = data.get("prev_sessions", [])
    adapted = await run_in_thread(gemini_adapt_next_session, exercises, logs, prev_sessions)
    if adapted != exercises:
        session = get_today_session(user_id)
        if session:
            update_session_exercise_plan(user_id, session_id,
                                          session.get("session_key", ""), adapted)

    # Обновляем счётчик тренировок
    add_workout(user_id)
    success, _, rank_up, _, new_rank = add_spark(user_id, "workout")
    update_streak(user_id)
    asyncio.create_task(run_in_thread(sync_activity_rating_for_today, user_id))

    # Строим итоговое сообщение
    lines = ["Тренировка завершена\n"]
    for log in logs:
        if log["status"] == "skipped":
            lines.append(f"⏭ {log['exercise_name']} — пропущено")
        elif log.get("result") and log["result"].get("note"):
            lines.append(f"⚠️ {log['exercise_name']} — {log['result']['note']}")

    feedback_failed = feedback.startswith("❌")
    if feedback_failed:
        lines.append("\n❌ ИИ не смог подготовить фидбек.")
    else:
        lines.append(f"\n{feedback}")

    plan_data = get_ai_plan(user_id)
    next_date, next_day = get_next_training_day(plan_data, user_id) if plan_data else (None, None)
    if next_date:
        lines.append(f"\nСледующая тренировка: {next_day}, {next_date}")
    if rank_up:
        lines.append(f"\n✨ Новый ранг: {get_rank_name(new_rank)}!")

    text = "\n".join(lines)
    # Кнопка повтора фидбека (без ретипинга) — данные сессии уже сохранены
    finish_kb = retry_ai_keyboard("session_feedback") if feedback_failed else ws_rest_day_keyboard()
    await state.clear()
    # Сохраняем после clear() — данные нужны для повтора фидбека
    await state.update_data(retry_session_id=session_id,
                            retry_session_exercises=exercises)
    temps = user_temp_messages.get(user_id, {})
    msg_id = temps.get("workout_menu")
    if msg_id:
        try:
            await bot.edit_message_text(text, message.chat.id, msg_id,
                                         reply_markup=finish_kb)
            return
        except:
            pass
    msg = await message.answer(text, reply_markup=finish_kb)
    temps["workout_menu"] = msg.message_id
    user_temp_messages[user_id] = temps

async def _retry_session_feedback(callback, bot, state):
    """Повторно генерирует ИИ-фидбек по завершённой тренировке."""
    data = await state.get_data()
    session_id = data.get("retry_session_id")
    exercises = data.get("retry_session_exercises") or []
    user_id = callback.from_user.id
    if not session_id:
        await callback.answer("Данные тренировки не найдены", show_alert=True)
        return
    await bot.send_chat_action(callback.message.chat.id, action=ChatAction.TYPING)
    logs = get_session_exercise_logs(session_id)
    feedback = await run_in_thread(gemini_session_feedback, logs, exercises)
    if feedback.startswith("❌"):
        await callback.message.edit_text(
            "❌ ИИ снова не смог подготовить фидбек.\n\n"
            "🔄 Нажми кнопку чтобы попробовать ещё раз.",
            reply_markup=retry_ai_keyboard("session_feedback")
        )
        await callback.answer()
        return
    lines = ["Тренировка завершена\n"]
    for log in logs:
        if log["status"] == "skipped":
            lines.append(f"⏭ {log['exercise_name']} — пропущено")
        elif log.get("result") and log["result"].get("note"):
            lines.append(f"⚠️ {log['exercise_name']} — {log['result']['note']}")
    lines.append(f"\n{feedback}")
    plan_data = get_ai_plan(user_id)
    next_date, next_day = get_next_training_day(plan_data, user_id) if plan_data else (None, None)
    if next_date:
        lines.append(f"\nСледующая тренировка: {next_day}, {next_date}")
    rank_data = get_or_create_rank_data(user_id)
    if rank_data:
        lines.append(f"\n✨ Текущий ранг: {get_rank_name(rank_data['current_rank'])}!")
    await callback.message.edit_text("\n".join(lines),
                                      reply_markup=ws_rest_day_keyboard())
    await callback.answer()

# --- Пропуск дня ---
@router.callback_query(F.data == "ws_skip_day")
async def ws_skip_day_start(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.set_state(WorkoutSessionState.skipping_day)
    temps = user_temp_messages.get(callback.from_user.id, {})
    msg_id = temps.get("workout_menu")
    text = "Почему пропускаешь тренировку? Напиши кратко (или просто отправь «-»):"
    if msg_id:
        try:
            await callback.message.edit_text(text, reply_markup=ws_skip_day_keyboard())
            await callback.answer()
            return
        except:
            pass
    msg = await callback.message.answer(text, reply_markup=ws_skip_day_keyboard())
    temps["workout_menu"] = msg.message_id
    user_temp_messages[callback.from_user.id] = temps
    await callback.answer()

@router.callback_query(WorkoutSessionState.skipping_day, F.data == "ws_back_to_today")
async def ws_back_to_today(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.clear()
    user_id = callback.from_user.id
    try:
        await callback.message.delete()
    except:
        pass
    temps = user_temp_messages.get(user_id, {})
    temps.pop("workout_menu", None)
    user_temp_messages[user_id] = temps
    await show_ai_workout_today(user_id, callback.message.chat.id, bot, state)
    await callback.answer()

@router.message(WorkoutSessionState.skipping_day)
async def ws_skip_day_reason(message: Message, bot: Bot, state: FSMContext):
    user_id = message.from_user.id
    reason = message.text.strip() if message.text.strip() != "-" else ""
    try:
        await message.delete()
    except:
        pass
    plan_data = get_ai_plan(user_id)
    if plan_data:
        session = create_today_session(user_id, plan_data)
        if session:
            db.execute("""
                UPDATE ai_workout_sessions SET status='skipped', skip_reason=? WHERE id=?
            """, (reason, session["id"]))
            db.commit()
    await state.clear()
    # Отнимаем искру за пропущенный тренировочный день
    _deduct_spark_for_skip(user_id)
    temps = user_temp_messages.get(user_id, {})
    msg_id = temps.get("workout_menu")
    text = "День пропущен."
    plan_data = get_ai_plan(user_id)
    next_date, next_day = get_next_training_day(plan_data, user_id) if plan_data else (None, None)
    if next_date:
        text += f"\nСледующая тренировка: {next_day}, {next_date}"
    if msg_id:
        try:
            await bot.edit_message_text(text, message.chat.id, msg_id,
                                         reply_markup=ws_rest_day_keyboard())
            return
        except:
            pass
    msg = await message.answer(text, reply_markup=ws_rest_day_keyboard())
    temps["workout_menu"] = msg.message_id
    user_temp_messages[user_id] = temps

# --- Настройки плана ---
@router.callback_query(F.data == "wp_settings")
async def wp_settings(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await callback.message.edit_text("Настройки плана тренировок:",
                                      reply_markup=wp_settings_keyboard())
    await callback.answer()

@router.callback_query(F.data == "wp_reset")
async def wp_reset(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    delete_all_workout_data(user_id)
    await state.clear()
    name = get_user_name(user_id, callback.from_user.first_name)
    await callback.message.edit_text(
        f"{name}, давай настроим тренировки!\n\nСоздать план с ИИ или введёшь свой?",
        reply_markup=wp_mode_keyboard()
    )
    await callback.answer()

# --- Месячный пересмотр ---
@router.callback_query(F.data == "wp_monthly_review")
async def wp_monthly_review_start(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    await callback.message.edit_text("Анализирую прогресс...")
    plan_data = get_ai_plan(user_id)
    if not plan_data:
        await callback.answer("Нет плана", show_alert=True)
        return
    cursor = db.execute("""
        SELECT date, plan_json, status FROM ai_workout_sessions
        WHERE user_id = ? ORDER BY date DESC LIMIT 20
    """, (user_id,))
    recent = []
    for row in cursor.fetchall():
        recent.append({"date": row[0], "status": row[2]})
    await state.update_data(retry_action="monthly_review")
    changes = await run_in_thread(gemini_monthly_review, plan_data["plan"], recent)
    if not changes:
        # Реальная ошибка ИИ — предлагаем повторить (не путать с «менять не нужно»)
        await callback.message.edit_text(
            "❌ Не удалось проанализировать прогресс.\n\n"
            "🔄 Нажми кнопку чтобы попробовать ещё раз.",
            reply_markup=retry_ai_keyboard("monthly_review")
        )
        await callback.answer()
        return
    if changes.get("no_changes_needed") or not changes.get("changes"):
        await callback.message.edit_text(
            "Менять ничего не нужно — план хорошо сбалансирован.",
            reply_markup=wp_settings_keyboard()
        )
        await callback.answer()
        return
    chg = changes["changes"]
    await state.set_state(WorkoutSessionState.monthly_review)
    await state.update_data(review_changes=chg)
    lines = ["Предлагаю заменить упражнения:\n"]
    for i, ch in enumerate(chg, 1):
        lines.append(f"{i}. {ch['old_exercise']} → {ch['new_exercise']}\n   {ch['reason']}")
    lines.append("\nНапиши номера изменений которые принять (например: 1 3) или «нет» чтобы отклонить всё:")
    await callback.message.edit_text("\n".join(lines),
                                      reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                                          [InlineKeyboardButton(text="🔙 Назад",
                                                                callback_data="wp_review_decline")]
                                      ]))
    await callback.answer()

@router.message(WorkoutSessionState.monthly_review)
async def wp_monthly_review_input(message: Message, bot: Bot, state: FSMContext):
    user_id = message.from_user.id
    try:
        await message.delete()
    except:
        pass
    data = await state.get_data()
    changes = data.get("review_changes", [])
    text = message.text.strip().lower()
    if text in ("нет", "no", "-"):
        await state.clear()
        await bot.send_message(message.chat.id, "Изменения отклонены. План остаётся прежним.",
                                reply_markup=wp_settings_keyboard())
        return
    try:
        indices = [int(x) - 1 for x in text.split() if x.isdigit()]
    except:
        indices = []
    if not indices:
        await bot.send_message(message.chat.id,
                                "Не понял. Напиши номера через пробел или «нет».")
        return
    plan_data = get_ai_plan(user_id)
    if plan_data:
        new_plan = apply_monthly_changes(user_id, plan_data, indices, changes)
        update_plan_json(user_id, new_plan)
        today = user_today_str(user_id)
        db.execute("UPDATE ai_workout_plan SET last_monthly_review=? WHERE user_id=?",
                   (today, user_id))
        db.commit()
    await state.clear()
    accepted = [changes[i]["old_exercise"] + " → " + changes[i]["new_exercise"]
                for i in indices if i < len(changes)]
    await bot.send_message(message.chat.id,
                            f"Принято: {', '.join(accepted)}\nПлан обновлён.",
                            reply_markup=wp_settings_keyboard())

@router.callback_query(F.data == "wp_review_decline")
async def wp_review_decline(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.clear()
    await callback.message.edit_text("Изменения отклонены.",
                                      reply_markup=wp_settings_keyboard())
    await callback.answer()

# --- Вспомогательная функция форматирования полного плана ---
def _format_full_plan(plan: dict, goal: str, level: str, days: int) -> str:
    print(f"[FORMAT_PLAN] Input: cycle_weeks={plan.get('cycle_weeks')}, keys={[k for k in plan.keys() if 'week' in k]}")
    lines = []
    if goal:
        lines.append(f"Твой план — {goal}, {level}\n")
    
    cycle = plan.get("cycle_weeks", 1)
    if not cycle or cycle < 1:
        print(f"[FORMAT_PLAN] WARNING: Invalid cycle_weeks={cycle}, defaulting to 1")
        cycle = 1
    
    for w in range(1, cycle + 1):
        week_key = f"week_{w}"
        week = plan.get(week_key, {})
        print(f"[FORMAT_PLAN] Week {w}: found={bool(week)}, days={list(week.keys()) if week else 'none'}")
        if not week:
            continue
        if cycle > 1:
            lines.append(f"Неделя {w}:")
        day_order = ["monday","tuesday","wednesday","thursday","friday","saturday","sunday"]
        day_names = {"monday":"Пн","tuesday":"Вт","wednesday":"Ср","thursday":"Чт",
                     "friday":"Пт","saturday":"Сб","sunday":"Вс"}
        for day_key in day_order:
            exs = week.get(day_key)
            if not exs:
                continue
            lines.append(f"\n{day_names[day_key]}:")
            for ex in exs:
                name = ex.get("exercise", ex.get("name", "?"))
                sets = ex.get("sets","?")
                reps = ex.get("reps","?")
                weight = ex.get("weight")
                line = f"  {name}  {sets}×{reps}"
                if weight:
                    line += f" @ {weight}кг"
                lines.append(line)
    
    result = "\n".join(lines)
    if not result:
        print(f"[FORMAT_PLAN] WARNING: Empty result! Plan structure: {plan}")
    else:
        print(f"[FORMAT_PLAN] Output ({len(lines)} lines): {result[:200]}")
    return result


# ---------- Управление категориями и упражнениями ----------
async def _do_workout_manage(user_id: int, chat_id: int, bot: Bot):
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, chat_id, temps.get('workout_menu'))
    if 'workout_menu' in temps:
        del temps['workout_menu']
    cursor = db.execute('SELECT id, name FROM exercise_categories WHERE user_id = ? ORDER BY name', (user_id,))
    categories = cursor.fetchall()
    msg = await bot.send_message(chat_id, "📋 Мои категории:", reply_markup=workout_categories_keyboard(categories, action="manage"))
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id


@router.message(F.text == "📋 Управление")
async def workout_manage_msg(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    user_id = message.from_user.id
    plan_data = get_ai_plan(user_id)
    if not plan_data:
        await message.answer("План не настроен. Зайди в «🏋️ Добавить выполнение» чтобы создать.",
                              reply_markup=workout_main_keyboard())
        return
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, temps.pop('workout_menu', None))
    user_temp_messages[user_id] = temps
    mode = plan_data.get("mode", "ai") if plan_data else "ai"
    msg = await message.answer("Управление планом:", reply_markup=workout_manage_reply_keyboard(mode))
    user_temp_messages.setdefault(user_id, {})['workout_menu'] = msg.message_id

@router.message(F.text == "✏️ Редактировать план (ИИ)")
async def workout_edit_plan_msg(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    user_id = message.from_user.id
    plan_data = get_ai_plan(user_id)
    if not plan_data:
        return
    await state.set_state(AIPlanState.editing_plan)
    await state.update_data(wp_plan=plan_data["plan"], wp_goal=plan_data.get("goal",""),
                            wp_level=plan_data.get("level",""), wp_days=plan_data.get("days_per_week",3))
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, temps.pop('workout_menu', None))
    msg = await message.answer(
        "Что изменить в плане?\n\nНапример:\n«убери приседания, замени на жим ногами»\n«добавь кардио в пятницу»",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="🔙 Назад", callback_data="workout_manage_back")]
        ])
    )
    user_temp_messages.setdefault(user_id, {})['workout_menu'] = msg.message_id

@router.message(F.text == "🆕 Новый план (ИИ)")
async def workout_new_ai_plan_msg(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    user_id = message.from_user.id
    name = get_user_name(user_id, message.from_user.first_name)
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, temps.pop('workout_menu', None))
    await state.set_state(AIPlanState.choosing_goal)
    msg = await message.answer(
        f"{name}, создаём новый план с нуля.\n\nШаг 1 из 3\nКакая твоя цель?",
        reply_markup=wp_goal_keyboard()
    )
    user_temp_messages.setdefault(user_id, {})['workout_menu'] = msg.message_id

@router.message(F.text == "📝 Загрузить свой план")
async def workout_replace_plan_msg(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    user_id = message.from_user.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, temps.pop('workout_menu', None))
    await delete_message_safe(bot, message.chat.id, temps.pop('workout_error', None))
    await state.set_state(AIPlanState.entering_manual_plan)
    msg = await message.answer(
        "Отправь план одним сообщением в таком формате:\n\n"
        "День недели:\n"
        "Название упражнения - СетыxПовторения(Вес)\n\n"
        "Примеры строк:\n"
        "Жим лёжа - 3x5(110кг)\n"
        "Подтягивания - 3x10(+20кг)\n"
        "Становая тяга - МАХ(120кг)\n"
        "Отжимания - МАХ повторений(20кг)\n"
        "Присед - 2x(от 80кг к 60кг)\n"
        "Тренировка навыков - 40 минут\n\n"
        "Если в один день разные упражнения по неделям:\n"
        "Понедельник:\n"
        "Неделя 1 - Жим лёжа - МАХ(120кг)\n"
        "Неделя 2 - Жим лёжа - 3x5(110кг)\n"
        "Неделя 3 - Жим на наклонной - 3x11(90кг)\n"
        "Разгибания трицепса - 3x12(40кг)\n\n"
        "Упражнения без метки «Неделя N» дублируются во все недели.\n\n"
        "⚠️ Чем точнее формат — тем лучше ИИ разберёт план.",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="🔙 Назад", callback_data="workout_manage_back")]
        ])
    )
    user_temp_messages.setdefault(user_id, {})['workout_menu'] = msg.message_id

@router.message(F.text == "🔙 Назад к тренировкам")
async def back_to_workout_main(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    await state.clear()
    await show_workout_main_menu(message.from_user.id, message.chat.id, bot)

@router.callback_query(F.data == "workout_manage_back")
async def workout_manage_back_cb(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.clear()
    user_id = callback.from_user.id
    try:
        await callback.message.delete()
    except:
        pass
    await show_workout_main_menu(user_id, callback.message.chat.id, bot)
    await callback.answer()



@router.callback_query(F.data == "workout_manage")
async def workout_manage(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    await callback.message.delete()
    await _do_workout_manage(user_id, callback.message.chat.id, bot)
    await callback.answer()

@router.callback_query(F.data == "workout_main")
async def workout_main_callback(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.clear()
    await callback.message.delete()
    await show_workout_main_menu(callback.from_user.id, callback.message.chat.id, bot)
    await callback.answer()

@router.callback_query(F.data == "w_cat_new")
async def workout_new_category(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    await callback.message.delete()
    await state.set_state(WorkoutState.creating_category)
    msg = await callback.message.answer(
        "Введи название новой категории (например, 'Грудь', 'Кардио'):"
    )
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.message(WorkoutState.creating_category)
async def workout_create_category(message: Message, bot: Bot, state: FSMContext):
    user_id = message.from_user.id
    cat_name = message.text.strip()
    if len(cat_name) < 2:
        await message.answer("❌ Слишком короткое название. Попробуй ещё раз:")
        return
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, message.message_id)
    await delete_message_safe(bot, message.chat.id, temps.get('workout_temp'))
    await state.update_data(new_cat_name=cat_name)
    msg = await message.answer(
        f"Тип категории «{cat_name}»:",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="💪 Силовая", callback_data="cat_type_strength")],
            [InlineKeyboardButton(text="🚴 Кардио", callback_data="cat_type_cardio")],
        ])
    )
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id

@router.callback_query(F.data.in_({"cat_type_strength", "cat_type_cardio"}))
async def workout_create_category_type(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    ex_type = 'strength' if callback.data == 'cat_type_strength' else 'cardio'
    data = await state.get_data()
    cat_name = data.get('new_cat_name', '').strip()
    await state.clear()
    await callback.message.delete()
    if not cat_name:
        await workout_manage_after_action(user_id, callback.message.chat.id, bot)
        await callback.answer()
        return
    try:
        db.execute('INSERT INTO exercise_categories (user_id, name, ex_type) VALUES (?, ?, ?)', (user_id, cat_name, ex_type))
        db.commit()
    except sqlite3.IntegrityError:
        await callback.answer("❌ Такая категория уже существует.", show_alert=True)
    await workout_manage_after_action(user_id, callback.message.chat.id, bot)
    await callback.answer()

async def workout_manage_after_action(user_id: int, chat_id: int, bot: Bot):
    temps = user_temp_messages.get(user_id, {})
    old = temps.pop('workout_temp', None)
    if old:
        await delete_message_safe(bot, chat_id, old)
    cursor = db.execute('SELECT id, name FROM exercise_categories WHERE user_id = ? ORDER BY name', (user_id,))
    categories = cursor.fetchall()
    msg = await bot.send_message(chat_id, "📋 Мои категории:", reply_markup=workout_categories_keyboard(categories, action="manage"))
    temps['workout_temp'] = msg.message_id
    user_temp_messages[user_id] = temps

@router.callback_query(F.data.startswith("w_manage_cat_"))
async def workout_manage_view_category(callback: CallbackQuery, bot: Bot, state: FSMContext):
    cat_id = int(callback.data.split("_")[3])
    user_id = callback.from_user.id
    await callback.message.delete()
    cursor = db.execute('SELECT name FROM exercise_categories WHERE id = ?', (cat_id,))
    row = cursor.fetchone()
    if not row:
        await callback.message.answer("❌ Категория не найдена.")
        await workout_manage(callback, bot, state)
        await callback.answer()
        return
    cat_name = row[0]
    await state.update_data(current_cat_id=cat_id)
    msg = await callback.message.answer(f"Категория: {cat_name}", reply_markup=workout_category_actions_keyboard(cat_id))
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.callback_query(F.data.startswith("w_cat_rename_"))
async def workout_rename_category(callback: CallbackQuery, bot: Bot, state: FSMContext):
    cat_id = int(callback.data.split("_")[3])
    await state.update_data(renaming_cat_id=cat_id)
    await callback.message.delete()
    await state.set_state(WorkoutState.renaming_category)
    msg = await callback.message.answer("Введи новое название для категории:")
    user_temp_messages.setdefault(callback.from_user.id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.message(WorkoutState.renaming_category)
async def workout_rename_category_finish(message: Message, bot: Bot, state: FSMContext):
    user_id = message.from_user.id
    new_name = message.text.strip()
    if len(new_name) < 2:
        await message.answer("❌ Слишком короткое название. Попробуй ещё раз:")
        return
    data = await state.get_data()
    cat_id = data.get('renaming_cat_id')
    await state.clear()
    try:
        await message.delete()
    except:
        pass
    if not cat_id:
        await workout_manage_after_action(user_id, message.chat.id, bot)
        return
    try:
        db.execute('UPDATE exercise_categories SET name = ? WHERE id = ? AND user_id = ?', (new_name, cat_id, user_id))
        db.commit()
    except sqlite3.IntegrityError:
        await message.answer("❌ Категория с таким именем уже существует.")
    await workout_manage_after_action(user_id, message.chat.id, bot)

@router.callback_query(F.data.regexp(r'^w_cat_delete_\d+$'))
async def workout_delete_category_confirm(callback: CallbackQuery, bot: Bot, state: FSMContext):
    cat_id = int(callback.data.split("_")[3])
    await state.update_data(deleting_cat_id=cat_id)
    await callback.message.delete()
    await state.set_state(WorkoutState.deleting_category_confirm)
    msg = await callback.message.answer(
        "⚠️ Ты уверен, что хочешь удалить эту категорию? Все упражнения внутри тоже будут удалены.",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="✅ Да, удалить", callback_data="w_cat_delete_yes"),
             InlineKeyboardButton(text="❌ Нет", callback_data="workout_manage")]
        ])
    )
    user_temp_messages.setdefault(callback.from_user.id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.callback_query(F.data == "w_cat_delete_yes", WorkoutState.deleting_category_confirm)
async def workout_delete_category_finish(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    data = await state.get_data()
    cat_id = data.get('deleting_cat_id')
    if not cat_id:
        await state.clear()
        await workout_manage_after_action(user_id, callback.message.chat.id, bot)
        await callback.answer()
        return
    db.execute('DELETE FROM exercise_categories WHERE id = ? AND user_id = ?', (cat_id, user_id))
    db.commit()
    await state.clear()
    await callback.message.delete()
    success_msg = await callback.message.answer("✅ Категория удалена.")
    await asyncio.sleep(2)
    await delete_message_safe(bot, callback.message.chat.id, success_msg.message_id)
    await workout_manage_after_action(user_id, callback.message.chat.id, bot)
    await callback.answer()

@router.callback_query(F.data.regexp(r'^w_manage_exercises_\d+$'))
async def workout_manage_exercises(callback: CallbackQuery, bot: Bot, state: FSMContext):
    cat_id = int(callback.data.split("_")[3])
    user_id = callback.from_user.id
    await callback.message.delete()
    cursor = db.execute('SELECT name FROM exercise_categories WHERE id = ?', (cat_id,))
    cat_row = cursor.fetchone()
    if not cat_row:
        await callback.message.answer("❌ Категория не найдена.")
        await workout_manage(callback, bot, state)
        await callback.answer()
        return
    cat_name = cat_row[0]
    ex_cursor = db.execute('SELECT id, name FROM exercises WHERE user_id = ? AND category_id = ? ORDER BY name', (user_id, cat_id))
    exercises = ex_cursor.fetchall()
    await state.update_data(current_cat_id=cat_id)
    msg = await callback.message.answer(
        f"Упражнения в категории '{cat_name}':",
        reply_markup=workout_exercises_keyboard(exercises, cat_id, action="manage")
    )
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.callback_query(F.data == "w_back_to_cats_from_ex")
async def workout_back_to_cats_from_ex(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    await callback.message.delete()
    cursor = db.execute('SELECT id, name FROM exercise_categories WHERE user_id = ? ORDER BY name', (user_id,))
    categories = cursor.fetchall()
    await state.set_state(WorkoutState.choosing_category)
    msg = await callback.message.answer(
        "Выбери категорию упражнения:",
        reply_markup=workout_categories_keyboard(categories, action="add")
    )
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.callback_query(F.data == "w_back_to_ex_from_actions")
async def workout_back_to_ex_from_actions(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await workout_manage(callback, bot, state)

@router.callback_query(F.data.startswith("w_manage_ex_"))
async def workout_manage_view_exercise(callback: CallbackQuery, bot: Bot, state: FSMContext):
    ex_id = int(callback.data.split("_")[3])
    user_id = callback.from_user.id
    await callback.message.delete()
    cursor = db.execute('SELECT name, category_id FROM exercises WHERE id = ?', (ex_id,))
    row = cursor.fetchone()
    if not row:
        await callback.message.answer("❌ Упражнение не найдено.")
        await workout_manage(callback, bot, state)
        await callback.answer()
        return
    ex_name, cat_id = row
    await state.update_data(current_ex_id=ex_id, current_cat_id=cat_id)
    msg = await callback.message.answer(f"Упражнение: {ex_name}", reply_markup=workout_exercise_actions_keyboard(ex_id))
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.callback_query(F.data.startswith("w_ex_set_goal_"))
async def workout_set_goal_from_manage(callback: CallbackQuery, bot: Bot, state: FSMContext):
    ex_id = int(callback.data.split("_")[4])
    user_id = callback.from_user.id
    await callback.message.delete()
    cursor = db.execute('SELECT category_id FROM exercises WHERE id = ? AND user_id = ?', (ex_id, user_id))
    row = cursor.fetchone()
    if not row:
        await callback.answer("❌ Упражнение не найдено", show_alert=True)
        return
    cat_id = row[0]
    await state.update_data(creating_ex_id=ex_id, category_id=cat_id)
    await state.set_state(WorkoutState.setting_goal_type)
    msg = await callback.message.answer(
        "Выбери тип цели:",
        reply_markup=workout_exercise_goal_keyboard()
    )
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.callback_query(F.data.regexp(r'^w_ex_new_\d+$'))
async def workout_new_exercise(callback: CallbackQuery, bot: Bot, state: FSMContext):
    cat_id = int(callback.data.split("_")[3])
    await state.update_data(category_id=cat_id)
    await callback.message.delete()
    await state.set_state(WorkoutState.creating_exercise)
    msg = await callback.message.answer("Введи название нового упражнения (например, 'Жим лёжа', 'Бег'):")
    user_temp_messages.setdefault(callback.from_user.id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.message(WorkoutState.creating_exercise)
async def workout_create_exercise(message: Message, bot: Bot, state: FSMContext):
    user_id = message.from_user.id
    ex_name = message.text.strip()
    if len(ex_name) < 2:
        await message.answer("❌ Слишком короткое название. Попробуй ещё раз:")
        return
    data = await state.get_data()
    cat_id = data.get('category_id')
    if not cat_id:
        await state.clear()
        await workout_manage_after_action(user_id, message.chat.id, bot)
        return
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, message.message_id)
    await delete_message_safe(bot, message.chat.id, temps.get('workout_temp'))
    try:
        cursor = db.execute('INSERT INTO exercises (user_id, category_id, name) VALUES (?, ?, ?)', (user_id, cat_id, ex_name))
        db.commit()
        new_ex_id = cursor.lastrowid
    except sqlite3.IntegrityError:
        await message.answer("❌ Такое упражнение уже есть в этой категории.")
        await workout_manage_exercises_cat(user_id, message.chat.id, cat_id, bot)
        return
    await state.update_data(creating_ex_id=new_ex_id)
    await prompt_set_goal(message, bot, state, user_id, cat_id)

async def prompt_set_goal(message: Message, bot: Bot, state: FSMContext, user_id: int, cat_id: int):
    await state.set_state(WorkoutState.setting_goal_type)
    msg = await message.answer(
        "Хочешь установить цель для этого упражнения?\nВыбери тип:",
        reply_markup=workout_exercise_goal_keyboard()
    )
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id

@router.callback_query(WorkoutState.setting_goal_type, F.data == "goal_strength")
async def set_goal_strength(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await callback.message.delete()
    await state.set_state(WorkoutState.setting_strength_goal)
    msg = await callback.message.answer(
        "Введи цель для силового упражнения в формате: подходы x повторения (например, 3x10)\n"
        "Если хочешь указать целевой вес и шаг увеличения, добавь ещё два числа через пробел: 3x10 50 2.5"
    )
    user_temp_messages.setdefault(callback.from_user.id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.message(WorkoutState.setting_strength_goal)
async def set_strength_goal_finish(message: Message, bot: Bot, state: FSMContext):
    text = message.text.strip()
    user_id = message.from_user.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, message.message_id)
    await delete_message_safe(bot, message.chat.id, temps.get('workout_temp'))

    parts = text.split()
    if not parts:
        await message.answer("❌ Введи цель (например, 3x10 или 10 8 6).")
        return

    goal_part = parts[0]
    numbers = []
    for part in parts[1:]:
        try:
            num = float(part.replace(',', '.'))
            numbers.append(num)
        except ValueError:
            continue

    target_weight = numbers[0] if len(numbers) > 0 else None
    weight_increment = numbers[1] if len(numbers) > 1 else None

    try:
        target_sets, target_reps_list = parse_reps_input(goal_part)
        target_reps = ','.join(str(r) for r in target_reps_list)
    except ValueError:
        msg = await message.answer("❌ Неверный формат цели. Используй примеры:\n- 3x10\n- 10 8 6\n- 3x10 50 2.5")
        user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id
        return

    data = await state.get_data()
    ex_id = data.get('creating_ex_id')
    if not ex_id:
        await state.clear()
        await workout_manage_after_action(user_id, message.chat.id, bot)
        return

    db.execute('''
        UPDATE exercises
        SET target_sets = ?, target_reps = ?, target_weight = ?, weight_increment = ?
        WHERE id = ? AND user_id = ?
    ''', (target_sets, target_reps, target_weight, weight_increment, ex_id, user_id))
    db.commit()

    await state.clear()
    success_msg = await message.answer("✅ Цель установлена!")
    await asyncio.sleep(2)
    await delete_message_safe(bot, message.chat.id, success_msg.message_id)
    await workout_manage_exercises_cat(user_id, message.chat.id, data.get('category_id'), bot)

@router.callback_query(WorkoutState.setting_goal_type, F.data == "goal_cardio")
async def set_goal_cardio(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await callback.message.delete()
    await state.set_state(WorkoutState.setting_cardio_goal)
    msg = await callback.message.answer(
        "Введи цель для кардио в формате: дистанция км / время мин (например, 5 30)"
    )
    user_temp_messages.setdefault(callback.from_user.id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.message(WorkoutState.setting_cardio_goal)
async def set_cardio_goal_finish(message: Message, bot: Bot, state: FSMContext):
    text = message.text.strip()
    user_id = message.from_user.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, message.message_id)
    await delete_message_safe(bot, message.chat.id, temps.get('workout_temp'))

    parts = text.split()
    if len(parts) != 2:
        msg = await message.answer("❌ Нужно два числа: дистанция (км) и время (мин).")
        user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id
        return

    try:
        target_distance = float(parts[0].replace(',', '.'))
        target_duration = int(parts[1])
    except ValueError:
        msg = await message.answer("❌ Неверный формат чисел.")
        user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id
        return

    data = await state.get_data()
    ex_id = data.get('creating_ex_id')
    cat_id = data.get('category_id')
    
    if ex_id:
        db.execute('''
            UPDATE exercises
            SET target_distance = ?, target_duration = ?
            WHERE id = ? AND user_id = ?
        ''', (target_distance, target_duration, ex_id, user_id))
        db.commit()
        success_msg = "✅ Новая цель для кардио установлена!"
    else:
        success_msg = "✅ Цель установлена (но упражнение не найдено)!"

    await state.clear()
    success_msg_obj = await message.answer(success_msg)
    await asyncio.sleep(2)
    await delete_message_safe(bot, message.chat.id, success_msg_obj.message_id)
    if cat_id:
        await workout_manage_exercises_cat(user_id, message.chat.id, cat_id, bot)
    else:
        await workout_manage_after_action(user_id, message.chat.id, bot)

async def workout_manage_exercises_cat(user_id: int, chat_id: int, cat_id: int, bot: Bot):
    temps = user_temp_messages.get(user_id, {})
    old = temps.pop('workout_temp', None)
    if old:
        await delete_message_safe(bot, chat_id, old)
    cursor = db.execute('SELECT name FROM exercise_categories WHERE id = ?', (cat_id,))
    cat_row = cursor.fetchone()
    cat_name = cat_row[0] if cat_row else "Категория"
    ex_cursor2 = db.execute('SELECT id, name FROM exercises WHERE user_id = ? AND category_id = ? ORDER BY name', (user_id, cat_id))
    exercises = ex_cursor2.fetchall()
    msg = await bot.send_message(
        chat_id,
        f"Упражнения в категории '{cat_name}':",
        reply_markup=workout_exercises_keyboard(exercises, cat_id, action="manage")
    )
    temps['workout_temp'] = msg.message_id
    user_temp_messages[user_id] = temps

@router.callback_query(F.data.regexp(r'^w_ex_rename_\d+$'))
async def workout_rename_exercise(callback: CallbackQuery, bot: Bot, state: FSMContext):
    ex_id = int(callback.data.split("_")[3])
    await state.update_data(renaming_ex_id=ex_id)
    await callback.message.delete()
    await state.set_state(WorkoutState.renaming_exercise)
    msg = await callback.message.answer("Введи новое название для категории:")
    user_temp_messages.setdefault(callback.from_user.id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.message(WorkoutState.renaming_exercise)
async def workout_rename_exercise_finish(message: Message, bot: Bot, state: FSMContext):
    user_id = message.from_user.id
    new_name = message.text.strip()
    if len(new_name) < 2:
        await message.answer("❌ Слишком короткое название. Попробуй ещё раз:")
        return
    data = await state.get_data()
    ex_id = data.get('renaming_ex_id')
    await state.clear()
    try:
        await message.delete()
    except:
        pass
    cursor = db.execute('SELECT category_id FROM exercises WHERE id = ?', (ex_id,)) if ex_id else None
    row = cursor.fetchone() if cursor else None
    cat_id = row[0] if row else None
    if not ex_id:
        await workout_manage_after_action(user_id, message.chat.id, bot)
        return
    try:
        db.execute('UPDATE exercises SET name = ? WHERE id = ? AND user_id = ?', (new_name, ex_id, user_id))
        db.commit()
    except sqlite3.IntegrityError:
        await message.answer("❌ Упражнение с таким именем уже существует в этой категории.")
    if cat_id:
        await workout_manage_exercises_cat(user_id, message.chat.id, cat_id, bot)
    else:
        await workout_manage_after_action(user_id, message.chat.id, bot)

@router.callback_query(F.data.regexp(r'^w_ex_delete_\d+$'))
async def workout_delete_exercise_confirm(callback: CallbackQuery, bot: Bot, state: FSMContext):
    ex_id = int(callback.data.split("_")[3])
    await state.update_data(deleting_ex_id=ex_id)
    await callback.message.delete()
    await state.set_state(WorkoutState.deleting_exercise_confirm)
    msg = await callback.message.answer(
        "⚠️ Ты уверен, что хочешь удалить это упражнение?",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="✅ Да, удалить", callback_data="w_ex_delete_yes"),
             InlineKeyboardButton(text="❌ Нет", callback_data="workout_manage")]
        ])
    )
    user_temp_messages.setdefault(callback.from_user.id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.callback_query(F.data == "w_ex_delete_yes", WorkoutState.deleting_exercise_confirm)
async def workout_delete_exercise_finish(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    data = await state.get_data()
    ex_id = data.get('deleting_ex_id')
    if not ex_id:
        await state.clear()
        await workout_manage_after_action(user_id, callback.message.chat.id, bot)
        await callback.answer()
        return
    cursor = db.execute('SELECT category_id FROM exercises WHERE id = ?', (ex_id,))
    row = cursor.fetchone()
    cat_id = row[0] if row else None
    db.execute('DELETE FROM exercises WHERE id = ? AND user_id = ?', (ex_id, user_id))
    db.commit()
    await state.clear()
    await callback.message.delete()
    success_msg = await callback.message.answer("✅ Упражнение удалено.")
    await asyncio.sleep(2)
    await delete_message_safe(bot, callback.message.chat.id, success_msg.message_id)
    if cat_id:
        await workout_manage_exercises_cat(user_id, callback.message.chat.id, cat_id, bot)
    else:
        await workout_manage_after_action(user_id, callback.message.chat.id, bot)
    await callback.answer()

# ---------- ИСТОРИЯ ТРЕНИРОВОК ----------

def _format_session_detail(session: dict) -> str:
    """Форматирует одну сессию с подробностями."""
    date_str = datetime.strptime(session["date"], "%Y-%m-%d").strftime("%d.%m.%Y")
    wd = WEEKDAY_RU.get(session.get("weekday", 0), "")
    status = session.get("status", "")
    lines = [f"📅 {wd}, {date_str}"]
    if status == "skipped":
        reason = session.get("skip_reason") or ""
        lines.append(f"⏭ Пропуск" + (f" — {reason}" if reason else ""))
        return "\n".join(lines)
    logs = get_session_exercise_logs(session["id"])
    for log in logs:
        icon = "✅" if log["status"] == "done" else "⏭"
        name = log["exercise_name"]
        planned = log.get("planned") or {}
        res = log.get("result")
        plan_str = f"{planned.get('sets','?')}×{planned.get('reps','?')}"
        if planned.get("weight"):
            plan_str += f" @ {planned['weight']}кг"
        if res and isinstance(res, dict) and log["status"] == "done":
            s = res.get("sets_done","?")
            r = res.get("reps_done","?")
            w = res.get("weight_done")
            done_str = f"{s}×{r}" + (f" @ {w}кг" if w else "")
            lines.append(f"{icon} {name}\n   План: {plan_str} → Факт: {done_str}")
        else:
            lines.append(f"{icon} {name} — {plan_str}")
    if session.get("feedback"):
        lines.append(f"\n💬 {session['feedback']}")
    return "\n".join(lines)

async def show_workout_history_page(user_id: int, chat_id: int, bot: Bot, page: int = 0, edit_msg_id: int = None):
    cursor = db.execute("""
        SELECT id, date, weekday, session_key, plan_json, status, skip_reason, feedback
        FROM ai_workout_sessions WHERE user_id = ? AND status != 'pending'
        ORDER BY date DESC
    """, (user_id,))
    rows = cursor.fetchall()
    if not rows:
        text = "Тренировок пока нет."
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="🔙 Назад", callback_data="workout_history_back")]
        ])
        if edit_msg_id:
            try:
                await bot.edit_message_text(text, chat_id, edit_msg_id, reply_markup=kb)
                return
            except:
                pass
        msg = await bot.send_message(chat_id, text, reply_markup=kb)
        user_temp_messages.setdefault(user_id, {})['workout_menu'] = msg.message_id
        return
    total = len(rows)
    page = max(0, min(page, total - 1))
    row = rows[page]
    session = dict(row)
    session["plan"] = json.loads(session["plan_json"])
    session["logs"] = get_session_exercise_logs(session["id"])
    text = _format_session_detail(session)
    nav = []
    if page < total - 1:
        nav.append(InlineKeyboardButton(text="← Раньше", callback_data=f"wh_page_{page+1}"))
    if page > 0:
        nav.append(InlineKeyboardButton(text="Позже →", callback_data=f"wh_page_{page-1}"))
    kb_rows = []
    if nav:
        kb_rows.append(nav)
    kb_rows.append([InlineKeyboardButton(text=f"{total - page}/{total}", callback_data="wh_noop")])
    kb_rows.append([InlineKeyboardButton(text="🔙 Назад", callback_data="workout_history_back")])
    kb = InlineKeyboardMarkup(inline_keyboard=kb_rows)
    if edit_msg_id:
        try:
            await bot.edit_message_text(text, chat_id, edit_msg_id, reply_markup=kb)
            return
        except:
            pass
    msg = await bot.send_message(chat_id, text, reply_markup=kb)
    user_temp_messages.setdefault(user_id, {})['workout_menu'] = msg.message_id


@router.message(F.text == "✏️ Изменить упражнение")
async def workout_edit_exercise_start(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    user_id = message.from_user.id
    plan_data = get_ai_plan(user_id)
    if not plan_data:
        return
    plan = plan_data.get("plan", {})
    # Collect all training days
    day_names = {"monday":"Пн","tuesday":"Вт","wednesday":"Ср","thursday":"Чт",
                 "friday":"Пт","saturday":"Сб","sunday":"Вс"}
    day_order = ["monday","tuesday","wednesday","thursday","friday","saturday","sunday"]
    cycle = plan_data.get("cycle_weeks", 1)
    buttons = []
    seen_days = set()
    for w in range(1, cycle + 1):
        week = plan.get(f"week_{w}", {})
        for day_key in day_order:
            if day_key in week and day_key not in seen_days:
                seen_days.add(day_key)
                buttons.append([InlineKeyboardButton(
                    text=day_names[day_key],
                    callback_data=f"wex_day_{day_key}"
                )])
    buttons.append([InlineKeyboardButton(text="🔙 Назад", callback_data="workout_manage_back")])
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, temps.pop('workout_menu', None))
    msg = await message.answer("Выбери день тренировки:", reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons))
    user_temp_messages.setdefault(user_id, {})['workout_menu'] = msg.message_id
    await state.set_state(AIPlanState.editing_plan)
    await state.update_data(wp_edit_mode="exercise")

@router.callback_query(AIPlanState.editing_plan, F.data.startswith("wex_day_"))
async def workout_edit_choose_day(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    day_key = callback.data.split("_")[2]
    plan_data = get_ai_plan(user_id)
    if not plan_data:
        await callback.answer("Нет плана", show_alert=True)
        return
    plan = plan_data.get("plan", {})
    cycle = plan_data.get("cycle_weeks", 1)
    # Find exercises for this day across all weeks (use first week that has it)
    exercises = []
    for w in range(1, cycle + 1):
        week = plan.get(f"week_{w}", {})
        exs = week.get(day_key, [])
        if exs:
            exercises = exs
            break
    if not exercises:
        await callback.answer("Нет упражнений", show_alert=True)
        return
    await state.update_data(wp_edit_day=day_key)
    buttons = []
    for i, ex in enumerate(exercises):
        name = ex.get("exercise", ex.get("name", f"Упражнение {i+1}"))
        buttons.append([InlineKeyboardButton(text=name, callback_data=f"wex_ex_{i}")])
    buttons.append([InlineKeyboardButton(text="🔙 Назад", callback_data="wex_back_to_days")])
    await callback.message.edit_text("Выбери упражнение для замены:", reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons))
    await callback.answer()

@router.callback_query(AIPlanState.editing_plan, F.data == "wex_back_to_days")
async def workout_edit_back_to_days(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    plan_data = get_ai_plan(user_id)
    if not plan_data:
        await callback.answer()
        return
    plan = plan_data.get("plan", {})
    day_names = {"monday":"Пн","tuesday":"Вт","wednesday":"Ср","thursday":"Чт",
                 "friday":"Пт","saturday":"Сб","sunday":"Вс"}
    day_order = ["monday","tuesday","wednesday","thursday","friday","saturday","sunday"]
    cycle = plan_data.get("cycle_weeks", 1)
    buttons = []
    seen_days = set()
    for w in range(1, cycle + 1):
        week = plan.get(f"week_{w}", {})
        for day_key in day_order:
            if day_key in week and day_key not in seen_days:
                seen_days.add(day_key)
                buttons.append([InlineKeyboardButton(text=day_names[day_key], callback_data=f"wex_day_{day_key}")])
    buttons.append([InlineKeyboardButton(text="🔙 Назад", callback_data="workout_manage_back")])
    await callback.message.edit_text("Выбери день тренировки:", reply_markup=InlineKeyboardMarkup(inline_keyboard=buttons))
    await callback.answer()

@router.callback_query(AIPlanState.editing_plan, F.data.startswith("wex_ex_"))
async def workout_edit_choose_exercise(callback: CallbackQuery, bot: Bot, state: FSMContext):
    ex_idx = int(callback.data.split("_")[2])
    data = await state.get_data()
    day_key = data.get("wp_edit_day", "monday")
    plan_data = get_ai_plan(callback.from_user.id)
    if not plan_data:
        await callback.answer()
        return
    plan = plan_data.get("plan", {})
    cycle = plan_data.get("cycle_weeks", 1)
    exercises = []
    for w in range(1, cycle + 1):
        week = plan.get(f"week_{w}", {})
        exs = week.get(day_key, [])
        if exs:
            exercises = exs
            break
    if ex_idx >= len(exercises):
        await callback.answer("Упражнение не найдено", show_alert=True)
        return
    ex = exercises[ex_idx]
    ex_name = ex.get("exercise", ex.get("name", "?"))
    await state.update_data(wp_edit_ex_idx=ex_idx, wp_edit_ex_name=ex_name,
                            wp_edit_mode="exercise_replace")
    await callback.message.edit_text(
        f"Чем заменить «{ex_name}»?\n\nНапиши название нового упражнения:",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="🔙 Назад", callback_data=f"wex_day_{day_key}")]
        ])
    )
    await callback.answer()

@router.message(F.text == "📊 История")
async def workout_history_ai_msg(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    user_id = message.from_user.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, temps.pop('workout_menu', None))
    user_temp_messages[user_id] = temps
    await show_workout_history_page(user_id, message.chat.id, bot, 0)

@router.callback_query(F.data.startswith("wh_page_"))
async def workout_history_page(callback: CallbackQuery, bot: Bot, state: FSMContext):
    page = int(callback.data.split("_")[2])
    await show_workout_history_page(callback.from_user.id, callback.message.chat.id, bot,
                                     page, callback.message.message_id)
    await callback.answer()

@router.callback_query(F.data == "wh_noop")
async def wh_noop(callback: CallbackQuery):
    await callback.answer()

@router.callback_query(F.data == "workout_history_back")
async def workout_history_back(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    try:
        await callback.message.delete()
    except:
        pass
    await show_workout_main_menu(user_id, callback.message.chat.id, bot)
    await callback.answer()

@router.message(F.text == "📊 История")
async def workout_history_msg(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    user_history_page[message.from_user.id] = 0
    await show_history_page(message.from_user.id, message.chat.id, bot, state)

@router.callback_query(F.data == "workout_history")
async def workout_history(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    user_history_page[user_id] = 0
    await callback.message.delete()
    await show_history_page(user_id, callback.message.chat.id, bot, state)

async def show_history_page(user_id: int, chat_id: int, bot: Bot, state: FSMContext, edit_message_id: int = None):
    page = user_history_page.get(user_id, 0)
    limit_days = 3
    offset_days = page * limit_days

    cursor = db.execute('''
        SELECT DISTINCT date
        FROM workout_log
        WHERE user_id = ?
        ORDER BY date DESC
    ''', (user_id,))
    all_dates = [row[0] for row in cursor.fetchall()]
    total_days = len(all_dates)
    total_pages = (total_days + limit_days - 1) // limit_days if total_days > 0 else 1

    if page >= total_pages and total_pages > 0:
        user_history_page[user_id] = total_pages - 1
        page = total_pages - 1
        offset_days = page * limit_days

    if total_days == 0:
        text = "📊 История тренировок пока пуста."
    else:
        start_idx = offset_days
        end_idx = min(offset_days + limit_days, total_days)
        page_dates = all_dates[start_idx:end_idx]

        lines = []
        for date in page_dates:
            day_cursor = db.execute('''
                SELECT wl.exercise_name, wl.sets, wl.reps, wl.weight, wl.distance, wl.duration, ec.name
                FROM workout_log wl
                LEFT JOIN exercise_categories ec ON wl.category_id = ec.id
                WHERE wl.user_id = ? AND wl.date = ?
                ORDER BY wl.id
            ''', (user_id, date))
            day_exercises = day_cursor.fetchall()

            formatted_date = datetime.strptime(date, '%Y-%m-%d').strftime('%d.%m.%Y')
            lines.append(f"\n📅 {formatted_date}")

            for ex_name, sets, reps, weight, dist, dur, cat_name in day_exercises:
                if sets is not None:
                    line = f"  💪 {cat_name or 'Без категории'}: {ex_name} – {sets}х{reps}"
                    if weight:
                        line += f" ({weight} кг)"
                else:
                    line = f"  🚴 {cat_name or 'Кардио'}: {ex_name} – "
                    parts = []
                    if dist:
                        parts.append(f"{dist} км")
                    if dur:
                        parts.append(f"{dur} мин")
                    line += " / ".join(parts)
                lines.append(line)
        text = "📊 История тренировок\n" + "\n".join(lines)

    nav_buttons = []
    if page > 0:
        nav_buttons.append(InlineKeyboardButton(text="⬅️ Предыдущая", callback_data="history_prev"))
    if page < total_pages - 1:
        nav_buttons.append(InlineKeyboardButton(text="Следующая ➡️", callback_data="history_next"))

    keyboard_buttons = []
    if nav_buttons:
        keyboard_buttons.append(nav_buttons)
    keyboard_buttons.append([InlineKeyboardButton(text="🔙 Назад", callback_data="workout_main")])

    reply_markup = InlineKeyboardMarkup(inline_keyboard=keyboard_buttons)

    if edit_message_id:
        await bot.edit_message_text(text, chat_id, edit_message_id, reply_markup=reply_markup)
    else:
        msg = await bot.send_message(chat_id, text, reply_markup=reply_markup)
        user_temp_messages.setdefault(user_id, {})['workout_history'] = msg.message_id

@router.callback_query(F.data == "history_prev")
async def history_prev(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    page = user_history_page.get(user_id, 0)
    if page > 0:
        user_history_page[user_id] = page - 1
    await show_history_page(user_id, callback.message.chat.id, bot, state, edit_message_id=callback.message.message_id)
    await callback.answer()

@router.callback_query(F.data == "history_next")
async def history_next(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    page = user_history_page.get(user_id, 0)
    user_history_page[user_id] = page + 1
    await show_history_page(user_id, callback.message.chat.id, bot, state, edit_message_id=callback.message.message_id)
    await callback.answer()

# ---------- ГРАФИКИ УПРАЖНЕНИЙ ----------
async def _do_workout_charts(user_id: int, chat_id: int, bot: Bot, state: FSMContext):
    cursor = db.execute('SELECT id, name FROM exercise_categories WHERE user_id = ? ORDER BY name', (user_id,))
    categories = cursor.fetchall()
    if not categories:
        await bot.send_message(chat_id, "❌ Нет категорий для графиков")
        await show_workout_main_menu(user_id, chat_id, bot)
        return
    await state.set_state(WorkoutState.choosing_category)
    await state.update_data(workout_charts_mode=True)
    msg = await bot.send_message(chat_id, "Выбери категорию для графика:", reply_markup=workout_categories_keyboard(categories, action="add"))
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id

@router.message(F.text == "📈 Графики упражнений")
async def workout_charts_msg(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    await _do_workout_charts(message.from_user.id, message.chat.id, bot, state)

@router.callback_query(F.data == "workout_charts")
async def workout_charts_start(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    await callback.message.delete()
    await _do_workout_charts(user_id, callback.message.chat.id, bot, state)
    await callback.answer()

@router.callback_query(WorkoutState.choosing_category, F.data.startswith("w_add_cat_"))
async def workout_charts_choose_category(callback: CallbackQuery, bot: Bot, state: FSMContext):
    cat_id = int(callback.data.split("_")[3])
    user_id = callback.from_user.id
    await callback.message.delete()
    cursor = db.execute('SELECT id, name FROM exercises WHERE user_id = ? AND category_id = ? ORDER BY name', (user_id, cat_id))
    exercises = cursor.fetchall()
    if not exercises:
        await callback.message.answer("❌ В этой категории нет упражнений.")
        await show_workout_main_menu(user_id, callback.message.chat.id, bot)
        await callback.answer()
        return
    await state.update_data(chart_cat_id=cat_id)
    await state.set_state(WorkoutState.choosing_exercise)
    msg = await callback.message.answer("Выбери упражнение для графика:", reply_markup=workout_exercises_keyboard(exercises, cat_id, action="add"))
    user_temp_messages.setdefault(user_id, {})['workout_temp'] = msg.message_id
    await callback.answer()

@router.callback_query(WorkoutState.choosing_exercise, F.data.startswith("w_add_ex_"))
async def workout_charts_generate(callback: CallbackQuery, bot: Bot, state: FSMContext):
    ex_id = int(callback.data.split("_")[3])
    user_id = callback.from_user.id
    await callback.message.delete()
    await state.clear()
    await bot.send_chat_action(callback.message.chat.id, action=ChatAction.UPLOAD_PHOTO)
    cursor = db.execute('''
        SELECT date, sets, reps, weight, distance, duration
        FROM workout_log
        WHERE user_id = ? AND exercise_name = (
            SELECT name FROM exercises WHERE id = ?
        )
        ORDER BY date
    ''', (user_id, ex_id))
    rows = cursor.fetchall()
    type_cursor2 = db.execute('SELECT ex_type FROM exercise_categories WHERE id = (SELECT category_id FROM exercises WHERE id = ?)', (ex_id,))
    type_row = type_cursor2.fetchone()
    ex_type = type_row[0] if type_row else 'strength'

    if len(rows) < 2:
        await callback.message.answer("❌ Недостаточно данных для графика (нужно минимум 2 записи).")
        await show_workout_main_menu(user_id, callback.message.chat.id, bot)
        await callback.answer()
        return

    dates = [datetime.strptime(r[0], '%Y-%m-%d').strftime('%d.%m') for r in rows]
    if ex_type == 'strength':
        avg_reps = []
        weights = []
        for r in rows:
            reps_str = r[2]
            reps_list = [int(x) for x in reps_str.split(',')] if reps_str else []
            avg = sum(reps_list)/len(reps_list) if reps_list else 0
            avg_reps.append(avg)
            weights.append(r[3] or 0)
        fig = make_subplots(rows=2, cols=1, subplot_titles=("Средние повторения", "Вес (кг)"))
        fig.add_trace(go.Scatter(x=dates, y=avg_reps, mode='lines+markers', name='Повторения'), row=1, col=1)
        fig.add_trace(go.Scatter(x=dates, y=weights, mode='lines+markers', name='Вес'), row=2, col=1)
        fig.update_layout(title="Прогресс упражнения", height=600, showlegend=False, template='plotly_dark')
    else:
        distances = [r[4] or 0 for r in rows]
        durations = [r[5] or 0 for r in rows]
        pace = [durations[i]/distances[i] if distances[i] else 0 for i in range(len(rows))]
        fig = make_subplots(rows=3, cols=1, subplot_titles=("Дистанция (км)", "Время (мин)", "Темп (мин/км)"))
        fig.add_trace(go.Scatter(x=dates, y=distances, mode='lines+markers', name='Дистанция'), row=1, col=1)
        fig.add_trace(go.Scatter(x=dates, y=durations, mode='lines+markers', name='Время'), row=2, col=1)
        fig.add_trace(go.Scatter(x=dates, y=pace, mode='lines+markers', name='Темп'), row=3, col=1)
        fig.update_layout(title="Прогресс кардио", height=800, showlegend=False, template='plotly_dark')

    chart_path = f"workout_chart_{user_id}.png"
    fig.write_image(chart_path, scale=2)
    photo = FSInputFile(chart_path)
    await callback.bot.send_photo(
        user_id,
        photo,
        caption="📈 Прогресс упражнения",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🔙 Назад", callback_data="back_to_workout")]])
    )
    os.remove(chart_path)
    await callback.answer()

# ---------- Обработчики для целей (показать) ----------
@router.callback_query(F.data.startswith("w_show_goal_"))
async def workout_show_goal(callback: CallbackQuery, bot: Bot):
    ex_id = int(callback.data.split("_")[3])
    user_id = callback.from_user.id
    cursor = db.execute('''
        SELECT name, target_sets, target_reps, target_weight, target_distance, target_duration 
        FROM exercises WHERE id = ? AND user_id = ?
    ''', (ex_id, user_id))
    row = cursor.fetchone()
    if not row:
        await callback.answer("❌ Упражнение не найдено", show_alert=True)
        return
    name, sets, reps, weight, dist, dur = row
    if sets and reps:
        text = f"🎯 Цель упражнения *{name}*:\n{sets}×{reps}" + (f" с весом {weight} кг" if weight else "")
    else:
        text = f"🎯 Цель упражнения *{name}*:\nДистанция {dist} км за {dur} мин"
    await callback.message.answer(text, parse_mode="Markdown")
    await callback.answer()
  
  
# ---------- ДИЕТА ----------
@router.message(F.text == "🍽 Диета")
async def handle_diet(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    user_id = message.from_user.id
    await state.clear()
    profile = get_diet_profile(user_id)
    old_menu = user_last_menu.get(user_id)
    if old_menu:
        await delete_message_safe(bot, message.chat.id, old_menu)
        user_last_menu[user_id] = None
    if not profile:
        await state.set_state(DietState.weight)
        await delete_temp_messages(bot, user_id, message.chat.id, keep_ai=True)
        msg = await message.answer("📝 Введи свой вес (в кг):")
        user_temp_messages.setdefault(user_id, {})['diet_setup'] = msg.message_id
        return
    await delete_temp_messages(bot, user_id, message.chat.id, keep_ai=True)
    await show_diet_menu(user_id, message.chat.id, bot)

async def show_diet_menu(user_id: int, chat_id: int, bot: Bot):
    profile = get_diet_profile(user_id)
    if not profile:
        return
    today_cal = get_today_calories(user_id)
    daily_goal = profile['daily_calories']
    percent = (today_cal / daily_goal * 100) if daily_goal > 0 else 0
    bar = create_new_progress_bar(int(percent//10), 10)

    food_log = get_today_food_log(user_id)
    food_lines = []
    for meal_type, desc, cal in food_log:
        food_lines.append(f"{meal_type}: {desc} ({int(cal)} ккал)")

    food_summary = "\n".join(food_lines) if food_lines else "Пока нет записей."

    text = f"""🍽 Меню диеты

Цель: {int(daily_goal)} ккал/день
Съедено сегодня: {int(today_cal)} ккал ({int(percent)}%)
{bar} {int(percent)}%

Сегодня:
{food_summary}

Выбери действие:"""
    msg = await bot.send_message(chat_id, text, reply_markup=diet_menu_reply_keyboard())
    user_temp_messages.setdefault(user_id, {})['diet_menu'] = msg.message_id

@router.message(F.text == "🍎 Записать еду")
async def diet_log_food_reply(message: Message, bot: Bot, state: FSMContext):
    await delete_message_safe(bot, message.chat.id, message.message_id)
    user_id = message.from_user.id
    # Удаляем меню диеты
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, temps.get('diet_menu'))
    old_menu = user_last_menu.get(user_id)
    if old_menu:
        await delete_message_safe(bot, message.chat.id, old_menu)
        user_last_menu[user_id] = None
    await delete_temp_messages(bot, user_id, message.chat.id, keep_ai=True)
    await state.clear()
    await state.set_state(DietState.meal_type)
    msg = await message.answer("Выбери приём пищи:", reply_markup=meal_type_keyboard())
    user_temp_messages.setdefault(user_id, {})['diet_temp'] = msg.message_id

@router.callback_query(DietState.meal_type, F.data.startswith("meal_type:"))
async def diet_choose_meal(callback: CallbackQuery, bot: Bot, state: FSMContext):
    meal_map = {
        "Завтрак": "Завтрак",
        "Обед": "Обед",
        "Ужин": "Ужин",
        "Перекус": "Перекус"
    }
    meal_type = meal_map.get(callback.data.split(":", 1)[1])
    if not meal_type:
        await callback.answer()
        return
    await state.update_data(meal_type=meal_type)

    temps = user_temp_messages.get(callback.from_user.id, {})
    await delete_message_safe(bot, callback.message.chat.id, temps.get('diet_temp'))

    msg = await callback.message.answer(
        f"Приём пищи: <b>{meal_type}</b>\n\n"
        "Опиши что съел — ИИ посчитает калории, или запиши вручную:",
        parse_mode="HTML",
        reply_markup=meal_chosen_keyboard()
    )
    user_temp_messages.setdefault(callback.from_user.id, {})['diet_temp'] = msg.message_id
    await callback.answer()

@router.callback_query(DietState.meal_type, F.data == "meal_entry_manual")
async def meal_entry_manual(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, callback.message.chat.id, temps.get('diet_temp'))
    await state.update_data(food_description='')
    await state.set_state(DietState.manual_calories)
    msg = await callback.message.answer(
        "✏️ Введи количество калорий (только число):",
        reply_markup=food_cancel_keyboard()
    )
    user_temp_messages.setdefault(user_id, {})['diet_temp'] = msg.message_id
    await callback.answer()

@router.callback_query(DietState.meal_type, F.data == "meal_entry_cancel")
async def meal_entry_cancel(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, callback.message.chat.id, temps.get('diet_temp'))
    await state.clear()
    await callback.answer()
    await show_diet_menu(user_id, callback.message.chat.id, bot)

@router.message(DietState.meal_type, F.text & ~F.text.startswith("/"))
async def meal_type_text_forward(message: Message, bot: Bot, state: FSMContext):
    """Пользователь написал описание еды прямо после выбора приёма пищи — переключаем стейт и обрабатываем."""
    await state.set_state(DietState.food_description)
    await process_food_description(message, bot, state)

@router.message(DietState.meal_type, F.photo)
async def meal_type_photo_forward(message: Message, bot: Bot, state: FSMContext):
    """Пользователь отправил фото прямо после выбора приёма пищи."""
    await state.set_state(DietState.food_description)
    await process_food_photo(message, bot, state)

@router.callback_query(DietState.food_description, F.data.startswith("food_choose_"))
async def diet_choose_my_food(callback: CallbackQuery, bot: Bot, state: FSMContext):
    food_name = callback.data.split("_", 2)[2]
    user_id = callback.from_user.id

    cursor = db.execute('SELECT calories FROM my_foods WHERE user_id = ? AND name = ?', (user_id, food_name))
    row = cursor.fetchone()
    if row:
        calories = row[0]
        await state.update_data(food_description=food_name, food_calories=calories)
        await callback.message.delete()
        await state.set_state(DietState.food_confirm)
        text = f"🍽 Ты съел: {food_name}\n🔢 Калории: {int(calories)} ккал\n\nВсё верно?"
        await callback.message.answer(text, reply_markup=diet_confirm_food_keyboard())
    else:
        await callback.answer("❌ Блюдо не найдено", show_alert=True)
        await diet_log_food_reply(callback.message, bot, state)
    await callback.answer()

@router.callback_query(DietState.food_description, F.data == "food_create_new")
async def diet_create_new_food(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await callback.message.delete()
    await state.set_state(DietState.food_description)
    msg = await callback.message.answer(
        "🍽 Опиши, что ты съел, или отправь фото блюда:\n\n"
        "Или нажми /cancel для отмены.",
        reply_markup=food_cancel_keyboard()
    )
    user_temp_messages.setdefault(callback.from_user.id, {})['diet_temp'] = msg.message_id
    await callback.answer()

@router.callback_query(DietState.food_description, F.data == "food_cancel")
async def diet_cancel_food(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.clear()
    await callback.message.delete()
    await show_diet_menu(callback.from_user.id, callback.message.chat.id, bot)
    await callback.answer()

@router.message(DietState.food_description, F.photo)
async def process_food_photo(message: Message, bot: Bot, state: FSMContext):
    """Оценка калорий по фото блюда."""
    user_id = message.from_user.id
    chat_id = message.chat.id
    temps = user_temp_messages.get(user_id, {})
    # Удаляем служебное "Опиши что съел", фото юзера НЕ трогаем
    await delete_message_safe(bot, chat_id, temps.get('diet_temp'))

    wait_msg = await message.answer("🔍 Анализирую фото блюда...")
    photo = message.photo[-1]
    file = await bot.get_file(photo.file_id)
    buffer = await bot.download_file(file.file_path)
    if buffer is None or not hasattr(buffer, 'read'):
        await wait_msg.edit_text("❌ Не удалось загрузить фото.")
        return
    if hasattr(buffer, 'seek'):
        buffer.seek(0)
    image = Image.open(buffer)
    img_buffer = io.BytesIO()
    image.save(img_buffer, format='PNG')
    image_bytes = img_buffer.getvalue()

    api_key = os.environ.get("GOOGLE_API_KEY") or os.environ.get("GEMINI_API_KEY")
    if not api_key:
        await wait_msg.edit_text("❌ ИИ недоступен (нет API-ключа).")
        return
    prompt = """Посмотри на фото еды и оцени калорийность.

    Ответь строго в формате: [название блюда] [число ккал]
    Название — 1-4 слова на русском. Число — только целые ккал без единиц.

    Правила оценки:
    - Считай реальную порцию на фото, не занижай
    - Учитывай видимые соусы, масло, хлеб рядом
    - Если несколько блюд — суммируй всё

    Примеры правильных ответов:
    гречка с курицей 480
    паста карбонара 650
    омлет с сыром 350
    бургер и картошка 900
    салат цезарь 520"""
    # Сохраняем данные для повтора без повторной загрузки фото
    await state.update_data(
        retry_food_photo_bytes=image_bytes,
        retry_food_photo_prompt=prompt,
        retry_action="food_photo"
    )
    text = await run_in_thread(analyze_food_photo, image_bytes, prompt)
    if text is None:
        await wait_msg.edit_text(
            "❌ Ошибка анализа фото.\n\n🔄 Нажми кнопку чтобы попробовать ещё раз.",
            reply_markup=retry_ai_keyboard("food_photo")
        )
        return

    description = "Блюдо на фото"
    calories = None
    nums = re.findall(r"\b(\d{2,5})\b", text)
    valid_nums = [float(n) for n in nums if 50 <= float(n) <= 9999]
    if valid_nums:
        calories = valid_nums[-1]  # берём последнее число — обычно итоговые ккал
    match = re.search(r"^([^0-9]+?)(?:\s*\d|$)", text)
    if match:
        desc = match.group(1).strip(" .,;:-")
        if 2 <= len(desc) <= 50:
            description = desc

    await delete_message_safe(bot, chat_id, wait_msg.message_id)
    if calories is None or calories <= 0 or calories > 5000:
        await state.update_data(food_description=description)
        await state.set_state(DietState.manual_calories)
        msg = await message.answer(
            f"🍽 Определено: {description}\n❌ Не удалось оценить калории. Введи вручную (число):",
            reply_markup=food_cancel_keyboard()
        )
        user_temp_messages.setdefault(user_id, {})['diet_temp'] = msg.message_id
        return

    await state.update_data(food_description=description, food_calories=calories)
    await state.set_state(DietState.food_confirm)
    await message.answer(
        f"🍽 Ты съел: {description}\n🔢 Калории: ~{int(calories)} ккал\n\nВсё верно?",
        reply_markup=diet_confirm_food_keyboard()
    )

@router.message(DietState.food_description, F.text)
async def process_food_description(message: Message, bot: Bot, state: FSMContext):
    description = message.text.strip()
    if len(description) < 3:
        temps = user_temp_messages.get(message.from_user.id, {})
        old_error = temps.get('diet_error')
        if old_error:
            await delete_message_safe(bot, message.chat.id, old_error)
        error_msg = await message.answer("❌ Слишком короткое описание. Попробуй ещё раз.")
        temps['diet_error'] = error_msg.message_id
        user_temp_messages[message.from_user.id] = temps
        return

    user_id = message.from_user.id
    temps = user_temp_messages.get(user_id, {})
    # Удаляем только служебное сообщение "Опиши что съел", сообщение юзера НЕ трогаем
    await delete_message_safe(bot, message.chat.id, temps.get('diet_temp'))
    if 'diet_error' in temps:
        await delete_message_safe(bot, message.chat.id, temps['diet_error'])
        del temps['diet_error']

    await bot.send_chat_action(message.chat.id, action=ChatAction.TYPING)
    prompt = f"""Ты — точный счётчик калорий. Пользователь описывает что он съел (на русском или английском языке).

Твоя задача: посчитать ОБЩЕЕ количество ккал во всём описанном количестве еды.

ПРАВИЛА:
- Если указано количество (2 бургера, 3 яйца, 200г) — умножай соответственно
- Если количество не указано — считай стандартную порцию (тарелка супа ~300мл, второе блюдо ~300-400г, бутерброд ~150г)
- Учитывай ВСЕ компоненты: хлеб, масло, соусы, напитки, гарнир
- Не занижай: реальная еда жирнее и калорийнее чем кажется
- Минимум для полноценного приёма пищи (обед/ужин): 350 ккал
- Перекус может быть 100-300 ккал

Ориентиры (на порцию):
гречка с курицей = 450, паста карбонара = 680, бургер = 550, пицца (2 куска) = 600,
борщ = 300, салат цезарь с курицей = 520, омлет 2 яйца = 200, овсянка на молоке = 280,
рис с мясом = 500, шаурма = 650, хинкали 5шт = 400, суши-сет 8шт = 480,
протеиновый коктейль = 150, кофе с молоком = 60, яблоко = 80, банан = 100

Еда: {description}

Ответь СТРОГО одним целым числом — суммарные килокалории. Никаких слов, никаких единиц:"""
    await state.update_data(retry_food_description=description, retry_action="food_calories")
    response = gemini_generate(prompt, max_tokens=100, raw=True)
    try:
        numbers = re.findall(r"\b(\d{2,5})\b", response)
        numbers = [float(n) for n in numbers if 50 <= float(n) <= 9999]
        calories = numbers[-1] if numbers else None
    except:
        calories = None

    if calories is None or calories <= 0:
        await state.update_data(food_description=description)
        await state.set_state(DietState.manual_calories)
        msg = await message.answer(
            "❌ Не удалось определить калории автоматически. Нажми кнопку чтобы попробовать ещё раз.",
            reply_markup=retry_ai_keyboard("food_calories")
        )
        user_temp_messages.setdefault(user_id, {})['diet_temp'] = msg.message_id
        return

    await state.update_data(food_description=description, food_calories=calories)
    await state.set_state(DietState.food_confirm)
    text = f"🍽 Ты съел: {description}\n🔢 Калории: {int(calories)} ккал\n\nВсё верно?"
    await message.answer(text, reply_markup=diet_confirm_food_keyboard())

@router.callback_query(DietState.food_confirm, F.data == "food_confirm_yes")
async def food_confirm_yes(callback: CallbackQuery, bot: Bot, state: FSMContext):
    # Убираем только кнопки, само сообщение с калориями остаётся
    await callback.message.edit_reply_markup(reply_markup=None)
    data = await state.get_data()
    meal_type = data.get('meal_type')
    description = data.get('food_description')
    calories = data.get('food_calories')
    user_id = callback.from_user.id
    save_food_log(user_id, meal_type, description, calories)
    asyncio.create_task(run_in_thread(sync_diet_rating_for_today, user_id))

    success_msg = await callback.message.answer(f"✅ Записано: {int(calories)} ккал.")
    await asyncio.sleep(2)
    await delete_message_safe(bot, callback.message.chat.id, success_msg.message_id)

    await state.set_state(DietState.food_confirm)
    question_msg = await callback.message.answer(
        "Хочешь добавить ещё запись?",
        reply_markup=food_add_more_keyboard()
    )
    asyncio.create_task(delete_message_after_delay(
        bot, callback.message.chat.id, question_msg.message_id, delay=10
    ))

@router.callback_query(F.data == "food_add_more_yes")
async def food_add_more(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.set_state(DietState.meal_type)
    await callback.message.delete()
    msg = await callback.message.answer("Выбери приём пищи:", reply_markup=meal_type_keyboard())
    user_temp_messages.setdefault(callback.from_user.id, {})['diet_temp'] = msg.message_id
    await callback.answer()

@router.callback_query(DietState.food_confirm, F.data == "food_confirm_redo")
async def food_confirm_redo(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.set_state(DietState.meal_type)
    chat_id = callback.message.chat.id
    await callback.message.edit_reply_markup(reply_markup=None)
    msg = await bot.send_message(chat_id, "Выбери приём пищи:", reply_markup=meal_type_keyboard())
    user_temp_messages.setdefault(callback.from_user.id, {})['diet_temp'] = msg.message_id
    await callback.message.delete()
    await callback.answer()

@router.callback_query(DietState.food_confirm, F.data == "food_confirm_manual")
async def food_confirm_manual(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.set_state(DietState.manual_calories)
    chat_id = callback.message.chat.id
    await callback.message.edit_reply_markup(reply_markup=None)
    msg = await bot.send_message(chat_id, "✏️ Введи количество калорий вручную (только число):", reply_markup=food_cancel_keyboard())
    user_temp_messages.setdefault(callback.from_user.id, {})['diet_temp'] = msg.message_id
    await callback.message.delete()
    await callback.answer()

@router.message(DietState.manual_calories)
async def manual_calories(message: Message, bot: Bot, state: FSMContext):
    try:
        calories = float(message.text.strip().replace(',', '.'))
        if calories <= 0 or calories > 10000:
            raise ValueError
    except ValueError:
        await message.answer("❌ Введи корректное число калорий (например, 350):")
        return

    user_id = message.from_user.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, message.message_id)
    await delete_message_safe(bot, message.chat.id, temps.get('diet_temp'))

    data = await state.get_data()
    meal_type = data.get('meal_type')
    description = data.get('food_description', '')
    save_food_log(user_id, meal_type, description, calories)
    asyncio.create_task(run_in_thread(sync_diet_rating_for_today, user_id))

    await state.update_data(manual_calories_value=calories)
    await state.set_state(DietState.new_food_name)
    msg = await message.answer(
        f"✅ Записано: {int(calories)} ккал\n\nСохранить в «Мои блюда»?",
        reply_markup=save_food_keyboard()
    )
    user_temp_messages.setdefault(user_id, {})['diet_temp'] = msg.message_id

@router.callback_query(DietState.new_food_name, F.data == "save_food_skip")
async def save_food_skip(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    data = await state.get_data()
    calories = data.get('manual_calories_value')
    await callback.message.delete()
    await state.clear()
    temp_msg = await callback.message.answer(f"✅ Записано: {int(calories)} ккал.")
    await asyncio.sleep(2)
    await delete_message_safe(bot, callback.message.chat.id, temp_msg.message_id)
    await show_diet_menu(user_id, callback.message.chat.id, bot)
    await callback.answer()

@router.callback_query(DietState.new_food_name, F.data == "save_food_yes")
async def save_food_yes_prompt(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await callback.message.delete()
    msg = await callback.message.answer("Введи название блюда для сохранения:")
    user_temp_messages.setdefault(callback.from_user.id, {})['diet_temp'] = msg.message_id
    await state.update_data(awaiting_food_name_input=True)
    await callback.answer()

@router.message(DietState.new_food_name, F.text)
async def save_my_food_name(message: Message, bot: Bot, state: FSMContext):
    name = message.text.strip()
    user_id = message.from_user.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, message.message_id)
    await delete_message_safe(bot, message.chat.id, temps.get('diet_temp'))

    data = await state.get_data()
    calories = data.get('manual_calories_value')

    add_my_food(user_id, name, calories)
    success_msg = await message.answer(f"✅ Блюдо «{name}» сохранено в Мои блюда.")
    await asyncio.sleep(2)
    await delete_message_safe(bot, message.chat.id, success_msg.message_id)

    await state.clear()
    temp_msg = await message.answer(f"✅ Записано: {int(calories)} ккал.")
    await asyncio.sleep(2)
    await delete_message_safe(bot, message.chat.id, temp_msg.message_id)
    await show_diet_menu(user_id, message.chat.id, bot)


@router.callback_query(F.data == "food_cancel")
async def food_cancel(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.clear()
    await callback.message.delete()
    await show_diet_menu(callback.from_user.id, callback.message.chat.id, bot)
    await callback.answer()

# ---------- Запись веса ----------
@router.message(F.text == "⚖️ Записать вес")
async def diet_log_weight_reply(message: Message, bot: Bot, state: FSMContext):
    await delete_message_safe(bot, message.chat.id, message.message_id)
    old_menu = user_last_menu.get(message.from_user.id)
    if old_menu:
        await delete_message_safe(bot, message.chat.id, old_menu)
        user_last_menu[message.from_user.id] = None
    await delete_temp_messages(bot, message.from_user.id, message.chat.id, keep_ai=True)
    await state.clear()
    await state.set_state(DietState.log_weight)
    msg = await message.answer("⚖️ Введи свой текущий вес (в кг):")
    user_temp_messages.setdefault(message.from_user.id, {})['diet_temp'] = msg.message_id

@router.message(DietState.log_weight)
async def diet_log_weight_finish(message: Message, bot: Bot, state: FSMContext):
    try:
        weight = float(message.text.strip().replace(',', '.'))
        if weight < 20 or weight > 300:
            raise ValueError
    except ValueError:
        await message.answer("❌ Введи корректный вес (например, 70.5):")
        return

    user_id = message.from_user.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, message.chat.id, message.message_id)
    await delete_message_safe(bot, message.chat.id, temps.get('diet_temp'))

    last_weight = get_last_weight(user_id)
    save_weight_log(user_id, weight)

    profile = get_diet_profile(user_id)
    motivation = ""
    if last_weight:
        diff = weight - last_weight
        if profile and profile['goal_type'] == 'loss':
            if diff < 0:
                motivation = f"\n✅ Отлично! Ты похудел на {abs(diff):.1f} кг. Так держать!"
            elif diff > 0:
                motivation = f"\n⚠️ Вес увеличился на {diff:.1f} кг. Не сдавайся, продолжай следить за питанием!"
            else:
                motivation = "\n👌 Вес не изменился. Держим уровень!"
        elif profile and profile['goal_type'] == 'gain':
            if diff > 0:
                motivation = f"\n✅ Отлично! Ты набрал {diff:.1f} кг. Прогресс!"
            elif diff < 0:
                motivation = f"\n⚠️ Вес уменьшился на {abs(diff):.1f} кг. Поднажми с питанием!"
            else:
                motivation = "\n👌 Вес не изменился."
        else:
            if abs(diff) < 1:
                motivation = "\n👍 Вес стабилен. Отлично!"
            elif diff > 0:
                motivation = f"\n📈 Вес вырос на {diff:.1f} кг. Если это не входило в планы, обрати внимание."
            else:
                motivation = f"\n📉 Вес снизился на {abs(diff):.1f} кг."

    await state.clear()
    success_msg = await message.answer(f"✅ Вес {weight} кг записан." + motivation)
    await asyncio.sleep(3)
    await delete_message_safe(bot, message.chat.id, success_msg.message_id)
    await show_diet_menu(user_id, message.chat.id, bot)

# ---------- Расчёт % жира ----------
@router.message(F.text == "🧮 Рассчитать % жира")
async def diet_body_fat_reply(message: Message, bot: Bot, state: FSMContext):
    await delete_message_safe(bot, message.chat.id, message.message_id)
    old_menu = user_last_menu.get(message.from_user.id)
    if old_menu:
        await delete_message_safe(bot, message.chat.id, old_menu)
        user_last_menu[message.from_user.id] = None
    await delete_temp_messages(bot, message.from_user.id, message.chat.id, keep_ai=True)
    await state.clear()
    instructions = (
        "Введи свои данные в одной строке через пробел:\n"
        "рост(см) вес(кг) обхват шеи(см) обхват талии(см) [обхват бёдер(см) для женщин]\n\n"
        "Пример для мужчины: 175 70 40 80\n"
        "Пример для женщины: 165 60 38 70 95"
    )
    await state.set_state(DietState.body_fat_measurements)
    msg = await message.answer(instructions)
    user_temp_messages.setdefault(message.from_user.id, {})['diet_temp'] = msg.message_id

@router.message(DietState.body_fat_measurements)
async def diet_body_fat_calculate(message: Message, bot: Bot, state: FSMContext):
    temps = user_temp_messages.get(message.from_user.id, {})
    error_msg_id = temps.get('body_fat_error')
    if error_msg_id:
        await delete_message_safe(bot, message.chat.id, error_msg_id)
        del temps['body_fat_error']
        user_temp_messages[message.from_user.id] = temps

    parts = message.text.strip().split()
    user_id = message.from_user.id

    if len(parts) not in (4, 5):
        error_msg = await message.answer("❌ Неверное количество чисел. Должно быть 4 (мужчины) или 5 (женщины).")
        temps['body_fat_error'] = error_msg.message_id
        user_temp_messages[user_id] = temps
        return

    try:
        numbers = [float(p.replace(',', '.')) for p in parts]
    except ValueError:
        error_msg = await message.answer("❌ Неверный формат чисел. Используй точки или запятые.")
        temps['body_fat_error'] = error_msg.message_id
        user_temp_messages[user_id] = temps
        return

    # Сохраняем сообщение пользователя с замерами (не удаляем)
    temps['body_fat_measurements'] = message.message_id
    user_temp_messages[user_id] = temps

    height_cm = numbers[0]
    weight = numbers[1]
    neck = numbers[2]
    waist = numbers[3]
    hip = numbers[4] if len(numbers) == 5 else None

    if hip is not None:  # женщина
        height_inch = height_cm * 0.393701
        diff = waist + hip - neck
        if diff <= 0:
            error_msg = await message.answer("❌ Сумма обхватов талии и бёдер должна быть больше обхвата шеи.")
            temps['body_fat_error'] = error_msg.message_id
            user_temp_messages[user_id] = temps
            return
        body_fat = 163.205 * math.log10(diff) - 97.684 * math.log10(height_inch) + 104.912
    else:  # мужчина — YMCA
        waist_inch = waist / 2.54
        weight_lb = weight * 2.20462
        body_fat = -98.42 + 4.15 * waist_inch - 0.082 * weight_lb
        if body_fat < 3:
            body_fat = 3.0
        elif body_fat > 50:
            body_fat = 50.0

    body_fat = round(body_fat, 2)
    warning = ""
    if body_fat < 2 or body_fat > 70:
        warning = f"\n⚠️ Результат ({body_fat}%) кажется необычным. Проверь измерения."

    # НЕ удаляем сообщение пользователя с замерами
    await delete_message_safe(bot, message.chat.id, temps.get('diet_temp'))

    save_body_fat(user_id, body_fat)
    await state.clear()
    success_msg = await message.answer(f"🧮 Процент жира: **{body_fat}%**{warning}", parse_mode="Markdown")
    # Сохраняем результат для возможного удаления позже
    temps['body_fat_result'] = success_msg.message_id
    user_temp_messages[user_id] = temps
    await show_diet_menu(user_id, message.chat.id, bot)

# ---------- История еды ----------
@router.message(F.text == "📖 История еды")
async def diet_food_history_reply(message: Message, bot: Bot, state: FSMContext):
    await delete_message_safe(bot, message.chat.id, message.message_id)
    old_menu = user_last_menu.get(message.from_user.id)
    if old_menu:
        await delete_message_safe(bot, message.chat.id, old_menu)
        user_last_menu[message.from_user.id] = None
    await delete_temp_messages(bot, message.from_user.id, message.chat.id, keep_ai=True)
    user_id = message.from_user.id
    user_food_history_page[user_id] = 0
    await show_food_history_page(user_id, message.chat.id, bot, state)

async def show_food_history_page(user_id: int, chat_id: int, bot: Bot, state: FSMContext, edit_message_id: int = None):
    page = user_food_history_page.get(user_id, 0)
    limit_days = 3
    offset_days = page * limit_days

    cursor = db.execute('''
        SELECT DISTINCT date
        FROM diet_log
        WHERE user_id = ?
        ORDER BY date DESC
    ''', (user_id,))
    all_dates = [row[0] for row in cursor.fetchall()]
    total_days = len(all_dates)
    total_pages = (total_days + limit_days - 1) // limit_days if total_days > 0 else 1

    if page >= total_pages and total_pages > 0:
        user_food_history_page[user_id] = total_pages - 1
        page = total_pages - 1
        offset_days = page * limit_days

    if total_days == 0:
        text = "📖 История еды пока пуста."
    else:
        start_idx = offset_days
        end_idx = min(offset_days + limit_days, total_days)
        page_dates = all_dates[start_idx:end_idx]

        lines = []
        for date in page_dates:
            food_cursor = db.execute('''
                SELECT meal_type, food_description, calories
                FROM diet_log
                WHERE user_id = ? AND date = ?
                ORDER BY timestamp
            ''', (user_id, date))
            day_foods = food_cursor.fetchall()
            formatted_date = datetime.strptime(date, '%Y-%m-%d').strftime('%d.%m.%Y')
            lines.append(f"\n📅 {formatted_date}")
            total_day_cal = 0
            for meal, desc, cal in day_foods:
                lines.append(f"  {meal}: {desc} ({int(cal)} ккал)")
                total_day_cal += cal
            lines.append(f"  🔥 Итого за день: {int(total_day_cal)} ккал")
        text = "📖 История еды\n" + "\n".join(lines)

    nav_buttons = []
    if page > 0:
        nav_buttons.append(InlineKeyboardButton(text="⬅️ Предыдущая", callback_data="food_history_prev"))
    if page < total_pages - 1:
        nav_buttons.append(InlineKeyboardButton(text="Следующая ➡️", callback_data="food_history_next"))

    keyboard_buttons = []
    if nav_buttons:
        keyboard_buttons.append(nav_buttons)
    keyboard_buttons.append([InlineKeyboardButton(text="🔙 Назад", callback_data="back_to_diet")])

    reply_markup = InlineKeyboardMarkup(inline_keyboard=keyboard_buttons)

    if edit_message_id:
        await bot.edit_message_text(text, chat_id, edit_message_id, reply_markup=reply_markup)
    else:
        msg = await bot.send_message(chat_id, text, reply_markup=reply_markup)
        user_temp_messages.setdefault(user_id, {})['food_history'] = msg.message_id

@router.callback_query(F.data == "food_history_prev")
async def food_history_prev(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    page = user_food_history_page.get(user_id, 0)
    if page > 0:
        user_food_history_page[user_id] = page - 1
    await show_food_history_page(user_id, callback.message.chat.id, bot, state, edit_message_id=callback.message.message_id)
    await callback.answer()

@router.callback_query(F.data == "food_history_next")
async def food_history_next(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    page = user_food_history_page.get(user_id, 0)
    user_food_history_page[user_id] = page + 1
    await show_food_history_page(user_id, callback.message.chat.id, bot, state, edit_message_id=callback.message.message_id)
    await callback.answer()

@router.callback_query(F.data == "back_to_diet")
async def back_to_diet(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await state.clear()
    await callback.message.delete()
    await show_diet_menu(callback.from_user.id, callback.message.chat.id, bot)
    await callback.answer()

# ---------- Графики диеты ----------
@router.message(F.text == "📈 Графики веса и % жира")
async def diet_charts_reply(message: Message, bot: Bot, state: FSMContext):
    await delete_message_safe(bot, message.chat.id, message.message_id)
    old_menu = user_last_menu.get(message.from_user.id)
    if old_menu:
        await delete_message_safe(bot, message.chat.id, old_menu)
        user_last_menu[message.from_user.id] = None
    await delete_temp_messages(bot, message.from_user.id, message.chat.id, keep_ai=True)
    user_id = message.from_user.id
    await bot.send_chat_action(message.chat.id, action=ChatAction.UPLOAD_PHOTO)

    cursor = db.execute('SELECT date, weight FROM weight_log WHERE user_id = ? ORDER BY date', (user_id,))
    weight_rows = cursor.fetchall()
    bf_cursor = db.execute('SELECT date, body_fat FROM body_fat_log WHERE user_id = ? ORDER BY date', (user_id,))
    fat_rows = cursor.fetchall()

    if len(weight_rows) < 2 and len(fat_rows) < 2:
        err = await message.answer("❌ Недостаточно данных для графиков (нужно минимум 2 записи по весу или % жира).")
        await asyncio.sleep(4)
        await delete_message_safe(bot, message.chat.id, err.message_id)
        await show_diet_menu(user_id, message.chat.id, bot)
        return

    dates_weight = [datetime.strptime(r[0], '%Y-%m-%d').strftime('%d.%m') for r in weight_rows]
    weights = [r[1] for r in weight_rows]
    dates_fat = [datetime.strptime(r[0], '%Y-%m-%d').strftime('%d.%m') for r in fat_rows]
    fats = [r[1] for r in fat_rows]

    fig = make_subplots(rows=2, cols=1, subplot_titles=("Вес (кг)", "Процент жира"))
    if dates_weight:
        fig.add_trace(go.Scatter(x=dates_weight, y=weights, mode='lines+markers', name='Вес'), row=1, col=1)
    if dates_fat:
        fig.add_trace(go.Scatter(x=dates_fat, y=fats, mode='lines+markers', name='% жира'), row=2, col=1)
    fig.update_layout(title="Динамика веса и % жира", height=600, showlegend=False, template='plotly_dark')

    chart_path = f"diet_chart_{user_id}.png"
    fig.write_image(chart_path, scale=2)
    photo = FSInputFile(chart_path)
    await bot.send_photo(
        user_id,
        photo,
        caption="📈 Динамика веса и % жира",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🔙 Назад", callback_data="back_to_diet")]])
    )
    os.remove(chart_path)

# ---------- Изменить цель ----------
@router.message(F.text == "⚙️ Изменить цель")
async def diet_change_goal_reply(message: Message, bot: Bot, state: FSMContext):
    await delete_message_safe(bot, message.chat.id, message.message_id)
    old_menu = user_last_menu.get(message.from_user.id)
    if old_menu:
        await delete_message_safe(bot, message.chat.id, old_menu)
        user_last_menu[message.from_user.id] = None
    await delete_temp_messages(bot, message.from_user.id, message.chat.id, keep_ai=True)
    await state.clear()
    await state.set_state(DietState.weight)
    msg = await message.answer("📝 Введи свой вес (в кг):")
    user_temp_messages.setdefault(message.from_user.id, {})['diet_setup'] = msg.message_id

# ---------- Обработчики шагов настройки диеты ----------

@router.message(DietState.weight)
async def diet_step_weight(message: Message, bot: Bot, state: FSMContext):
    try:
        weight = float(message.text.strip().replace(',', '.'))
        if not 20 <= weight <= 300:
            raise ValueError
    except ValueError:
        await message.answer("❌ Введи корректный вес (например, 75.5):")
        return
    try:
        await message.delete()
    except:
        pass
    temps = user_temp_messages.get(message.from_user.id, {})
    await delete_message_safe(bot, message.chat.id, temps.get('diet_setup'))
    await state.update_data(weight=weight)
    await state.set_state(DietState.height)
    msg = await message.answer("📝 Введи свой рост (в см):")
    user_temp_messages.setdefault(message.from_user.id, {})['diet_setup'] = msg.message_id

@router.message(DietState.height)
async def diet_step_height(message: Message, bot: Bot, state: FSMContext):
    try:
        height = float(message.text.strip().replace(',', '.'))
        if not 100 <= height <= 250:
            raise ValueError
    except ValueError:
        await message.answer("❌ Введи корректный рост (например, 175):")
        return
    try:
        await message.delete()
    except:
        pass
    temps = user_temp_messages.get(message.from_user.id, {})
    await delete_message_safe(bot, message.chat.id, temps.get('diet_setup'))
    await state.update_data(height=height)
    await state.set_state(DietState.age)
    msg = await message.answer("📝 Введи свой возраст (лет):")
    user_temp_messages.setdefault(message.from_user.id, {})['diet_setup'] = msg.message_id

@router.message(DietState.age)
async def diet_step_age(message: Message, bot: Bot, state: FSMContext):
    try:
        age = int(message.text.strip())
        if not 10 <= age <= 120:
            raise ValueError
    except ValueError:
        await message.answer("❌ Введи корректный возраст (например, 25):")
        return
    try:
        await message.delete()
    except:
        pass
    temps = user_temp_messages.get(message.from_user.id, {})
    await delete_message_safe(bot, message.chat.id, temps.get('diet_setup'))
    await state.update_data(age=age)
    await state.set_state(DietState.gender)
    msg = await message.answer("👤 Укажи пол:", reply_markup=gender_keyboard())
    user_temp_messages.setdefault(message.from_user.id, {})['diet_setup'] = msg.message_id

@router.callback_query(DietState.gender, F.data.in_({"gender_male", "gender_female"}))
async def diet_step_gender(callback: CallbackQuery, bot: Bot, state: FSMContext):
    gender = "мужской" if callback.data == "gender_male" else "женский"
    await callback.message.delete()
    await state.update_data(gender=gender)
    await state.set_state(DietState.activity)
    msg = await callback.message.answer("🏃 Выбери уровень активности:", reply_markup=activity_keyboard())
    user_temp_messages.setdefault(callback.from_user.id, {})['diet_setup'] = msg.message_id
    await callback.answer()

@router.callback_query(DietState.activity, F.data.startswith("activity_"))
async def diet_step_activity(callback: CallbackQuery, bot: Bot, state: FSMContext):
    try:
        activity_level = float(callback.data.split("_")[1])
    except (ValueError, IndexError):
        await callback.answer("❌ Ошибка выбора", show_alert=True)
        return
    await callback.message.delete()
    await state.update_data(activity_level=activity_level)
    await state.set_state(DietState.goal)
    msg = await callback.message.answer("🎯 Выбери цель:", reply_markup=goal_keyboard())
    user_temp_messages.setdefault(callback.from_user.id, {})['diet_setup'] = msg.message_id
    await callback.answer()

@router.callback_query(DietState.goal, F.data.in_({"goal_loss", "goal_maintain", "goal_gain"}))
async def diet_step_goal(callback: CallbackQuery, bot: Bot, state: FSMContext):
    goal_map = {"goal_loss": "loss", "goal_maintain": "maintain", "goal_gain": "gain"}
    goal_type = goal_map[callback.data]
    await callback.message.delete()
    await state.update_data(goal_type=goal_type)
    if goal_type == "maintain":
        await state.update_data(target_weight_change=0.0, target_days=30)
        await state.set_state(DietState.confirm)
        await _show_diet_confirm(callback.message, callback.from_user.id, state)
    else:
        await state.set_state(DietState.target_weight)
        direction = "сбросить" if goal_type == "loss" else "набрать"
        msg = await callback.message.answer(f"⚖️ Сколько кг хочешь {direction}? (например, 5):")
        user_temp_messages.setdefault(callback.from_user.id, {})['diet_setup'] = msg.message_id
    await callback.answer()

@router.message(DietState.target_weight)
async def diet_step_target_weight(message: Message, bot: Bot, state: FSMContext):
    try:
        change = float(message.text.strip().replace(',', '.'))
        if not 0.1 <= change <= 100:
            raise ValueError
    except ValueError:
        await message.answer("❌ Введи число (например, 5):")
        return
    try:
        await message.delete()
    except:
        pass
    temps = user_temp_messages.get(message.from_user.id, {})
    await delete_message_safe(bot, message.chat.id, temps.get('diet_setup'))
    await state.update_data(target_weight_change=change)
    await state.set_state(DietState.target_days)
    msg = await message.answer("📅 За сколько дней хочешь достичь цели? (например, 90):")
    user_temp_messages.setdefault(message.from_user.id, {})['diet_setup'] = msg.message_id

@router.message(DietState.target_days)
async def diet_step_target_days(message: Message, bot: Bot, state: FSMContext):
    try:
        days = int(message.text.strip())
        if not 7 <= days <= 730:
            raise ValueError
    except ValueError:
        await message.answer("❌ Введи число дней от 7 до 730:")
        return
    try:
        await message.delete()
    except:
        pass
    temps = user_temp_messages.get(message.from_user.id, {})
    await delete_message_safe(bot, message.chat.id, temps.get('diet_setup'))
    await state.update_data(target_days=days)
    await state.set_state(DietState.confirm)
    await _show_diet_confirm(message, message.from_user.id, state)

async def _show_diet_confirm(message, user_id: int, state: FSMContext):
    data = await state.get_data()
    weight = data.get('weight')
    height = data.get('height')
    age = data.get('age')
    gender = data.get('gender')
    activity_level = data.get('activity_level')
    goal_type = data.get('goal_type')
    target_change = data.get('target_weight_change', 0.0)
    target_days = data.get('target_days', 30)

    bmr = calculate_bmr(weight, height, age, gender)
    tdee = calculate_tdee(bmr, activity_level)
    daily_calories, warning = calculate_daily_calories(tdee, goal_type, target_change, target_days, gender)

    goal_label = {"loss": "Снижение веса", "maintain": "Поддержание веса", "gain": "Набор массы"}.get(goal_type, goal_type)
    activity_labels = {1.2: "Сидячий", 1.375: "Лёгкий", 1.55: "Умеренный", 1.725: "Высокий", 1.9: "Очень высокий"}
    activity_label = activity_labels.get(activity_level, str(activity_level))

    text = f"""📋 Проверь данные:

👤 Вес: {weight} кг | Рост: {height} см | Возраст: {age} лет
🚻 Пол: {gender} | Активность: {activity_label}
🎯 Цель: {goal_label}"""
    if goal_type != "maintain":
        text += f"\n⚖️ Изменение: {target_change} кг за {target_days} дней"
    text += f"\n\n🔥 Норма калорий: <b>{int(daily_calories)} ккал/день</b>"
    if warning != "ok":
        text += f"\n\n{warning}"
    text += "\n\nВсё верно?"

    await state.update_data(daily_calories=daily_calories)
    msg = await message.answer(text, parse_mode="HTML", reply_markup=diet_confirm_keyboard())
    user_temp_messages.setdefault(user_id, {})['diet_setup'] = msg.message_id

@router.callback_query(DietState.confirm, F.data == "diet_confirm")
async def diet_step_confirm(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    data = await state.get_data()
    await callback.message.delete()
    save_diet_profile(
        user_id=user_id,
        weight=data['weight'],
        height=data['height'],
        age=data['age'],
        gender=data['gender'],
        activity_level=data['activity_level'],
        goal_type=data['goal_type'],
        target_weight_change=data.get('target_weight_change', 0.0),
        target_days=data.get('target_days', 30),
        daily_calories=data['daily_calories']
    )
    await state.clear()
    success_msg = await callback.message.answer("✅ Профиль сохранён!")
    await asyncio.sleep(2)
    await delete_message_safe(bot, callback.message.chat.id, success_msg.message_id)
    await show_diet_menu(user_id, callback.message.chat.id, bot)
    await callback.answer()

@router.callback_query(DietState.confirm, F.data == "diet_restart")
async def diet_step_restart(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    await callback.message.delete()
    await state.clear()
    await state.set_state(DietState.weight)
    msg = await callback.message.answer("📝 Введи свой вес (в кг):")
    user_temp_messages.setdefault(user_id, {})['diet_setup'] = msg.message_id
    await callback.answer()

# ============ ЗАДАЧИ ============
async def show_tasks_menu(user_id: int, chat_id: int, bot: Bot):
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, chat_id, temps.get('tasks_menu'))
    tasks = get_all_active_tasks(user_id)
    if tasks:
        text = "📝 Твои задачи:"
    else:
        text = "📝 Задач пока нет. Добавь первую!"
    kb = tasks_menu_keyboard(tasks, user_id)
    msg = await bot.send_message(chat_id, text, reply_markup=kb)
    temps['tasks_menu'] = msg.message_id
    user_temp_messages[user_id] = temps

@router.message(F.text == "📝 Задачи")
async def handle_tasks(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    await state.clear()
    user_id = message.from_user.id
    old_menu = user_last_menu.get(user_id)
    if old_menu:
        await delete_message_safe(bot, message.chat.id, old_menu)
        user_last_menu[user_id] = None
    await delete_temp_messages(bot, user_id, message.chat.id, keep_ai=True)
    await show_tasks_menu(user_id, message.chat.id, bot)

@router.callback_query(F.data == "task_noop")
async def task_noop(callback: CallbackQuery):
    await callback.answer()

@router.callback_query(F.data.startswith("task_done_"))
async def task_done_press(callback: CallbackQuery, bot: Bot, state: FSMContext):
    task_id = int(callback.data.split("_")[2])
    user_id = callback.from_user.id
    # Проверяем откуда нажали: из меню задач или из главного меню
    cursor = db.execute('SELECT title, is_priority FROM tasks WHERE id = ? AND user_id = ?', (task_id, user_id))
    row = cursor.fetchone()
    if not row:
        await callback.answer("Задача не найдена", show_alert=True)
        return
    title = row[0][:40]
    await callback.message.edit_reply_markup(reply_markup=tasks_confirm_keyboard(task_id))
    await callback.answer(f"Выполнена: «{title}»?")

@router.callback_query(F.data.startswith("task_confirm_"))
async def task_confirm(callback: CallbackQuery, bot: Bot, state: FSMContext):
    task_id = int(callback.data.split("_")[2])
    user_id = callback.from_user.id
    complete_task(task_id, user_id)
    await callback.answer("✅ Готово!")
    # Check if this was from tasks_menu or urgent tasks in main menu
    temps = user_temp_messages.get(user_id, {})
    is_tasks_menu = temps.get('tasks_menu') == callback.message.message_id
    is_urgent_tasks = temps.get('urgent_tasks') == callback.message.message_id
    
    if is_urgent_tasks:
        # Urgent tasks in main menu area - just delete the message, don't show tasks menu
        urgent = get_urgent_tasks_for_menu(user_id)
        if not urgent:
            # Last task done - delete the urgent message
            try:
                await callback.message.delete()
            except:
                pass
            temps.pop('urgent_tasks', None)
            user_temp_messages[user_id] = temps
        else:
            # More tasks remain - edit the message with updated keyboard
            kb = urgent_tasks_keyboard(urgent, user_id)
            try:
                await callback.message.edit_reply_markup(reply_markup=kb)
            except:
                pass
    elif is_tasks_menu:
        # In tasks menu - refresh it
        try:
            await callback.message.delete()
        except:
            pass
        temps.pop('tasks_menu', None)
        user_temp_messages[user_id] = temps
        await show_tasks_menu(user_id, callback.message.chat.id, bot)
    else:
        # Unknown source - just delete the confirmation button
        try:
            await callback.message.delete()
        except:
            pass

@router.callback_query(F.data.startswith("task_del_"))
async def task_delete(callback: CallbackQuery, bot: Bot, state: FSMContext):
    task_id = int(callback.data.split("_")[2])
    user_id = callback.from_user.id
    delete_task(task_id, user_id)
    await callback.answer("🗑 Удалено")
    await show_tasks_menu(user_id, callback.message.chat.id, bot)
    try:
        await callback.message.delete()
    except:
        pass

@router.callback_query(F.data == "task_new")
async def task_new_start(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await callback.message.delete()
    await state.set_state(TaskState.entering_title)
    msg = await callback.message.answer("📝 Введи название задачи:")
    user_temp_messages.setdefault(callback.from_user.id, {})['task_create'] = msg.message_id
    await callback.answer()

@router.message(TaskState.entering_title)
async def task_enter_title(message: Message, bot: Bot, state: FSMContext):
    title = message.text.strip()
    if len(title) < 2:
        await message.answer("❌ Слишком короткое название, попробуй ещё раз:")
        return
    try:
        await message.delete()
    except:
        pass
    temps = user_temp_messages.get(message.from_user.id, {})
    await delete_message_safe(bot, message.chat.id, temps.get('task_create'))
    await state.update_data(task_title=title)
    await state.set_state(TaskState.choosing_repeat)
    msg = await message.answer(f"Задача \u00ab{title}\u00bb\n\nОна разовая или повторяющаяся?", reply_markup=task_repeat_keyboard())
    user_temp_messages.setdefault(message.from_user.id, {})['task_create'] = msg.message_id

@router.callback_query(TaskState.choosing_repeat, F.data.in_({"task_type_once", "task_type_repeat"}))
async def task_choose_type(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await callback.message.delete()
    if callback.data == "task_type_once":
        await state.update_data(repeat_days=None)
        await state.set_state(TaskState.choosing_priority)
        msg = await callback.message.answer("🔥 Это важная задача?", reply_markup=task_priority_keyboard())
    else:
        await state.update_data(selected_days=[])
        await state.set_state(TaskState.choosing_days)
        msg = await callback.message.answer(
            "🔁 Выбери дни недели (можно несколько):",
            reply_markup=task_days_keyboard([])
        )
    user_temp_messages.setdefault(callback.from_user.id, {})['task_create'] = msg.message_id
    await callback.answer()

@router.callback_query(TaskState.choosing_days, F.data.startswith("task_day_"))
async def task_toggle_day(callback: CallbackQuery, bot: Bot, state: FSMContext):
    day = callback.data.split("_")[2]
    data = await state.get_data()
    selected = data.get('selected_days', [])
    if day in selected:
        selected.remove(day)
    else:
        selected.append(day)
    await state.update_data(selected_days=selected)
    await callback.message.edit_reply_markup(reply_markup=task_days_keyboard(selected))
    await callback.answer()

@router.callback_query(TaskState.choosing_days, F.data == "task_days_done")
async def task_days_done(callback: CallbackQuery, bot: Bot, state: FSMContext):
    data = await state.get_data()
    selected = data.get('selected_days', [])
    if not selected:
        await callback.answer("Выбери хотя бы один день!", show_alert=True)
        return
    repeat_days = ",".join(sorted(selected, key=int))
    await state.update_data(repeat_days=repeat_days)
    await callback.message.delete()
    await state.set_state(TaskState.choosing_priority)
    msg = await callback.message.answer("🔥 Это важная задача?", reply_markup=task_priority_keyboard())
    user_temp_messages.setdefault(callback.from_user.id, {})['task_create'] = msg.message_id
    await callback.answer()

@router.callback_query(TaskState.choosing_priority, F.data.in_({"task_priority_yes", "task_priority_no"}))
async def task_choose_priority(callback: CallbackQuery, bot: Bot, state: FSMContext):
    is_priority = callback.data == "task_priority_yes"
    await state.update_data(is_priority=is_priority)
    await callback.message.delete()
    await state.set_state(TaskState.choosing_deadline)
    msg = await callback.message.answer("📅 Хочешь добавить дедлайн?", reply_markup=task_deadline_keyboard())
    user_temp_messages.setdefault(callback.from_user.id, {})['task_create'] = msg.message_id
    await callback.answer()

@router.callback_query(TaskState.choosing_deadline, F.data.in_({"task_deadline_yes", "task_deadline_no"}))
async def task_choose_deadline(callback: CallbackQuery, bot: Bot, state: FSMContext):
    await callback.message.delete()
    if callback.data == "task_deadline_yes":
        await state.set_state(TaskState.entering_deadline)
        msg = await callback.message.answer("📅 Введи дату дедлайна в формате ДД.ММ.ГГГГ:")
        user_temp_messages.setdefault(callback.from_user.id, {})['task_create'] = msg.message_id
    else:
        await state.update_data(deadline=None)
        await _save_task(callback.message, callback.from_user.id, bot, state)
    await callback.answer()

@router.message(TaskState.entering_deadline)
async def task_enter_deadline(message: Message, bot: Bot, state: FSMContext):
    text = message.text.strip()
    try:
        dl = datetime.strptime(text, '%d.%m.%Y')
        if dl.date() < user_today_date(message.from_user.id):
            await message.answer("❌ Дата уже прошла. Введи будущую дату:")
            return
        deadline_str = dl.strftime('%Y-%m-%d')
    except ValueError:
        err = await message.answer("❌ Неверный формат. Используй ДД.ММ.ГГГГ (например, 25.12.2025):")
        await asyncio.sleep(3)
        await delete_message_safe(bot, message.chat.id, err.message_id)
        return
    try:
        await message.delete()
    except:
        pass
    await state.update_data(deadline=deadline_str)
    await _save_task(message, message.from_user.id, bot, state)

async def _save_task(message, user_id: int, bot: Bot, state: FSMContext):
    data = await state.get_data()
    await state.clear()
    title = data.get('task_title', '')
    is_priority = data.get('is_priority', False)
    deadline = data.get('deadline')
    repeat_days = data.get('repeat_days')
    add_task(user_id, title, is_priority, deadline, repeat_days)
    chat_id = message.chat.id
    temps = user_temp_messages.get(user_id, {})
    await delete_message_safe(bot, chat_id, temps.get('task_create'))
    # Показываем подтверждение
    parts = []
    if is_priority:
        parts.append("🔥 важная")
    if repeat_days:
        parts.append(f"🔁 {format_repeat_days(repeat_days)}")
    if deadline:
        parts.append(f"⏰ до {datetime.strptime(deadline, '%Y-%m-%d').strftime('%d.%m.%Y')}")
    detail = " | ".join(parts)
    confirm_msg = await bot.send_message(chat_id, f"\u2705 Задача добавлена!\n\u00ab{title}\u00bb" + (f"\n{detail}" if detail else ""))
    await asyncio.sleep(2)
    await delete_message_safe(bot, chat_id, confirm_msg.message_id)
    await show_tasks_menu(user_id, chat_id, bot)

# ---------- СТАТИСТИКА ----------
@router.message(F.text == "📊 Статистика")
async def handle_stats(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    await state.clear()
    old_menu = user_last_menu.get(message.from_user.id)
    if old_menu:
        await delete_message_safe(bot, message.chat.id, old_menu)
        user_last_menu[message.from_user.id] = None
    await delete_temp_messages(bot, message.from_user.id, message.chat.id, keep_ai=True)
    msg = await message.answer("📊 Выбери тип статистики:", reply_markup=stats_keyboard())
    user_temp_messages.setdefault(message.from_user.id, {})['stats_choice'] = msg.message_id

@router.callback_query(F.data.startswith("stats:"))
async def show_stats(callback: CallbackQuery, bot: Bot, state: FSMContext):
    period = callback.data.split(":")[1]
    name = get_user_name(callback.from_user.id, callback.from_user.first_name)
    temps = user_temp_messages.get(callback.from_user.id, {})
    await delete_message_safe(bot, callback.message.chat.id, temps.get('stats_choice'))
    if period == "week":
        ratings = get_ratings(callback.from_user.id, days=7)
        text = f"📊 Статистика за неделю | {name}\n\n"
        for cat, avg, count in ratings:
            bar = create_short_progress_bar(int(avg))
            text += f"{cat}: {avg:.1f}/10 {bar}\n"
        msg = await callback.message.answer(text, reply_markup=rank_back_keyboard())
        user_temp_messages.setdefault(callback.from_user.id, {})['stats_result'] = msg.message_id
    elif period == "month":
        ratings = get_ratings(callback.from_user.id, days=30)
        text = f"📊 Статистика за месяц | {name}\n\n"
        for cat, avg, count in ratings:
            bar = create_short_progress_bar(int(avg))
            text += f"{cat}: {avg:.1f}/10 {bar}\n"
        msg = await callback.message.answer(text, reply_markup=rank_back_keyboard())
        user_temp_messages.setdefault(callback.from_user.id, {})['stats_result'] = msg.message_id
    elif period == "chart_week":
        await callback.answer("📈 Генерирую...")
        daily_data = get_daily_ratings(callback.from_user.id, days=7)
        if not daily_data:
            msg = await callback.message.answer("❌ Нет данных для графика", reply_markup=rank_back_keyboard())
            user_temp_messages.setdefault(callback.from_user.id, {})['stats_result'] = msg.message_id
            return
        temp_msg = await callback.message.answer("📈 Генерирую график...")
        chart_path = create_line_chart(daily_data, callback.from_user.id, days=7)
        photo = FSInputFile(chart_path)
        await callback.bot.send_photo(
            callback.from_user.id,
            photo,
            caption="📈 Динамика за неделю",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🔙 Назад", callback_data="back_to_main")]])
        )
        await delete_message_safe(bot, callback.message.chat.id, temp_msg.message_id)
        os.remove(chart_path)
    elif period == "chart_month":
        await callback.answer("📈 Генерирую...")
        daily_data = get_daily_ratings(callback.from_user.id, days=30)
        if not daily_data:
            msg = await callback.message.answer("❌ Нет данных для графика", reply_markup=rank_back_keyboard())
            user_temp_messages.setdefault(callback.from_user.id, {})['stats_result'] = msg.message_id
            return
        temp_msg = await callback.message.answer("📈 Генерирую график...")
        chart_path = create_line_chart(daily_data, callback.from_user.id, days=30)
        photo = FSInputFile(chart_path)
        await callback.bot.send_photo(
            callback.from_user.id,
            photo,
            caption="📈 Динамика за месяц",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🔙 Назад", callback_data="back_to_main")]])
        )
        await delete_message_safe(bot, callback.message.chat.id, temp_msg.message_id)
        os.remove(chart_path)
    await callback.answer()

# ---------- РАНГ ----------
@router.message(F.text == "⭐ Ранг")
async def handle_rank(message: Message, bot: Bot, state: FSMContext):
    try:
        await message.delete()
    except:
        pass
    await state.clear()
    rank_data = get_or_create_rank_data(message.from_user.id)
    name = get_user_name(message.from_user.id, message.from_user.first_name)
    rank_id = rank_data['current_rank']
    total = rank_data['total_sparks']
    needed, next_total = get_sparks_for_next_rank(rank_id, total)
    old_menu = user_last_menu.get(message.from_user.id)
    if old_menu:
        await delete_message_safe(bot, message.chat.id, old_menu)
        user_last_menu[message.from_user.id] = None
    text = f"""{name}, твой прогресс:

{get_rank_emoji(rank_id)} <b>{get_rank_name(rank_id)}</b>
✨ Искр: {total}/{next_total}
📊 Осталось до следующего ранга: {needed}

<i>{get_rank_motivation(rank_id)}</i>"""
    await delete_temp_messages(bot, message.from_user.id, message.chat.id, keep_ai=True)
    msg = await message.answer(text, parse_mode="HTML", reply_markup=rank_back_keyboard())
    user_temp_messages.setdefault(message.from_user.id, {})['rank'] = msg.message_id
    
    
def generate_proactive_ai_message(user_id: int) -> str:
    stats = get_user_stats_for_ai(user_id)
    name = get_user_name(user_id)
    yesterday = stats['yesterday']
    today = stats['today']

    prompt = f"""Пользователь {name}. Вчерашние данные: {yesterday}. Сегодня уже оценил: {today}.
    Составь короткое персональное приветствие-вопрос (макс 2 предложения) на основе вчерашних данных.
    Если вчера что-то было плохо (оценка <=4), спроси как сегодня.
    Если всё было хорошо, похвали и спроси что оценим сегодня.
    Обращайся по имени."""
    return gemini_generate(prompt, max_tokens=1024)
    
def analyze_low_rating(user_id: int, category: str, rating: int) -> str:
    name = get_user_name(user_id)
    stats = get_user_stats_for_ai(user_id)
    prompt = f"""Пользователь {name} поставил {category} {rating}/10. 
    Его статистика за неделю: {stats['week_avg']}. 
    Дай 1 конкретный совет что могло пойти не так и как улучшить. Макс 2 предложения. Обращайся по имени."""
    return gemini_generate(prompt, max_tokens=1024)
    
def generate_weekly_report(user_id: int) -> str:
    stats = get_user_stats_for_ai(user_id)
    name = get_user_name(user_id)
    daily_data = get_daily_ratings(user_id, days=7)

    day_scores = {}
    for date, cat, rating in daily_data:
        if date not in day_scores:
            day_scores[date] = []
        day_scores[date].append(rating)

    avg_by_day = {date: sum(ratings)/len(ratings) for date, ratings in day_scores.items() if ratings}

    best_day = max(avg_by_day, key=avg_by_day.get) if avg_by_day else None
    worst_day = min(avg_by_day, key=avg_by_day.get) if avg_by_day else None

    workout_data = stats['workouts']

    prompt = f"""Составь разбор недели для {name}:
    Лучший день: {best_day} (средняя {avg_by_day.get(best_day, 0):.1f})
    Худший день: {worst_day} (средняя {avg_by_day.get(worst_day, 0):.1f})
    Тренировок: {workout_data['current_count']}/{workout_data['monthly_goal']}
    Средние за неделю: {stats['week_avg']}

    Напиши:
    1. Краткий анализ лучшего дня (что было хорошо)
    2. Краткий анализ худшего дня (что пошло не так)
    3. Паттерн если виден (связь сна и активности и т.д.)
    4. Мотивирующий совет на следующую неделю

    Используй эмодзи, обращайся по имени, макс 5-6 предложений."""
    ai_analysis = gemini_generate(prompt, max_tokens=2048)

    best_day_str = f"{best_day[8:10]}.{best_day[5:7]}" if best_day else '--'
    worst_day_str = f"{worst_day[8:10]}.{worst_day[5:7]}" if worst_day else '--'

    report = f"""┌─ Разбор недели | {name}
│
│ 📈 Лучший день: {best_day_str}
│    Средняя оценка: {avg_by_day.get(best_day, 0):.1f}/10
│
│ 📉 Худший день: {worst_day_str}
│    Средняя оценка: {avg_by_day.get(worst_day, 0):.1f}/10
│
│ 🏋️ Тренировок: {workout_data['current_count']}/{workout_data['monthly_goal']}
│
│ 🤖 Анализ ИИ:
│    {ai_analysis}
└─────────────────────"""
    return report
    
async def main():
    global scheduler
    print("[BOOT] Старт...")
    init_db()
    print("[BOOT] База инициализирована")
    log_db_persistence_diagnostics()
    log_ratings_ai_diagnostics()
    
    dp = Dispatcher(storage=MemoryStorage())
    dp.include_router(router)
    print("[BOOT] Диспетчер готов")
    
    bot = Bot(token=BOT_TOKEN)
    print("[BOOT] Бот создан")

    scheduler = AsyncIOScheduler()
    for _, tz_name in RUSSIAN_TIMEZONES:
        scheduler.add_job(
            finalize_daily_ratings_for_timezone, 'cron',
            hour=23, minute=55, timezone=ZoneInfo(tz_name),
            args=[tz_name], id=f"finalize_ratings_{tz_name}", replace_existing=True
        )
    scheduler.start()
    print("[BOOT] Планировщик запущен")
    
    await bot.delete_webhook(drop_pending_updates=True)
    print("[BOOT] Webhook удалён")
    
    polling_task = asyncio.create_task(dp.start_polling(bot))
    print("[BOOT] Polling запущен")
    
    stop_signal = asyncio.Event()
    loop = asyncio.get_running_loop()
    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            loop.add_signal_handler(sig, stop_signal.set)
        except (NotImplementedError, AttributeError):
            signal.signal(sig, lambda *_: stop_signal.set())
    
    await stop_signal.wait()
    print("Получен сигнал остановки...")

    # Отменяем задачи
    polling_task.cancel()
    try:
        await asyncio.gather(polling_task, return_exceptions=True)
    except asyncio.CancelledError:
        pass

    # Закрываем соединения
    await bot.session.close()
    db.close()
    if scheduler:
        scheduler.shutdown()
    print("Бот остановлен")

if __name__ == "__main__":
    asyncio.run(main())

"""
Визуальный планировщик тем в виде графа.
Один файл. Запуск: python main.py
Требуется: Python 3.11+ и PySide6 (pip install PySide6).
"""
from __future__ import annotations

import json
import math
import os
import sys
import tempfile
import uuid
from pathlib import Path
from typing import Any

from PySide6.QtCore import (
    QEasingCurve,
    QLineF,
    QPoint,
    QPointF,
    QRectF,
    Qt,
    QTimer,
    QVariantAnimation,
    Signal,
)
from PySide6.QtGui import (
    QAction,
    QColor,
    QFont,
    QFontMetricsF,
    QKeySequence,
    QPainter,
    QPainterPath,
    QPen,
    QShortcut,
    QTransform,
)
from PySide6.QtWidgets import (
    QApplication,
    QGraphicsEllipseItem,
    QGraphicsItem,
    QGraphicsPathItem,
    QGraphicsScene,
    QGraphicsView,
    QInputDialog,
    QLabel,
    QMainWindow,
    QMenu,
    QMessageBox,
    QToolBar,
)


# ============================================================== КОНСТАНТЫ
DATA_FILE = Path(__file__).resolve().parent / "graph.json"
DATA_VERSION = 1

GRID_STEP = 22
MAJOR_EVERY = 5
MIN_RADIUS = 6.0
ROOT_RADIUS = 14.0

NODE_COLOR = QColor("#0D0D0D")
EDGE_COLOR = QColor("#2E2E2E")
SELECT_COLOR = QColor("#2D7FF9")
HOVER_COLOR = QColor("#9AA0A6")

# Анимации имени
LABEL_FADE_IN_MS = 180
LABEL_FADE_OUT_MS = 150
LABEL_SLIDE_PX = 8          # насколько плашка «выезжает» снизу вверх

AUTOSAVE_DELAY_MS = 400

STATUS_HINTS = (
    "Двойной клик по холсту — новая тема  ·  Двойной клик по точке — переименовать  ·  "
    "ПКМ по точке — меню  ·  Del — удалить  ·  Колесо — масштаб  ·  "
    "СКМ или Пробел+ЛКМ — панорама"
)


# ============================================================== ХРАНИЛИЩЕ
class GraphStore:
    """Атомарное JSON-хранилище графа с бэкапом повреждённого файла."""

    def __init__(self, path: Path) -> None:
        self.path = path

    def load(self) -> dict[str, Any]:
        if not self.path.exists():
            return {"version": DATA_VERSION, "nodes": []}
        raw = self.path.read_text(encoding="utf-8")
        data = json.loads(raw)
        if not isinstance(data, dict):
            raise ValueError("Корневой элемент JSON должен быть объектом")
        if not isinstance(data.get("nodes", []), list):
            raise ValueError("Поле 'nodes' должно быть списком")
        return data

    def save(self, data: dict[str, Any]) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        fd, tmp_name = tempfile.mkstemp(
            dir=str(self.path.parent), prefix=".graph-", suffix=".tmp"
        )
        tmp_path = Path(tmp_name)
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as fh:
                json.dump(data, fh, ensure_ascii=False, indent=2)
                fh.flush()
                os.fsync(fh.fileno())
            os.replace(tmp_path, self.path)
        finally:
            try:
                if tmp_path.exists():
                    tmp_path.unlink()
            except OSError:
                pass

    def backup_corrupted(self) -> Path | None:
        if not self.path.exists():
            return None
        backup = self.path.with_suffix(self.path.suffix + ".bak")
        try:
            if backup.exists():
                backup.unlink()
            self.path.rename(backup)
            return backup
        except OSError:
            return None


# ============================================================== ПЛАШКА
class HoverLabel(QGraphicsItem):
    """Всплывающая плашка с названием темы (динамическая, с анимацией)."""

    def __init__(self, text: str) -> None:
        super().__init__()
        self._text = text
        self._font = QFont()
        self._font.setPointSize(10)
        self._font.setBold(True)

        fm = QFontMetricsF(self._font)
        r = fm.boundingRect(text)
        pad_x, pad_y = 12.0, 6.0
        w = r.width() + pad_x * 2
        h = r.height() + pad_y * 2
        # Локальные координаты: «низ» плашки — в точке (0, 0),
        # чтобы удобно вешать её над узлом.
        self._rect = QRectF(-w / 2.0, -h, w, h)

        self.setZValue(1000)
        self.setOpacity(0.0)
        self.setAcceptedMouseButtons(Qt.NoButton)
        self.setAcceptHoverEvents(False)

    def boundingRect(self) -> QRectF:  # noqa: N802
        # Запас под тень и скругления.
        return self._rect.adjusted(-6, -6, 6, 10)

    def paint(self, painter: QPainter, option, widget=None) -> None:  # noqa: N802
        painter.setRenderHint(QPainter.Antialiasing, True)

        # Мягкая тень
        painter.setPen(Qt.NoPen)
        painter.setBrush(QColor(0, 0, 0, 35))
        painter.drawRoundedRect(self._rect.translated(0, 2), 9, 9)

        # Белая плашка с чёрной обводкой
        painter.setPen(QPen(QColor("#0D0D0D"), 1.3))
        painter.setBrush(QColor("#FFFFFF"))
        painter.drawRoundedRect(self._rect, 9, 9)

        # Текст
        painter.setPen(QColor("#0D0D0D"))
        painter.setFont(self._font)
        painter.drawText(self._rect, Qt.AlignCenter, self._text)


# ============================================================== ЭЛЕМЕНТЫ
class NodeItem(QGraphicsEllipseItem):
    """Тема графа — чёрная жирная точка с динамически всплывающим именем."""

    def __init__(
        self,
        node_id: str,
        title: str,
        parent_id: str | None,
        depth: int,
        radius: float,
    ) -> None:
        super().__init__(-radius, -radius, radius * 2.0, radius * 2.0)
        self.node_id = node_id
        self.title = title
        self.parent_id = parent_id
        self.depth = depth
        self.radius = radius
        self.attached_edges: set["EdgeItem"] = set()
        self._hovered = False

        # Состояние всплывающей плашки
        self._hover_label: HoverLabel | None = None
        self._label_base = QPointF()        # «финальная» позиция плашки
        self._label_anim: QVariantAnimation | None = None
        self._fade_out_anim: QVariantAnimation | None = None

        self.setFlag(QGraphicsItem.ItemIsMovable, True)
        self.setFlag(QGraphicsItem.ItemIsSelectable, True)
        self.setFlag(QGraphicsItem.ItemSendsGeometryChanges, True)
        self.setAcceptHoverEvents(True)
        self.setCursor(Qt.PointingHandCursor)
        self.setZValue(10)
        # Стандартный Qt-тултип выключён — теперь у нас своя красивая плашка.
        self.setToolTip("")

    # ------------------------------------------------------------ геометрия
    def boundingRect(self):  # noqa: N802
        return self.rect().adjusted(-8, -8, 8, 8)

    def shape(self):
        path = QPainterPath()
        path.addEllipse(self.rect().adjusted(-4, -4, 4, 4))
        return path

    # ---------------------------------------------------------------- paint
    def paint(self, painter: QPainter, option, widget=None) -> None:  # noqa: N802
        painter.setRenderHint(QPainter.Antialiasing, True)
        painter.setPen(Qt.NoPen)
        painter.setBrush(NODE_COLOR)
        painter.drawEllipse(self.rect())

        if self.isSelected():
            painter.setBrush(Qt.NoBrush)
            painter.setPen(QPen(SELECT_COLOR, 2.0))
            painter.drawEllipse(self.rect().adjusted(-5, -5, 5, 5))
        elif self._hovered:
            painter.setBrush(Qt.NoBrush)
            painter.setPen(QPen(HOVER_COLOR, 1.5))
            painter.drawEllipse(self.rect().adjusted(-5, -5, 5, 5))

    # --------------------------------------------------------------- hover
    def hoverEnterEvent(self, event):  # noqa: N802
        self._hovered = True
        self.update()
        self._show_label()
        super().hoverEnterEvent(event)

    def hoverLeaveEvent(self, event):  # noqa: N802
        self._hovered = False
        self.update()
        self._hide_label()
        super().hoverLeaveEvent(event)

    # ------------------------------------------------------- анимация имени
    def _label_final_pos(self) -> QPointF:
        """Финальная позиция плашки — чуть выше точки."""
        return self.pos() + QPointF(0.0, -self.radius - 10.0)

    def _show_label(self) -> None:
        scene = self.scene()
        if scene is None:
            return

        # Если плашка уже была (или в процессе исчезновения) — убираем немедленно.
        self._kill_label_immediate()

        label = HoverLabel(self.title)
        base = self._label_final_pos()
        self._label_base = base

        # Стартуем чуть ниже финальной позиции, чтобы «выехать» вверх.
        label.setPos(base + QPointF(0.0, LABEL_SLIDE_PX))
        label.setOpacity(0.0)
        scene.addItem(label)
        self._hover_label = label

        anim = QVariantAnimation()
        anim.setDuration(LABEL_FADE_IN_MS)
        anim.setStartValue(0.0)
        anim.setEndValue(1.0)
        anim.setEasingCurve(QEasingCurve.OutCubic)

        def _apply(v: float) -> None:
            # Плашка могла быть уже заменена новой — тогда ничего не делаем.
            if self._hover_label is not label:
                return
            label.setOpacity(float(v))
            label.setPos(base + QPointF(0.0, LABEL_SLIDE_PX * (1.0 - float(v))))

        anim.valueChanged.connect(_apply)
        self._label_anim = anim
        anim.start()

    def _hide_label(self) -> None:
        label = self._hover_label
        if label is None:
            return

        # Останавливаем «въезд», если он ещё идёт.
        if self._label_anim is not None:
            try:
                self._label_anim.stop()
            except Exception:
                pass
            self._label_anim = None

        anim = QVariantAnimation()
        anim.setDuration(LABEL_FADE_OUT_MS)
        anim.setStartValue(label.opacity())
        anim.setEndValue(0.0)
        anim.setEasingCurve(QEasingCurve.InCubic)

        def _apply(v: float) -> None:
            if self._hover_label is label:
                label.setOpacity(float(v))

        def _finished() -> None:
            if self._hover_label is label:
                self._hover_label = None
            sc = label.scene()
            if sc is not None:
                sc.removeItem(label)

        anim.valueChanged.connect(_apply)
        anim.finished.connect(_finished)
        self._fade_out_anim = anim
        anim.start()

    def _kill_label_immediate(self) -> None:
        """Мгновенно убирает плашку и все её анимации."""
        for attr in ("_label_anim", "_fade_out_anim"):
            a = getattr(self, attr, None)
            if a is not None:
                try:
                    a.stop()
                except Exception:
                    pass
                setattr(self, attr, None)

        label = self._hover_label
        if label is not None:
            sc = label.scene()
            if sc is not None:
                sc.removeItem(label)
        self._hover_label = None

    # ------------------------------------------------------- перемещение
    def itemChange(self, change, value):  # noqa: N802
        if change == QGraphicsItem.ItemPositionHasChanged:
            # Линии перерисовываются вслед за точкой.
            for edge in list(self.attached_edges):
                edge.update_path()

            # Плашка (если видна) следует за точкой.
            if self._hover_label is not None:
                base = self._label_final_pos()
                self._label_base = base
                # Сохраняем текущий офсет «въезда», зависящий от прозрачности.
                offset = LABEL_SLIDE_PX * (1.0 - self._hover_label.opacity())
                self._hover_label.setPos(base + QPointF(0.0, offset))

            scene = self.scene()
            notify = getattr(scene, "notify_changed", None)
            if notify is not None:
                notify()

        elif change == QGraphicsItem.ItemSceneChange and value is None:
            # Точку убирают из сцены — плашка должна исчезнуть вместе с ней.
            self._kill_label_immediate()

        return super().itemChange(change, value)

    # ------------------------------------------------------- контекстное меню
    def contextMenuEvent(self, event):  # noqa: N802
        scene = self.scene()
        if scene is None:
            return
        if not self.isSelected():
            scene.clearSelection()
            self.setSelected(True)

        menu = QMenu()
        act_branch = menu.addAction("Добавить ответвление")
        act_rename = menu.addAction("Переименовать")
        menu.addSeparator()
        act_delete = menu.addAction("Удалить")

        chosen = menu.exec(event.screenPos())
        if chosen is act_branch:
            scene.branchRequested.emit(self)
        elif chosen is act_rename:
            scene.renameRequested.emit(self)
        elif chosen is act_delete:
            scene.deleteRequested.emit(self)
        event.accept()


class EdgeItem(QGraphicsPathItem):
    """Изогнутая связь родитель → ребёнок (кубическая кривая Безье)."""

    def __init__(self, source: NodeItem, target: NodeItem) -> None:
        super().__init__()
        self.source = source
        self.target = target

        pen = QPen(EDGE_COLOR, 2.0)
        pen.setCapStyle(Qt.RoundCap)
        pen.setJoinStyle(Qt.RoundJoin)
        self.setPen(pen)
        self.setBrush(Qt.NoBrush)
        self.setZValue(-1)
        self.setAcceptedMouseButtons(Qt.NoButton)

        source.attached_edges.add(self)
        target.attached_edges.add(self)
        self.update_path()

    def update_path(self) -> None:
        p1 = self.source.pos()
        p2 = self.target.pos()

        dx = p2.x() - p1.x()
        dy = p2.y() - p1.y()
        dist = math.hypot(dx, dy)
        if dist < 1e-6:
            dx, dy, dist = 1.0, 0.0, 1.0

        nx, ny = -dy / dist, dx / dist
        bend = min(90.0, max(12.0, dist * 0.22))

        c1 = QPointF(p1.x() + dx * 0.25 + nx * bend, p1.y() + dy * 0.25 + ny * bend)
        c2 = QPointF(p1.x() + dx * 0.75 - nx * bend, p1.y() + dy * 0.75 - ny * bend)

        path = QPainterPath(p1)
        path.cubicTo(c1, c2, p2)
        self.setPath(path)

    def detach(self) -> None:
        self.source.attached_edges.discard(self)
        self.target.attached_edges.discard(self)


# ============================================================== СЦЕНА
class GraphScene(QGraphicsScene):
    """Холст с сеткой, управление темами и связями."""

    graphChanged = Signal()
    newRootRequested = Signal(QPointF)
    branchRequested = Signal(object)
    renameRequested = Signal(object)
    deleteRequested = Signal(object)

    def __init__(self, parent=None) -> None:
        super().__init__(parent)
        self.setSceneRect(QRectF(-4000, -4000, 8000, 8000))
        self._nodes: dict[str, NodeItem] = {}
        self._edges: list[EdgeItem] = []

    # ---------------------------------------------------------- фон
    def drawBackground(self, painter: QPainter, rect: QRectF) -> None:  # noqa: N802
        painter.fillRect(rect, QColor("#FFFFFF"))

        left = math.floor(rect.left() / GRID_STEP) * GRID_STEP
        top = math.floor(rect.top() / GRID_STEP) * GRID_STEP

        minor: list[QLineF] = []
        major: list[QLineF] = []
        major_step = GRID_STEP * MAJOR_EVERY

        x = left
        while x < rect.right() + GRID_STEP:
            line = QLineF(x, rect.top(), x, rect.bottom())
            (major if int(round(x)) % major_step == 0 else minor).append(line)
            x += GRID_STEP

        y = top
        while y < rect.bottom() + GRID_STEP:
            line = QLineF(rect.left(), y, rect.right(), y)
            (major if int(round(y)) % major_step == 0 else minor).append(line)
            y += GRID_STEP

        painter.setPen(QPen(QColor("#EFEFEF"), 0))
        painter.drawLines(minor)
        painter.setPen(QPen(QColor("#E1E1E1"), 0))
        painter.drawLines(major)

    # ---------------------------------------------------------- утилиты
    @staticmethod
    def _radius_for_depth(depth: int) -> float:
        return max(MIN_RADIUS, ROOT_RADIUS - depth * 2.5)

    def notify_changed(self) -> None:
        self.graphChanged.emit()

    def children_of(self, node_id: str) -> list[NodeItem]:
        return [n for n in self._nodes.values() if n.parent_id == node_id]

    def _is_occupied(self, pos: QPointF) -> bool:
        return any((n.pos() - pos).manhattanLength() < 34 for n in self._nodes.values())

    def _free_position(self, pos: QPointF) -> QPointF:
        p = QPointF(pos)
        step = 0
        while self._is_occupied(p):
            step += 1
            p = pos + QPointF(26 * step, 26 * step)
            if step > 40:
                break
        return p

    def _child_position(self, parent: NodeItem) -> QPointF:
        existing = sum(1 for n in self._nodes.values() if n.parent_id == parent.node_id)
        angle = -math.pi / 2 + existing * 2.399963
        dist = 120 + 12 * parent.depth
        return parent.pos() + QPointF(math.cos(angle) * dist, math.sin(angle) * dist)

    def _root_position(self) -> QPointF:
        views = self.views()
        if views:
            return views[0].mapToScene(views[0].viewport().rect().center())
        return QPointF(0, 0)

    # ---------------------------------------------------------- создание
    def create_node(
        self,
        title: str,
        parent_item: NodeItem | None = None,
        pos: QPointF | None = None,
    ) -> NodeItem | None:
        title = (title or "").strip()
        if not title:
            return None

        if parent_item is not None:
            depth = parent_item.depth + 1
            parent_id = parent_item.node_id
            if pos is None:
                pos = self._child_position(parent_item)
        else:
            depth = 0
            parent_id = None
            if pos is None:
                pos = self._root_position()

        pos = self._free_position(pos)
        return self._insert_node(
            uuid.uuid4().hex, title, parent_id, float(pos.x()), float(pos.y()), depth
        )

    def _insert_node(
        self,
        node_id: str,
        title: str,
        parent_id: str | None,
        x: float,
        y: float,
        depth: int,
    ) -> NodeItem:
        item = NodeItem(node_id, title, parent_id, depth, self._radius_for_depth(depth))
        item.setPos(x, y)
        self.addItem(item)
        self._nodes[node_id] = item

        if parent_id is not None and parent_id in self._nodes:
            edge = EdgeItem(self._nodes[parent_id], item)
            self.addItem(edge)
            self._edges.append(edge)

        self.notify_changed()
        return item

    # ---------------------------------------------------------- удаление
    def _remove_edge(self, edge: EdgeItem) -> None:
        edge.detach()
        if edge in self._edges:
            self._edges.remove(edge)
        self.removeItem(edge)

    def delete_node(self, item: NodeItem) -> None:
        for child in list(self.children_of(item.node_id)):
            self.delete_node(child)
        for edge in list(item.attached_edges):
            self._remove_edge(edge)
        self._nodes.pop(item.node_id, None)
        self.removeItem(item)
        self.notify_changed()

    def delete_selected(self) -> None:
        selected = [i for i in self.selectedItems() if isinstance(i, NodeItem)]
        if not selected:
            return
        ids = {i.node_id for i in selected}
        for item in selected:
            if not self._has_selected_ancestor(item, ids):
                self.delete_node(item)

    def _has_selected_ancestor(self, item: NodeItem, ids: set[str]) -> bool:
        pid = item.parent_id
        while pid:
            if pid in ids:
                return True
            parent = self._nodes.get(pid)
            pid = parent.parent_id if parent else None
        return False

    # ---------------------------------------------------------- правка
    def rename_node(self, item: NodeItem, title: str) -> bool:
        title = (title or "").strip()
        if not title:
            return False
        item.title = title
        # Обновляем текст активной плашки, если она видна.
        if item._hover_label is not None:
            try:
                item._hover_label._text = title  # noqa: SLF001
                item._hover_label.update()
            except Exception:
                pass
        item.update()
        self.notify_changed()
        return True

    # ---------------------------------------------------------- сериализация
    def serialize(self) -> dict:
        return {
            "version": DATA_VERSION,
            "nodes": [
                {
                    "id": item.node_id,
                    "title": item.title,
                    "parent_id": item.parent_id,
                    "x": round(item.pos().x(), 2),
                    "y": round(item.pos().y(), 2),
                }
                for item in self._nodes.values()
            ],
        }

    def clear_graph(self) -> None:
        for edge in list(self._edges):
            edge.detach()
            self.removeItem(edge)
        self._edges.clear()
        for item in list(self._nodes.values()):
            self.removeItem(item)
        self._nodes.clear()

    def load_graph(self, data: dict) -> None:
        self.clear_graph()
        raw_nodes = data.get("nodes", []) if isinstance(data, dict) else []

        prepared: dict[str, dict] = {}
        for entry in raw_nodes:
            if not isinstance(entry, dict):
                continue
            node_id = entry.get("id")
            title = entry.get("title")
            if not isinstance(node_id, str) or not node_id:
                continue
            if not isinstance(title, str) or not title.strip():
                continue

            parent_id = entry.get("parent_id")
            if not isinstance(parent_id, str):
                parent_id = None

            try:
                x = float(entry.get("x", 0.0))
                y = float(entry.get("y", 0.0))
            except (TypeError, ValueError):
                x, y = 0.0, 0.0

            prepared[node_id] = {
                "id": node_id,
                "title": title.strip(),
                "parent_id": parent_id,
                "x": x,
                "y": y,
            }

        for node in prepared.values():
            if node["parent_id"] not in prepared:
                node["parent_id"] = None

        depth_cache: dict[str, int] = {}

        def depth_of(node_id: str, guard: int = 0) -> int:
            if node_id in depth_cache:
                return depth_cache[node_id]
            parent_id = prepared[node_id]["parent_id"]
            depth = 0 if parent_id is None or guard > 200 else depth_of(parent_id, guard + 1) + 1
            depth_cache[node_id] = depth
            return depth

        ordered = sorted(prepared.values(), key=lambda n: depth_of(n["id"]))
        for node in ordered:
            self._insert_node(
                node["id"],
                node["title"],
                node["parent_id"],
                node["x"],
                node["y"],
                depth_of(node["id"]),
            )

        self.notify_changed()

    # ---------------------------------------------------------- мышь
    def mouseDoubleClickEvent(self, event) -> None:  # noqa: N802
        item = self.itemAt(event.scenePos(), QTransform())
        if isinstance(item, NodeItem):
            self.renameRequested.emit(item)
            event.accept()
            return
        if item is None and event.button() == Qt.LeftButton:
            self.newRootRequested.emit(event.scenePos())
            event.accept()
            return
        super().mouseDoubleClickEvent(event)


# ============================================================== ВИД
class GraphView(QGraphicsView):
    """Холст: зум колесом, панорама СКМ / Пробел+ЛКМ."""

    MIN_SCALE = 0.25
    MAX_SCALE = 3.0

    def __init__(self, scene: GraphScene, parent=None) -> None:
        super().__init__(scene, parent)

        self.setRenderHints(
            QPainter.Antialiasing | QPainter.TextAntialiasing | QPainter.SmoothPixmapTransform
        )
        self.setDragMode(QGraphicsView.NoDrag)
        self.setTransformationAnchor(QGraphicsView.AnchorUnderMouse)
        self.setResizeAnchor(QGraphicsView.AnchorViewCenter)
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.setViewportUpdateMode(QGraphicsView.FullViewportUpdate)
        self.setFocusPolicy(Qt.StrongFocus)
        self.setMouseTracking(True)

        self._space_pressed = False
        self._panning = False
        self._pan_last = QPoint()
        self._centered = False

    def showEvent(self, event):  # noqa: N802
        super().showEvent(event)
        if not self._centered:
            self._centered = True
            self.centerOn(0, 0)

    def wheelEvent(self, event):  # noqa: N802
        delta = event.angleDelta().y()
        if delta == 0:
            event.ignore()
            return
        self.zoom_by(1.0015 ** delta)
        event.accept()

    def zoom_by(self, factor: float) -> None:
        current = self.transform().m11()
        target = current * factor
        if target < self.MIN_SCALE:
            factor = self.MIN_SCALE / current
        elif target > self.MAX_SCALE:
            factor = self.MAX_SCALE / current
        if abs(factor - 1.0) < 1e-6:
            return
        self.scale(factor, factor)

    def fit_rect(self, rect) -> None:
        if rect.isNull() or rect.isEmpty():
            self.resetTransform()
            self.centerOn(0, 0)
            return
        padded = rect.adjusted(-120, -120, 120, 120)
        self.fitInView(padded, Qt.KeepAspectRatio)
        scale = self.transform().m11()
        if scale > self.MAX_SCALE:
            k = self.MAX_SCALE / scale
            self.scale(k, k)
        elif scale < self.MIN_SCALE:
            k = self.MIN_SCALE / scale
            self.scale(k, k)

    def _start_pan(self, pos: QPoint) -> None:
        self._panning = True
        self._pan_last = pos
        self.viewport().setCursor(Qt.ClosedHandCursor)

    def _stop_pan(self) -> None:
        self._panning = False
        if self._space_pressed:
            self.viewport().setCursor(Qt.OpenHandCursor)
        else:
            self.viewport().unsetCursor()

    def mousePressEvent(self, event):  # noqa: N802
        middle = event.button() == Qt.MiddleButton
        space_left = event.button() == Qt.LeftButton and self._space_pressed
        if middle or space_left:
            self._start_pan(event.position().toPoint())
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):  # noqa: N802
        if self._panning:
            pos = event.position().toPoint()
            delta = pos - self._pan_last
            self._pan_last = pos
            hbar = self.horizontalScrollBar()
            vbar = self.verticalScrollBar()
            hbar.setValue(hbar.value() - delta.x())
            vbar.setValue(vbar.value() - delta.y())
            event.accept()
            return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):  # noqa: N802
        if self._panning and event.button() in (Qt.MiddleButton, Qt.LeftButton):
            self._stop_pan()
            event.accept()
            return
        super().mouseReleaseEvent(event)

    def keyPressEvent(self, event):  # noqa: N802
        if event.key() == Qt.Key_Space and not event.isAutoRepeat():
            self._space_pressed = True
            if not self._panning:
                self.viewport().setCursor(Qt.OpenHandCursor)
            event.accept()
            return
        super().keyPressEvent(event)

    def keyReleaseEvent(self, event):  # noqa: N802
        if event.key() == Qt.Key_Space and not event.isAutoRepeat():
            self._space_pressed = False
            if not self._panning:
                self.viewport().unsetCursor()
            event.accept()
            return
        super().keyReleaseEvent(event)


# ============================================================== ОКНО
class MainWindow(QMainWindow):
    def __init__(self, store: GraphStore, parent=None) -> None:
        super().__init__(parent)
        self.store = store
        self.setWindowTitle("Планировщик тем — граф знаний")
        self.resize(1280, 820)

        self.scene = GraphScene(self)
        self.view = GraphView(self.scene, self)
        self.setCentralWidget(self.view)

        self._save_timer = QTimer(self)
        self._save_timer.setSingleShot(True)
        self._save_timer.setInterval(AUTOSAVE_DELAY_MS)
        self._save_timer.timeout.connect(self.save_graph)

        self._build_ui()
        self._load_graph()
        self._connect_scene()

    # ---------------------------------------------------------- UI
    def _build_ui(self) -> None:
        toolbar = QToolBar("Инструменты", self)
        toolbar.setMovable(False)
        toolbar.setToolButtonStyle(Qt.ToolButtonTextOnly)
        self.addToolBar(toolbar)

        act_add = QAction("Добавить тему", self)
        act_add.setShortcut(QKeySequence("Ctrl+N"))
        act_add.triggered.connect(self.add_root_topic)
        toolbar.addAction(act_add)

        act_fit = QAction("Показать всё", self)
        act_fit.triggered.connect(self.fit_all)
        toolbar.addAction(act_fit)

        act_delete = QAction("Удалить", self)
        act_delete.setShortcut(QKeySequence("Delete"))
        act_delete.triggered.connect(self.scene_delete_selected)
        toolbar.addAction(act_delete)

        esc = QShortcut(QKeySequence("Esc"), self)
        esc.activated.connect(self.scene.clearSelection)

        self._state_label = QLabel("Готово", self)
        self.statusBar().addPermanentWidget(self._state_label)
        self.statusBar().showMessage(STATUS_HINTS)

    def _connect_scene(self) -> None:
        self.scene.graphChanged.connect(self._on_graph_changed)
        self.scene.newRootRequested.connect(self._add_root_at)
        self.scene.branchRequested.connect(self.add_branch)
        self.scene.renameRequested.connect(self.rename_topic)
        self.scene.deleteRequested.connect(self.delete_topic)

    def _on_graph_changed(self) -> None:
        self._state_label.setText("Изменено…")
        self._save_timer.start()

    # ---------------------------------------------------------- действия
    def add_root_topic(self) -> None:
        pos = self.view.mapToScene(self.view.viewport().rect().center())
        self._add_root_at(pos)

    def _add_root_at(self, scene_pos) -> None:
        title, ok = QInputDialog.getText(self, "Новая тема", "Название темы:")
        if not ok:
            return
        title = title.strip()
        if not title:
            self._warn_empty()
            return
        item = self.scene.create_node(title, None, scene_pos)
        if item is not None:
            self.scene.clearSelection()
            item.setSelected(True)
            self.view.setFocus()

    def add_branch(self, parent: NodeItem) -> None:
        title, ok = QInputDialog.getText(
            self, "Новое ответвление", f"Название ответвления от «{parent.title}»:"
        )
        if not ok:
            return
        title = title.strip()
        if not title:
            self._warn_empty()
            return
        item = self.scene.create_node(title, parent)
        if item is not None:
            self.scene.clearSelection()
            item.setSelected(True)
            self.view.setFocus()

    def rename_topic(self, item: NodeItem) -> None:
        title, ok = QInputDialog.getText(
            self, "Переименовать", "Название темы:", text=item.title
        )
        if not ok:
            return
        if not self.scene.rename_node(item, title):
            self._warn_empty()
        self.view.setFocus()

    def delete_topic(self, item: NodeItem) -> None:
        self.scene.delete_node(item)

    def scene_delete_selected(self) -> None:
        self.scene.delete_selected()

    def fit_all(self) -> None:
        self.view.fit_rect(self.scene.itemsBoundingRect())

    # ---------------------------------------------------------- сохранение
    def save_graph(self) -> None:
        try:
            self.store.save(self.scene.serialize())
        except OSError as exc:
            self._state_label.setText("Ошибка сохранения")
            QMessageBox.critical(
                self, "Ошибка сохранения", f"Не удалось сохранить граф:\n{exc}"
            )
            return
        self._state_label.setText("Сохранено")

    def _load_graph(self) -> None:
        try:
            data = self.store.load()
        except FileNotFoundError:
            return
        except (ValueError, OSError) as exc:
            backup = self.store.backup_corrupted()
            extra = f"\n\nРезервная копия: {backup.name}" if backup else ""
            QMessageBox.warning(
                self,
                "Повреждённый файл данных",
                "Не удалось прочитать файл графа, будет создан пустой граф."
                f"\n\nПричина: {exc}{extra}",
            )
            return
        self.scene.load_graph(data)
        self.view.fit_rect(self.scene.itemsBoundingRect())
        self._state_label.setText("Загружено")

    # ---------------------------------------------------------- прочее
    def _warn_empty(self) -> None:
        QMessageBox.warning(
            self, "Пустое название", "Название темы не может быть пустым."
        )

    def closeEvent(self, event):  # noqa: N802
        if self._save_timer.isActive():
            self._save_timer.stop()
        self.save_graph()
        super().closeEvent(event)


# ============================================================== ЗАПУСК
def main() -> int:
    app = QApplication(sys.argv)
    app.setApplicationName("Планировщик тем")
    app.setOrganizationName("GraphPlanner")

    window = MainWindow(GraphStore(DATA_FILE))
    window.show()
    return app.exec()


if __name__ == "__main__":
    sys.exit(main())
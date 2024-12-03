/*!
 * chartjs-chart-matrix v2.0.1
 * https://chartjs-chart-matrix.pages.dev/
 * (c) 2023 Jukka Kurkela
 * Released under the MIT license
 */
import { DatasetController, Element } from 'chart.js';
import { toTRBLCorners, addRoundedRectPath, isObject } from 'chart.js/helpers';

var version = "2.0.1";

class MatrixController extends DatasetController {

  static id = 'matrix';
  static version = version;

  static defaults = {
    dataElementType: 'matrix',

    animations: {
      numbers: {
        type: 'number',
        properties: ['x', 'y', 'width', 'height']
      }
    },
  };

  static overrides = {
    interaction: {
      mode: 'nearest',
      intersect: true
    },
    scales: {
      x: {
        type: 'linear',
        offset: true
      },
      y: {
        type: 'linear',
        reverse: true
      }
    },
  };

  initialize() {
    this.enableOptionSharing = true;
    super.initialize();
  }

  update(mode) {
    const me = this;
    const meta = me._cachedMeta;

    me.updateElements(meta.data, 0, meta.data.length, mode);
  }

  updateElements(rects, start, count, mode) {
    const me = this;
    const reset = mode === 'reset';
    const {xScale, yScale} = me._cachedMeta;
    const firstOpts = me.resolveDataElementOptions(start, mode);
    const sharedOptions = me.getSharedOptions(mode, rects[start], firstOpts);

    for (let i = start; i < start + count; i++) {
      const parsed = !reset && me.getParsed(i);
      const x = reset ? xScale.getBasePixel() : xScale.getPixelForValue(parsed.x);
      const y = reset ? yScale.getBasePixel() : yScale.getPixelForValue(parsed.y);
      const options = me.resolveDataElementOptions(i, mode);
      const {width, height, anchorX, anchorY} = options;
      const properties = {
        x: resolveX(anchorX, x, width),
        y: resolveY(anchorY, y, height),
        width,
        height,
        options
      };
      me.updateElement(rects[i], i, properties, mode);
    }

    me.updateSharedOptions(sharedOptions, mode);
  }

  draw() {
    const me = this;
    const data = me.getMeta().data || [];
    let i, ilen;

    for (i = 0, ilen = data.length; i < ilen; ++i) {
      data[i].draw(me._ctx);
    }
  }
}

function resolveX(anchorX, x, width) {
  if (anchorX === 'left' || anchorX === 'start') {
    return x;
  }
  if (anchorX === 'right' || anchorX === 'end') {
    return x - width;
  }
  return x - width / 2;
}

function resolveY(anchorY, y, height) {
  if (anchorY === 'top' || anchorY === 'start') {
    return y;
  }
  if (anchorY === 'bottom' || anchorY === 'end') {
    return y - height;
  }
  return y - height / 2;
}

/**
 * Helper function to get the bounds of the rect
 * @param {MatrixElement} rect the rect
 * @param {boolean} [useFinalPosition]
 * @return {object} bounds of the rect
 * @private
 */
function getBounds(rect, useFinalPosition) {
  const {x, y, width, height} = rect.getProps(['x', 'y', 'width', 'height'], useFinalPosition);
  return {left: x, top: y, right: x + width, bottom: y + height};
}

function limit(value, min, max) {
  return Math.max(Math.min(value, max), min);
}

function parseBorderWidth(rect, maxW, maxH) {
  const value = rect.options.borderWidth;
  let t, r, b, l;

  if (isObject(value)) {
    t = +value.top || 0;
    r = +value.right || 0;
    b = +value.bottom || 0;
    l = +value.left || 0;
  } else {
    t = r = b = l = +value || 0;
  }

  return {
    t: limit(t, 0, maxH),
    r: limit(r, 0, maxW),
    b: limit(b, 0, maxH),
    l: limit(l, 0, maxW)
  };
}

function boundingRects(rect) {
  const bounds = getBounds(rect);
  const width = bounds.right - bounds.left;
  const height = bounds.bottom - bounds.top;
  const border = parseBorderWidth(rect, width / 2, height / 2);

  return {
    outer: {
      x: bounds.left,
      y: bounds.top,
      w: width,
      h: height
    },
    inner: {
      x: bounds.left + border.l,
      y: bounds.top + border.t,
      w: width - border.l - border.r,
      h: height - border.t - border.b
    }
  };
}

function inRange(rect, x, y, useFinalPosition) {
  const skipX = x === null;
  const skipY = y === null;
  const bounds = !rect || (skipX && skipY) ? false : getBounds(rect, useFinalPosition);

  return bounds
		&& (skipX || x >= bounds.left && x <= bounds.right)
		&& (skipY || y >= bounds.top && y <= bounds.bottom);
}

class MatrixElement extends Element {

  static id = 'matrix';

  static defaults = {
    backgroundColor: undefined,
    borderColor: undefined,
    borderWidth: undefined,
    borderRadius: 0,
    anchorX: 'center',
    anchorY: 'center',
    width: 20,
    height: 20
  };

  constructor(cfg) {
    super();

    this.options = undefined;
    this.width = undefined;
    this.height = undefined;

    if (cfg) {
      Object.assign(this, cfg);
    }
  }

  draw(ctx) {
    const options = this.options;
    const {inner, outer} = boundingRects(this);
    const radius = toTRBLCorners(options.borderRadius);

    ctx.save();

    if (outer.w !== inner.w || outer.h !== inner.h) {
      ctx.beginPath();
      addRoundedRectPath(ctx, {x: outer.x, y: outer.y, w: outer.w, h: outer.h, radius});
      addRoundedRectPath(ctx, {x: inner.x, y: inner.y, w: inner.w, h: inner.h, radius});
      ctx.fillStyle = options.backgroundColor;
      ctx.fill();
      ctx.fillStyle = options.borderColor;
      ctx.fill('evenodd');
    } else {
      ctx.beginPath();
      addRoundedRectPath(ctx, {x: inner.x, y: inner.y, w: inner.w, h: inner.h, radius});
      ctx.fillStyle = options.backgroundColor;
      ctx.fill();
    }

    ctx.restore();
  }

  inRange(mouseX, mouseY, useFinalPosition) {
    return inRange(this, mouseX, mouseY, useFinalPosition);
  }

  inXRange(mouseX, useFinalPosition) {
    return inRange(this, mouseX, null, useFinalPosition);
  }

  inYRange(mouseY, useFinalPosition) {
    return inRange(this, null, mouseY, useFinalPosition);
  }

  getCenterPoint(useFinalPosition) {
    const {x, y, width, height} = this.getProps(['x', 'y', 'width', 'height'], useFinalPosition);
    return {
      x: x + width / 2,
      y: y + height / 2
    };
  }

  tooltipPosition() {
    return this.getCenterPoint();
  }

  getRange(axis) {
    return axis === 'x' ? this.width / 2 : this.height / 2;
  }
}

export { MatrixController, MatrixElement };

import React, {forwardRef, Children} from 'react';

function _classCallCheck(instance, Constructor) {
  if (!(instance instanceof Constructor)) {
    throw new TypeError('Cannot call a class as a function');
  }
}

function _defineProperties(target, props) {
  for (let i = 0; i < props.length; i++) {
    const descriptor = props[i];
    descriptor.enumerable = descriptor.enumerable || false;
    descriptor.configurable = true;
    if ('value' in descriptor) descriptor.writable = true;
    Object.defineProperty(target, descriptor.key, descriptor);
  }
}

function _createClass(Constructor, protoProps, staticProps) {
  if (protoProps) _defineProperties(Constructor.prototype, protoProps);
  if (staticProps) _defineProperties(Constructor, staticProps);
  return Constructor;
}

function _defineProperty(obj, key, value) {
  if (key in obj) {
    Object.defineProperty(obj, key, {
      value,
      enumerable: true,
      configurable: true,
      writable: true,
    });
  } else {
    obj[key] = value;
  }

  return obj;
}

function _extends() {
  _extends =
    Object.assign ||
    function (target) {
      for (let i = 1; i < arguments.length; i++) {
        const source = arguments[i];

        for (const key in source) {
          if (Object.prototype.hasOwnProperty.call(source, key)) {
            target[key] = source[key];
          }
        }
      }

      return target;
    };

  return _extends.apply(this, arguments);
}

function ownKeys(object, enumerableOnly) {
  const keys = Object.keys(object);

  if (Object.getOwnPropertySymbols) {
    let symbols = Object.getOwnPropertySymbols(object);
    if (enumerableOnly)
      symbols = symbols.filter(
        sym => Object.getOwnPropertyDescriptor(object, sym).enumerable
      );
    keys.push.apply(keys, symbols);
  }

  return keys;
}

function _objectSpread2(target) {
  for (let i = 1; i < arguments.length; i++) {
    var source = arguments[i] != null ? arguments[i] : {};

    if (i % 2) {
      ownKeys(Object(source), true).forEach(key => {
        _defineProperty(target, key, source[key]);
      });
    } else if (Object.getOwnPropertyDescriptors) {
      Object.defineProperties(target, Object.getOwnPropertyDescriptors(source));
    } else {
      ownKeys(Object(source)).forEach(key => {
        Object.defineProperty(
          target,
          key,
          Object.getOwnPropertyDescriptor(source, key)
        );
      });
    }
  }

  return target;
}

function _inherits(subClass, superClass) {
  if (typeof superClass !== 'function' && superClass !== null) {
    throw new TypeError('Super expression must either be null or a function');
  }

  subClass.prototype = Object.create(superClass && superClass.prototype, {
    constructor: {
      value: subClass,
      writable: true,
      configurable: true,
    },
  });
  if (superClass) _setPrototypeOf(subClass, superClass);
}

function _getPrototypeOf(o) {
  _getPrototypeOf = Object.setPrototypeOf
    ? Object.getPrototypeOf
    : function _getPrototypeOf(o) {
        return o.__proto__ || Object.getPrototypeOf(o);
      };
  return _getPrototypeOf(o);
}

function _setPrototypeOf(o, p) {
  _setPrototypeOf =
    Object.setPrototypeOf ||
    function _setPrototypeOf(o, p) {
      o.__proto__ = p;
      return o;
    };

  return _setPrototypeOf(o, p);
}

function _isNativeReflectConstruct() {
  if (typeof Reflect === 'undefined' || !Reflect.construct) return false;
  if (Reflect.construct.sham) return false;
  if (typeof Proxy === 'function') return true;

  try {
    Boolean.prototype.valueOf.call(Reflect.construct(Boolean, [], () => {}));
    return true;
  } catch (e) {
    return false;
  }
}

function _objectWithoutPropertiesLoose(source, excluded) {
  if (source == null) return {};
  const target = {};
  const sourceKeys = Object.keys(source);
  let key;
  let i;

  for (i = 0; i < sourceKeys.length; i++) {
    key = sourceKeys[i];
    if (excluded.indexOf(key) >= 0) continue;
    target[key] = source[key];
  }

  return target;
}

function _objectWithoutProperties(source, excluded) {
  if (source == null) return {};

  const target = _objectWithoutPropertiesLoose(source, excluded);

  let key;
  let i;

  if (Object.getOwnPropertySymbols) {
    const sourceSymbolKeys = Object.getOwnPropertySymbols(source);

    for (i = 0; i < sourceSymbolKeys.length; i++) {
      key = sourceSymbolKeys[i];
      if (excluded.indexOf(key) >= 0) continue;
      if (!Object.prototype.propertyIsEnumerable.call(source, key)) continue;
      target[key] = source[key];
    }
  }

  return target;
}

function _assertThisInitialized(self) {
  if (self === void 0) {
    throw new ReferenceError(
      "this hasn't been initialised - super() hasn't been called"
    );
  }

  return self;
}

function _possibleConstructorReturn(self, call) {
  if (call && (typeof call === 'object' || typeof call === 'function')) {
    return call;
  }

  return _assertThisInitialized(self);
}

function _createSuper(Derived) {
  const hasNativeReflectConstruct = _isNativeReflectConstruct();

  return function _createSuperInternal() {
    const Super = _getPrototypeOf(Derived);
    let result;

    if (hasNativeReflectConstruct) {
      const NewTarget = _getPrototypeOf(this).constructor;

      result = Reflect.construct(Super, arguments, NewTarget);
    } else {
      result = Super.apply(this, arguments);
    }

    return _possibleConstructorReturn(this, result);
  };
}

function createCommonjsModule(fn) {
  const module = {exports: {}};
  return fn(module, module.exports), module.exports;
}

/** @license React v16.13.1
 * react-is.production.min.js
 *
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */
const b = typeof Symbol === 'function' && Symbol.for;
const c = b ? Symbol.for('react.element') : 60103;
const d = b ? Symbol.for('react.portal') : 60106;
const e = b ? Symbol.for('react.fragment') : 60107;
const f = b ? Symbol.for('react.strict_mode') : 60108;
const g = b ? Symbol.for('react.profiler') : 60114;
const h = b ? Symbol.for('react.provider') : 60109;
const k = b ? Symbol.for('react.context') : 60110;
const l = b ? Symbol.for('react.async_mode') : 60111;
const m = b ? Symbol.for('react.concurrent_mode') : 60111;
const n = b ? Symbol.for('react.forward_ref') : 60112;
const p = b ? Symbol.for('react.suspense') : 60113;
const q = b ? Symbol.for('react.suspense_list') : 60120;
const r = b ? Symbol.for('react.memo') : 60115;
const t = b ? Symbol.for('react.lazy') : 60116;
const v = b ? Symbol.for('react.block') : 60121;
const w = b ? Symbol.for('react.fundamental') : 60117;
const x = b ? Symbol.for('react.responder') : 60118;
const y = b ? Symbol.for('react.scope') : 60119;
function z(a) {
  if (typeof a === 'object' && a !== null) {
    const u = a.$$typeof;
    switch (u) {
      case c:
        switch (((a = a.type), a)) {
          case l:
          case m:
          case e:
          case g:
          case f:
          case p:
            return a;
          default:
            switch (((a = a && a.$$typeof), a)) {
              case k:
              case n:
              case t:
              case r:
              case h:
                return a;
              default:
                return u;
            }
        }
      case d:
        return u;
    }
  }
}
function A(a) {
  return z(a) === m;
}
const AsyncMode = l;
const ConcurrentMode = m;
const ContextConsumer = k;
const ContextProvider = h;
const Element$1 = c;
const ForwardRef = n;
const Fragment = e;
const Lazy = t;
const Memo = r;
const Portal = d;
const Profiler = g;
const StrictMode = f;
const Suspense = p;
const isAsyncMode = function (a) {
  return A(a) || z(a) === l;
};
const isConcurrentMode = A;
const isContextConsumer = function (a) {
  return z(a) === k;
};
const isContextProvider = function (a) {
  return z(a) === h;
};
const isElement = function (a) {
  return typeof a === 'object' && a !== null && a.$$typeof === c;
};
const isForwardRef = function (a) {
  return z(a) === n;
};
const isFragment = function (a) {
  return z(a) === e;
};
const isLazy = function (a) {
  return z(a) === t;
};
const isMemo = function (a) {
  return z(a) === r;
};
const isPortal = function (a) {
  return z(a) === d;
};
const isProfiler = function (a) {
  return z(a) === g;
};
const isStrictMode = function (a) {
  return z(a) === f;
};
const isSuspense = function (a) {
  return z(a) === p;
};
const isValidElementType = function (a) {
  return (
    typeof a === 'string' ||
    typeof a === 'function' ||
    a === e ||
    a === m ||
    a === g ||
    a === f ||
    a === p ||
    a === q ||
    (typeof a === 'object' &&
      a !== null &&
      (a.$$typeof === t ||
        a.$$typeof === r ||
        a.$$typeof === h ||
        a.$$typeof === k ||
        a.$$typeof === n ||
        a.$$typeof === w ||
        a.$$typeof === x ||
        a.$$typeof === y ||
        a.$$typeof === v))
  );
};
const typeOf = z;

const reactIs_production_min = {
  AsyncMode,
  ConcurrentMode,
  ContextConsumer,
  ContextProvider,
  Element: Element$1,
  ForwardRef,
  Fragment,
  Lazy,
  Memo,
  Portal,
  Profiler,
  StrictMode,
  Suspense,
  isAsyncMode,
  isConcurrentMode,
  isContextConsumer,
  isContextProvider,
  isElement,
  isForwardRef,
  isFragment,
  isLazy,
  isMemo,
  isPortal,
  isProfiler,
  isStrictMode,
  isSuspense,
  isValidElementType,
  typeOf,
};

/** @license React v16.13.1
 * react-is.development.js
 *
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

const reactIs_development = createCommonjsModule((module, exports) => {
  if (process.env.NODE_ENV !== 'production') {
    (function () {
      // The Symbol used to tag the ReactElement-like types. If there is no native Symbol
      // nor polyfill, then a plain number is used for performance.
      const hasSymbol = typeof Symbol === 'function' && Symbol.for;
      const REACT_ELEMENT_TYPE = hasSymbol
        ? Symbol.for('react.element')
        : 0xeac7;
      const REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
      const REACT_FRAGMENT_TYPE = hasSymbol
        ? Symbol.for('react.fragment')
        : 0xeacb;
      const REACT_STRICT_MODE_TYPE = hasSymbol
        ? Symbol.for('react.strict_mode')
        : 0xeacc;
      const REACT_PROFILER_TYPE = hasSymbol
        ? Symbol.for('react.profiler')
        : 0xead2;
      const REACT_PROVIDER_TYPE = hasSymbol
        ? Symbol.for('react.provider')
        : 0xeacd;
      const REACT_CONTEXT_TYPE = hasSymbol
        ? Symbol.for('react.context')
        : 0xeace; // TODO: We don't use AsyncMode or ConcurrentMode anymore. They were temporary
      // (unstable) APIs that have been removed. Can we remove the symbols?

      const REACT_ASYNC_MODE_TYPE = hasSymbol
        ? Symbol.for('react.async_mode')
        : 0xeacf;
      const REACT_CONCURRENT_MODE_TYPE = hasSymbol
        ? Symbol.for('react.concurrent_mode')
        : 0xeacf;
      const REACT_FORWARD_REF_TYPE = hasSymbol
        ? Symbol.for('react.forward_ref')
        : 0xead0;
      const REACT_SUSPENSE_TYPE = hasSymbol
        ? Symbol.for('react.suspense')
        : 0xead1;
      const REACT_SUSPENSE_LIST_TYPE = hasSymbol
        ? Symbol.for('react.suspense_list')
        : 0xead8;
      const REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
      const REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;
      const REACT_BLOCK_TYPE = hasSymbol ? Symbol.for('react.block') : 0xead9;
      const REACT_FUNDAMENTAL_TYPE = hasSymbol
        ? Symbol.for('react.fundamental')
        : 0xead5;
      const REACT_RESPONDER_TYPE = hasSymbol
        ? Symbol.for('react.responder')
        : 0xead6;
      const REACT_SCOPE_TYPE = hasSymbol ? Symbol.for('react.scope') : 0xead7;

      function isValidElementType(type) {
        return (
          typeof type === 'string' ||
          typeof type === 'function' || // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
          type === REACT_FRAGMENT_TYPE ||
          type === REACT_CONCURRENT_MODE_TYPE ||
          type === REACT_PROFILER_TYPE ||
          type === REACT_STRICT_MODE_TYPE ||
          type === REACT_SUSPENSE_TYPE ||
          type === REACT_SUSPENSE_LIST_TYPE ||
          (typeof type === 'object' &&
            type !== null &&
            (type.$$typeof === REACT_LAZY_TYPE ||
              type.$$typeof === REACT_MEMO_TYPE ||
              type.$$typeof === REACT_PROVIDER_TYPE ||
              type.$$typeof === REACT_CONTEXT_TYPE ||
              type.$$typeof === REACT_FORWARD_REF_TYPE ||
              type.$$typeof === REACT_FUNDAMENTAL_TYPE ||
              type.$$typeof === REACT_RESPONDER_TYPE ||
              type.$$typeof === REACT_SCOPE_TYPE ||
              type.$$typeof === REACT_BLOCK_TYPE))
        );
      }

      function typeOf(object) {
        if (typeof object === 'object' && object !== null) {
          const {$$typeof} = object;

          switch ($$typeof) {
            case REACT_ELEMENT_TYPE:
              var {type} = object;

              switch (type) {
                case REACT_ASYNC_MODE_TYPE:
                case REACT_CONCURRENT_MODE_TYPE:
                case REACT_FRAGMENT_TYPE:
                case REACT_PROFILER_TYPE:
                case REACT_STRICT_MODE_TYPE:
                case REACT_SUSPENSE_TYPE:
                  return type;

                default:
                  var $$typeofType = type && type.$$typeof;

                  switch ($$typeofType) {
                    case REACT_CONTEXT_TYPE:
                    case REACT_FORWARD_REF_TYPE:
                    case REACT_LAZY_TYPE:
                    case REACT_MEMO_TYPE:
                    case REACT_PROVIDER_TYPE:
                      return $$typeofType;

                    default:
                      return $$typeof;
                  }
              }

            case REACT_PORTAL_TYPE:
              return $$typeof;
          }
        }

        return undefined;
      } // AsyncMode is deprecated along with isAsyncMode

      const AsyncMode = REACT_ASYNC_MODE_TYPE;
      const ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
      const ContextConsumer = REACT_CONTEXT_TYPE;
      const ContextProvider = REACT_PROVIDER_TYPE;
      const Element = REACT_ELEMENT_TYPE;
      const ForwardRef = REACT_FORWARD_REF_TYPE;
      const Fragment = REACT_FRAGMENT_TYPE;
      const Lazy = REACT_LAZY_TYPE;
      const Memo = REACT_MEMO_TYPE;
      const Portal = REACT_PORTAL_TYPE;
      const Profiler = REACT_PROFILER_TYPE;
      const StrictMode = REACT_STRICT_MODE_TYPE;
      const Suspense = REACT_SUSPENSE_TYPE;
      let hasWarnedAboutDeprecatedIsAsyncMode = false; // AsyncMode should be deprecated

      function isAsyncMode(object) {
        {
          if (!hasWarnedAboutDeprecatedIsAsyncMode) {
            hasWarnedAboutDeprecatedIsAsyncMode = true; // Using console['warn'] to evade Babel and ESLint

            console.warn(
              'The ReactIs.isAsyncMode() alias has been deprecated, ' +
                'and will be removed in React 17+. Update your code to use ' +
                'ReactIs.isConcurrentMode() instead. It has the exact same API.'
            );
          }
        }

        return (
          isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE
        );
      }
      function isConcurrentMode(object) {
        return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
      }
      function isContextConsumer(object) {
        return typeOf(object) === REACT_CONTEXT_TYPE;
      }
      function isContextProvider(object) {
        return typeOf(object) === REACT_PROVIDER_TYPE;
      }
      function isElement(object) {
        return (
          typeof object === 'object' &&
          object !== null &&
          object.$$typeof === REACT_ELEMENT_TYPE
        );
      }
      function isForwardRef(object) {
        return typeOf(object) === REACT_FORWARD_REF_TYPE;
      }
      function isFragment(object) {
        return typeOf(object) === REACT_FRAGMENT_TYPE;
      }
      function isLazy(object) {
        return typeOf(object) === REACT_LAZY_TYPE;
      }
      function isMemo(object) {
        return typeOf(object) === REACT_MEMO_TYPE;
      }
      function isPortal(object) {
        return typeOf(object) === REACT_PORTAL_TYPE;
      }
      function isProfiler(object) {
        return typeOf(object) === REACT_PROFILER_TYPE;
      }
      function isStrictMode(object) {
        return typeOf(object) === REACT_STRICT_MODE_TYPE;
      }
      function isSuspense(object) {
        return typeOf(object) === REACT_SUSPENSE_TYPE;
      }

      exports.AsyncMode = AsyncMode;
      exports.ConcurrentMode = ConcurrentMode;
      exports.ContextConsumer = ContextConsumer;
      exports.ContextProvider = ContextProvider;
      exports.Element = Element;
      exports.ForwardRef = ForwardRef;
      exports.Fragment = Fragment;
      exports.Lazy = Lazy;
      exports.Memo = Memo;
      exports.Portal = Portal;
      exports.Profiler = Profiler;
      exports.StrictMode = StrictMode;
      exports.Suspense = Suspense;
      exports.isAsyncMode = isAsyncMode;
      exports.isConcurrentMode = isConcurrentMode;
      exports.isContextConsumer = isContextConsumer;
      exports.isContextProvider = isContextProvider;
      exports.isElement = isElement;
      exports.isForwardRef = isForwardRef;
      exports.isFragment = isFragment;
      exports.isLazy = isLazy;
      exports.isMemo = isMemo;
      exports.isPortal = isPortal;
      exports.isProfiler = isProfiler;
      exports.isStrictMode = isStrictMode;
      exports.isSuspense = isSuspense;
      exports.isValidElementType = isValidElementType;
      exports.typeOf = typeOf;
    })();
  }
});

const reactIs = createCommonjsModule(module => {
  if (process.env.NODE_ENV === 'production') {
    module.exports = reactIs_production_min;
  } else {
    module.exports = reactIs_development;
  }
});

/*
object-assign
(c) Sindre Sorhus
@license MIT
*/
/* eslint-disable no-unused-vars */
const {getOwnPropertySymbols} = Object;
const {hasOwnProperty} = Object.prototype;
const propIsEnumerable = Object.prototype.propertyIsEnumerable;

function toObject(val) {
  if (val === null || val === undefined) {
    throw new TypeError(
      'Object.assign cannot be called with null or undefined'
    );
  }

  return Object(val);
}

function shouldUseNative() {
  try {
    if (!Object.assign) {
      return false;
    }

    // Detect buggy property enumeration order in older V8 versions.

    // https://bugs.chromium.org/p/v8/issues/detail?id=4118
    const test1 = new String('abc'); // eslint-disable-line no-new-wrappers
    test1[5] = 'de';
    if (Object.getOwnPropertyNames(test1)[0] === '5') {
      return false;
    }

    // https://bugs.chromium.org/p/v8/issues/detail?id=3056
    const test2 = {};
    for (let i = 0; i < 10; i++) {
      test2[`_${String.fromCharCode(i)}`] = i;
    }
    const order2 = Object.getOwnPropertyNames(test2).map(n => test2[n]);
    if (order2.join('') !== '0123456789') {
      return false;
    }

    // https://bugs.chromium.org/p/v8/issues/detail?id=3056
    const test3 = {};
    'abcdefghijklmnopqrst'.split('').forEach(letter => {
      test3[letter] = letter;
    });
    if (Object.keys({...test3}).join('') !== 'abcdefghijklmnopqrst') {
      return false;
    }

    return true;
  } catch (err) {
    // We don't expect any of the above to throw, but better to be safe.
    return false;
  }
}

const objectAssign = shouldUseNative()
  ? Object.assign
  : function (target, source) {
      let from;
      const to = toObject(target);
      let symbols;

      for (let s = 1; s < arguments.length; s++) {
        from = Object(arguments[s]);

        for (const key in from) {
          if (hasOwnProperty.call(from, key)) {
            to[key] = from[key];
          }
        }

        if (getOwnPropertySymbols) {
          symbols = getOwnPropertySymbols(from);
          for (let i = 0; i < symbols.length; i++) {
            if (propIsEnumerable.call(from, symbols[i])) {
              to[symbols[i]] = from[symbols[i]];
            }
          }
        }
      }

      return to;
    };

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

const ReactPropTypesSecret$1 = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';

const ReactPropTypesSecret_1 = ReactPropTypesSecret$1;

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

let printWarning$1 = function () {};

if (process.env.NODE_ENV !== 'production') {
  var ReactPropTypesSecret = ReactPropTypesSecret_1;
  var loggedTypeFailures = {};
  var has$1 = Function.call.bind(Object.prototype.hasOwnProperty);

  printWarning$1 = function (text) {
    const message = `Warning: ${text}`;
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };
}

/**
 * Assert that the values match with the type specs.
 * Error messages are memorized and will only be shown once.
 *
 * @param {object} typeSpecs Map of name to a ReactPropType
 * @param {object} values Runtime values that need to be type-checked
 * @param {string} location e.g. "prop", "context", "child context"
 * @param {string} componentName Name of the component for error messages.
 * @param {?Function} getStack Returns the component stack.
 * @private
 */
function checkPropTypes(typeSpecs, values, location, componentName, getStack) {
  if (process.env.NODE_ENV !== 'production') {
    for (const typeSpecName in typeSpecs) {
      if (has$1(typeSpecs, typeSpecName)) {
        var error;
        // Prop type validation may throw. In case they do, we don't want to
        // fail the render phase where it didn't fail before. So we log it.
        // After these have been cleaned up, we'll let them throw.
        try {
          // This is intentionally an invariant that gets caught. It's the same
          // behavior as without this statement except with a better message.
          if (typeof typeSpecs[typeSpecName] !== 'function') {
            const err = Error(
              `${
                componentName || 'React class'
              }: ${location} type \`${typeSpecName}\` is invalid; ` +
                `it must be a function, usually from the \`prop-types\` package, but received \`${typeof typeSpecs[
                  typeSpecName
                ]}\`.`
            );
            err.name = 'Invariant Violation';
            throw err;
          }
          error = typeSpecs[typeSpecName](
            values,
            typeSpecName,
            componentName,
            location,
            null,
            ReactPropTypesSecret
          );
        } catch (ex) {
          error = ex;
        }
        if (error && !(error instanceof Error)) {
          printWarning$1(
            `${
              componentName || 'React class'
            }: type specification of ${location} \`${typeSpecName}\` is invalid; the type checker ` +
              `function must return \`null\` or an \`Error\` but returned a ${typeof error}. ` +
              `You may have forgotten to pass an argument to the type checker ` +
              `creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ` +
              `shape all require an argument).`
          );
        }
        if (error instanceof Error && !(error.message in loggedTypeFailures)) {
          // Only monitor this failure once because there tends to be a lot of the
          // same error.
          loggedTypeFailures[error.message] = true;

          const stack = getStack ? getStack() : '';

          printWarning$1(
            `Failed ${location} type: ${error.message}${
              stack != null ? stack : ''
            }`
          );
        }
      }
    }
  }
}

/**
 * Resets warning cache when testing.
 *
 * @private
 */
checkPropTypes.resetWarningCache = function () {
  if (process.env.NODE_ENV !== 'production') {
    loggedTypeFailures = {};
  }
};

const checkPropTypes_1 = checkPropTypes;

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

const has = Function.call.bind(Object.prototype.hasOwnProperty);
let printWarning = function () {};

if (process.env.NODE_ENV !== 'production') {
  printWarning = function (text) {
    const message = `Warning: ${text}`;
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };
}

function emptyFunctionThatReturnsNull() {
  return null;
}

const factoryWithTypeCheckers = function (isValidElement, throwOnDirectAccess) {
  /* global Symbol */
  const ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
  const FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

  /**
   * Returns the iterator method function contained on the iterable object.
   *
   * Be sure to invoke the function with the iterable as context:
   *
   *     var iteratorFn = getIteratorFn(myIterable);
   *     if (iteratorFn) {
   *       var iterator = iteratorFn.call(myIterable);
   *       ...
   *     }
   *
   * @param {?object} maybeIterable
   * @return {?function}
   */
  function getIteratorFn(maybeIterable) {
    const iteratorFn =
      maybeIterable &&
      ((ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL]) ||
        maybeIterable[FAUX_ITERATOR_SYMBOL]);
    if (typeof iteratorFn === 'function') {
      return iteratorFn;
    }
  }

  /**
   * Collection of methods that allow declaration and validation of props that are
   * supplied to React components. Example usage:
   *
   *   var Props = require('ReactPropTypes');
   *   var MyArticle = React.createClass({
   *     propTypes: {
   *       // An optional string prop named "description".
   *       description: Props.string,
   *
   *       // A required enum prop named "category".
   *       category: Props.oneOf(['News','Photos']).isRequired,
   *
   *       // A prop named "dialog" that requires an instance of Dialog.
   *       dialog: Props.instanceOf(Dialog).isRequired
   *     },
   *     render: function() { ... }
   *   });
   *
   * A more formal specification of how these methods are used:
   *
   *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
   *   decl := ReactPropTypes.{type}(.isRequired)?
   *
   * Each and every declaration produces a function with the same signature. This
   * allows the creation of custom validation functions. For example:
   *
   *  var MyLink = React.createClass({
   *    propTypes: {
   *      // An optional string or URI prop named "href".
   *      href: function(props, propName, componentName) {
   *        var propValue = props[propName];
   *        if (propValue != null && typeof propValue !== 'string' &&
   *            !(propValue instanceof URI)) {
   *          return new Error(
   *            'Expected a string or an URI for ' + propName + ' in ' +
   *            componentName
   *          );
   *        }
   *      }
   *    },
   *    render: function() {...}
   *  });
   *
   * @internal
   */

  const ANONYMOUS = '<<anonymous>>';

  // Important!
  // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
  const ReactPropTypes = {
    array: createPrimitiveTypeChecker('array'),
    bool: createPrimitiveTypeChecker('boolean'),
    func: createPrimitiveTypeChecker('function'),
    number: createPrimitiveTypeChecker('number'),
    object: createPrimitiveTypeChecker('object'),
    string: createPrimitiveTypeChecker('string'),
    symbol: createPrimitiveTypeChecker('symbol'),

    any: createAnyTypeChecker(),
    arrayOf: createArrayOfTypeChecker,
    element: createElementTypeChecker(),
    elementType: createElementTypeTypeChecker(),
    instanceOf: createInstanceTypeChecker,
    node: createNodeChecker(),
    objectOf: createObjectOfTypeChecker,
    oneOf: createEnumTypeChecker,
    oneOfType: createUnionTypeChecker,
    shape: createShapeTypeChecker,
    exact: createStrictShapeTypeChecker,
  };

  /**
   * inlined Object.is polyfill to avoid requiring consumers ship their own
   * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
   */
  /* eslint-disable no-self-compare */
  function is(x, y) {
    // SameValue algorithm
    if (x === y) {
      // Steps 1-5, 7-10
      // Steps 6.b-6.e: +0 != -0
      return x !== 0 || 1 / x === 1 / y;
    }
    // Step 6.a: NaN == NaN
    return x !== x && y !== y;
  }
  /* eslint-enable no-self-compare */

  /**
   * We use an Error-like object for backward compatibility as people may call
   * PropTypes directly and inspect their output. However, we don't use real
   * Errors anymore. We don't inspect their stack anyway, and creating them
   * is prohibitively expensive if they are created too often, such as what
   * happens in oneOfType() for any type before the one that matched.
   */
  function PropTypeError(message) {
    this.message = message;
    this.stack = '';
  }
  // Make `instanceof Error` still work for returned errors.
  PropTypeError.prototype = Error.prototype;

  function createChainableTypeChecker(validate) {
    if (process.env.NODE_ENV !== 'production') {
      var manualPropTypeCallCache = {};
      var manualPropTypeWarningCount = 0;
    }
    function checkType(
      isRequired,
      props,
      propName,
      componentName,
      location,
      propFullName,
      secret
    ) {
      componentName = componentName || ANONYMOUS;
      propFullName = propFullName || propName;

      if (secret !== ReactPropTypesSecret_1) {
        if (throwOnDirectAccess) {
          // New behavior only for users of `prop-types` package
          const err = new Error(
            'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
              'Use `PropTypes.checkPropTypes()` to call them. ' +
              'Read more at http://fb.me/use-check-prop-types'
          );
          err.name = 'Invariant Violation';
          throw err;
        } else if (
          process.env.NODE_ENV !== 'production' &&
          typeof console !== 'undefined'
        ) {
          // Old behavior for people using React.PropTypes
          const cacheKey = `${componentName}:${propName}`;
          if (
            !manualPropTypeCallCache[cacheKey] &&
            // Avoid spamming the console because they are often not actionable except for lib authors
            manualPropTypeWarningCount < 3
          ) {
            printWarning(
              `${
                'You are manually calling a React.PropTypes validation ' +
                'function for the `'
              }${propFullName}\` prop on \`${componentName}\`. This is deprecated ` +
                `and will throw in the standalone \`prop-types\` package. ` +
                `You may be seeing this warning due to a third-party PropTypes ` +
                `library. See https://fb.me/react-warning-dont-call-proptypes ` +
                `for details.`
            );
            manualPropTypeCallCache[cacheKey] = true;
            manualPropTypeWarningCount++;
          }
        }
      }
      if (props[propName] == null) {
        if (isRequired) {
          if (props[propName] === null) {
            return new PropTypeError(
              `The ${location} \`${propFullName}\` is marked as required ` +
                `in \`${componentName}\`, but its value is \`null\`.`
            );
          }
          return new PropTypeError(
            `The ${location} \`${propFullName}\` is marked as required in ` +
              `\`${componentName}\`, but its value is \`undefined\`.`
          );
        }
        return null;
      }
      return validate(props, propName, componentName, location, propFullName);
    }

    const chainedCheckType = checkType.bind(null, false);
    chainedCheckType.isRequired = checkType.bind(null, true);

    return chainedCheckType;
  }

  function createPrimitiveTypeChecker(expectedType) {
    function validate(
      props,
      propName,
      componentName,
      location,
      propFullName,
      secret
    ) {
      const propValue = props[propName];
      const propType = getPropType(propValue);
      if (propType !== expectedType) {
        // `propValue` being instance of, say, date/regexp, pass the 'object'
        // check, but we can offer a more precise error message here rather than
        // 'of type `object`'.
        const preciseType = getPreciseType(propValue);

        return new PropTypeError(
          `Invalid ${location} \`${propFullName}\` of type ` +
            `\`${preciseType}\` supplied to \`${componentName}\`, expected ` +
            `\`${expectedType}\`.`
        );
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createAnyTypeChecker() {
    return createChainableTypeChecker(emptyFunctionThatReturnsNull);
  }

  function createArrayOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError(
          `Property \`${propFullName}\` of component \`${componentName}\` has invalid PropType notation inside arrayOf.`
        );
      }
      const propValue = props[propName];
      if (!Array.isArray(propValue)) {
        const propType = getPropType(propValue);
        return new PropTypeError(
          `Invalid ${location} \`${propFullName}\` of type ` +
            `\`${propType}\` supplied to \`${componentName}\`, expected an array.`
        );
      }
      for (let i = 0; i < propValue.length; i++) {
        const error = typeChecker(
          propValue,
          i,
          componentName,
          location,
          `${propFullName}[${i}]`,
          ReactPropTypesSecret_1
        );
        if (error instanceof Error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      const propValue = props[propName];
      if (!isValidElement(propValue)) {
        const propType = getPropType(propValue);
        return new PropTypeError(
          `Invalid ${location} \`${propFullName}\` of type ` +
            `\`${propType}\` supplied to \`${componentName}\`, expected a single ReactElement.`
        );
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      const propValue = props[propName];
      if (!reactIs.isValidElementType(propValue)) {
        const propType = getPropType(propValue);
        return new PropTypeError(
          `Invalid ${location} \`${propFullName}\` of type ` +
            `\`${propType}\` supplied to \`${componentName}\`, expected a single ReactElement type.`
        );
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createInstanceTypeChecker(expectedClass) {
    function validate(props, propName, componentName, location, propFullName) {
      if (!(props[propName] instanceof expectedClass)) {
        const expectedClassName = expectedClass.name || ANONYMOUS;
        const actualClassName = getClassName(props[propName]);
        return new PropTypeError(
          `Invalid ${location} \`${propFullName}\` of type ` +
            `\`${actualClassName}\` supplied to \`${componentName}\`, expected ` +
            `instance of \`${expectedClassName}\`.`
        );
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createEnumTypeChecker(expectedValues) {
    if (!Array.isArray(expectedValues)) {
      if (process.env.NODE_ENV !== 'production') {
        if (arguments.length > 1) {
          printWarning(
            `Invalid arguments supplied to oneOf, expected an array, got ${arguments.length} arguments. ` +
              `A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).`
          );
        } else {
          printWarning(
            'Invalid argument supplied to oneOf, expected an array.'
          );
        }
      }
      return emptyFunctionThatReturnsNull;
    }

    function validate(props, propName, componentName, location, propFullName) {
      const propValue = props[propName];
      for (let i = 0; i < expectedValues.length; i++) {
        if (is(propValue, expectedValues[i])) {
          return null;
        }
      }

      const valuesString = JSON.stringify(expectedValues, (key, value) => {
        const type = getPreciseType(value);
        if (type === 'symbol') {
          return String(value);
        }
        return value;
      });
      return new PropTypeError(
        `Invalid ${location} \`${propFullName}\` of value \`${String(
          propValue
        )}\` ` +
          `supplied to \`${componentName}\`, expected one of ${valuesString}.`
      );
    }
    return createChainableTypeChecker(validate);
  }

  function createObjectOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError(
          `Property \`${propFullName}\` of component \`${componentName}\` has invalid PropType notation inside objectOf.`
        );
      }
      const propValue = props[propName];
      const propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError(
          `Invalid ${location} \`${propFullName}\` of type ` +
            `\`${propType}\` supplied to \`${componentName}\`, expected an object.`
        );
      }
      for (const key in propValue) {
        if (has(propValue, key)) {
          const error = typeChecker(
            propValue,
            key,
            componentName,
            location,
            `${propFullName}.${key}`,
            ReactPropTypesSecret_1
          );
          if (error instanceof Error) {
            return error;
          }
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createUnionTypeChecker(arrayOfTypeCheckers) {
    if (!Array.isArray(arrayOfTypeCheckers)) {
      process.env.NODE_ENV !== 'production'
        ? printWarning(
            'Invalid argument supplied to oneOfType, expected an instance of array.'
          )
        : void 0;
      return emptyFunctionThatReturnsNull;
    }

    for (let i = 0; i < arrayOfTypeCheckers.length; i++) {
      const checker = arrayOfTypeCheckers[i];
      if (typeof checker !== 'function') {
        printWarning(
          `${
            'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
            'received '
          }${getPostfixForTypeWarning(checker)} at index ${i}.`
        );
        return emptyFunctionThatReturnsNull;
      }
    }

    function validate(props, propName, componentName, location, propFullName) {
      for (let i = 0; i < arrayOfTypeCheckers.length; i++) {
        const checker = arrayOfTypeCheckers[i];
        if (
          checker(
            props,
            propName,
            componentName,
            location,
            propFullName,
            ReactPropTypesSecret_1
          ) == null
        ) {
          return null;
        }
      }

      return new PropTypeError(
        `Invalid ${location} \`${propFullName}\` supplied to ` +
          `\`${componentName}\`.`
      );
    }
    return createChainableTypeChecker(validate);
  }

  function createNodeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      if (!isNode(props[propName])) {
        return new PropTypeError(
          `Invalid ${location} \`${propFullName}\` supplied to ` +
            `\`${componentName}\`, expected a ReactNode.`
        );
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      const propValue = props[propName];
      const propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError(
          `Invalid ${location} \`${propFullName}\` of type \`${propType}\` ` +
            `supplied to \`${componentName}\`, expected \`object\`.`
        );
      }
      for (const key in shapeTypes) {
        const checker = shapeTypes[key];
        if (!checker) {
          continue;
        }
        const error = checker(
          propValue,
          key,
          componentName,
          location,
          `${propFullName}.${key}`,
          ReactPropTypesSecret_1
        );
        if (error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createStrictShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      const propValue = props[propName];
      const propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError(
          `Invalid ${location} \`${propFullName}\` of type \`${propType}\` ` +
            `supplied to \`${componentName}\`, expected \`object\`.`
        );
      }
      // We need to check all keys in case some are required but missing from
      // props.
      const allKeys = {...props[propName], ...shapeTypes};
      for (const key in allKeys) {
        const checker = shapeTypes[key];
        if (!checker) {
          return new PropTypeError(
            `Invalid ${location} \`${propFullName}\` key \`${key}\` supplied to \`${componentName}\`.` +
              `\nBad object: ${JSON.stringify(
                props[propName],
                null,
                '  '
              )}\nValid keys: ${JSON.stringify(
                Object.keys(shapeTypes),
                null,
                '  '
              )}`
          );
        }
        const error = checker(
          propValue,
          key,
          componentName,
          location,
          `${propFullName}.${key}`,
          ReactPropTypesSecret_1
        );
        if (error) {
          return error;
        }
      }
      return null;
    }

    return createChainableTypeChecker(validate);
  }

  function isNode(propValue) {
    switch (typeof propValue) {
      case 'number':
      case 'string':
      case 'undefined':
        return true;
      case 'boolean':
        return !propValue;
      case 'object':
        if (Array.isArray(propValue)) {
          return propValue.every(isNode);
        }
        if (propValue === null || isValidElement(propValue)) {
          return true;
        }

        var iteratorFn = getIteratorFn(propValue);
        if (iteratorFn) {
          const iterator = iteratorFn.call(propValue);
          let step;
          if (iteratorFn !== propValue.entries) {
            while (!(step = iterator.next()).done) {
              if (!isNode(step.value)) {
                return false;
              }
            }
          } else {
            // Iterator will provide entry [k,v] tuples rather than values.
            while (!(step = iterator.next()).done) {
              const entry = step.value;
              if (entry) {
                if (!isNode(entry[1])) {
                  return false;
                }
              }
            }
          }
        } else {
          return false;
        }

        return true;
      default:
        return false;
    }
  }

  function isSymbol(propType, propValue) {
    // Native Symbol.
    if (propType === 'symbol') {
      return true;
    }

    // falsy value can't be a Symbol
    if (!propValue) {
      return false;
    }

    // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
    if (propValue['@@toStringTag'] === 'Symbol') {
      return true;
    }

    // Fallback for non-spec compliant Symbols which are polyfilled.
    if (typeof Symbol === 'function' && propValue instanceof Symbol) {
      return true;
    }

    return false;
  }

  // Equivalent of `typeof` but with special handling for array and regexp.
  function getPropType(propValue) {
    const propType = typeof propValue;
    if (Array.isArray(propValue)) {
      return 'array';
    }
    if (propValue instanceof RegExp) {
      // Old webkits (at least until Android 4.0) return 'function' rather than
      // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
      // passes PropTypes.object.
      return 'object';
    }
    if (isSymbol(propType, propValue)) {
      return 'symbol';
    }
    return propType;
  }

  // This handles more types than `getPropType`. Only used for error messages.
  // See `createPrimitiveTypeChecker`.
  function getPreciseType(propValue) {
    if (typeof propValue === 'undefined' || propValue === null) {
      return `${propValue}`;
    }
    const propType = getPropType(propValue);
    if (propType === 'object') {
      if (propValue instanceof Date) {
        return 'date';
      }
      if (propValue instanceof RegExp) {
        return 'regexp';
      }
    }
    return propType;
  }

  // Returns a string that is postfixed to a warning about an invalid type.
  // For example, "undefined" or "of type array"
  function getPostfixForTypeWarning(value) {
    const type = getPreciseType(value);
    switch (type) {
      case 'array':
      case 'object':
        return `an ${type}`;
      case 'boolean':
      case 'date':
      case 'regexp':
        return `a ${type}`;
      default:
        return type;
    }
  }

  // Returns class name of the object, if any.
  function getClassName(propValue) {
    if (!propValue.constructor || !propValue.constructor.name) {
      return ANONYMOUS;
    }
    return propValue.constructor.name;
  }

  ReactPropTypes.checkPropTypes = checkPropTypes_1;
  ReactPropTypes.resetWarningCache = checkPropTypes_1.resetWarningCache;
  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

function emptyFunction() {}
function emptyFunctionWithReset() {}
emptyFunctionWithReset.resetWarningCache = emptyFunction;

const factoryWithThrowingShims = function () {
  function shim(
    props,
    propName,
    componentName,
    location,
    propFullName,
    secret
  ) {
    if (secret === ReactPropTypesSecret_1) {
      // It is still safe when called from React.
      return;
    }
    const err = new Error(
      'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
        'Use PropTypes.checkPropTypes() to call them. ' +
        'Read more at http://fb.me/use-check-prop-types'
    );
    err.name = 'Invariant Violation';
    throw err;
  }
  shim.isRequired = shim;
  function getShim() {
    return shim;
  } // Important!
  // Keep this list in sync with production version in `./factoryWithTypeCheckers.js`.
  const ReactPropTypes = {
    array: shim,
    bool: shim,
    func: shim,
    number: shim,
    object: shim,
    string: shim,
    symbol: shim,

    any: shim,
    arrayOf: getShim,
    element: shim,
    elementType: shim,
    instanceOf: getShim,
    node: shim,
    objectOf: getShim,
    oneOf: getShim,
    oneOfType: getShim,
    shape: getShim,
    exact: getShim,

    checkPropTypes: emptyFunctionWithReset,
    resetWarningCache: emptyFunction,
  };

  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

const propTypes = createCommonjsModule(module => {
  if (process.env.NODE_ENV !== 'production') {
    const ReactIs = reactIs;

    // By explicitly using `prop-types` you are opting into new development behavior.
    // http://fb.me/prop-types-in-prod
    const throwOnDirectAccess = true;
    module.exports = factoryWithTypeCheckers(
      ReactIs.isElement,
      throwOnDirectAccess
    );
  } else {
    // By explicitly using `prop-types` you are opting into new production behavior.
    // http://fb.me/prop-types-in-prod
    module.exports = factoryWithThrowingShims();
  }
});

/*!
  Copyright (c) 2018 Jed Watson.
  Licensed under the MIT License (MIT), see
  http://jedwatson.github.io/classnames
*/

const bind = createCommonjsModule(module => {
  /* global define */

  (function () {
    const hasOwn = {}.hasOwnProperty;

    function classNames() {
      const classes = [];

      for (let i = 0; i < arguments.length; i++) {
        const arg = arguments[i];
        if (!arg) continue;

        const argType = typeof arg;

        if (argType === 'string' || argType === 'number') {
          classes.push((this && this[arg]) || arg);
        } else if (Array.isArray(arg)) {
          classes.push(classNames.apply(this, arg));
        } else if (argType === 'object') {
          if (arg.toString === Object.prototype.toString) {
            for (const key in arg) {
              if (hasOwn.call(arg, key) && arg[key]) {
                classes.push((this && this[key]) || key);
              }
            }
          } else {
            classes.push(arg.toString());
          }
        }
      }

      return classes.join(' ');
    }

    if (module.exports) {
      classNames.default = classNames;
      module.exports = classNames;
    } else {
      window.classNames = classNames;
    }
  })();
});

function styleInject(css, ref) {
  if (ref === void 0) ref = {};
  const {insertAt} = ref;

  if (!css || typeof document === 'undefined') {
    return;
  }

  const head = document.head || document.getElementsByTagName('head')[0];
  const style = document.createElement('style');
  style.type = 'text/css';

  if (insertAt === 'top') {
    if (head.firstChild) {
      head.insertBefore(style, head.firstChild);
    } else {
      head.appendChild(style);
    }
  } else {
    head.appendChild(style);
  }

  if (style.styleSheet) {
    style.styleSheet.cssText = css;
  } else {
    style.appendChild(document.createTextNode(css));
  }
}

const css_248z =
  '.icons-module_svg-icon__108-h:not(.icons-module_--disable-current-color__sFGIk) path {\n  fill: currentColor;\n}\n.icons-module_svg-icon__108-h.icons-module_--indication__1vDYl {\n  border-radius: 2px;\n  color: #097fde;\n}\n.icons-module_svg-icon__108-h.icons-module_--indication__1vDYl:not(.icons-module_--clean__19lqz) {\n  background: #e8f2fe;\n}\n.icons-module_svg-icon__108-h.icons-module_--success__3GmpO {\n  border-radius: 2px;\n  color: #76ca95;\n}\n.icons-module_svg-icon__108-h.icons-module_--success__3GmpO:not(.icons-module_--clean__19lqz) {\n  background: #e0f8e9;\n}\n.icons-module_svg-icon__108-h.icons-module_--error__3eNix {\n  border-radius: 2px;\n  color: #da4444;\n}\n.icons-module_svg-icon__108-h.icons-module_--error__3eNix:not(.icons-module_--clean__19lqz) {\n  background: #fdeded;\n}\n\n@keyframes icons-module_three-dots-loader-icon__grow-bounce__2bheM {\n  0%, 80%, 100% {\n    -webkit-transform: scale(0);\n    transform: scale(0);\n  }\n  40% {\n    -webkit-transform: scale(1);\n    transform: scale(1);\n  }\n}\n.icons-module_three-dots-loader-icon__3WYwo {\n  margin: 2px 3px;\n}\n.icons-module_three-dots-loader-icon__3WYwo .icons-module_circle__35L_Y {\n  animation: icons-module_three-dots-loader-icon__grow-bounce__2bheM 1.4s infinite ease-in-out both;\n  transform-box: fill-box;\n  transform-origin: center;\n}\n.icons-module_three-dots-loader-icon__3WYwo .icons-module_circle__35L_Y:nth-child(1) {\n  -webkit-animation-delay: -0.32s;\n  animation-delay: -0.32s;\n}\n.icons-module_three-dots-loader-icon__3WYwo .icons-module_circle__35L_Y:nth-child(2) {\n  -webkit-animation-delay: -0.16s;\n  animation-delay: -0.16s;\n}';
const styles = {
  'svg-icon': 'icons-module_svg-icon__108-h',
  '--disable-current-color': 'icons-module_--disable-current-color__sFGIk',
  '--indication': 'icons-module_--indication__1vDYl',
  '--clean': 'icons-module_--clean__19lqz',
  '--success': 'icons-module_--success__3GmpO',
  '--error': 'icons-module_--error__3eNix',
  'three-dots-loader-icon': 'icons-module_three-dots-loader-icon__3WYwo',
  circle: 'icons-module_circle__35L_Y',
  'three-dots-loader-icon__grow-bounce':
    'icons-module_three-dots-loader-icon__grow-bounce__2bheM',
};
styleInject(css_248z);

const cx = bind.bind(styles);
/**
 * @type React.FC<svgIconPropTypes>
 */

const SvgIcon = forwardRef((_ref, ref) => {
  const {children} = _ref;
  const {className} = _ref;
  const {nuance} = _ref;
  const {cleanNuance} = _ref;
  const _ref$dataTestId = _ref.dataTestId;
  const dataTestId = _ref$dataTestId === void 0 ? '' : _ref$dataTestId;
  const _ref$width = _ref.width;
  const width = _ref$width === void 0 ? 24 : _ref$width;
  const _ref$height = _ref.height;
  const height = _ref$height === void 0 ? 24 : _ref$height;
  const _ref$viewBox = _ref.viewBox;
  const viewBox = _ref$viewBox === void 0 ? '0 0 24 24' : _ref$viewBox;
  const _ref$disableCurrentCo = _ref.disableCurrentColor;
  const disableCurrentColor =
    _ref$disableCurrentCo === void 0 ? false : _ref$disableCurrentCo;
  const rest = _objectWithoutProperties(_ref, [
    'children',
    'className',
    'nuance',
    'cleanNuance',
    'dataTestId',
    'width',
    'height',
    'viewBox',
    'disableCurrentColor',
  ]);

  return /* #__PURE__ */ React.createElement(
    'svg',
    {
      ref,
      fill: 'none',
      xmlns: 'http://www.w3.org/2000/svg',
      ...rest,
      'data-testid': dataTestId,
      width,
      height,
      viewBox,
      className: cx(className, 'svg-icon', `--${nuance || cleanNuance}`, {
        '--clean': !!cleanNuance,
        '--disable-current-color': disableCurrentColor,
      }),
    },
    children
  );
});
const svgIconPropTypes = {
  className: propTypes.string,
  children: propTypes.oneOfType([
    propTypes.arrayOf(propTypes.node),
    propTypes.node,
  ]),
  nuance: propTypes.oneOf(['indication', 'success', 'error']),
  cleanNuance: propTypes.oneOf(['indication', 'success', 'error']),
  dataTestId: propTypes.string,
  width: propTypes.number,
  height: propTypes.number,
  viewBox: propTypes.string,
  disableCurrentColor: propTypes.bool,
};
SvgIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const AlertMessageIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M7 15C6.44772 15 6 14.5523 6 14V6C6 5.44772 6.44772 5 7 5H18C18.5523 5 19 5.44772 19 6V14C19 14.5523 18.5523 15 18 15H14.7273L12.5 18L10 15H7ZM12 7H13V11H12V7ZM12.5 13C12.2238 13 12 12.7762 12 12.5C12 12.2238 12.2238 12 12.5 12C12.7762 12 13 12.2238 13 12.5C13 12.7762 12.7762 13 12.5 13Z',
    })
  );
});
AlertMessageIcon.propTypes = svgIconPropTypes;

const SwitchCase = function SwitchCase(_ref) {
  const {expr} = _ref;
  const {children} = _ref;
  let caseFound = false;
  const filteredChildren = Children.toArray(children).filter(child => {
    if (child.type === Case && (child.props.value !== expr || caseFound)) {
      return false;
    }

    if (child.type === Case && child.props.value === expr) {
      caseFound = true;
    }

    return true;
  });
  return filteredChildren;
};
var Case = function Case(_ref2) {
  _ref2.value;
  const {children} = _ref2;
  return children || null;
};

/**
 * a proptypes validator for type component
 */

const isValidElementPropType = propTypes.oneOfType([
  propTypes.func,
  propTypes.string,
  propTypes.node,
  propTypes.element,
  propTypes.shape({
    render: propTypes.func.isRequired,
  }),
]);
/**
 * a proptypes validator for type ref
 */

propTypes.oneOfType([
  propTypes.func, // Or the instance of a DOM native element
  propTypes.shape({
    current: propTypes.instanceOf(Element),
  }),
]);

/**
 * @typedef {object} Props
 * @prop {JSX|Component} fallback - a component to render on error
 * @prop {function} renderFallback - receives (error, errorInfo) and renders the fallback instead
 * @prop {function} onError - receives (error, errorInfo)
 * @prop {children}
 *
 * @extends {React.Component<Props>}
 */

const ErrorBoundary = /* #__PURE__ */ (function (_React$Component) {
  _inherits(ErrorBoundary, _React$Component);

  const _super = _createSuper(ErrorBoundary);

  function ErrorBoundary(props) {
    let _this;

    _classCallCheck(this, ErrorBoundary);

    _this = _super.call(this, props);
    _this.state = {
      hasError: false,
      error: {
        message: '',
        stack: '',
      },
      info: {
        componentStack: '',
      },
    };
    return _this;
  }

  _createClass(
    ErrorBoundary,
    [
      {
        key: 'componentDidCatch',
        value: function componentDidCatch(error, info) {
          let _this$props$onError;
          let _this$props;

          (_this$props$onError = (_this$props = this.props).onError) === null ||
          _this$props$onError === void 0
            ? void 0
            : _this$props$onError.call(_this$props, error, info);
          this.setState({
            error,
            info,
          });
        },
      },
      {
        key: 'render',
        value: function render() {
          if (this.state.hasError) {
            if (typeof this.props.renderFallback === 'function') {
              return this.props.renderFallback(
                this.state.error,
                this.state.errorInfo
              );
            }

            return this.props.fallback;
          }

          return this.props.children;
        },
      },
    ],
    [
      {
        key: 'getDerivedStateFromError',
        value: function getDerivedStateFromError(error) {
          return {
            hasError: true,
          };
        },
      },
    ]
  );

  return ErrorBoundary;
})(React.Component);

const errorBoundaryProptypes = {
  fallback: isValidElementPropType,
  renderFallback: propTypes.func,
  onError: propTypes.func,
  children: isValidElementPropType,
};
ErrorBoundary.propTypes = errorBoundaryProptypes;

const directions$2 = {
  UP: 'up',
  DOWN: 'down',
  RIGHT: 'right',
  LEFT: 'left',
  SWITCH: 'switch',
  TOP_RIGHT: 'top-right',
};
/**
 * @type React.FC<arrowIconPropTypes>
 */

const ArrowIcon = forwardRef((_ref, ref) => {
  const _ref$direction = _ref.direction;
  const direction = _ref$direction === void 0 ? 'up' : _ref$direction;
  const rest = _objectWithoutProperties(_ref, ['direction']);

  return /* #__PURE__ */ React.createElement(
    SwitchCase,
    {
      expr: direction,
    },
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: directions$2.UP,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          fillRule: 'evenodd',
          d: 'M16.1464 11.8536C16.3417 12.0488 16.6583 12.0488 16.8536 11.8536C17.0488 11.6583 17.0488 11.3417 16.8536 11.1464L12.8536 7.14645C12.6583 6.95118 12.3417 6.95118 12.1464 7.14645L8.14645 11.1464C7.95118 11.3417 7.95118 11.6583 8.14645 11.8536C8.34171 12.0488 8.65829 12.0488 8.85355 11.8536L12 8.70711L12 16.5C12 16.7761 12.2239 17 12.5 17C12.7761 17 13 16.7761 13 16.5L13 8.70711L16.1464 11.8536Z',
        })
      )
    ),
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: directions$2.DOWN,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          fillRule: 'evenodd',
          d: 'M16.3536 12.3536C16.5488 12.1583 16.5488 11.8417 16.3536 11.6464C16.1583 11.4512 15.8417 11.4512 15.6464 11.6464L12.5 14.7929L12.5 8C12.5 7.72386 12.2761 7.5 12 7.5C11.7239 7.5 11.5 7.72386 11.5 8L11.5 14.7929L8.35355 11.6464C8.15829 11.4512 7.84171 11.4512 7.64645 11.6464C7.45118 11.8417 7.45118 12.1583 7.64645 12.3536L11.6464 16.3536C11.6944 16.4015 11.7496 16.4377 11.8086 16.4621C11.8622 16.4842 11.9189 16.4967 11.976 16.4994C11.984 16.4998 11.992 16.5 12 16.5M12.1914 16.4621C12.2504 16.4377 12.3056 16.4015 12.3536 16.3536L16.3536 12.3536M12.1914 16.4621C12.1333 16.4861 12.0697 16.4996 12.003 16.5L12.1914 16.4621Z',
        })
      )
    ),
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: directions$2.RIGHT,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          fillRule: 'evenodd',
          d: 'M12.3536 7.64645C12.1583 7.45118 11.8417 7.45118 11.6464 7.64645C11.4512 7.84171 11.4512 8.15829 11.6464 8.35355L14.7929 11.5H8C7.72386 11.5 7.5 11.7239 7.5 12C7.5 12.2761 7.72386 12.5 8 12.5H14.7929L11.6464 15.6464C11.4512 15.8417 11.4512 16.1583 11.6464 16.3536C11.8417 16.5488 12.1583 16.5488 12.3536 16.3536L16.3536 12.3536C16.4015 12.3056 16.4377 12.2504 16.4621 12.1914C16.4842 12.1378 16.4967 12.0811 16.4994 12.024C16.4998 12.016 16.5 12.008 16.5 12M16.4621 11.8086C16.4377 11.7496 16.4015 11.6944 16.3536 11.6464L12.3536 7.64645M16.4621 11.8086C16.4861 11.8667 16.4996 11.9303 16.5 11.997L16.4621 11.8086Z',
        })
      )
    ),
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: directions$2.LEFT,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          fillRule: 'evenodd',
          d: 'M12.3536 8.35355C12.5488 8.15829 12.5488 7.84171 12.3536 7.64645C12.1583 7.45118 11.8417 7.45118 11.6464 7.64645L7.64645 11.6464C7.45118 11.8417 7.45118 12.1583 7.64645 12.3536L11.6464 16.3536C11.8417 16.5488 12.1583 16.5488 12.3536 16.3536C12.5488 16.1583 12.5488 15.8417 12.3536 15.6464L9.20711 12.5L17 12.5C17.2761 12.5 17.5 12.2761 17.5 12C17.5 11.7239 17.2761 11.5 17 11.5L9.20711 11.5L12.3536 8.35355Z',
        })
      )
    ),
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: directions$2.SWITCH,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          fillRule: 'evenodd',
          d: 'M14.5 5.99994L14.5 15.0151L13.3536 13.8686C13.1583 13.6733 12.8417 13.6733 12.6464 13.8686C12.4512 14.0639 12.4512 14.3805 12.6464 14.5757L14.6464 16.5757C14.8417 16.771 15.1583 16.771 15.3536 16.5757L17.3536 14.5757C17.5488 14.3805 17.5488 14.0639 17.3536 13.8686C17.1583 13.6733 16.8417 13.6733 16.6464 13.8686L15.5 15.0151V5.99994C15.5 5.7238 15.2761 5.49994 15 5.49994C14.7239 5.49994 14.5 5.7238 14.5 5.99994ZM6.64645 9.86861C6.45118 10.0639 6.45118 10.3805 6.64645 10.5757C6.84171 10.771 7.15829 10.771 7.35355 10.5757L8.5 9.42927V18C8.5 18.2761 8.72386 18.5 9 18.5C9.27614 18.5 9.5 18.2761 9.5 18V9.42927L10.6464 10.5757C10.8417 10.771 11.1583 10.771 11.3536 10.5757C11.5488 10.3805 11.5488 10.0639 11.3536 9.86861L9.35355 7.86861C9.15829 7.67335 8.84171 7.67335 8.64645 7.86861L6.64645 9.86861Z',
        })
      )
    ),
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: directions$2.TOP_RIGHT,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          fillRule: 'evenodd',
          d: 'M17.4621 5.80861C17.4377 5.74964 17.4015 5.69439 17.3536 5.64645C17.3056 5.59851 17.2504 5.56234 17.1914 5.53794C17.1324 5.51349 17.0678 5.5 17 5.5H16.9999H7C6.72386 5.5 6.5 5.72386 6.5 6C6.5 6.27614 6.72386 6.5 7 6.5H15.7929L6.64645 15.6464C6.45118 15.8417 6.45118 16.1583 6.64645 16.3536C6.84171 16.5488 7.15829 16.5488 7.35355 16.3536L16.5 7.20711V16C16.5 16.2761 16.7239 16.5 17 16.5C17.2761 16.5 17.5 16.2761 17.5 16V6.00049V6C17.5 5.999 17.5 5.998 17.5 5.997C17.4996 5.9303 17.4861 5.86669 17.4621 5.80861Z',
        })
      )
    )
  );
});

const arrowIconPropTypes = _objectSpread2(
  _objectSpread2({}, svgIconPropTypes),
  {},
  {
    /*
     * defaults to 'up'.
     */
    direction: propTypes.oneOf([
      'up',
      'down',
      'right',
      'left',
      'switch',
      'top-right',
    ]),
  }
);

ArrowIcon.propTypes = arrowIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const BellIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M12 4C10.7168 4 9.48884 4.52886 8.58558 5.46573C7.68276 6.40215 7.17781 7.66946 7.17781 8.9882C7.17781 9.20527 7.17402 9.41554 7.16678 9.61919C7.08839 11.8249 6.60515 13.2542 6.1433 14.1324C5.89051 14.6131 5.64181 14.9332 5.46372 15.1282C5.37456 15.2258 5.30277 15.2924 5.25657 15.3323C5.23347 15.3523 5.20745 15.3728 5.20745 15.3728L5.19926 15.379C5.03309 15.4961 4.96083 15.7083 5.02095 15.9039C5.0815 16.1009 5.26218 16.2352 5.4667 16.2352H18.5333C18.7378 16.2352 18.9185 16.1009 18.9791 15.9039C19.0392 15.7083 18.9668 15.496 18.8006 15.3789L18.7926 15.3728C18.7833 15.3656 18.7666 15.3523 18.7434 15.3323C18.6973 15.2924 18.6255 15.2258 18.5363 15.1282C18.3582 14.9332 18.1095 14.6131 17.8567 14.1324C17.3522 13.1731 16.8222 11.5563 16.8222 8.9882C16.8222 7.66946 16.3173 6.40215 15.4144 5.46573C14.5112 4.52886 13.2832 4 12 4ZM17.0322 14.5733C17.1807 14.8558 17.3303 15.0945 17.4718 15.294H6.52822C6.6697 15.0945 6.81931 14.8558 6.96787 14.5733C7.55227 13.4621 8.11114 11.6907 8.11114 8.9882C8.11114 7.91065 8.52396 6.87981 9.25478 6.1218C9.98516 5.36424 10.9729 4.94117 12 4.94117C13.0271 4.94117 14.0149 5.36424 14.7452 6.1218C15.4761 6.87981 15.8889 7.91065 15.8889 8.9882C15.8889 11.6907 16.4478 13.4621 17.0322 14.5733ZM11.0787 18.3774C10.9705 18.145 10.7076 18.0511 10.4916 18.1675C10.2756 18.284 10.1882 18.5667 10.2965 18.7991C10.4613 19.1528 10.7018 19.4549 11.0001 19.6688C11.2992 19.8833 11.6442 20 12.0001 20C12.356 20 12.701 19.8833 13.0001 19.6688C13.2984 19.4549 13.5389 19.1528 13.7037 18.7991C13.812 18.5667 13.7246 18.284 13.5086 18.1675C13.2926 18.0511 13.0297 18.145 12.9215 18.3774C12.8195 18.5963 12.6771 18.7693 12.5147 18.8857C12.3531 19.0016 12.1758 19.0588 12.0001 19.0588C11.8244 19.0588 11.6471 19.0016 11.4855 18.8857C11.3231 18.7693 11.1807 18.5963 11.0787 18.3774Z',
    })
  );
});
BellIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const CheckMarkIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M17.3533 8.64615C17.5487 8.84125 17.5489 9.15783 17.3538 9.35326L11.3538 15.3633C11.2601 15.4572 11.1329 15.5099 11.0002 15.51C10.8675 15.5101 10.7403 15.4574 10.6464 15.3636L7.64645 12.3636C7.45118 12.1683 7.45118 11.8517 7.64645 11.6564C7.84171 11.4612 8.15829 11.4612 8.35355 11.6564L10.9997 14.3026L16.6462 8.64674C16.8413 8.45132 17.1578 8.45105 17.3533 8.64615Z',
    })
  );
});
CheckMarkIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const CrossedCheckmarkIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M9.48344 8.14645C9.28817 8.34171 9.28817 8.65829 9.48344 8.85355L16.4247 15.7948C16.6199 15.9901 16.9365 15.9901 17.1318 15.7948C17.327 15.5995 17.3271 15.283 17.1318 15.0877L14.3555 12.3114L16.8538 9.80895C17.0489 9.61352 17.0487 9.29694 16.8533 9.10184C16.6578 8.90674 16.3413 8.907 16.1462 9.10243L13.6484 11.6043L10.1905 8.14645C9.99528 7.95118 9.6787 7.95118 9.48344 8.14645ZM12.2739 12.9811L12.981 13.6882L10.8538 15.8189C10.7601 15.9128 10.6329 15.9656 10.5002 15.9657C10.3675 15.9657 10.2403 15.9131 10.1464 15.8192L7.14645 12.8192C6.95118 12.624 6.95118 12.3074 7.14645 12.1121C7.34171 11.9169 7.65829 11.9169 7.85355 12.1121L10.4997 14.7583L12.2739 12.9811Z',
    })
  );
});
CrossedCheckmarkIcon.propTypes = svgIconPropTypes;

const directions$1 = {
  UP: 'up',
  DOWN: 'down',
  RIGHT: 'right',
  LEFT: 'left',
};
/**
 * @type React.FC<chevronIconPropTypes>
 */

const ChevronIcon = forwardRef((_ref, ref) => {
  const _ref$direction = _ref.direction;
  const direction = _ref$direction === void 0 ? 'up' : _ref$direction;
  const rest = _objectWithoutProperties(_ref, ['direction']);

  return /* #__PURE__ */ React.createElement(
    SwitchCase,
    {
      expr: direction,
    },
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: directions$1.UP,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          fillRule: 'evenodd',
          d: 'M11.2929 9.29289C11.6834 8.90237 12.3166 8.90237 12.7071 9.29289L16.7071 13.2929C17.0976 13.6834 17.0976 14.3166 16.7071 14.7071C16.3166 15.0976 15.6834 15.0976 15.2929 14.7071L12 11.4142L8.70711 14.7071C8.31658 15.0976 7.68342 15.0976 7.29289 14.7071C6.90237 14.3166 6.90237 13.6834 7.29289 13.2929L11.2929 9.29289Z',
        })
      )
    ),
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: directions$1.DOWN,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          fillRule: 'evenodd',
          d: 'M7.29289 9.29289C7.68342 8.90237 8.31658 8.90237 8.70711 9.29289L12 12.5858L15.2929 9.29289C15.6834 8.90237 16.3166 8.90237 16.7071 9.29289C17.0976 9.68342 17.0976 10.3166 16.7071 10.7071L12.7071 14.7071C12.3166 15.0976 11.6834 15.0976 11.2929 14.7071L7.29289 10.7071C6.90237 10.3166 6.90237 9.68342 7.29289 9.29289Z',
        })
      )
    ),
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: directions$1.LEFT,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          fillRule: 'evenodd',
          d: 'M15.7071 5.29289C16.0976 5.68342 16.0976 6.31658 15.7071 6.70711L10.4142 12L15.7071 17.2929C16.0976 17.6834 16.0976 18.3166 15.7071 18.7071C15.3166 19.0976 14.6834 19.0976 14.2929 18.7071L8.29289 12.7071C7.90237 12.3166 7.90237 11.6834 8.29289 11.2929L14.2929 5.29289C14.6834 4.90237 15.3166 4.90237 15.7071 5.29289Z',
        })
      )
    ),
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: directions$1.RIGHT,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          fillRule: 'evenodd',
          d: 'M8.29289 5.29289C8.68342 4.90237 9.31658 4.90237 9.70711 5.29289L15.7071 11.2929C16.0976 11.6834 16.0976 12.3166 15.7071 12.7071L9.70711 18.7071C9.31658 19.0976 8.68342 19.0976 8.29289 18.7071C7.90237 18.3166 7.90237 17.6834 8.29289 17.2929L13.5858 12L8.29289 6.70711C7.90237 6.31658 7.90237 5.68342 8.29289 5.29289Z',
        })
      )
    )
  );
});

const chevronIconPropTypes = _objectSpread2(
  _objectSpread2({}, svgIconPropTypes),
  {},
  {
    /*
     * defaults to 'up'.
     */
    direction: propTypes.oneOf(['up', 'down', 'left', 'right']),
  }
);

ChevronIcon.propTypes = chevronIconPropTypes;

const directions = {
  UP: 'up',
  DOWN: 'down',
  RIGHT: 'right',
  LEFT: 'left',
};
/**
 * @type React.FC<doubleChevronIconPropTypes>
 */

const DoubleChevronIcon = forwardRef((_ref, ref) => {
  const _ref$direction = _ref.direction;
  const direction = _ref$direction === void 0 ? 'up' : _ref$direction;
  const rest = _objectWithoutProperties(_ref, ['direction']);

  return /* #__PURE__ */ React.createElement(
    SwitchCase,
    {
      expr: direction,
    },
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: directions.UP,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          fillRule: 'evenodd',
          d: 'M7.64645 15.6464C7.45118 15.8417 7.45118 16.1583 7.64645 16.3536C7.84171 16.5488 8.15829 16.5488 8.35355 16.3536L12 12.7071L15.6464 16.3536C15.8417 16.5488 16.1583 16.5488 16.3536 16.3536C16.5488 16.1583 16.5488 15.8417 16.3536 15.6464L12.3536 11.6464C12.1583 11.4512 11.8417 11.4512 11.6464 11.6464L7.64645 15.6464ZM7.64645 11.6464C7.45118 11.8417 7.45118 12.1583 7.64645 12.3536C7.84171 12.5488 8.15829 12.5488 8.35355 12.3536L12 8.70711L15.6464 12.3536C15.8417 12.5488 16.1583 12.5488 16.3536 12.3536C16.5488 12.1583 16.5488 11.8417 16.3536 11.6464L12.3536 7.64645C12.1583 7.45118 11.8417 7.45118 11.6464 7.64645L7.64645 11.6464Z',
        })
      )
    ),
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: directions.DOWN,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          fillRule: 'evenodd',
          d: 'M16.3536 8.35355C16.5488 8.15829 16.5488 7.84171 16.3536 7.64645C16.1583 7.45118 15.8417 7.45118 15.6464 7.64645L12 11.2929L8.35355 7.64645C8.15829 7.45118 7.84171 7.45118 7.64645 7.64645C7.45118 7.84171 7.45118 8.15829 7.64645 8.35355L11.6464 12.3536C11.8417 12.5488 12.1583 12.5488 12.3536 12.3536L16.3536 8.35355ZM16.3536 12.3536C16.5488 12.1583 16.5488 11.8417 16.3536 11.6464C16.1583 11.4512 15.8417 11.4512 15.6464 11.6464L12 15.2929L8.35355 11.6464C8.15829 11.4512 7.84171 11.4512 7.64645 11.6464C7.45118 11.8417 7.45118 12.1583 7.64645 12.3536L11.6464 16.3536C11.8417 16.5488 12.1583 16.5488 12.3536 16.3536L16.3536 12.3536Z',
        })
      )
    ),
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: directions.LEFT,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          fillRule: 'evenodd',
          d: 'M15.6464 16.3536C15.8417 16.5488 16.1583 16.5488 16.3536 16.3536C16.5488 16.1583 16.5488 15.8417 16.3536 15.6464L12.7071 12L16.3536 8.35355C16.5488 8.15829 16.5488 7.84171 16.3536 7.64645C16.1583 7.45118 15.8417 7.45118 15.6464 7.64645L11.6464 11.6464C11.4512 11.8417 11.4512 12.1583 11.6464 12.3536L15.6464 16.3536ZM11.6464 16.3536C11.8417 16.5488 12.1583 16.5488 12.3536 16.3536C12.5488 16.1583 12.5488 15.8417 12.3536 15.6464L8.70711 12L12.3536 8.35355C12.5488 8.15829 12.5488 7.84171 12.3536 7.64645C12.1583 7.45118 11.8417 7.45118 11.6464 7.64645L7.64645 11.6464C7.45118 11.8417 7.45118 12.1583 7.64645 12.3536L11.6464 16.3536Z',
        })
      )
    ),
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: directions.RIGHT,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          fillRule: 'evenodd',
          d: 'M8.35355 7.64645C8.15829 7.45118 7.84171 7.45118 7.64645 7.64645C7.45118 7.84171 7.45118 8.15829 7.64645 8.35355L11.2929 12L7.64645 15.6464C7.45118 15.8417 7.45118 16.1583 7.64645 16.3536C7.84171 16.5488 8.15829 16.5488 8.35355 16.3536L12.3536 12.3536C12.5488 12.1583 12.5488 11.8417 12.3536 11.6464L8.35355 7.64645ZM12.3536 7.64645C12.1583 7.45118 11.8417 7.45118 11.6464 7.64645C11.4512 7.84171 11.4512 8.15829 11.6464 8.35355L15.2929 12L11.6464 15.6464C11.4512 15.8417 11.4512 16.1583 11.6464 16.3536C11.8417 16.5488 12.1583 16.5488 12.3536 16.3536L16.3536 12.3536C16.5488 12.1583 16.5488 11.8417 16.3536 11.6464L12.3536 7.64645Z',
        })
      )
    )
  );
});

const doubleChevronIconPropTypes = _objectSpread2(
  _objectSpread2({}, svgIconPropTypes),
  {},
  {
    /**
     * defaults to 'up'
     */
    direction: propTypes.oneOf(['up', 'down', 'left', 'right']),
  }
);

DoubleChevronIcon.propTypes = doubleChevronIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const CircleCheckMarkIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M10.4444 5.11473C11.9291 4.77927 13.4825 4.93275 14.8729 5.55228C15.1103 5.65806 15.3885 5.55136 15.4943 5.31396C15.6001 5.07656 15.4934 4.79836 15.256 4.69258C13.6802 3.99045 11.9197 3.81651 10.2369 4.1967C8.55423 4.57688 7.03948 5.49083 5.91862 6.80224C4.79777 8.11364 4.13085 9.75223 4.01734 11.4736C3.90383 13.195 4.34981 14.907 5.28877 16.3542C6.22772 17.8015 7.60934 18.9064 9.22757 19.5042C10.8458 20.1021 12.6139 20.1608 14.2683 19.6717C15.9226 19.1826 17.3745 18.1718 18.4075 16.79C19.4404 15.4083 19.999 13.7294 20 12.0043V11.3116C20 11.0517 19.7893 10.841 19.5294 10.841C19.2695 10.841 19.0588 11.0517 19.0588 11.3116V12.004C19.058 13.5262 18.5651 15.0073 17.6536 16.2265C16.7422 17.4457 15.4611 18.3376 14.0014 18.7691C12.5417 19.2007 10.9816 19.1489 9.55374 18.6214C8.12589 18.0939 6.90682 17.1189 6.07833 15.842C5.24984 14.565 4.85632 13.0544 4.95648 11.5356C5.05663 10.0167 5.64509 8.57086 6.63408 7.41374C7.62307 6.25662 8.95961 5.45019 10.4444 5.11473ZM19.8731 6.75249C20.0471 6.57556 20.0415 6.29421 19.8605 6.12407C19.6795 5.95394 19.3918 5.95946 19.2178 6.1364L12.5523 12.9145L10.782 11.1161C10.608 10.9393 10.3202 10.9339 10.1393 11.1041C9.95846 11.2744 9.95296 11.5557 10.1271 11.7326L12.225 13.8638C12.3107 13.9508 12.429 14 12.5526 14C12.6762 14 12.7944 13.9507 12.8801 13.8636L19.8731 6.75249Z',
    })
  );
});
CircleCheckMarkIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const CircleCrossMarkIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M12 6.5C8.96243 6.5 6.5 8.96243 6.5 12C6.5 15.0376 8.96243 17.5 12 17.5C15.0376 17.5 17.5 15.0376 17.5 12C17.5 8.96243 15.0376 6.5 12 6.5ZM5.5 12C5.5 8.41015 8.41015 5.5 12 5.5C15.5899 5.5 18.5 8.41015 18.5 12C18.5 15.5899 15.5899 18.5 12 18.5C8.41015 18.5 5.5 15.5899 5.5 12ZM14.3536 9.64645C14.5488 9.84171 14.5488 10.1583 14.3536 10.3536L12.7071 12L14.3536 13.6464C14.5488 13.8417 14.5488 14.1583 14.3536 14.3536C14.1583 14.5488 13.8417 14.5488 13.6464 14.3536L12 12.7071L10.3536 14.3536C10.1583 14.5488 9.84171 14.5488 9.64645 14.3536C9.45118 14.1583 9.45118 13.8417 9.64645 13.6464L11.2929 12L9.64645 10.3536C9.45118 10.1583 9.45118 9.84171 9.64645 9.64645C9.84171 9.45118 10.1583 9.45118 10.3536 9.64645L12 11.2929L13.6464 9.64645C13.8417 9.45118 14.1583 9.45118 14.3536 9.64645Z',
    })
  );
});
CircleCrossMarkIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const CircleInfoIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M12 5.5C8.41015 5.5 5.5 8.41015 5.5 12C5.5 15.5899 8.41015 18.5 12 18.5C15.5899 18.5 18.5 15.5899 18.5 12C18.5 8.41015 15.5899 5.5 12 5.5ZM4.5 12C4.5 7.85786 7.85786 4.5 12 4.5C16.1421 4.5 19.5 7.85786 19.5 12C19.5 16.1421 16.1421 19.5 12 19.5C7.85786 19.5 4.5 16.1421 4.5 12ZM12 10.5C12.2761 10.5 12.5 10.7239 12.5 11V15C12.5 15.2761 12.2761 15.5 12 15.5C11.7239 15.5 11.5 15.2761 11.5 15V11C11.5 10.7239 11.7239 10.5 12 10.5ZM12 8.5C11.7239 8.5 11.5 8.72386 11.5 9C11.5 9.27614 11.7239 9.5 12 9.5H12.01C12.2861 9.5 12.51 9.27614 12.51 9C12.51 8.72386 12.2861 8.5 12.01 8.5H12Z',
    })
  );
});
CircleInfoIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const CirclePlusIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M12 6.5C8.96243 6.5 6.5 8.96243 6.5 12C6.5 15.0376 8.96243 17.5 12 17.5C15.0376 17.5 17.5 15.0376 17.5 12C17.5 8.96243 15.0376 6.5 12 6.5ZM5.5 12C5.5 8.41015 8.41015 5.5 12 5.5C15.5899 5.5 18.5 8.41015 18.5 12C18.5 15.5899 15.5899 18.5 12 18.5C8.41015 18.5 5.5 15.5899 5.5 12ZM15.3284 12C15.3284 12.2761 15.1046 12.5 14.8284 12.5H12.5V14.8284C12.5 15.1046 12.2761 15.3284 12 15.3284C11.7239 15.3284 11.5 15.1046 11.5 14.8284V12.5H9.17157C8.89543 12.5 8.67157 12.2761 8.67157 12C8.67157 11.7239 8.89543 11.5 9.17157 11.5H11.5V9.17157C11.5 8.89543 11.7239 8.67157 12 8.67157C12.2761 8.67157 12.5 8.89543 12.5 9.17157V11.5H14.8284C15.1046 11.5 15.3284 11.7239 15.3284 12Z',
    })
  );
});
CirclePlusIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const CrossMarkIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M8.11094 7.40383C7.91568 7.20857 7.59909 7.20857 7.40383 7.40383C7.20857 7.59909 7.20857 7.91568 7.40383 8.11094L11.2929 12L7.40383 15.8891C7.20857 16.0844 7.20857 16.401 7.40383 16.5962C7.59909 16.7915 7.91568 16.7915 8.11094 16.5962L12 12.7071L15.8891 16.5962C16.0844 16.7915 16.401 16.7915 16.5962 16.5962C16.7915 16.401 16.7915 16.0844 16.5962 15.8891L12.7071 12L16.5962 8.11094C16.7915 7.91568 16.7915 7.59909 16.5962 7.40383C16.401 7.20857 16.0844 7.20857 15.8891 7.40383L12 11.2929L8.11094 7.40383Z',
    })
  );
});
CrossMarkIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const DownloadIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M11.5 5C11.7761 5 12 5.22386 12 5.5L12 13.2929L14.1464 11.1464C14.3417 10.9512 14.6583 10.9512 14.8536 11.1464C15.0488 11.3417 15.0488 11.6583 14.8536 11.8536L11.8536 14.8536C11.7567 14.9504 11.63 14.9992 11.503 15L11.5 15L11.497 15C11.4303 14.9996 11.3667 14.9861 11.3086 14.9621C11.2496 14.9377 11.1944 14.9015 11.1464 14.8536L8.14645 11.8536C7.95118 11.6583 7.95118 11.3417 8.14645 11.1464C8.34171 10.9512 8.65829 10.9512 8.85355 11.1464L11 13.2929L11 5.5C11 5.22386 11.2239 5 11.5 5ZM7.5 18C7.22386 18 7 18.2239 7 18.5C7 18.7761 7.22386 19 7.5 19H15.5C15.7761 19 16 18.7761 16 18.5C16 18.2239 15.7761 18 15.5 18H7.5Z',
    })
  );
});
DownloadIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const ExportIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M10.5 8C10.7761 8 11 7.77614 11 7.5C11 7.22386 10.7761 7 10.5 7H4.5C4.22386 7 4 7.22386 4 7.5C4 7.77614 4.22386 8 4.5 8H10.5ZM16.5 7C16.7761 7 17 7.22386 17 7.5L17 15.2929L19.1464 13.1464C19.3417 12.9512 19.6583 12.9512 19.8536 13.1464C20.0488 13.3417 20.0488 13.6583 19.8536 13.8536L16.8536 16.8536C16.6583 17.0488 16.3417 17.0488 16.1464 16.8536L13.1464 13.8536C12.9512 13.6583 12.9512 13.3417 13.1464 13.1464C13.3417 12.9512 13.6583 12.9512 13.8536 13.1464L16 15.2929L16 7.5C16 7.22386 16.2239 7 16.5 7ZM11 11.5C11 11.7761 10.7761 12 10.5 12L4.5 12C4.22386 12 4 11.7761 4 11.5C4 11.2239 4.22386 11 4.5 11L10.5 11C10.7761 11 11 11.2239 11 11.5ZM10.5 16C10.7761 16 11 15.7761 11 15.5C11 15.2239 10.7761 15 10.5 15L4.5 15C4.22386 15 4 15.2239 4 15.5C4 15.7761 4.22386 16 4.5 16H10.5Z',
    })
  );
});
ExportIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const GridIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M4.5 4C4.22386 4 4 4.22386 4 4.5V9.5C4 9.77614 4.22386 10 4.5 10H9.5C9.77614 10 10 9.77614 10 9.5V4.5C10 4.22386 9.77614 4 9.5 4H4.5ZM5 9V5H9V9H5ZM13.5 4C13.2239 4 13 4.22386 13 4.5V9.5C13 9.77614 13.2239 10 13.5 10H18.5C18.7761 10 19 9.77614 19 9.5V4.5C19 4.22386 18.7761 4 18.5 4H13.5ZM14 9V5H18V9H14ZM13 13.5C13 13.2239 13.2239 13 13.5 13H18.5C18.7761 13 19 13.2239 19 13.5V18.5C19 18.7761 18.7761 19 18.5 19H13.5C13.2239 19 13 18.7761 13 18.5V13.5ZM14 14V18H18V14H14ZM4.5 13C4.22386 13 4 13.2239 4 13.5V18.5C4 18.7761 4.22386 19 4.5 19H9.5C9.77614 19 10 18.7761 10 18.5V13.5C10 13.2239 9.77614 13 9.5 13H4.5ZM5 18V14H9V18H5Z',
    })
  );
});
GridIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const HideSourceIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      d: 'M18.268 5.43917C18.0727 5.24391 17.7562 5.24391 17.5609 5.43917L5.69332 17.3068C5.49806 17.502 5.49806 17.8186 5.69332 18.0139C5.88858 18.2091 6.20516 18.2091 6.40043 18.0139L18.268 6.14628C18.4633 5.95102 18.4633 5.63443 18.268 5.43917Z',
    }),
    /* #__PURE__ */ React.createElement('path', {
      d: 'M11.9999 6.50005C12.8699 6.50005 13.6927 6.70205 14.4241 7.06172L13.6669 7.8189C13.1513 7.61318 12.5888 7.50005 11.9999 7.50005C9.51462 7.50005 7.49991 9.51477 7.49991 12C7.49991 12.589 7.61304 13.1515 7.81876 13.667L7.06158 14.4242C6.70191 13.6929 6.49991 12.8701 6.49991 12C6.49991 8.96248 8.96234 6.50005 11.9999 6.50005Z',
    }),
    /* #__PURE__ */ React.createElement('path', {
      d: 'M11.9999 16.5C11.2243 16.5 10.4945 16.3038 9.85747 15.9583L9.12562 16.6901C9.96204 17.2038 10.9464 17.5 11.9999 17.5C15.0375 17.5 17.4999 15.0376 17.4999 12C17.4999 10.9465 17.2037 9.96218 16.69 9.12576L15.9582 9.85761C16.3037 10.4946 16.4999 11.2244 16.4999 12C16.4999 14.4853 14.4852 16.5 11.9999 16.5Z',
    })
  );
});
HideSourceIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const LightBulbIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M12.5 6.91338C9.96073 6.91338 7.91667 8.92501 7.91667 11.3889C7.91667 12.437 8.26195 13.3619 8.96166 14.1473L8.97546 14.1336L8.97658 14.1347L8.97871 14.1369L8.98511 14.1434L9.00615 14.1652C9.02371 14.1837 9.0482 14.2098 9.07861 14.2435C9.13941 14.3108 9.22406 14.4083 9.32456 14.5339C9.5253 14.7848 9.79071 15.15 10.0557 15.6138C10.5289 16.4418 10.9041 17.6113 10.9999 19L12 19L12 13H10V12H12H13H15V13H13L13 18.9999L14.0171 18.9999C14.1129 17.6112 14.5268 16.3318 15 15.5038C15.265 15.04 15.5304 14.6748 15.7312 14.4239C15.8317 14.2983 15.9163 14.2008 15.9771 14.1335C16.0075 14.0998 16.032 14.0737 16.0496 14.0552L16.0706 14.0334L16.077 14.0269L16.0792 14.0247L16.08 14.0239C16.08 14.0239 16.0801 14.0238 16.1153 14.0587C16.7634 13.2927 17.0833 12.3978 17.0833 11.3889C17.0833 8.92501 15.0393 6.91338 12.5 6.91338ZM7 11.3889C7 12.6805 7.44095 13.8351 8.31329 14.7949L8.26783 14.8402L8.26961 14.842L8.28201 14.8549C8.29375 14.8672 8.31223 14.8869 8.33651 14.9138C8.38508 14.9676 8.45668 15.0498 8.54369 15.1586C8.71795 15.3764 8.95253 15.6987 9.1875 16.1099C9.65862 16.9344 10.0171 18.1119 10.0171 19.5V20L14.9999 19.9999V19.4999C14.9999 18.1118 15.3971 16.8244 15.8682 15.9999C16.1032 15.5887 16.3378 15.2664 16.5121 15.0486C16.5991 14.9398 16.6707 14.8576 16.7192 14.8038C16.7435 14.7769 16.762 14.7572 16.7737 14.7449L16.7861 14.732L16.7879 14.7302L16.7648 14.7072C17.5853 13.7651 18 12.6414 18 11.3889C18 8.40484 15.5296 6 12.5 6C9.4704 6 7 8.40484 7 11.3889ZM15 22V21H10V22H15Z',
    }),
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M12 2H13V4H12V2Z',
    }),
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M22 11L22 12L20 12L20 11L22 11Z',
    }),
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M5 11L5 12L3 12L3 11L5 11Z',
    }),
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M19.4143 5L20.1214 5.70711L18.7072 7.12132L18.0001 6.41421L19.4143 5Z',
    }),
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M5 5.70715L5.70711 5.00005L7.12132 6.41426L6.41421 7.12137L5 5.70715Z',
    })
  );
});
LightBulbIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const LockIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M10.5644 6.52458C10.9362 6.19411 11.4518 6 12 6C12.5482 6 13.0638 6.19411 13.4356 6.52458C13.8054 6.85334 14 7.28574 14 7.72222V8.5C14 8.77614 14.2239 9 14.5 9C14.7761 9 15 8.77614 15 8.5V7.72222C15 6.97997 14.6678 6.2819 14.0999 5.77717C13.534 5.27414 12.7779 5 12 5C11.2221 5 10.466 5.27414 9.90005 5.77717C9.33223 6.2819 9 6.97997 9 7.72222V8.5C9 8.77614 9.22386 9 9.5 9C9.77614 9 10 8.77614 10 8.5V7.72222C10 7.28574 10.1946 6.85334 10.5644 6.52458ZM7 11.7727C7 11.3267 7.34224 11 7.72222 11H16.2778C16.6578 11 17 11.3267 17 11.7727V16.2273C17 16.6733 16.6578 17 16.2778 17H7.72222C7.34224 17 7 16.6733 7 16.2273V11.7727ZM7.72222 10C6.75218 10 6 10.813 6 11.7727V16.2273C6 17.187 6.75218 18 7.72222 18H16.2778C17.2478 18 18 17.187 18 16.2273V11.7727C18 10.813 17.2478 10 16.2778 10H7.72222Z',
    })
  );
});
LockIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const MagnifyingGlassIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M10.5 5.5C7.73858 5.5 5.5 7.73858 5.5 10.5C5.5 13.2614 7.73858 15.5 10.5 15.5C13.2614 15.5 15.5 13.2614 15.5 10.5C15.5 7.73858 13.2614 5.5 10.5 5.5ZM4.5 10.5C4.5 7.18629 7.18629 4.5 10.5 4.5C13.8137 4.5 16.5 7.18629 16.5 10.5C16.5 13.8137 13.8137 16.5 10.5 16.5C7.18629 16.5 4.5 13.8137 4.5 10.5Z',
      className: 'aquiIcon__path '.concat(styles['icon__default-fill']),
    }),
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M14.6464 14.6464C14.8417 14.4512 15.1583 14.4512 15.3536 14.6464L19.3536 18.6464C19.5488 18.8417 19.5488 19.1583 19.3536 19.3536C19.1583 19.5488 18.8417 19.5488 18.6464 19.3536L14.6464 15.3536C14.4512 15.1583 14.4512 14.8417 14.6464 14.6464Z',
      className: 'aquiIcon__path '.concat(styles['icon__default-fill']),
    })
  );
});
MagnifyingGlassIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const MergeIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M4.5 6C3.67157 6 3 6.67157 3 7.5C3 8.32843 3.67157 9 4.5 9C5.32843 9 6 8.32843 6 7.5C6 6.67157 5.32843 6 4.5 6ZM4.5 5C5.70948 5 6.71836 5.85888 6.94999 7H10.5C11.2869 7 12.0279 7.37049 12.5 8L14.6 10.8C14.6944 10.9259 14.8426 11 15 11H20.2929L17.1464 7.85355C16.9512 7.65829 16.9512 7.34171 17.1464 7.14645C17.3417 6.95118 17.6583 6.95118 17.8536 7.14645L21.8536 11.1464C22.0488 11.3417 22.0488 11.6583 21.8536 11.8536L17.8536 15.8536C17.6583 16.0488 17.3417 16.0488 17.1464 15.8536C16.9512 15.6583 16.9512 15.3417 17.1464 15.1464L20.2929 12H15C14.5279 12 14.0833 11.7777 13.8 11.4L11.7 8.6C11.4167 8.22229 10.9721 8 10.5 8H6.94999C6.71836 9.14112 5.70948 10 4.5 10C3.11929 10 2 8.88071 2 7.5C2 6.11929 3.11929 5 4.5 5ZM3 15.5C3 14.6716 3.67157 14 4.5 14C5.32843 14 6 14.6716 6 15.5C6 16.3284 5.32843 17 4.5 17C3.67157 17 3 16.3284 3 15.5ZM4.5 13C5.70948 13 6.71836 13.8589 6.94999 15H10.5387C10.9944 15 11.4254 14.7929 11.7101 14.437L13 13C13.1725 12.7844 13.4872 12.7494 13.7028 12.9219C13.9184 13.0944 13.9534 13.4091 13.7809 13.6247L12.5 15C12.0256 15.593 11.2982 16 10.5387 16H6.94999C6.71836 17.1411 5.70948 18 4.5 18C3.11929 18 2 16.8807 2 15.5C2 14.1193 3.11929 13 4.5 13Z',
    })
  );
});
MergeIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const UnmergeIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M17.8536 10.8536L21.8536 6.85355C22.0488 6.65829 22.0488 6.34171 21.8536 6.14645L17.8536 2.14645C17.6583 1.95118 17.3417 1.95118 17.1464 2.14645C16.9512 2.34171 16.9512 2.65829 17.1464 2.85355L20.2929 6H12C11.5279 6 11.0833 6.22229 10.8 6.6L8.7 9.4C8.41672 9.77771 7.97214 10 7.5 10H6.50018C6.04408 9.39278 5.31791 9 4.5 9C3.11929 9 2 10.1193 2 11.5C2 12.8807 3.11929 14 4.5 14C5.31791 14 6.04408 13.6072 6.50018 13H7.5C7.97214 13 8.41672 13.2223 8.7 13.6L10.8 16.4C11.0833 16.7777 11.5279 17 12 17H20.2929L17.1464 20.1464C16.9512 20.3417 16.9512 20.6583 17.1464 20.8536C17.3417 21.0488 17.6583 21.0488 17.8536 20.8536L21.8536 16.8536C22.0488 16.6583 22.0488 16.3417 21.8536 16.1464L17.8536 12.1464C17.6583 11.9512 17.3417 11.9512 17.1464 12.1464C16.9512 12.3417 16.9512 12.6583 17.1464 12.8536L20.2929 16H12C11.8426 16 11.6944 15.9259 11.6 15.8L9.5 13C9.02786 12.3705 8.28689 12 7.5 12H6.94999C6.98278 11.8384 7 11.6712 7 11.5C7 11.3288 6.98278 11.1616 6.94999 11H7.5C8.28689 11 9.02786 10.6295 9.5 10L11.6 7.2C11.6944 7.0741 11.8426 7 12 7H20.2929L17.1464 10.1464C16.9512 10.3417 16.9512 10.6583 17.1464 10.8536C17.3417 11.0488 17.6583 11.0488 17.8536 10.8536ZM3 11.5C3 10.6716 3.67157 10 4.5 10C5.32843 10 6 10.6716 6 11.5C6 12.3284 5.32843 13 4.5 13C3.67157 13 3 12.3284 3 11.5Z',
    })
  );
});
UnmergeIcon.propTypes = svgIconPropTypes;

const orientations = {
  HORIZONTAL: 'horizontal',
  VERTICAL: 'vertical',
};
/**
 * @type React.FC<moreIconPropTypes>
 */

const MoreIcon = forwardRef((_ref, ref) => {
  const _ref$orientation = _ref.orientation;
  const orientation =
    _ref$orientation === void 0 ? 'horizontal' : _ref$orientation;
  const rest = _objectWithoutProperties(_ref, ['orientation']);

  return /* #__PURE__ */ React.createElement(
    SwitchCase,
    {
      expr: orientation,
    },
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: orientations.HORIZONTAL,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          d: 'M11 12C11 12.5523 11.4477 13 12 13C12.5523 13 13 12.5523 13 12C13 11.4477 12.5523 11 12 11C11.4477 11 11 11.4477 11 12Z',
        }),
        /* #__PURE__ */ React.createElement('path', {
          d: 'M16 12C16 12.5523 16.4477 13 17 13C17.5523 13 18 12.5523 18 12C18 11.4477 17.5523 11 17 11C16.4477 11 16 11.4477 16 12Z',
        }),
        /* #__PURE__ */ React.createElement('path', {
          d: 'M6 12C6 12.5523 6.44772 13 7 13C7.55228 13 8 12.5523 8 12C8 11.4477 7.55228 11 7 11C6.44772 11 6 11.4477 6 12Z',
        })
      )
    ),
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: orientations.VERTICAL,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          d: 'm11,12c0,0.5523 0.4477,1 1,1c0.5523,0 1,-0.4477 1,-1c0,-0.5523 -0.4477,-1 -1,-1c-0.5523,0 -1,0.4477 -1,1z',
        }),
        /* #__PURE__ */ React.createElement('path', {
          d: 'm11,17c0,0.5523 0.4477,1 1,1c0.5523,0 1,-0.4477 1,-1c0,-0.5523 -0.4477,-1 -1,-1c-0.5523,0 -1,0.4477 -1,1z',
        }),
        /* #__PURE__ */ React.createElement('path', {
          d: 'm11,7c0,0.5523 0.44772,1 1,1c0.55228,0 1,-0.4477 1,-1c0,-0.5523 -0.44772,-1 -1,-1c-0.55228,0 -1,0.4477 -1,1z',
        })
      )
    )
  );
});

const moreIconPropTypes = _objectSpread2(
  _objectSpread2({}, svgIconPropTypes),
  {},
  {
    /**
     * defaults to "horizontal"
     */
    orientation: propTypes.oneOf(['horizontal', 'vertical']),
  }
);

MoreIcon.propTypes = moreIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const PencilEditIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M14.2385 7.71645C14.3771 7.57786 14.565 7.5 14.761 7.5C14.8581 7.5 14.9542 7.51911 15.0438 7.55625C15.1335 7.59339 15.2149 7.64782 15.2836 7.71645C15.3522 7.78507 15.4066 7.86653 15.4438 7.95619C15.4809 8.04585 15.5 8.14195 15.5 8.23899C15.5 8.33604 15.4809 8.43213 15.4438 8.52179C15.4066 8.61145 15.3522 8.69292 15.2836 8.76154L8.08065 15.9645L6.68719 16.3128L7.03556 14.9194L14.2385 7.71645ZM14.761 6.5C14.2998 6.5 13.8575 6.68321 13.5314 7.00934L6.23052 14.3102C6.16644 14.3743 6.12099 14.4545 6.09901 14.5425L5.51494 16.8787C5.47234 17.0491 5.52227 17.2294 5.64646 17.3536C5.77065 17.4777 5.95089 17.5277 6.12128 17.4851L8.45755 16.901C8.54546 16.879 8.62575 16.8336 8.68983 16.7695L15.9907 9.46865C16.1522 9.30717 16.2802 9.11546 16.3676 8.90448C16.455 8.69349 16.5 8.46736 16.5 8.23899C16.5 8.01063 16.455 7.78449 16.3676 7.57351C16.2802 7.36252 16.1522 7.17082 15.9907 7.00934C15.8292 6.84786 15.6375 6.71977 15.4265 6.63237C15.2155 6.54498 14.9894 6.5 14.761 6.5ZM12 16.5C11.7239 16.5 11.5 16.7239 11.5 17C11.5 17.2761 11.7239 17.5 12 17.5H18C18.2761 17.5 18.5 17.2761 18.5 17C18.5 16.7239 18.2761 16.5 18 16.5H12Z',
      className: 'aquiIcon__path '.concat(styles['icon__default-fill']),
    })
  );
});
PencilEditIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const ReloadIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M13.2863 6.65253C12.0855 6.3637 10.8225 6.4874 9.70065 7.00371C8.57876 7.52002 7.66329 8.39889 7.10165 9.49878C6.54002 10.5987 6.36491 11.8556 6.60452 13.0671C6.84414 14.2786 7.48453 15.3743 8.42257 16.1776C9.36062 16.9809 10.5417 17.4451 11.7757 17.4954C13.0097 17.5458 14.2247 17.1794 15.2251 16.4552C15.4487 16.2933 15.4988 15.9807 15.3369 15.757C15.175 15.5333 14.8624 15.4833 14.6387 15.6452C13.8202 16.2377 12.8261 16.5375 11.8165 16.4963C10.8069 16.455 9.84051 16.0752 9.07302 15.418C8.30552 14.7608 7.78157 13.8643 7.58552 12.8731C7.38947 11.8819 7.53274 10.8535 7.99226 9.95355C8.45178 9.05363 9.2008 8.33456 10.1187 7.91213C11.0366 7.48969 12.07 7.38849 13.0524 7.6248C14.0348 7.86111 14.9092 8.42119 15.5345 9.21485C15.9579 9.7521 16.2505 10.3752 16.3954 11.0352L13.7071 11.4497C13.4309 11.4497 13.2071 11.6736 13.2071 11.9497C13.2071 12.2259 13.4309 12.4497 13.7071 12.4497H16.7813C16.8473 12.4819 16.9216 12.5 17 12.5C17.0784 12.5 17.1527 12.4819 17.2187 12.4497H17.9497C18.2258 12.4497 18.4497 12.2259 18.4497 11.9497V7.70711C18.4497 7.43096 18.2258 7.20711 17.9497 7.20711C17.6736 7.20711 17.4497 7.43096 17.4497 7.70711L17.1038 9.95032C16.9097 9.46706 16.6467 9.01057 16.32 8.59593C15.5556 7.6259 14.487 6.94136 13.2863 6.65253Z',
    })
  );
});
ReloadIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const RestoreIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M12.7666 5.06375C14.1328 4.86628 15.5238 5.13054 16.7292 5.8151C17.9344 6.4995 18.8876 7.56601 19.4479 8.85146C20.0082 10.1367 20.1464 11.5732 19.8425 12.9453C19.5385 14.3174 18.8081 15.5535 17.7584 16.466C16.7084 17.3786 15.396 17.9177 14.0185 17.9992C13.7612 18.0144 13.5402 17.8192 13.525 17.5632C13.5097 17.3073 13.7058 17.0874 13.9631 17.0722C15.1312 17.0032 16.2478 16.546 17.1443 15.7667C18.0411 14.9872 18.6692 13.9273 18.931 12.7454C19.1928 11.5635 19.0735 10.3262 18.5917 9.22093C18.1099 8.1158 17.2929 7.20439 16.2666 6.62155C15.2405 6.03886 14.0594 5.81521 12.9007 5.98267C11.7419 6.15015 10.665 6.70027 9.83329 7.55325L9.82331 7.56319L7.29881 10H10.5C10.7761 10 11 10.2239 11 10.5C11 10.7761 10.7761 11 10.5 11H6.5C6.22386 11 6 10.7761 6 10.5V10.1566V10.1562V6.5C6 6.22386 6.22386 6 6.5 6C6.77614 6 7 6.22386 7 6.5V8.99464L9.16842 6.90154C10.1405 5.90686 11.4028 5.26086 12.7666 5.06375ZM4.5 13C4.22386 13 4 13.2239 4 13.5C4 13.7761 4.22386 14 4.5 14H10.5C10.7761 14 11 13.7761 11 13.5C11 13.2239 10.7761 13 10.5 13H4.5Z',
      className: 'aquiIcon__path '.concat(styles['icon__default-fill']),
    })
  );
});
RestoreIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const SlidersIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M6.5 5C6.77614 5 7 5.22386 7 5.5V10.5C7 10.7761 6.77614 11 6.5 11C6.22386 11 6 10.7761 6 10.5V5.5C6 5.22386 6.22386 5 6.5 5ZM6 14H4.5C4.22386 14 4 13.7761 4 13.5C4 13.2239 4.22386 13 4.5 13H8.5C8.77614 13 9 13.2239 9 13.5C9 13.7761 8.77614 14 8.5 14H7V19.5C7 19.7761 6.77614 20 6.5 20C6.22386 20 6 19.7761 6 19.5V14ZM12 13.5C12 13.2239 11.7761 13 11.5 13C11.2239 13 11 13.2239 11 13.5V19.5C11 19.7761 11.2239 20 11.5 20C11.7761 20 12 19.7761 12 19.5V13.5ZM11.5 5C11.7761 5 12 5.22386 12 5.5V10H13.5C13.7761 10 14 10.2239 14 10.5C14 10.7761 13.7761 11 13.5 11H11.5H9.5C9.22386 11 9 10.7761 9 10.5C9 10.2239 9.22386 10 9.5 10H11V5.5C11 5.22386 11.2239 5 11.5 5ZM16 16H14.5C14.2239 16 14 15.7761 14 15.5C14 15.2239 14.2239 15 14.5 15H18.5C18.7761 15 19 15.2239 19 15.5C19 15.7761 18.7761 16 18.5 16H17V19.5C17 19.7761 16.7761 20 16.5 20C16.2239 20 16 19.7761 16 19.5V16ZM16.5 5C16.7761 5 17 5.22386 17 5.5V12.5C17 12.7761 16.7761 13 16.5 13C16.2239 13 16 12.7761 16 12.5V5.5C16 5.22386 16.2239 5 16.5 5Z',
    })
  );
});
SlidersIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const StarIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      className: ''.concat(styles['icon__default-fill']),
      d: 'M12 3.5C12.1893 3.5 12.3624 3.60689 12.4471 3.77614L14.8021 8.4793L20.0713 9.23855C20.2605 9.26581 20.4176 9.3985 20.476 9.58044C20.5345 9.76238 20.4842 9.96174 20.3463 10.0941L16.5382 13.7505L17.4366 18.9143C17.4692 19.1015 17.3928 19.291 17.2396 19.4033C17.0863 19.5156 16.8826 19.5314 16.7139 19.4439L12 17.0001L7.28614 19.4439C7.11744 19.5314 6.91375 19.5156 6.76048 19.4033C6.60721 19.291 6.53084 19.1015 6.56342 18.9143L7.46181 13.7505L3.65372 10.0941C3.51587 9.96174 3.46552 9.76238 3.524 9.58044C3.58248 9.3985 3.73955 9.26581 3.92871 9.23855L9.19797 8.4793L11.5529 3.77614C11.6377 3.60689 11.8107 3.5 12 3.5ZM12 5.11675L9.9751 9.16077C9.90178 9.3072 9.76141 9.40844 9.59932 9.4318L5.0852 10.0822L8.34631 13.2135C8.46629 13.3287 8.52112 13.496 8.49262 13.6598L7.72154 18.0918L11.7699 15.993C11.9142 15.9182 12.0858 15.9182 12.2301 15.993L16.2785 18.0918L15.5074 13.6598C15.4789 13.496 15.5337 13.3287 15.6537 13.2135L18.9148 10.0822L14.4007 9.4318C14.2386 9.40844 14.0982 9.3072 14.0249 9.16077L12 5.11675Z',
    })
  );
});
StarIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const SubNodesIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      className: ''.concat(styles['icon__default-fill']),
      d: 'M6 9V15.9C6 16.1737 6.12035 16.4484 6.35518 16.6597C6.59175 16.8726 6.92288 17 7.27778 17H12.5C12.5 15.3431 13.8431 14 15.5 14C17.1569 14 18.5 15.3431 18.5 17C18.5 18.6569 17.1569 20 15.5 20C14.1838 20 13.0657 19.1525 12.6614 17.9734C12.6108 17.9906 12.5565 18 12.5 18H7.27778C6.68968 18 6.11645 17.7902 5.68622 17.403C5.25425 17.0142 5 16.475 5 15.9V8.5V3.5C5 3.22386 5.22386 3 5.5 3C5.77614 3 6 3.22386 6 3.5V8L12.5 8C12.5139 8 12.5276 8.00057 12.5412 8.00167C12.7785 6.58199 14.0129 5.5 15.5 5.5C17.1569 5.5 18.5 6.84315 18.5 8.5C18.5 10.1569 17.1569 11.5 15.5 11.5C14.0129 11.5 12.7785 10.418 12.5412 8.99833C12.5276 8.99943 12.5139 9 12.5 9L6 9ZM15.5 6.5C14.3954 6.5 13.5 7.39543 13.5 8.5C13.5 9.60457 14.3954 10.5 15.5 10.5C16.6046 10.5 17.5 9.60457 17.5 8.5C17.5 7.39543 16.6046 6.5 15.5 6.5ZM13.5 17C13.5 15.8954 14.3954 15 15.5 15C16.6046 15 17.5 15.8954 17.5 17C17.5 18.1046 16.6046 19 15.5 19C14.3954 19 13.5 18.1046 13.5 17Z',
    })
  );
});
SubNodesIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const ThreeDotsLoaderIcon = forwardRef((_ref, ref) => {
  const {className} = _ref;
  const rest = _objectWithoutProperties(_ref, ['className']);

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
      className: ''
        .concat(className || '', ' ')
        .concat(styles['three-dots-loader-icon']),
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      className: styles.circle,
      d: 'M 0, 12 a 2.8,2.8 0 1,1 5.6,0 a 2.8,2.8 0 1,1 -5.6,0',
    }),
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      className: styles.circle,
      d: 'M 9.2, 12 a 2.8,2.8 0 1,1 5.6,0 a 2.8,2.8 0 1,1 -5.6,0',
    }),
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      className: styles.circle,
      d: 'M 18.2, 12 a 2.8,2.8 0 1,1 5.6,0 a 2.8,2.8 0 1,1 -5.6,0',
    })
  );
});
ThreeDotsLoaderIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const TrashIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M10.211 7.23236C10.3588 7.08293 10.558 7 10.7646 7H13.2354C13.442 7 13.6412 7.08293 13.789 7.23236C13.937 7.38197 14.0211 7.58605 14.0211 7.8V9H9.97892V7.8C9.97892 7.58606 10.063 7.38197 10.211 7.23236ZM8.97892 9V7.8C8.97892 7.32438 9.16573 6.86715 9.5 6.52917C9.83445 6.191 10.2892 6 10.7646 6H13.2354C13.7108 6 14.1656 6.191 14.5 6.52917C14.8343 6.86715 15.0211 7.32438 15.0211 7.8V9H17.5714C17.8081 9 18 9.22386 18 9.5C18 9.77614 17.8081 10 17.5714 10H16.0001V16.2C16.0001 16.6756 15.8133 17.1329 15.479 17.4708C15.1445 17.809 14.6898 18 14.2144 18H9.78571C9.31032 18 8.85553 17.809 8.52108 17.4708C8.18681 17.1329 8 16.6756 8 16.2V10H6.42857C6.19188 10 6 9.77614 6 9.5C6 9.22386 6.19188 9 6.42857 9H8.97892ZM9 10V16.2C9 16.4139 9.08411 16.618 9.23208 16.7676C9.37986 16.9171 9.57912 17 9.78571 17H14.2144C14.4209 17 14.6202 16.9171 14.768 16.7676C14.916 16.618 15.0001 16.4139 15.0001 16.2V10H9Z',
    })
  );
});
TrashIcon.propTypes = svgIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const UserIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M9.5 8C9.5 6.61929 10.6193 5.5 12 5.5C13.3807 5.5 14.5 6.61929 14.5 8C14.5 9.38071 13.3807 10.5 12 10.5C10.6193 10.5 9.5 9.38071 9.5 8ZM12 4.5C10.067 4.5 8.5 6.067 8.5 8C8.5 9.933 10.067 11.5 12 11.5C13.933 11.5 15.5 9.933 15.5 8C15.5 6.067 13.933 4.5 12 4.5ZM9 12.5C8.08951 12.5 7.20617 12.821 6.5465 13.4073C5.88491 13.9954 5.5 14.8065 5.5 15.6667V17C5.5 17.1894 5.607 17.3625 5.77639 17.4472L6 17C5.77639 17.4472 5.77658 17.4473 5.77677 17.4474L5.77718 17.4476L5.77816 17.4481L5.78067 17.4493L5.7879 17.4529L5.81122 17.464C5.83071 17.4731 5.85809 17.4856 5.89334 17.501C5.96385 17.5319 6.06589 17.5743 6.19944 17.6244C6.46656 17.7246 6.85968 17.8553 7.37873 17.9851C8.41717 18.2447 9.95788 18.5 12 18.5C14.0421 18.5 15.5828 18.2447 16.6213 17.9851C17.1403 17.8553 17.5334 17.7246 17.8006 17.6244C17.9341 17.5743 18.0361 17.5319 18.1067 17.501C18.1419 17.4856 18.1693 17.4731 18.1888 17.464L18.2121 17.4529L18.2193 17.4493L18.2218 17.4481L18.2228 17.4476L18.2232 17.4474C18.2234 17.4473 18.2236 17.4472 18 17L18.2236 17.4472C18.393 17.3625 18.5 17.1894 18.5 17V15.6667C18.5 14.8065 18.1151 13.9954 17.4535 13.4073C16.7938 12.821 15.9105 12.5 15 12.5H9ZM6.55056 16.6881L6.5 16.6689V15.6667C6.5 15.1123 6.74723 14.5669 7.21086 14.1548C7.67641 13.7409 8.31919 13.5 9 13.5H15C15.6808 13.5 16.3236 13.7409 16.7891 14.1548C17.2528 14.5669 17.5 15.1123 17.5 15.6667V16.6689L17.4494 16.6881C17.2166 16.7754 16.8597 16.8947 16.3787 17.0149C15.4172 17.2553 13.9579 17.5 12 17.5C10.0421 17.5 8.58283 17.2553 7.62127 17.0149C7.14032 16.8947 6.78344 16.7754 6.55056 16.6881Z',
    })
  );
});
UserIcon.propTypes = svgIconPropTypes;

const outlineShapes = {
  HEXAGON: 'hexagon',
  TRIANGLE: 'triangle',
};
/**
 * @type React.FC<warningIconPropTypes>
 */

const WarningIcon = forwardRef((_ref, ref) => {
  const _ref$outlineShape = _ref.outlineShape;
  const outlineShape =
    _ref$outlineShape === void 0 ? 'triangle' : _ref$outlineShape;
  const rest = _objectWithoutProperties(_ref, ['outlineShape']);

  return /* #__PURE__ */ React.createElement(
    SwitchCase,
    {
      expr: outlineShape,
    },
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: outlineShapes.HEXAGON,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          fillRule: 'evenodd',
          d: 'M9.26569 5.12922C9.34842 5.04648 9.46064 5 9.57765 5H15.4224C15.5394 5 15.6516 5.04648 15.7343 5.12922L19.8708 9.26569C19.9535 9.34842 20 9.46064 20 9.57765V15.4224C20 15.5394 19.9535 15.6516 19.8708 15.7343L15.7343 19.8708C15.6516 19.9535 15.5394 20 15.4224 20H9.57765C9.46064 20 9.34842 19.9535 9.26569 19.8708L5.12922 15.7343C5.04648 15.6516 5 15.5394 5 15.4224V9.57765C5 9.46064 5.04648 9.34842 5.12922 9.26569L9.26569 5.12922ZM10 6L6 10V15L10 19H15L19 15V10L15 6H10ZM12.5 9.00002C12.7436 9.00002 13 9.25637 13 9.50002V12.6765C13 12.9201 12.7437 13.1176 12.5 13.1176C12.2563 13.1176 12 12.9201 12 12.6765V9.50002C12 9.25637 12.2563 9.00002 12.5 9.00002ZM13 15C13 14.7564 12.7436 14.5 12.5 14.5C12.2563 14.5 12 14.7564 12 15V16C12 16.2437 12.2563 16.5 12.5 16.5C12.7437 16.5 13 16.2437 13 16V15Z',
        })
      )
    ),
    /* #__PURE__ */ React.createElement(
      Case,
      {
        value: outlineShapes.TRIANGLE,
      },
      /* #__PURE__ */ React.createElement(
        SvgIcon,
        {
          ref,
          ...rest,
        },
        /* #__PURE__ */ React.createElement('path', {
          fillRule: 'evenodd',
          d: 'M11.0603 5.24667C11.3469 5.08507 11.6705 5 12 5C12.3295 5 12.6531 5.08507 12.9397 5.24667C13.2263 5.40825 13.4658 5.64076 13.6357 5.92131L13.6371 5.92353L19.7448 16.1362C19.9112 16.4249 19.9991 16.7518 20 17.0844C20.0009 17.4171 19.9149 17.7445 19.7501 18.034C19.5853 18.3236 19.3474 18.5655 19.0595 18.7351C18.7715 18.9048 18.4439 18.9963 18.1092 18.9999L18.1039 19L5.89083 19C5.55611 18.9963 5.22847 18.9048 4.94054 18.7351C4.65264 18.5655 4.41469 18.3236 4.24989 18.034C4.08511 17.7445 3.99908 17.4171 4.00001 17.0844C4.00094 16.7518 4.0888 16.4249 4.2552 16.1363L4.25893 16.1298L10.3629 5.92353L10.7677 6.16158L10.3643 5.92131C10.5342 5.64076 10.7737 5.40825 11.0603 5.24667ZM11.1717 6.40083L11.1711 6.40184L5.07059 16.6024C4.98638 16.7497 4.94166 16.9167 4.94118 17.087C4.9407 17.2585 4.98507 17.4269 5.06955 17.5753C5.15401 17.7237 5.27547 17.8468 5.42138 17.9328C5.56658 18.0184 5.73117 18.0644 5.89895 18.0666H18.101C18.2688 18.0644 18.4334 18.0184 18.5786 17.9328C18.7245 17.8468 18.846 17.7237 18.9305 17.5753C19.0149 17.4269 19.0593 17.2585 19.0588 17.087C19.0583 16.9167 19.0136 16.7497 18.9294 16.6024L12.8289 6.40184L12.8283 6.40088C12.7413 6.2576 12.6193 6.13968 12.4745 6.058C12.3293 5.97615 12.1659 5.93333 12 5.93333C11.8341 5.93333 11.6707 5.97615 11.5255 6.058C11.3807 6.13967 11.2587 6.25758 11.1717 6.40083ZM12 8.5C12.2761 8.5 12.5 8.72386 12.5 9V13C12.5 13.2761 12.2761 13.5 12 13.5C11.7239 13.5 11.5 13.2761 11.5 13V9C11.5 8.72386 11.7239 8.5 12 8.5ZM12.5 15C12.5 14.7239 12.2761 14.5 12 14.5C11.7239 14.5 11.5 14.7239 11.5 15V16C11.5 16.2761 11.7239 16.5 12 16.5C12.2761 16.5 12.5 16.2761 12.5 16V15Z',
        })
      )
    )
  );
});

const warningIconPropTypes = _objectSpread2(
  _objectSpread2({}, svgIconPropTypes),
  {},
  {
    /**
     * @prop {("triangle"|"hexagon")} outlineShape
     * defaults to "triangle"
     */
    outlineShape: propTypes.oneOf(['triangle', 'hexagon']),
  }
);

WarningIcon.propTypes = warningIconPropTypes;

/**
 * @type React.FC<svgIconPropTypes>
 */

const WrenchIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      d: 'M15.4776 5.60539C14.9536 5.48139 14.4071 5.46602 13.8721 5.56349C13.0882 5.70633 12.3664 6.08467 11.803 6.64811C11.2395 7.21156 10.8612 7.93333 10.7183 8.71726C10.5755 9.50118 10.675 10.31 11.0035 11.036C11.0893 11.2256 11.0487 11.4485 10.9015 11.5957L5.81125 16.6859C5.61196 16.8852 5.5 17.1555 5.5 17.4373C5.5 17.7192 5.61196 17.9895 5.81125 18.1888C6.01054 18.388 6.28083 18.5 6.56267 18.5C6.84451 18.5 7.1148 18.388 7.31409 18.1888L12.4043 13.0985C12.5515 12.9513 12.7744 12.9107 12.964 12.9965C13.69 13.325 14.4988 13.4245 15.2827 13.2817C16.0667 13.1388 16.7884 12.7605 17.3519 12.197C17.9153 11.6336 18.2937 10.9118 18.4365 10.1279C18.534 9.59294 18.5186 9.04636 18.3946 8.52244L16.1797 10.7373C15.9486 10.9639 15.6378 11.0908 15.3141 11.0908C14.9904 11.0908 14.6796 10.9639 14.4484 10.7373L14.4448 10.7338L13.2627 9.5516C13.0361 9.32044 12.9092 9.00963 12.9092 8.68593C12.9092 8.36223 13.0361 8.05144 13.2627 7.82028L13.2662 7.81671L15.4776 5.60539ZM13.6928 4.57969C14.6767 4.40042 15.6919 4.52526 16.6031 4.93758C16.7526 5.00525 16.8594 5.142 16.8888 5.30348C16.9183 5.46496 16.8666 5.6306 16.7505 5.74666L13.9756 8.52158C13.933 8.56568 13.9092 8.62459 13.9092 8.68593C13.9092 8.74728 13.933 8.8062 13.9756 8.8503L15.1497 10.0244C15.1938 10.067 15.2527 10.0908 15.3141 10.0908C15.3754 10.0908 15.4343 10.067 15.4784 10.0244L18.2533 7.2495C18.3694 7.13344 18.535 7.08173 18.6965 7.11116C18.858 7.14058 18.9948 7.24738 19.0624 7.39692C19.4747 8.30808 19.5996 9.32325 19.4203 10.3072C19.241 11.2911 18.7662 12.197 18.059 12.9042C17.3518 13.6113 16.4459 14.0862 15.462 14.2655C14.5935 14.4237 13.7005 14.345 12.8763 14.0407L8.0212 18.8959C7.63437 19.2827 7.10972 19.5 6.56267 19.5C6.01562 19.5 5.49097 19.2827 5.10414 18.8959C4.71732 18.509 4.5 17.9844 4.5 17.4373C4.5 16.8903 4.71732 16.3656 5.10414 15.9788L9.95927 11.1237C9.655 10.2995 9.57628 9.40655 9.73453 8.538C9.9138 7.5541 10.3887 6.64819 11.0958 5.94101C11.803 5.23383 12.7089 4.75896 13.6928 4.57969Z',
    })
  );
});
WrenchIcon.propTypes = svgIconPropTypes;

const CopyIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      clipRule: 'evenodd',
      d: 'M5.7591 5.7591C5.925 5.5932 6.15 5.5 6.38462 5.5H12.6154C12.85 5.5 13.075 5.5932 13.2409 5.7591C13.4068 5.925 13.5 6.15 13.5 6.38462V7.07692C13.5 7.35307 13.7239 7.57692 14 7.57692C14.2761 7.57692 14.5 7.35307 14.5 7.07692V6.38462C14.5 5.88478 14.3014 5.40542 13.948 5.05199C13.5946 4.69856 13.1152 4.5 12.6154 4.5H6.38462C5.88478 4.5 5.40542 4.69856 5.05199 5.05199C4.69856 5.40542 4.5 5.88478 4.5 6.38462V12.6154C4.5 13.1152 4.69856 13.5946 5.05199 13.948C5.40542 14.3014 5.88478 14.5 6.38462 14.5H7.07692C7.35307 14.5 7.57692 14.2761 7.57692 14C7.57692 13.7239 7.35307 13.5 7.07692 13.5H6.38462C6.15 13.5 5.925 13.4068 5.7591 13.2409C5.5932 13.075 5.5 12.85 5.5 12.6154V6.38462C5.5 6.15 5.5932 5.925 5.7591 5.7591ZM10.5 11.3846C10.5 10.8961 10.8961 10.5 11.3846 10.5H17.6154C18.1039 10.5 18.5 10.8961 18.5 11.3846V17.6154C18.5 18.1039 18.1039 18.5 17.6154 18.5H11.3846C10.8961 18.5 10.5 18.1039 10.5 17.6154V11.3846ZM11.3846 9.5C10.3438 9.5 9.5 10.3438 9.5 11.3846V17.6154C9.5 18.6562 10.3438 19.5 11.3846 19.5H17.6154C18.6562 19.5 19.5 18.6562 19.5 17.6154V11.3846C19.5 10.3438 18.6562 9.5 17.6154 9.5H11.3846Z',
    })
  );
});
CopyIcon.propTypes = svgIconPropTypes;

const UploadIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      clipRule: 'evenodd',
      d: 'M14.8536 8.85355C14.6583 9.04882 14.3417 9.04882 14.1464 8.85355L11.1486 5.14433C11.196 5.09744 11.2505 5.06198 11.3086 5.03794C11.3667 5.01385 11.4303 5.0004 11.497 5.00001L11.5 5L11.503 5.00001C11.5697 5.0004 11.6333 5.01385 11.6914 5.03794C11.7504 5.06234 11.8056 5.09851 11.8536 5.14645L14.8536 8.14645C15.0488 8.34171 15.0488 8.65829 14.8536 8.85355ZM14.1464 8.85355L11.1461 5.14681L8.14645 8.14645C7.95119 8.34171 7.95119 8.65829 8.14645 8.85355C8.34171 9.04882 8.65829 9.04882 8.85355 8.85355L11 6.70711L11 14.5C11 14.7761 11.2239 15 11.5 15C11.7761 15 12 14.7761 12 14.5L12 6.70711L14.1464 8.85355ZM7.5 18C7.22386 18 7 18.2239 7 18.5C7 18.7762 7.22386 19 7.5 19H15.5C15.7761 19 16 18.7762 16 18.5C16 18.2239 15.7761 18 15.5 18H7.5Z',
    })
  );
});
UploadIcon.propTypes = svgIconPropTypes;

const PlusIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      clipRule: 'evenodd',
      d: 'M12.5 6C12.5 5.72386 12.2761 5.5 12 5.5C11.7239 5.5 11.5 5.72386 11.5 6V11.5H6C5.72386 11.5 5.5 11.7239 5.5 12C5.5 12.2761 5.72386 12.5 6 12.5H11.5V18C11.5 18.2761 11.7239 18.5 12 18.5C12.2761 18.5 12.5 18.2761 12.5 18V12.5H18C18.2761 12.5 18.5 12.2761 18.5 12C18.5 11.7239 18.2761 11.5 18 11.5H12.5V6Z',
    })
  );
});
PlusIcon.propTypes = svgIconPropTypes;

const FilterIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      clipRule: 'evenodd',
      d: 'M6 7.5C6 7.22386 6.22386 7 6.5 7H17.5C17.7761 7 18 7.22386 18 7.5C18 7.77614 17.7761 8 17.5 8H6.5C6.22386 8 6 7.77614 6 7.5ZM8 11.5C8 11.2239 8.22386 11 8.5 11H15.5C15.7761 11 16 11.2239 16 11.5C16 11.7761 15.7761 12 15.5 12H8.5C8.22386 12 8 11.7761 8 11.5ZM10.5 15C10.2239 15 10 15.2239 10 15.5C10 15.7761 10.2239 16 10.5 16H13.5C13.7761 16 14 15.7761 14 15.5C14 15.2239 13.7761 15 13.5 15H10.5Z',
    })
  );
});
FilterIcon.propTypes = svgIconPropTypes;

const ArrowsSwitchIcon = forwardRef((_ref, ref) => {
  const _ref$direction = _ref.direction;
  const direction = _ref$direction === void 0 ? 'horizontal' : _ref$direction;
  const rest = _objectWithoutProperties(_ref, ['direction']);

  const getPath = function getPath() {
    if (direction === 'horizontal') {
      return 'M18.0001 14.5L8.98494 14.5L10.1314 13.3536C10.3267 13.1583 10.3267 12.8417 10.1314 12.6464C9.93613 12.4512 9.61955 12.4512 9.42428 12.6464L7.42428 14.6464C7.22902 14.8417 7.22902 15.1583 7.42429 15.3536L9.42428 17.3536C9.61955 17.5488 9.93613 17.5488 10.1314 17.3536C10.3267 17.1583 10.3267 16.8417 10.1314 16.6464L8.98494 15.5L18.0001 15.5C18.2762 15.5 18.5001 15.2761 18.5001 15C18.5001 14.7239 18.2762 14.5 18.0001 14.5ZM14.1314 6.64645C13.9361 6.45118 13.6195 6.45118 13.4243 6.64645C13.229 6.84171 13.229 7.15829 13.4243 7.35355L14.5707 8.5L6.00001 8.5C5.72386 8.5 5.50001 8.72386 5.50001 9C5.50001 9.27614 5.72386 9.5 6.00001 9.5L14.5707 9.5L13.4243 10.6464C13.229 10.8417 13.229 11.1583 13.4243 11.3536C13.6195 11.5488 13.9361 11.5488 14.1314 11.3536L16.1314 9.35355C16.3267 9.15829 16.3267 8.84171 16.1314 8.64645L14.1314 6.64645Z';
    }
    return 'M14.5 5.99994L14.5 15.0151L13.3536 13.8686C13.1583 13.6733 12.8417 13.6733 12.6464 13.8686C12.4512 14.0639 12.4512 14.3805 12.6464 14.5757L14.6464 16.5757C14.8417 16.771 15.1583 16.771 15.3536 16.5757L17.3536 14.5757C17.5488 14.3805 17.5488 14.0639 17.3536 13.8686C17.1583 13.6733 16.8417 13.6733 16.6464 13.8686L15.5 15.0151V5.99994C15.5 5.7238 15.2761 5.49994 15 5.49994C14.7239 5.49994 14.5 5.7238 14.5 5.99994ZM6.64645 9.86861C6.45118 10.0639 6.45118 10.3805 6.64645 10.5757C6.84171 10.771 7.15829 10.771 7.35355 10.5757L8.5 9.42927V18C8.5 18.2761 8.72386 18.5 9 18.5C9.27614 18.5 9.5 18.2761 9.5 18V9.42927L10.6464 10.5757C10.8417 10.771 11.1583 10.771 11.3536 10.5757C11.5488 10.3805 11.5488 10.0639 11.3536 9.86861L9.35355 7.86861C9.15829 7.67335 8.84171 7.67335 8.64645 7.86861L6.64645 9.86861Z';
  };

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      clipRule: 'evenodd',
      d: getPath(),
    })
  );
});

const arrowsSwitchIconPropTypes = _objectSpread2(
  _objectSpread2({}, svgIconPropTypes),
  {},
  {
    /*
     * defaults to 'horizontal'.
     */
    direction: propTypes.oneOf(['horizontal', 'vertical']),
  }
);

ArrowsSwitchIcon.propTypes = arrowsSwitchIconPropTypes;

const UndoIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      clipRule: 'evenodd',
      d: 'M13.2863 6.65253C12.0855 6.3637 10.8225 6.4874 9.70065 7.00371C8.57876 7.52002 7.66329 8.39889 7.10165 9.49878C6.54002 10.5987 6.36491 11.8556 6.60452 13.0671C6.84414 14.2786 7.48453 15.3743 8.42257 16.1776C9.36062 16.9809 10.5417 17.4451 11.7757 17.4954C13.0097 17.5458 14.2247 17.1794 15.2251 16.4552C15.4487 16.2933 15.4988 15.9807 15.3369 15.757C15.175 15.5333 14.8624 15.4833 14.6387 15.6452C13.8202 16.2377 12.8261 16.5375 11.8165 16.4963C10.8069 16.455 9.84051 16.0752 9.07302 15.418C8.30552 14.7608 7.78157 13.8643 7.58552 12.8731C7.38947 11.8819 7.53274 10.8535 7.99226 9.95355C8.45178 9.05363 9.2008 8.33456 10.1187 7.91213C11.0366 7.48969 12.07 7.38849 13.0524 7.6248C14.0348 7.86111 14.9092 8.42119 15.5345 9.21485C15.9579 9.7521 16.2505 10.3752 16.3954 11.0352L13.7071 11.4497C13.4309 11.4497 13.2071 11.6736 13.2071 11.9497C13.2071 12.2259 13.4309 12.4497 13.7071 12.4497H16.7813C16.8473 12.4819 16.9216 12.5 17 12.5C17.0784 12.5 17.1527 12.4819 17.2187 12.4497H17.9497C18.2258 12.4497 18.4497 12.2259 18.4497 11.9497V7.70711C18.4497 7.43096 18.2258 7.20711 17.9497 7.20711C17.6736 7.20711 17.4497 7.43096 17.4497 7.70711L17.1038 9.95032C16.9097 9.46706 16.6467 9.01057 16.32 8.59593C15.5556 7.6259 14.487 6.94136 13.2863 6.65253Z',
    })
  );
});
UndoIcon.propTypes = svgIconPropTypes;

const NotAllowedIcon = forwardRef((_ref, ref) => {
  const rest = {..._ref};

  return /* #__PURE__ */ React.createElement(
    SvgIcon,
    {
      ref,
      ...rest,
    },
    /* #__PURE__ */ React.createElement('path', {
      fillRule: 'evenodd',
      clipRule: 'evenodd',
      d: 'M7.80783 6.39362C8.97641 5.5184 10.4277 5 12 5C15.866 5 19 8.13401 19 12C19 13.5723 18.4816 15.0236 17.6064 16.1922L7.80783 6.39362ZM6.39362 7.80783C5.5184 8.97641 5 10.4277 5 12C5 15.866 8.13401 19 12 19C13.5723 19 15.0236 18.4816 16.1922 17.6064L6.39362 7.80783ZM12 3C7.02944 3 3 7.02944 3 12C3 16.9706 7.02944 21 12 21C16.9706 21 21 16.9706 21 12C21 7.02944 16.9706 3 12 3Z',
    })
  );
});
NotAllowedIcon.propTypes = svgIconPropTypes;

export {
  AlertMessageIcon,
  ArrowIcon,
  ArrowsSwitchIcon,
  BellIcon,
  CheckMarkIcon,
  ChevronIcon,
  CircleCheckMarkIcon,
  CircleCrossMarkIcon,
  CircleInfoIcon,
  CirclePlusIcon,
  CopyIcon,
  CrossMarkIcon,
  CrossedCheckmarkIcon,
  DoubleChevronIcon,
  DownloadIcon,
  ExportIcon,
  FilterIcon,
  GridIcon,
  HideSourceIcon,
  LightBulbIcon,
  LockIcon,
  MagnifyingGlassIcon,
  MergeIcon,
  MoreIcon,
  NotAllowedIcon,
  PencilEditIcon,
  PlusIcon,
  ReloadIcon,
  RestoreIcon,
  SlidersIcon,
  StarIcon,
  SubNodesIcon,
  ThreeDotsLoaderIcon,
  TrashIcon,
  UndoIcon,
  UnmergeIcon,
  UploadIcon,
  UserIcon,
  WarningIcon,
  WrenchIcon,
};

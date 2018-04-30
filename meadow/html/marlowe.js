"use strict";
var __haste_prog_id = '7f169c2c2d6a07f8591b239df7501bc594d76ba37a8ae695b1f9dae4d0cf3c36';
var __haste_script_elem = typeof document == 'object' ? document.currentScript : null;
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined' && typeof global !== 'undefined') window = global;
window['__haste_crypto'] = window.crypto || window.msCrypto;
if(window['__haste_crypto'] && !window['__haste_crypto'].subtle && window.crypto.webkitSubtle) {
    window['__haste_crypto'].subtle = window.crypto.webkitSubtle;
}

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(738919189, 2683596561, true)
  var y = new Long(3648966346, 573393410, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var len = buffer.byteLength;
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': len % 2 ? null : new Int16Array(buffer)
        , 'i32': len % 4 ? null : new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': len % 2 ? null : new Uint16Array(buffer)
        , 'w32': len % 4 ? null : new Uint32Array(buffer)
        , 'f32': len % 4 ? null : new Float32Array(buffer)
        , 'f64': len % 8 ? null : new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __isUndef = function(x) {return typeof x == 'undefined';}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

/* Code for creating and querying the static pointer table. */
window.__hs_spt = [];

function __spt_insert(ptr) {
    ptr = E(B(ptr));
    var ks = [ (ptr.a.a.low>>>0).toString(16)
             , (ptr.a.a.high>>>0).toString(16)
             , (ptr.a.b.low>>>0).toString(16)
             , (ptr.a.b.high>>>0).toString(16)
             ]
    var key = ks.join();
    window.__hs_spt[key] = ptr;
}

function hs_spt_lookup(k) {
    var ks = [ k['v']['w32'][0].toString(16)
             , k['v']['w32'][1].toString(16)
             , k['v']['w32'][2].toString(16)
             , k['v']['w32'][3].toString(16)
             ]
    var key = ks.join();
    return window.__hs_spt[key];
}

var _0=new T0(1),_1=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_2=function(_3){return new F(function(){return err(_1);});},_4=new T(function(){return B(_2(_));}),_5=function(_6,_7,_8){var _9=E(_8);if(!_9._){var _a=_9.a,_b=E(_7);if(!_b._){var _c=_b.a,_d=_b.b;if(_c<=(imul(3,_a)|0)){return new T4(0,(1+_c|0)+_a|0,E(_6),E(_b),E(_9));}else{var _e=E(_b.c);if(!_e._){var _f=_e.a,_g=E(_b.d);if(!_g._){var _h=_g.a,_i=_g.b,_j=_g.c;if(_h>=(imul(2,_f)|0)){var _k=function(_l){var _m=E(_g.d);return (_m._==0)?new T4(0,(1+_c|0)+_a|0,E(_i),E(new T4(0,(1+_f|0)+_l|0,E(_d),E(_e),E(_j))),E(new T4(0,(1+_a|0)+_m.a|0,E(_6),E(_m),E(_9)))):new T4(0,(1+_c|0)+_a|0,E(_i),E(new T4(0,(1+_f|0)+_l|0,E(_d),E(_e),E(_j))),E(new T4(0,1+_a|0,E(_6),E(_0),E(_9))));},_n=E(_j);if(!_n._){return new F(function(){return _k(_n.a);});}else{return new F(function(){return _k(0);});}}else{return new T4(0,(1+_c|0)+_a|0,E(_d),E(_e),E(new T4(0,(1+_a|0)+_h|0,E(_6),E(_g),E(_9))));}}else{return E(_4);}}else{return E(_4);}}}else{return new T4(0,1+_a|0,E(_6),E(_0),E(_9));}}else{var _o=E(_7);if(!_o._){var _p=_o.a,_q=_o.b,_r=_o.d,_s=E(_o.c);if(!_s._){var _t=_s.a,_u=E(_r);if(!_u._){var _v=_u.a,_w=_u.b,_x=_u.c;if(_v>=(imul(2,_t)|0)){var _y=function(_z){var _A=E(_u.d);return (_A._==0)?new T4(0,1+_p|0,E(_w),E(new T4(0,(1+_t|0)+_z|0,E(_q),E(_s),E(_x))),E(new T4(0,1+_A.a|0,E(_6),E(_A),E(_0)))):new T4(0,1+_p|0,E(_w),E(new T4(0,(1+_t|0)+_z|0,E(_q),E(_s),E(_x))),E(new T4(0,1,E(_6),E(_0),E(_0))));},_B=E(_x);if(!_B._){return new F(function(){return _y(_B.a);});}else{return new F(function(){return _y(0);});}}else{return new T4(0,1+_p|0,E(_q),E(_s),E(new T4(0,1+_v|0,E(_6),E(_u),E(_0))));}}else{return new T4(0,3,E(_q),E(_s),E(new T4(0,1,E(_6),E(_0),E(_0))));}}else{var _C=E(_r);return (_C._==0)?new T4(0,3,E(_C.b),E(new T4(0,1,E(_q),E(_0),E(_0))),E(new T4(0,1,E(_6),E(_0),E(_0)))):new T4(0,2,E(_6),E(_o),E(_0));}}else{return new T4(0,1,E(_6),E(_0),E(_0));}}},_D=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_E=function(_F){return new F(function(){return err(_D);});},_G=new T(function(){return B(_E(_));}),_H=function(_I,_J,_K){var _L=E(_J);if(!_L._){var _M=_L.a,_N=E(_K);if(!_N._){var _O=_N.a,_P=_N.b;if(_O<=(imul(3,_M)|0)){return new T4(0,(1+_M|0)+_O|0,E(_I),E(_L),E(_N));}else{var _Q=E(_N.c);if(!_Q._){var _R=_Q.a,_S=_Q.b,_T=_Q.c,_U=E(_N.d);if(!_U._){var _V=_U.a;if(_R>=(imul(2,_V)|0)){var _W=function(_X){var _Y=E(_I),_Z=E(_Q.d);return (_Z._==0)?new T4(0,(1+_M|0)+_O|0,E(_S),E(new T4(0,(1+_M|0)+_X|0,E(_Y),E(_L),E(_T))),E(new T4(0,(1+_V|0)+_Z.a|0,E(_P),E(_Z),E(_U)))):new T4(0,(1+_M|0)+_O|0,E(_S),E(new T4(0,(1+_M|0)+_X|0,E(_Y),E(_L),E(_T))),E(new T4(0,1+_V|0,E(_P),E(_0),E(_U))));},_10=E(_T);if(!_10._){return new F(function(){return _W(_10.a);});}else{return new F(function(){return _W(0);});}}else{return new T4(0,(1+_M|0)+_O|0,E(_P),E(new T4(0,(1+_M|0)+_R|0,E(_I),E(_L),E(_Q))),E(_U));}}else{return E(_G);}}else{return E(_G);}}}else{return new T4(0,1+_M|0,E(_I),E(_L),E(_0));}}else{var _11=E(_K);if(!_11._){var _12=_11.a,_13=_11.b,_14=_11.d,_15=E(_11.c);if(!_15._){var _16=_15.a,_17=_15.b,_18=_15.c,_19=E(_14);if(!_19._){var _1a=_19.a;if(_16>=(imul(2,_1a)|0)){var _1b=function(_1c){var _1d=E(_I),_1e=E(_15.d);return (_1e._==0)?new T4(0,1+_12|0,E(_17),E(new T4(0,1+_1c|0,E(_1d),E(_0),E(_18))),E(new T4(0,(1+_1a|0)+_1e.a|0,E(_13),E(_1e),E(_19)))):new T4(0,1+_12|0,E(_17),E(new T4(0,1+_1c|0,E(_1d),E(_0),E(_18))),E(new T4(0,1+_1a|0,E(_13),E(_0),E(_19))));},_1f=E(_18);if(!_1f._){return new F(function(){return _1b(_1f.a);});}else{return new F(function(){return _1b(0);});}}else{return new T4(0,1+_12|0,E(_13),E(new T4(0,1+_16|0,E(_I),E(_0),E(_15))),E(_19));}}else{return new T4(0,3,E(_17),E(new T4(0,1,E(_I),E(_0),E(_0))),E(new T4(0,1,E(_13),E(_0),E(_0))));}}else{var _1g=E(_14);return (_1g._==0)?new T4(0,3,E(_13),E(new T4(0,1,E(_I),E(_0),E(_0))),E(_1g)):new T4(0,2,E(_I),E(_0),E(_11));}}else{return new T4(0,1,E(_I),E(_0),E(_0));}}},_1h=function(_1i,_1j,_1k,_1l,_1m){var _1n=E(_1m);if(!_1n._){var _1o=_1n.c,_1p=_1n.d,_1q=E(_1n.b),_1r=E(_1i),_1s=E(_1q.a);if(_1r>=_1s){if(_1r!=_1s){return new F(function(){return _H(_1q,_1o,B(_1h(_1r,_1j,_1k,_1l,_1p)));});}else{var _1t=E(_1j),_1u=E(_1q.b);if(_1t>=_1u){if(_1t!=_1u){return new F(function(){return _H(_1q,_1o,B(_1h(_1r,_1t,_1k,_1l,_1p)));});}else{var _1v=E(_1k),_1w=E(_1q.c);if(_1v>=_1w){if(_1v!=_1w){return new F(function(){return _H(_1q,_1o,B(_1h(_1r,_1t,_1v,_1l,_1p)));});}else{var _1x=E(_1l),_1y=E(_1q.d);if(_1x>=_1y){if(_1x!=_1y){return new F(function(){return _H(_1q,_1o,B(_1h(_1r,_1t,_1v,_1x,_1p)));});}else{return new T4(0,_1n.a,E(new T4(0,_1r,_1t,_1v,_1x)),E(_1o),E(_1p));}}else{return new F(function(){return _5(_1q,B(_1h(_1r,_1t,_1v,_1x,_1o)),_1p);});}}}else{return new F(function(){return _5(_1q,B(_1h(_1r,_1t,_1v,_1l,_1o)),_1p);});}}}else{return new F(function(){return _5(_1q,B(_1h(_1r,_1t,_1k,_1l,_1o)),_1p);});}}}else{return new F(function(){return _5(_1q,B(_1h(_1r,_1j,_1k,_1l,_1o)),_1p);});}}else{return new T4(0,1,E(new T4(0,_1i,_1j,_1k,_1l)),E(_0),E(_0));}},_1z=function(_1A,_1B){while(1){var _1C=E(_1B);if(!_1C._){return E(_1A);}else{var _1D=E(_1C.a),_1E=B(_1h(_1D.a,_1D.b,_1D.c,_1D.d,_1A));_1A=_1E;_1B=_1C.b;continue;}}},_1F=function(_1G,_1H,_1I,_1J,_1K,_1L){return new F(function(){return _1z(B(_1h(_1H,_1I,_1J,_1K,_1G)),_1L);});},_1M=__Z,_1N=function(_1O){return new T4(0,1,E(_1O),E(_0),E(_0));},_1P=function(_1Q,_1R){var _1S=E(_1R);if(!_1S._){return new F(function(){return _H(_1S.b,_1S.c,B(_1P(_1Q,_1S.d)));});}else{return new F(function(){return _1N(_1Q);});}},_1T=function(_1U,_1V){var _1W=E(_1V);if(!_1W._){return new F(function(){return _5(_1W.b,B(_1T(_1U,_1W.c)),_1W.d);});}else{return new F(function(){return _1N(_1U);});}},_1X=function(_1Y,_1Z,_20,_21,_22){return new F(function(){return _H(_20,_21,B(_1P(_1Y,_22)));});},_23=function(_24,_25,_26,_27,_28){return new F(function(){return _5(_26,B(_1T(_24,_27)),_28);});},_29=function(_2a,_2b,_2c,_2d,_2e,_2f){var _2g=E(_2b);if(!_2g._){var _2h=_2g.a,_2i=_2g.b,_2j=_2g.c,_2k=_2g.d;if((imul(3,_2h)|0)>=_2c){if((imul(3,_2c)|0)>=_2h){return new T4(0,(_2h+_2c|0)+1|0,E(_2a),E(_2g),E(new T4(0,_2c,E(_2d),E(_2e),E(_2f))));}else{return new F(function(){return _H(_2i,_2j,B(_29(_2a,_2k,_2c,_2d,_2e,_2f)));});}}else{return new F(function(){return _5(_2d,B(_2l(_2a,_2h,_2i,_2j,_2k,_2e)),_2f);});}}else{return new F(function(){return _23(_2a,_2c,_2d,_2e,_2f);});}},_2l=function(_2m,_2n,_2o,_2p,_2q,_2r){var _2s=E(_2r);if(!_2s._){var _2t=_2s.a,_2u=_2s.b,_2v=_2s.c,_2w=_2s.d;if((imul(3,_2n)|0)>=_2t){if((imul(3,_2t)|0)>=_2n){return new T4(0,(_2n+_2t|0)+1|0,E(_2m),E(new T4(0,_2n,E(_2o),E(_2p),E(_2q))),E(_2s));}else{return new F(function(){return _H(_2o,_2p,B(_29(_2m,_2q,_2t,_2u,_2v,_2w)));});}}else{return new F(function(){return _5(_2u,B(_2l(_2m,_2n,_2o,_2p,_2q,_2v)),_2w);});}}else{return new F(function(){return _1X(_2m,_2n,_2o,_2p,_2q);});}},_2x=function(_2y,_2z,_2A){var _2B=E(_2z);if(!_2B._){var _2C=_2B.a,_2D=_2B.b,_2E=_2B.c,_2F=_2B.d,_2G=E(_2A);if(!_2G._){var _2H=_2G.a,_2I=_2G.b,_2J=_2G.c,_2K=_2G.d;if((imul(3,_2C)|0)>=_2H){if((imul(3,_2H)|0)>=_2C){return new T4(0,(_2C+_2H|0)+1|0,E(_2y),E(_2B),E(_2G));}else{return new F(function(){return _H(_2D,_2E,B(_29(_2y,_2F,_2H,_2I,_2J,_2K)));});}}else{return new F(function(){return _5(_2I,B(_2l(_2y,_2C,_2D,_2E,_2F,_2J)),_2K);});}}else{return new F(function(){return _1X(_2y,_2C,_2D,_2E,_2F);});}}else{return new F(function(){return _1T(_2y,_2A);});}},_2L=function(_2M,_2N){var _2O=E(_2N);if(!_2O._){return new T3(0,_0,_1M,_1M);}else{var _2P=_2O.a,_2Q=E(_2M);if(_2Q==1){var _2R=E(_2O.b);if(!_2R._){return new T3(0,new T(function(){return new T4(0,1,E(_2P),E(_0),E(_0));}),_1M,_1M);}else{var _2S=E(_2P),_2T=E(_2S.a),_2U=E(_2R.a),_2V=E(_2U.a);if(_2T>=_2V){if(_2T!=_2V){return new T3(0,new T4(0,1,E(_2S),E(_0),E(_0)),_1M,_2R);}else{var _2W=E(_2S.b),_2X=E(_2U.b);if(_2W>=_2X){if(_2W!=_2X){return new T3(0,new T4(0,1,E(_2S),E(_0),E(_0)),_1M,_2R);}else{var _2Y=E(_2S.c),_2Z=E(_2U.c);return (_2Y>=_2Z)?(_2Y!=_2Z)?new T3(0,new T4(0,1,E(_2S),E(_0),E(_0)),_1M,_2R):(E(_2S.d)<E(_2U.d))?new T3(0,new T4(0,1,E(_2S),E(_0),E(_0)),_2R,_1M):new T3(0,new T4(0,1,E(_2S),E(_0),E(_0)),_1M,_2R):new T3(0,new T4(0,1,E(_2S),E(_0),E(_0)),_2R,_1M);}}else{return new T3(0,new T4(0,1,E(_2S),E(_0),E(_0)),_2R,_1M);}}}else{return new T3(0,new T4(0,1,E(_2S),E(_0),E(_0)),_2R,_1M);}}}else{var _30=B(_2L(_2Q>>1,_2O)),_31=_30.a,_32=_30.c,_33=E(_30.b);if(!_33._){return new T3(0,_31,_1M,_32);}else{var _34=_33.a,_35=E(_33.b);if(!_35._){return new T3(0,new T(function(){return B(_1P(_34,_31));}),_1M,_32);}else{var _36=E(_34),_37=E(_36.a),_38=E(_35.a),_39=E(_38.a);if(_37>=_39){if(_37!=_39){return new T3(0,_31,_1M,_33);}else{var _3a=E(_36.b),_3b=E(_38.b);if(_3a>=_3b){if(_3a!=_3b){return new T3(0,_31,_1M,_33);}else{var _3c=E(_36.c),_3d=E(_38.c);if(_3c>=_3d){if(_3c!=_3d){return new T3(0,_31,_1M,_33);}else{if(E(_36.d)<E(_38.d)){var _3e=B(_2L(_2Q>>1,_35));return new T3(0,new T(function(){return B(_2x(_36,_31,_3e.a));}),_3e.b,_3e.c);}else{return new T3(0,_31,_1M,_33);}}}else{var _3f=B(_2L(_2Q>>1,_35));return new T3(0,new T(function(){return B(_2x(_36,_31,_3f.a));}),_3f.b,_3f.c);}}}else{var _3g=B(_2L(_2Q>>1,_35));return new T3(0,new T(function(){return B(_2x(_36,_31,_3g.a));}),_3g.b,_3g.c);}}}else{var _3h=B(_2L(_2Q>>1,_35));return new T3(0,new T(function(){return B(_2x(_36,_31,_3h.a));}),_3h.b,_3h.c);}}}}}},_3i=function(_3j,_3k,_3l){var _3m=E(_3l);if(!_3m._){return E(_3k);}else{var _3n=_3m.a,_3o=E(_3m.b);if(!_3o._){return new F(function(){return _1P(_3n,_3k);});}else{var _3p=E(_3n),_3q=_3p.b,_3r=_3p.c,_3s=_3p.d,_3t=E(_3p.a),_3u=E(_3o.a),_3v=E(_3u.a),_3w=function(_3x){var _3y=B(_2L(_3j,_3o)),_3z=_3y.a,_3A=E(_3y.c);if(!_3A._){return new F(function(){return _3i(_3j<<1,B(_2x(_3p,_3k,_3z)),_3y.b);});}else{return new F(function(){return _1z(B(_2x(_3p,_3k,_3z)),_3A);});}};if(_3t>=_3v){if(_3t!=_3v){return new F(function(){return _1F(_3k,_3t,_3q,_3r,_3s,_3o);});}else{var _3B=E(_3q),_3C=E(_3u.b);if(_3B>=_3C){if(_3B!=_3C){return new F(function(){return _1F(_3k,_3t,_3B,_3r,_3s,_3o);});}else{var _3D=E(_3r),_3E=E(_3u.c);if(_3D>=_3E){if(_3D!=_3E){return new F(function(){return _1F(_3k,_3t,_3B,_3D,_3s,_3o);});}else{var _3F=E(_3s);if(_3F<E(_3u.d)){return new F(function(){return _3w(_);});}else{return new F(function(){return _1F(_3k,_3t,_3B,_3D,_3F,_3o);});}}}else{return new F(function(){return _3w(_);});}}}else{return new F(function(){return _3w(_);});}}}else{return new F(function(){return _3w(_);});}}}},_3G=function(_3H){var _3I=E(_3H);if(!_3I._){return new T0(1);}else{var _3J=_3I.a,_3K=E(_3I.b);if(!_3K._){return new T4(0,1,E(_3J),E(_0),E(_0));}else{var _3L=_3K.b,_3M=E(_3J),_3N=E(_3M.a),_3O=E(_3K.a),_3P=_3O.b,_3Q=_3O.c,_3R=_3O.d,_3S=E(_3O.a);if(_3N>=_3S){if(_3N!=_3S){return new F(function(){return _1F(new T4(0,1,E(_3M),E(_0),E(_0)),_3S,_3P,_3Q,_3R,_3L);});}else{var _3T=E(_3M.b),_3U=E(_3P);if(_3T>=_3U){if(_3T!=_3U){return new F(function(){return _1F(new T4(0,1,E(_3M),E(_0),E(_0)),_3S,_3U,_3Q,_3R,_3L);});}else{var _3V=E(_3M.c),_3W=E(_3Q);if(_3V>=_3W){if(_3V!=_3W){return new F(function(){return _1F(new T4(0,1,E(_3M),E(_0),E(_0)),_3S,_3U,_3W,_3R,_3L);});}else{var _3X=E(_3R);if(E(_3M.d)<_3X){return new F(function(){return _3i(1,new T4(0,1,E(_3M),E(_0),E(_0)),_3K);});}else{return new F(function(){return _1F(new T4(0,1,E(_3M),E(_0),E(_0)),_3S,_3U,_3W,_3X,_3L);});}}}else{return new F(function(){return _3i(1,new T4(0,1,E(_3M),E(_0),E(_0)),_3K);});}}}else{return new F(function(){return _3i(1,new T4(0,1,E(_3M),E(_0),E(_0)),_3K);});}}}else{return new F(function(){return _3i(1,new T4(0,1,E(_3M),E(_0),E(_0)),_3K);});}}}},_3Y=function(_3Z,_40,_41,_42,_43){var _44=E(_3Z);if(_44==1){var _45=E(_43);if(!_45._){return new T3(0,new T4(0,1,E(new T3(0,_40,_41,_42)),E(_0),E(_0)),_1M,_1M);}else{var _46=E(_40),_47=E(_45.a),_48=E(_47.a);if(_46>=_48){if(_46!=_48){return new T3(0,new T4(0,1,E(new T3(0,_46,_41,_42)),E(_0),E(_0)),_1M,_45);}else{var _49=E(_47.b);return (_41>=_49)?(_41!=_49)?new T3(0,new T4(0,1,E(new T3(0,_46,_41,_42)),E(_0),E(_0)),_1M,_45):(_42<E(_47.c))?new T3(0,new T4(0,1,E(new T3(0,_46,_41,_42)),E(_0),E(_0)),_45,_1M):new T3(0,new T4(0,1,E(new T3(0,_46,_41,_42)),E(_0),E(_0)),_1M,_45):new T3(0,new T4(0,1,E(new T3(0,_46,_41,_42)),E(_0),E(_0)),_45,_1M);}}else{return new T3(0,new T4(0,1,E(new T3(0,_46,_41,_42)),E(_0),E(_0)),_45,_1M);}}}else{var _4a=B(_3Y(_44>>1,_40,_41,_42,_43)),_4b=_4a.a,_4c=_4a.c,_4d=E(_4a.b);if(!_4d._){return new T3(0,_4b,_1M,_4c);}else{var _4e=_4d.a,_4f=E(_4d.b);if(!_4f._){return new T3(0,new T(function(){return B(_1P(_4e,_4b));}),_1M,_4c);}else{var _4g=_4f.b,_4h=E(_4e),_4i=E(_4h.a),_4j=E(_4f.a),_4k=_4j.b,_4l=_4j.c,_4m=E(_4j.a);if(_4i>=_4m){if(_4i!=_4m){return new T3(0,_4b,_1M,_4d);}else{var _4n=E(_4h.b),_4o=E(_4k);if(_4n>=_4o){if(_4n!=_4o){return new T3(0,_4b,_1M,_4d);}else{var _4p=E(_4l);if(E(_4h.c)<_4p){var _4q=B(_3Y(_44>>1,_4m,_4o,_4p,_4g));return new T3(0,new T(function(){return B(_2x(_4h,_4b,_4q.a));}),_4q.b,_4q.c);}else{return new T3(0,_4b,_1M,_4d);}}}else{var _4r=B(_4s(_44>>1,_4m,_4o,_4l,_4g));return new T3(0,new T(function(){return B(_2x(_4h,_4b,_4r.a));}),_4r.b,_4r.c);}}}else{var _4t=B(_4u(_44>>1,_4m,_4k,_4l,_4g));return new T3(0,new T(function(){return B(_2x(_4h,_4b,_4t.a));}),_4t.b,_4t.c);}}}}},_4s=function(_4v,_4w,_4x,_4y,_4z){var _4A=E(_4v);if(_4A==1){var _4B=E(_4z);if(!_4B._){return new T3(0,new T4(0,1,E(new T3(0,_4w,_4x,_4y)),E(_0),E(_0)),_1M,_1M);}else{var _4C=E(_4w),_4D=E(_4B.a),_4E=E(_4D.a);if(_4C>=_4E){if(_4C!=_4E){return new T3(0,new T4(0,1,E(new T3(0,_4C,_4x,_4y)),E(_0),E(_0)),_1M,_4B);}else{var _4F=E(_4D.b);if(_4x>=_4F){if(_4x!=_4F){return new T3(0,new T4(0,1,E(new T3(0,_4C,_4x,_4y)),E(_0),E(_0)),_1M,_4B);}else{var _4G=E(_4y);return (_4G<E(_4D.c))?new T3(0,new T4(0,1,E(new T3(0,_4C,_4x,_4G)),E(_0),E(_0)),_4B,_1M):new T3(0,new T4(0,1,E(new T3(0,_4C,_4x,_4G)),E(_0),E(_0)),_1M,_4B);}}else{return new T3(0,new T4(0,1,E(new T3(0,_4C,_4x,_4y)),E(_0),E(_0)),_4B,_1M);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_4C,_4x,_4y)),E(_0),E(_0)),_4B,_1M);}}}else{var _4H=B(_4s(_4A>>1,_4w,_4x,_4y,_4z)),_4I=_4H.a,_4J=_4H.c,_4K=E(_4H.b);if(!_4K._){return new T3(0,_4I,_1M,_4J);}else{var _4L=_4K.a,_4M=E(_4K.b);if(!_4M._){return new T3(0,new T(function(){return B(_1P(_4L,_4I));}),_1M,_4J);}else{var _4N=_4M.b,_4O=E(_4L),_4P=E(_4O.a),_4Q=E(_4M.a),_4R=_4Q.b,_4S=_4Q.c,_4T=E(_4Q.a);if(_4P>=_4T){if(_4P!=_4T){return new T3(0,_4I,_1M,_4K);}else{var _4U=E(_4O.b),_4V=E(_4R);if(_4U>=_4V){if(_4U!=_4V){return new T3(0,_4I,_1M,_4K);}else{var _4W=E(_4S);if(E(_4O.c)<_4W){var _4X=B(_3Y(_4A>>1,_4T,_4V,_4W,_4N));return new T3(0,new T(function(){return B(_2x(_4O,_4I,_4X.a));}),_4X.b,_4X.c);}else{return new T3(0,_4I,_1M,_4K);}}}else{var _4Y=B(_4s(_4A>>1,_4T,_4V,_4S,_4N));return new T3(0,new T(function(){return B(_2x(_4O,_4I,_4Y.a));}),_4Y.b,_4Y.c);}}}else{var _4Z=B(_4u(_4A>>1,_4T,_4R,_4S,_4N));return new T3(0,new T(function(){return B(_2x(_4O,_4I,_4Z.a));}),_4Z.b,_4Z.c);}}}}},_4u=function(_50,_51,_52,_53,_54){var _55=E(_50);if(_55==1){var _56=E(_54);if(!_56._){return new T3(0,new T4(0,1,E(new T3(0,_51,_52,_53)),E(_0),E(_0)),_1M,_1M);}else{var _57=E(_51),_58=E(_56.a),_59=E(_58.a);if(_57>=_59){if(_57!=_59){return new T3(0,new T4(0,1,E(new T3(0,_57,_52,_53)),E(_0),E(_0)),_1M,_56);}else{var _5a=E(_52),_5b=E(_58.b);if(_5a>=_5b){if(_5a!=_5b){return new T3(0,new T4(0,1,E(new T3(0,_57,_5a,_53)),E(_0),E(_0)),_1M,_56);}else{var _5c=E(_53);return (_5c<E(_58.c))?new T3(0,new T4(0,1,E(new T3(0,_57,_5a,_5c)),E(_0),E(_0)),_56,_1M):new T3(0,new T4(0,1,E(new T3(0,_57,_5a,_5c)),E(_0),E(_0)),_1M,_56);}}else{return new T3(0,new T4(0,1,E(new T3(0,_57,_5a,_53)),E(_0),E(_0)),_56,_1M);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_57,_52,_53)),E(_0),E(_0)),_56,_1M);}}}else{var _5d=B(_4u(_55>>1,_51,_52,_53,_54)),_5e=_5d.a,_5f=_5d.c,_5g=E(_5d.b);if(!_5g._){return new T3(0,_5e,_1M,_5f);}else{var _5h=_5g.a,_5i=E(_5g.b);if(!_5i._){return new T3(0,new T(function(){return B(_1P(_5h,_5e));}),_1M,_5f);}else{var _5j=_5i.b,_5k=E(_5h),_5l=E(_5k.a),_5m=E(_5i.a),_5n=_5m.b,_5o=_5m.c,_5p=E(_5m.a);if(_5l>=_5p){if(_5l!=_5p){return new T3(0,_5e,_1M,_5g);}else{var _5q=E(_5k.b),_5r=E(_5n);if(_5q>=_5r){if(_5q!=_5r){return new T3(0,_5e,_1M,_5g);}else{var _5s=E(_5o);if(E(_5k.c)<_5s){var _5t=B(_3Y(_55>>1,_5p,_5r,_5s,_5j));return new T3(0,new T(function(){return B(_2x(_5k,_5e,_5t.a));}),_5t.b,_5t.c);}else{return new T3(0,_5e,_1M,_5g);}}}else{var _5u=B(_4s(_55>>1,_5p,_5r,_5o,_5j));return new T3(0,new T(function(){return B(_2x(_5k,_5e,_5u.a));}),_5u.b,_5u.c);}}}else{var _5v=B(_4u(_55>>1,_5p,_5n,_5o,_5j));return new T3(0,new T(function(){return B(_2x(_5k,_5e,_5v.a));}),_5v.b,_5v.c);}}}}},_5w=function(_5x,_5y,_5z,_5A,_5B){var _5C=E(_5B);if(!_5C._){var _5D=_5C.c,_5E=_5C.d,_5F=E(_5C.b),_5G=E(_5F.a);if(_5x>=_5G){if(_5x!=_5G){return new F(function(){return _H(_5F,_5D,B(_5w(_5x,_,_5z,_5A,_5E)));});}else{var _5H=E(_5F.b);if(_5z>=_5H){if(_5z!=_5H){return new F(function(){return _H(_5F,_5D,B(_5w(_5x,_,_5z,_5A,_5E)));});}else{var _5I=E(_5F.c);if(_5A>=_5I){if(_5A!=_5I){return new F(function(){return _H(_5F,_5D,B(_5w(_5x,_,_5z,_5A,_5E)));});}else{return new T4(0,_5C.a,E(new T3(0,_5x,_5z,_5A)),E(_5D),E(_5E));}}else{return new F(function(){return _5(_5F,B(_5w(_5x,_,_5z,_5A,_5D)),_5E);});}}}else{return new F(function(){return _5(_5F,B(_5w(_5x,_,_5z,_5A,_5D)),_5E);});}}}else{return new F(function(){return _5(_5F,B(_5w(_5x,_,_5z,_5A,_5D)),_5E);});}}else{return new T4(0,1,E(new T3(0,_5x,_5z,_5A)),E(_0),E(_0));}},_5J=function(_5K,_5L,_5M,_5N,_5O){var _5P=E(_5O);if(!_5P._){var _5Q=_5P.c,_5R=_5P.d,_5S=E(_5P.b),_5T=E(_5S.a);if(_5K>=_5T){if(_5K!=_5T){return new F(function(){return _H(_5S,_5Q,B(_5J(_5K,_,_5M,_5N,_5R)));});}else{var _5U=E(_5S.b);if(_5M>=_5U){if(_5M!=_5U){return new F(function(){return _H(_5S,_5Q,B(_5J(_5K,_,_5M,_5N,_5R)));});}else{var _5V=E(_5N),_5W=E(_5S.c);if(_5V>=_5W){if(_5V!=_5W){return new F(function(){return _H(_5S,_5Q,B(_5w(_5K,_,_5M,_5V,_5R)));});}else{return new T4(0,_5P.a,E(new T3(0,_5K,_5M,_5V)),E(_5Q),E(_5R));}}else{return new F(function(){return _5(_5S,B(_5w(_5K,_,_5M,_5V,_5Q)),_5R);});}}}else{return new F(function(){return _5(_5S,B(_5J(_5K,_,_5M,_5N,_5Q)),_5R);});}}}else{return new F(function(){return _5(_5S,B(_5J(_5K,_,_5M,_5N,_5Q)),_5R);});}}else{return new T4(0,1,E(new T3(0,_5K,_5M,_5N)),E(_0),E(_0));}},_5X=function(_5Y,_5Z,_60,_61,_62){var _63=E(_62);if(!_63._){var _64=_63.c,_65=_63.d,_66=E(_63.b),_67=E(_66.a);if(_5Y>=_67){if(_5Y!=_67){return new F(function(){return _H(_66,_64,B(_5X(_5Y,_,_60,_61,_65)));});}else{var _68=E(_60),_69=E(_66.b);if(_68>=_69){if(_68!=_69){return new F(function(){return _H(_66,_64,B(_5J(_5Y,_,_68,_61,_65)));});}else{var _6a=E(_61),_6b=E(_66.c);if(_6a>=_6b){if(_6a!=_6b){return new F(function(){return _H(_66,_64,B(_5w(_5Y,_,_68,_6a,_65)));});}else{return new T4(0,_63.a,E(new T3(0,_5Y,_68,_6a)),E(_64),E(_65));}}else{return new F(function(){return _5(_66,B(_5w(_5Y,_,_68,_6a,_64)),_65);});}}}else{return new F(function(){return _5(_66,B(_5J(_5Y,_,_68,_61,_64)),_65);});}}}else{return new F(function(){return _5(_66,B(_5X(_5Y,_,_60,_61,_64)),_65);});}}else{return new T4(0,1,E(new T3(0,_5Y,_60,_61)),E(_0),E(_0));}},_6c=function(_6d,_6e,_6f,_6g){var _6h=E(_6g);if(!_6h._){var _6i=_6h.c,_6j=_6h.d,_6k=E(_6h.b),_6l=E(_6d),_6m=E(_6k.a);if(_6l>=_6m){if(_6l!=_6m){return new F(function(){return _H(_6k,_6i,B(_5X(_6l,_,_6e,_6f,_6j)));});}else{var _6n=E(_6e),_6o=E(_6k.b);if(_6n>=_6o){if(_6n!=_6o){return new F(function(){return _H(_6k,_6i,B(_5J(_6l,_,_6n,_6f,_6j)));});}else{var _6p=E(_6f),_6q=E(_6k.c);if(_6p>=_6q){if(_6p!=_6q){return new F(function(){return _H(_6k,_6i,B(_5w(_6l,_,_6n,_6p,_6j)));});}else{return new T4(0,_6h.a,E(new T3(0,_6l,_6n,_6p)),E(_6i),E(_6j));}}else{return new F(function(){return _5(_6k,B(_5w(_6l,_,_6n,_6p,_6i)),_6j);});}}}else{return new F(function(){return _5(_6k,B(_5J(_6l,_,_6n,_6f,_6i)),_6j);});}}}else{return new F(function(){return _5(_6k,B(_5X(_6l,_,_6e,_6f,_6i)),_6j);});}}else{return new T4(0,1,E(new T3(0,_6d,_6e,_6f)),E(_0),E(_0));}},_6r=function(_6s,_6t){while(1){var _6u=E(_6t);if(!_6u._){return E(_6s);}else{var _6v=E(_6u.a),_6w=B(_6c(_6v.a,_6v.b,_6v.c,_6s));_6s=_6w;_6t=_6u.b;continue;}}},_6x=function(_6y,_6z,_6A,_6B,_6C){return new F(function(){return _6r(B(_6c(_6z,_6A,_6B,_6y)),_6C);});},_6D=function(_6E,_6F,_6G){var _6H=E(_6F);return new F(function(){return _6r(B(_6c(_6H.a,_6H.b,_6H.c,_6E)),_6G);});},_6I=function(_6J,_6K,_6L){var _6M=E(_6L);if(!_6M._){return E(_6K);}else{var _6N=_6M.a,_6O=E(_6M.b);if(!_6O._){return new F(function(){return _1P(_6N,_6K);});}else{var _6P=E(_6N),_6Q=_6P.b,_6R=_6P.c,_6S=E(_6P.a),_6T=E(_6O.a),_6U=_6T.b,_6V=_6T.c,_6W=E(_6T.a),_6X=function(_6Y){var _6Z=B(_4u(_6J,_6W,_6U,_6V,_6O.b)),_70=_6Z.a,_71=E(_6Z.c);if(!_71._){return new F(function(){return _6I(_6J<<1,B(_2x(_6P,_6K,_70)),_6Z.b);});}else{return new F(function(){return _6D(B(_2x(_6P,_6K,_70)),_71.a,_71.b);});}};if(_6S>=_6W){if(_6S!=_6W){return new F(function(){return _6x(_6K,_6S,_6Q,_6R,_6O);});}else{var _72=E(_6Q),_73=E(_6U);if(_72>=_73){if(_72!=_73){return new F(function(){return _6x(_6K,_6S,_72,_6R,_6O);});}else{var _74=E(_6R);if(_74<E(_6V)){return new F(function(){return _6X(_);});}else{return new F(function(){return _6x(_6K,_6S,_72,_74,_6O);});}}}else{return new F(function(){return _6X(_);});}}}else{return new F(function(){return _6X(_);});}}}},_75=function(_76,_77,_78,_79,_7a,_7b){var _7c=E(_7b);if(!_7c._){return new F(function(){return _1P(new T3(0,_78,_79,_7a),_77);});}else{var _7d=E(_78),_7e=E(_7c.a),_7f=_7e.b,_7g=_7e.c,_7h=E(_7e.a),_7i=function(_7j){var _7k=B(_4u(_76,_7h,_7f,_7g,_7c.b)),_7l=_7k.a,_7m=E(_7k.c);if(!_7m._){return new F(function(){return _6I(_76<<1,B(_2x(new T3(0,_7d,_79,_7a),_77,_7l)),_7k.b);});}else{return new F(function(){return _6D(B(_2x(new T3(0,_7d,_79,_7a),_77,_7l)),_7m.a,_7m.b);});}};if(_7d>=_7h){if(_7d!=_7h){return new F(function(){return _6x(_77,_7d,_79,_7a,_7c);});}else{var _7n=E(_7f);if(_79>=_7n){if(_79!=_7n){return new F(function(){return _6x(_77,_7d,_79,_7a,_7c);});}else{var _7o=E(_7a);if(_7o<E(_7g)){return new F(function(){return _7i(_);});}else{return new F(function(){return _6x(_77,_7d,_79,_7o,_7c);});}}}else{return new F(function(){return _7i(_);});}}}else{return new F(function(){return _7i(_);});}}},_7p=function(_7q,_7r,_7s,_7t,_7u,_7v){var _7w=E(_7v);if(!_7w._){return new F(function(){return _1P(new T3(0,_7s,_7t,_7u),_7r);});}else{var _7x=E(_7s),_7y=E(_7w.a),_7z=_7y.b,_7A=_7y.c,_7B=E(_7y.a),_7C=function(_7D){var _7E=B(_4u(_7q,_7B,_7z,_7A,_7w.b)),_7F=_7E.a,_7G=E(_7E.c);if(!_7G._){return new F(function(){return _6I(_7q<<1,B(_2x(new T3(0,_7x,_7t,_7u),_7r,_7F)),_7E.b);});}else{return new F(function(){return _6D(B(_2x(new T3(0,_7x,_7t,_7u),_7r,_7F)),_7G.a,_7G.b);});}};if(_7x>=_7B){if(_7x!=_7B){return new F(function(){return _6x(_7r,_7x,_7t,_7u,_7w);});}else{var _7H=E(_7z);if(_7t>=_7H){if(_7t!=_7H){return new F(function(){return _6x(_7r,_7x,_7t,_7u,_7w);});}else{if(_7u<E(_7A)){return new F(function(){return _7C(_);});}else{return new F(function(){return _6x(_7r,_7x,_7t,_7u,_7w);});}}}else{return new F(function(){return _7C(_);});}}}else{return new F(function(){return _7C(_);});}}},_7I=function(_7J,_7K,_7L,_7M,_7N,_7O){var _7P=E(_7O);if(!_7P._){return new F(function(){return _1P(new T3(0,_7L,_7M,_7N),_7K);});}else{var _7Q=E(_7L),_7R=E(_7P.a),_7S=_7R.b,_7T=_7R.c,_7U=E(_7R.a),_7V=function(_7W){var _7X=B(_4u(_7J,_7U,_7S,_7T,_7P.b)),_7Y=_7X.a,_7Z=E(_7X.c);if(!_7Z._){return new F(function(){return _6I(_7J<<1,B(_2x(new T3(0,_7Q,_7M,_7N),_7K,_7Y)),_7X.b);});}else{return new F(function(){return _6D(B(_2x(new T3(0,_7Q,_7M,_7N),_7K,_7Y)),_7Z.a,_7Z.b);});}};if(_7Q>=_7U){if(_7Q!=_7U){return new F(function(){return _6x(_7K,_7Q,_7M,_7N,_7P);});}else{var _80=E(_7M),_81=E(_7S);if(_80>=_81){if(_80!=_81){return new F(function(){return _6x(_7K,_7Q,_80,_7N,_7P);});}else{var _82=E(_7N);if(_82<E(_7T)){return new F(function(){return _7V(_);});}else{return new F(function(){return _6x(_7K,_7Q,_80,_82,_7P);});}}}else{return new F(function(){return _7V(_);});}}}else{return new F(function(){return _7V(_);});}}},_83=function(_84){var _85=E(_84);if(!_85._){return new T0(1);}else{var _86=_85.a,_87=E(_85.b);if(!_87._){return new T4(0,1,E(_86),E(_0),E(_0));}else{var _88=_87.b,_89=E(_86),_8a=E(_89.a),_8b=E(_87.a),_8c=_8b.b,_8d=_8b.c,_8e=E(_8b.a);if(_8a>=_8e){if(_8a!=_8e){return new F(function(){return _6x(new T4(0,1,E(_89),E(_0),E(_0)),_8e,_8c,_8d,_88);});}else{var _8f=E(_89.b),_8g=E(_8c);if(_8f>=_8g){if(_8f!=_8g){return new F(function(){return _6x(new T4(0,1,E(_89),E(_0),E(_0)),_8e,_8g,_8d,_88);});}else{var _8h=E(_8d);if(E(_89.c)<_8h){return new F(function(){return _7p(1,new T4(0,1,E(_89),E(_0),E(_0)),_8e,_8g,_8h,_88);});}else{return new F(function(){return _6x(new T4(0,1,E(_89),E(_0),E(_0)),_8e,_8g,_8h,_88);});}}}else{return new F(function(){return _75(1,new T4(0,1,E(_89),E(_0),E(_0)),_8e,_8g,_8d,_88);});}}}else{return new F(function(){return _7I(1,new T4(0,1,E(_89),E(_0),E(_0)),_8e,_8c,_8d,_88);});}}}},_8i=new T0(1),_8j=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_8k=function(_8l){return new F(function(){return err(_8j);});},_8m=new T(function(){return B(_8k(_));}),_8n=function(_8o,_8p,_8q,_8r){var _8s=E(_8q);if(!_8s._){var _8t=_8s.a,_8u=E(_8r);if(!_8u._){var _8v=_8u.a,_8w=_8u.b,_8x=_8u.c;if(_8v<=(imul(3,_8t)|0)){return new T5(0,(1+_8t|0)+_8v|0,E(_8o),_8p,E(_8s),E(_8u));}else{var _8y=E(_8u.d);if(!_8y._){var _8z=_8y.a,_8A=_8y.b,_8B=_8y.c,_8C=_8y.d,_8D=E(_8u.e);if(!_8D._){var _8E=_8D.a;if(_8z>=(imul(2,_8E)|0)){var _8F=function(_8G){var _8H=E(_8o),_8I=E(_8y.e);return (_8I._==0)?new T5(0,(1+_8t|0)+_8v|0,E(_8A),_8B,E(new T5(0,(1+_8t|0)+_8G|0,E(_8H),_8p,E(_8s),E(_8C))),E(new T5(0,(1+_8E|0)+_8I.a|0,E(_8w),_8x,E(_8I),E(_8D)))):new T5(0,(1+_8t|0)+_8v|0,E(_8A),_8B,E(new T5(0,(1+_8t|0)+_8G|0,E(_8H),_8p,E(_8s),E(_8C))),E(new T5(0,1+_8E|0,E(_8w),_8x,E(_8i),E(_8D))));},_8J=E(_8C);if(!_8J._){return new F(function(){return _8F(_8J.a);});}else{return new F(function(){return _8F(0);});}}else{return new T5(0,(1+_8t|0)+_8v|0,E(_8w),_8x,E(new T5(0,(1+_8t|0)+_8z|0,E(_8o),_8p,E(_8s),E(_8y))),E(_8D));}}else{return E(_8m);}}else{return E(_8m);}}}else{return new T5(0,1+_8t|0,E(_8o),_8p,E(_8s),E(_8i));}}else{var _8K=E(_8r);if(!_8K._){var _8L=_8K.a,_8M=_8K.b,_8N=_8K.c,_8O=_8K.e,_8P=E(_8K.d);if(!_8P._){var _8Q=_8P.a,_8R=_8P.b,_8S=_8P.c,_8T=_8P.d,_8U=E(_8O);if(!_8U._){var _8V=_8U.a;if(_8Q>=(imul(2,_8V)|0)){var _8W=function(_8X){var _8Y=E(_8o),_8Z=E(_8P.e);return (_8Z._==0)?new T5(0,1+_8L|0,E(_8R),_8S,E(new T5(0,1+_8X|0,E(_8Y),_8p,E(_8i),E(_8T))),E(new T5(0,(1+_8V|0)+_8Z.a|0,E(_8M),_8N,E(_8Z),E(_8U)))):new T5(0,1+_8L|0,E(_8R),_8S,E(new T5(0,1+_8X|0,E(_8Y),_8p,E(_8i),E(_8T))),E(new T5(0,1+_8V|0,E(_8M),_8N,E(_8i),E(_8U))));},_90=E(_8T);if(!_90._){return new F(function(){return _8W(_90.a);});}else{return new F(function(){return _8W(0);});}}else{return new T5(0,1+_8L|0,E(_8M),_8N,E(new T5(0,1+_8Q|0,E(_8o),_8p,E(_8i),E(_8P))),E(_8U));}}else{return new T5(0,3,E(_8R),_8S,E(new T5(0,1,E(_8o),_8p,E(_8i),E(_8i))),E(new T5(0,1,E(_8M),_8N,E(_8i),E(_8i))));}}else{var _91=E(_8O);return (_91._==0)?new T5(0,3,E(_8M),_8N,E(new T5(0,1,E(_8o),_8p,E(_8i),E(_8i))),E(_91)):new T5(0,2,E(_8o),_8p,E(_8i),E(_8K));}}else{return new T5(0,1,E(_8o),_8p,E(_8i),E(_8i));}}},_92=function(_93,_94){return new T5(0,1,E(_93),_94,E(_8i),E(_8i));},_95=function(_96,_97,_98){var _99=E(_98);if(!_99._){return new F(function(){return _8n(_99.b,_99.c,_99.d,B(_95(_96,_97,_99.e)));});}else{return new F(function(){return _92(_96,_97);});}},_9a=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_9b=function(_9c){return new F(function(){return err(_9a);});},_9d=new T(function(){return B(_9b(_));}),_9e=function(_9f,_9g,_9h,_9i){var _9j=E(_9i);if(!_9j._){var _9k=_9j.a,_9l=E(_9h);if(!_9l._){var _9m=_9l.a,_9n=_9l.b,_9o=_9l.c;if(_9m<=(imul(3,_9k)|0)){return new T5(0,(1+_9m|0)+_9k|0,E(_9f),_9g,E(_9l),E(_9j));}else{var _9p=E(_9l.d);if(!_9p._){var _9q=_9p.a,_9r=E(_9l.e);if(!_9r._){var _9s=_9r.a,_9t=_9r.b,_9u=_9r.c,_9v=_9r.d;if(_9s>=(imul(2,_9q)|0)){var _9w=function(_9x){var _9y=E(_9r.e);return (_9y._==0)?new T5(0,(1+_9m|0)+_9k|0,E(_9t),_9u,E(new T5(0,(1+_9q|0)+_9x|0,E(_9n),_9o,E(_9p),E(_9v))),E(new T5(0,(1+_9k|0)+_9y.a|0,E(_9f),_9g,E(_9y),E(_9j)))):new T5(0,(1+_9m|0)+_9k|0,E(_9t),_9u,E(new T5(0,(1+_9q|0)+_9x|0,E(_9n),_9o,E(_9p),E(_9v))),E(new T5(0,1+_9k|0,E(_9f),_9g,E(_8i),E(_9j))));},_9z=E(_9v);if(!_9z._){return new F(function(){return _9w(_9z.a);});}else{return new F(function(){return _9w(0);});}}else{return new T5(0,(1+_9m|0)+_9k|0,E(_9n),_9o,E(_9p),E(new T5(0,(1+_9k|0)+_9s|0,E(_9f),_9g,E(_9r),E(_9j))));}}else{return E(_9d);}}else{return E(_9d);}}}else{return new T5(0,1+_9k|0,E(_9f),_9g,E(_8i),E(_9j));}}else{var _9A=E(_9h);if(!_9A._){var _9B=_9A.a,_9C=_9A.b,_9D=_9A.c,_9E=_9A.e,_9F=E(_9A.d);if(!_9F._){var _9G=_9F.a,_9H=E(_9E);if(!_9H._){var _9I=_9H.a,_9J=_9H.b,_9K=_9H.c,_9L=_9H.d;if(_9I>=(imul(2,_9G)|0)){var _9M=function(_9N){var _9O=E(_9H.e);return (_9O._==0)?new T5(0,1+_9B|0,E(_9J),_9K,E(new T5(0,(1+_9G|0)+_9N|0,E(_9C),_9D,E(_9F),E(_9L))),E(new T5(0,1+_9O.a|0,E(_9f),_9g,E(_9O),E(_8i)))):new T5(0,1+_9B|0,E(_9J),_9K,E(new T5(0,(1+_9G|0)+_9N|0,E(_9C),_9D,E(_9F),E(_9L))),E(new T5(0,1,E(_9f),_9g,E(_8i),E(_8i))));},_9P=E(_9L);if(!_9P._){return new F(function(){return _9M(_9P.a);});}else{return new F(function(){return _9M(0);});}}else{return new T5(0,1+_9B|0,E(_9C),_9D,E(_9F),E(new T5(0,1+_9I|0,E(_9f),_9g,E(_9H),E(_8i))));}}else{return new T5(0,3,E(_9C),_9D,E(_9F),E(new T5(0,1,E(_9f),_9g,E(_8i),E(_8i))));}}else{var _9Q=E(_9E);return (_9Q._==0)?new T5(0,3,E(_9Q.b),_9Q.c,E(new T5(0,1,E(_9C),_9D,E(_8i),E(_8i))),E(new T5(0,1,E(_9f),_9g,E(_8i),E(_8i)))):new T5(0,2,E(_9f),_9g,E(_9A),E(_8i));}}else{return new T5(0,1,E(_9f),_9g,E(_8i),E(_8i));}}},_9R=function(_9S,_9T,_9U){var _9V=E(_9U);if(!_9V._){return new F(function(){return _9e(_9V.b,_9V.c,B(_9R(_9S,_9T,_9V.d)),_9V.e);});}else{return new F(function(){return _92(_9S,_9T);});}},_9W=function(_9X,_9Y,_9Z,_a0,_a1,_a2,_a3){return new F(function(){return _9e(_a0,_a1,B(_9R(_9X,_9Y,_a2)),_a3);});},_a4=function(_a5,_a6,_a7,_a8,_a9,_aa,_ab,_ac){var _ad=E(_a7);if(!_ad._){var _ae=_ad.a,_af=_ad.b,_ag=_ad.c,_ah=_ad.d,_ai=_ad.e;if((imul(3,_ae)|0)>=_a8){if((imul(3,_a8)|0)>=_ae){return new T5(0,(_ae+_a8|0)+1|0,E(_a5),_a6,E(_ad),E(new T5(0,_a8,E(_a9),_aa,E(_ab),E(_ac))));}else{return new F(function(){return _8n(_af,_ag,_ah,B(_a4(_a5,_a6,_ai,_a8,_a9,_aa,_ab,_ac)));});}}else{return new F(function(){return _9e(_a9,_aa,B(_aj(_a5,_a6,_ae,_af,_ag,_ah,_ai,_ab)),_ac);});}}else{return new F(function(){return _9W(_a5,_a6,_a8,_a9,_aa,_ab,_ac);});}},_aj=function(_ak,_al,_am,_an,_ao,_ap,_aq,_ar){var _as=E(_ar);if(!_as._){var _at=_as.a,_au=_as.b,_av=_as.c,_aw=_as.d,_ax=_as.e;if((imul(3,_am)|0)>=_at){if((imul(3,_at)|0)>=_am){return new T5(0,(_am+_at|0)+1|0,E(_ak),_al,E(new T5(0,_am,E(_an),_ao,E(_ap),E(_aq))),E(_as));}else{return new F(function(){return _8n(_an,_ao,_ap,B(_a4(_ak,_al,_aq,_at,_au,_av,_aw,_ax)));});}}else{return new F(function(){return _9e(_au,_av,B(_aj(_ak,_al,_am,_an,_ao,_ap,_aq,_aw)),_ax);});}}else{return new F(function(){return _95(_ak,_al,new T5(0,_am,E(_an),_ao,E(_ap),E(_aq)));});}},_ay=function(_az,_aA,_aB,_aC){var _aD=E(_aB);if(!_aD._){var _aE=_aD.a,_aF=_aD.b,_aG=_aD.c,_aH=_aD.d,_aI=_aD.e,_aJ=E(_aC);if(!_aJ._){var _aK=_aJ.a,_aL=_aJ.b,_aM=_aJ.c,_aN=_aJ.d,_aO=_aJ.e;if((imul(3,_aE)|0)>=_aK){if((imul(3,_aK)|0)>=_aE){return new T5(0,(_aE+_aK|0)+1|0,E(_az),_aA,E(_aD),E(_aJ));}else{return new F(function(){return _8n(_aF,_aG,_aH,B(_a4(_az,_aA,_aI,_aK,_aL,_aM,_aN,_aO)));});}}else{return new F(function(){return _9e(_aL,_aM,B(_aj(_az,_aA,_aE,_aF,_aG,_aH,_aI,_aN)),_aO);});}}else{return new F(function(){return _95(_az,_aA,_aD);});}}else{return new F(function(){return _9R(_az,_aA,_aC);});}},_aP=function(_aQ,_aR,_aS,_aT,_aU){var _aV=E(_aQ);if(_aV==1){var _aW=E(_aU);if(!_aW._){return new T3(0,new T5(0,1,E(new T2(0,_aR,_aS)),_aT,E(_8i),E(_8i)),_1M,_1M);}else{var _aX=E(E(_aW.a).a),_aY=E(_aR),_aZ=E(_aX.a);return (_aY>=_aZ)?(_aY!=_aZ)?new T3(0,new T5(0,1,E(new T2(0,_aY,_aS)),_aT,E(_8i),E(_8i)),_1M,_aW):(_aS<E(_aX.b))?new T3(0,new T5(0,1,E(new T2(0,_aY,_aS)),_aT,E(_8i),E(_8i)),_aW,_1M):new T3(0,new T5(0,1,E(new T2(0,_aY,_aS)),_aT,E(_8i),E(_8i)),_1M,_aW):new T3(0,new T5(0,1,E(new T2(0,_aY,_aS)),_aT,E(_8i),E(_8i)),_aW,_1M);}}else{var _b0=B(_aP(_aV>>1,_aR,_aS,_aT,_aU)),_b1=_b0.a,_b2=_b0.c,_b3=E(_b0.b);if(!_b3._){return new T3(0,_b1,_1M,_b2);}else{var _b4=E(_b3.a),_b5=_b4.a,_b6=_b4.b,_b7=E(_b3.b);if(!_b7._){return new T3(0,new T(function(){return B(_95(_b5,_b6,_b1));}),_1M,_b2);}else{var _b8=_b7.b,_b9=E(_b7.a),_ba=_b9.b,_bb=E(_b5),_bc=E(_b9.a),_bd=_bc.b,_be=E(_bb.a),_bf=E(_bc.a);if(_be>=_bf){if(_be!=_bf){return new T3(0,_b1,_1M,_b3);}else{var _bg=E(_bd);if(E(_bb.b)<_bg){var _bh=B(_aP(_aV>>1,_bf,_bg,_ba,_b8));return new T3(0,new T(function(){return B(_ay(_bb,_b6,_b1,_bh.a));}),_bh.b,_bh.c);}else{return new T3(0,_b1,_1M,_b3);}}}else{var _bi=B(_bj(_aV>>1,_bf,_bd,_ba,_b8));return new T3(0,new T(function(){return B(_ay(_bb,_b6,_b1,_bi.a));}),_bi.b,_bi.c);}}}}},_bj=function(_bk,_bl,_bm,_bn,_bo){var _bp=E(_bk);if(_bp==1){var _bq=E(_bo);if(!_bq._){return new T3(0,new T5(0,1,E(new T2(0,_bl,_bm)),_bn,E(_8i),E(_8i)),_1M,_1M);}else{var _br=E(E(_bq.a).a),_bs=E(_bl),_bt=E(_br.a);if(_bs>=_bt){if(_bs!=_bt){return new T3(0,new T5(0,1,E(new T2(0,_bs,_bm)),_bn,E(_8i),E(_8i)),_1M,_bq);}else{var _bu=E(_bm);return (_bu<E(_br.b))?new T3(0,new T5(0,1,E(new T2(0,_bs,_bu)),_bn,E(_8i),E(_8i)),_bq,_1M):new T3(0,new T5(0,1,E(new T2(0,_bs,_bu)),_bn,E(_8i),E(_8i)),_1M,_bq);}}else{return new T3(0,new T5(0,1,E(new T2(0,_bs,_bm)),_bn,E(_8i),E(_8i)),_bq,_1M);}}}else{var _bv=B(_bj(_bp>>1,_bl,_bm,_bn,_bo)),_bw=_bv.a,_bx=_bv.c,_by=E(_bv.b);if(!_by._){return new T3(0,_bw,_1M,_bx);}else{var _bz=E(_by.a),_bA=_bz.a,_bB=_bz.b,_bC=E(_by.b);if(!_bC._){return new T3(0,new T(function(){return B(_95(_bA,_bB,_bw));}),_1M,_bx);}else{var _bD=_bC.b,_bE=E(_bC.a),_bF=_bE.b,_bG=E(_bA),_bH=E(_bE.a),_bI=_bH.b,_bJ=E(_bG.a),_bK=E(_bH.a);if(_bJ>=_bK){if(_bJ!=_bK){return new T3(0,_bw,_1M,_by);}else{var _bL=E(_bI);if(E(_bG.b)<_bL){var _bM=B(_aP(_bp>>1,_bK,_bL,_bF,_bD));return new T3(0,new T(function(){return B(_ay(_bG,_bB,_bw,_bM.a));}),_bM.b,_bM.c);}else{return new T3(0,_bw,_1M,_by);}}}else{var _bN=B(_bj(_bp>>1,_bK,_bI,_bF,_bD));return new T3(0,new T(function(){return B(_ay(_bG,_bB,_bw,_bN.a));}),_bN.b,_bN.c);}}}}},_bO=function(_bP,_bQ,_bR,_bS,_bT){var _bU=E(_bT);if(!_bU._){var _bV=_bU.c,_bW=_bU.d,_bX=_bU.e,_bY=E(_bU.b),_bZ=E(_bY.a);if(_bP>=_bZ){if(_bP!=_bZ){return new F(function(){return _8n(_bY,_bV,_bW,B(_bO(_bP,_,_bR,_bS,_bX)));});}else{var _c0=E(_bY.b);if(_bR>=_c0){if(_bR!=_c0){return new F(function(){return _8n(_bY,_bV,_bW,B(_bO(_bP,_,_bR,_bS,_bX)));});}else{return new T5(0,_bU.a,E(new T2(0,_bP,_bR)),_bS,E(_bW),E(_bX));}}else{return new F(function(){return _9e(_bY,_bV,B(_bO(_bP,_,_bR,_bS,_bW)),_bX);});}}}else{return new F(function(){return _9e(_bY,_bV,B(_bO(_bP,_,_bR,_bS,_bW)),_bX);});}}else{return new T5(0,1,E(new T2(0,_bP,_bR)),_bS,E(_8i),E(_8i));}},_c1=function(_c2,_c3,_c4,_c5,_c6){var _c7=E(_c6);if(!_c7._){var _c8=_c7.c,_c9=_c7.d,_ca=_c7.e,_cb=E(_c7.b),_cc=E(_cb.a);if(_c2>=_cc){if(_c2!=_cc){return new F(function(){return _8n(_cb,_c8,_c9,B(_c1(_c2,_,_c4,_c5,_ca)));});}else{var _cd=E(_c4),_ce=E(_cb.b);if(_cd>=_ce){if(_cd!=_ce){return new F(function(){return _8n(_cb,_c8,_c9,B(_bO(_c2,_,_cd,_c5,_ca)));});}else{return new T5(0,_c7.a,E(new T2(0,_c2,_cd)),_c5,E(_c9),E(_ca));}}else{return new F(function(){return _9e(_cb,_c8,B(_bO(_c2,_,_cd,_c5,_c9)),_ca);});}}}else{return new F(function(){return _9e(_cb,_c8,B(_c1(_c2,_,_c4,_c5,_c9)),_ca);});}}else{return new T5(0,1,E(new T2(0,_c2,_c4)),_c5,E(_8i),E(_8i));}},_cf=function(_cg,_ch,_ci,_cj){var _ck=E(_cj);if(!_ck._){var _cl=_ck.c,_cm=_ck.d,_cn=_ck.e,_co=E(_ck.b),_cp=E(_cg),_cq=E(_co.a);if(_cp>=_cq){if(_cp!=_cq){return new F(function(){return _8n(_co,_cl,_cm,B(_c1(_cp,_,_ch,_ci,_cn)));});}else{var _cr=E(_ch),_cs=E(_co.b);if(_cr>=_cs){if(_cr!=_cs){return new F(function(){return _8n(_co,_cl,_cm,B(_bO(_cp,_,_cr,_ci,_cn)));});}else{return new T5(0,_ck.a,E(new T2(0,_cp,_cr)),_ci,E(_cm),E(_cn));}}else{return new F(function(){return _9e(_co,_cl,B(_bO(_cp,_,_cr,_ci,_cm)),_cn);});}}}else{return new F(function(){return _9e(_co,_cl,B(_c1(_cp,_,_ch,_ci,_cm)),_cn);});}}else{return new T5(0,1,E(new T2(0,_cg,_ch)),_ci,E(_8i),E(_8i));}},_ct=function(_cu,_cv){while(1){var _cw=E(_cv);if(!_cw._){return E(_cu);}else{var _cx=E(_cw.a),_cy=E(_cx.a),_cz=B(_cf(_cy.a,_cy.b,_cx.b,_cu));_cu=_cz;_cv=_cw.b;continue;}}},_cA=function(_cB,_cC,_cD,_cE,_cF){return new F(function(){return _ct(B(_cf(_cC,_cD,_cE,_cB)),_cF);});},_cG=function(_cH,_cI,_cJ){var _cK=E(_cI),_cL=E(_cK.a);return new F(function(){return _ct(B(_cf(_cL.a,_cL.b,_cK.b,_cH)),_cJ);});},_cM=function(_cN,_cO,_cP){var _cQ=E(_cP);if(!_cQ._){return E(_cO);}else{var _cR=E(_cQ.a),_cS=_cR.a,_cT=_cR.b,_cU=E(_cQ.b);if(!_cU._){return new F(function(){return _95(_cS,_cT,_cO);});}else{var _cV=E(_cU.a),_cW=E(_cS),_cX=_cW.b,_cY=E(_cV.a),_cZ=_cY.b,_d0=E(_cW.a),_d1=E(_cY.a),_d2=function(_d3){var _d4=B(_bj(_cN,_d1,_cZ,_cV.b,_cU.b)),_d5=_d4.a,_d6=E(_d4.c);if(!_d6._){return new F(function(){return _cM(_cN<<1,B(_ay(_cW,_cT,_cO,_d5)),_d4.b);});}else{return new F(function(){return _cG(B(_ay(_cW,_cT,_cO,_d5)),_d6.a,_d6.b);});}};if(_d0>=_d1){if(_d0!=_d1){return new F(function(){return _cA(_cO,_d0,_cX,_cT,_cU);});}else{var _d7=E(_cX);if(_d7<E(_cZ)){return new F(function(){return _d2(_);});}else{return new F(function(){return _cA(_cO,_d0,_d7,_cT,_cU);});}}}else{return new F(function(){return _d2(_);});}}}},_d8=function(_d9,_da,_db,_dc,_dd,_de){var _df=E(_de);if(!_df._){return new F(function(){return _95(new T2(0,_db,_dc),_dd,_da);});}else{var _dg=E(_df.a),_dh=E(_dg.a),_di=_dh.b,_dj=E(_db),_dk=E(_dh.a),_dl=function(_dm){var _dn=B(_bj(_d9,_dk,_di,_dg.b,_df.b)),_do=_dn.a,_dp=E(_dn.c);if(!_dp._){return new F(function(){return _cM(_d9<<1,B(_ay(new T2(0,_dj,_dc),_dd,_da,_do)),_dn.b);});}else{return new F(function(){return _cG(B(_ay(new T2(0,_dj,_dc),_dd,_da,_do)),_dp.a,_dp.b);});}};if(_dj>=_dk){if(_dj!=_dk){return new F(function(){return _cA(_da,_dj,_dc,_dd,_df);});}else{if(_dc<E(_di)){return new F(function(){return _dl(_);});}else{return new F(function(){return _cA(_da,_dj,_dc,_dd,_df);});}}}else{return new F(function(){return _dl(_);});}}},_dq=function(_dr,_ds,_dt,_du,_dv,_dw){var _dx=E(_dw);if(!_dx._){return new F(function(){return _95(new T2(0,_dt,_du),_dv,_ds);});}else{var _dy=E(_dx.a),_dz=E(_dy.a),_dA=_dz.b,_dB=E(_dt),_dC=E(_dz.a),_dD=function(_dE){var _dF=B(_bj(_dr,_dC,_dA,_dy.b,_dx.b)),_dG=_dF.a,_dH=E(_dF.c);if(!_dH._){return new F(function(){return _cM(_dr<<1,B(_ay(new T2(0,_dB,_du),_dv,_ds,_dG)),_dF.b);});}else{return new F(function(){return _cG(B(_ay(new T2(0,_dB,_du),_dv,_ds,_dG)),_dH.a,_dH.b);});}};if(_dB>=_dC){if(_dB!=_dC){return new F(function(){return _cA(_ds,_dB,_du,_dv,_dx);});}else{var _dI=E(_du);if(_dI<E(_dA)){return new F(function(){return _dD(_);});}else{return new F(function(){return _cA(_ds,_dB,_dI,_dv,_dx);});}}}else{return new F(function(){return _dD(_);});}}},_dJ=function(_dK){var _dL=E(_dK);if(!_dL._){return new T0(1);}else{var _dM=E(_dL.a),_dN=_dM.a,_dO=_dM.b,_dP=E(_dL.b);if(!_dP._){return new T5(0,1,E(_dN),_dO,E(_8i),E(_8i));}else{var _dQ=_dP.b,_dR=E(_dP.a),_dS=_dR.b,_dT=E(_dN),_dU=E(_dR.a),_dV=_dU.b,_dW=E(_dT.a),_dX=E(_dU.a);if(_dW>=_dX){if(_dW!=_dX){return new F(function(){return _cA(new T5(0,1,E(_dT),_dO,E(_8i),E(_8i)),_dX,_dV,_dS,_dQ);});}else{var _dY=E(_dV);if(E(_dT.b)<_dY){return new F(function(){return _d8(1,new T5(0,1,E(_dT),_dO,E(_8i),E(_8i)),_dX,_dY,_dS,_dQ);});}else{return new F(function(){return _cA(new T5(0,1,E(_dT),_dO,E(_8i),E(_8i)),_dX,_dY,_dS,_dQ);});}}}else{return new F(function(){return _dq(1,new T5(0,1,E(_dT),_dO,E(_8i),E(_8i)),_dX,_dV,_dS,_dQ);});}}}},_dZ=function(_e0,_e1,_e2,_e3,_e4){var _e5=E(_e0);if(_e5==1){var _e6=E(_e4);if(!_e6._){return new T3(0,new T5(0,1,E(new T2(0,_e1,_e2)),_e3,E(_8i),E(_8i)),_1M,_1M);}else{var _e7=E(E(_e6.a).a),_e8=E(_e1),_e9=E(_e7.a);return (_e8>=_e9)?(_e8!=_e9)?new T3(0,new T5(0,1,E(new T2(0,_e8,_e2)),_e3,E(_8i),E(_8i)),_1M,_e6):(_e2<E(_e7.b))?new T3(0,new T5(0,1,E(new T2(0,_e8,_e2)),_e3,E(_8i),E(_8i)),_e6,_1M):new T3(0,new T5(0,1,E(new T2(0,_e8,_e2)),_e3,E(_8i),E(_8i)),_1M,_e6):new T3(0,new T5(0,1,E(new T2(0,_e8,_e2)),_e3,E(_8i),E(_8i)),_e6,_1M);}}else{var _ea=B(_dZ(_e5>>1,_e1,_e2,_e3,_e4)),_eb=_ea.a,_ec=_ea.c,_ed=E(_ea.b);if(!_ed._){return new T3(0,_eb,_1M,_ec);}else{var _ee=E(_ed.a),_ef=_ee.a,_eg=_ee.b,_eh=E(_ed.b);if(!_eh._){return new T3(0,new T(function(){return B(_95(_ef,_eg,_eb));}),_1M,_ec);}else{var _ei=_eh.b,_ej=E(_eh.a),_ek=_ej.b,_el=E(_ef),_em=E(_ej.a),_en=_em.b,_eo=E(_el.a),_ep=E(_em.a);if(_eo>=_ep){if(_eo!=_ep){return new T3(0,_eb,_1M,_ed);}else{var _eq=E(_en);if(E(_el.b)<_eq){var _er=B(_dZ(_e5>>1,_ep,_eq,_ek,_ei));return new T3(0,new T(function(){return B(_ay(_el,_eg,_eb,_er.a));}),_er.b,_er.c);}else{return new T3(0,_eb,_1M,_ed);}}}else{var _es=B(_et(_e5>>1,_ep,_en,_ek,_ei));return new T3(0,new T(function(){return B(_ay(_el,_eg,_eb,_es.a));}),_es.b,_es.c);}}}}},_et=function(_eu,_ev,_ew,_ex,_ey){var _ez=E(_eu);if(_ez==1){var _eA=E(_ey);if(!_eA._){return new T3(0,new T5(0,1,E(new T2(0,_ev,_ew)),_ex,E(_8i),E(_8i)),_1M,_1M);}else{var _eB=E(E(_eA.a).a),_eC=E(_ev),_eD=E(_eB.a);if(_eC>=_eD){if(_eC!=_eD){return new T3(0,new T5(0,1,E(new T2(0,_eC,_ew)),_ex,E(_8i),E(_8i)),_1M,_eA);}else{var _eE=E(_ew);return (_eE<E(_eB.b))?new T3(0,new T5(0,1,E(new T2(0,_eC,_eE)),_ex,E(_8i),E(_8i)),_eA,_1M):new T3(0,new T5(0,1,E(new T2(0,_eC,_eE)),_ex,E(_8i),E(_8i)),_1M,_eA);}}else{return new T3(0,new T5(0,1,E(new T2(0,_eC,_ew)),_ex,E(_8i),E(_8i)),_eA,_1M);}}}else{var _eF=B(_et(_ez>>1,_ev,_ew,_ex,_ey)),_eG=_eF.a,_eH=_eF.c,_eI=E(_eF.b);if(!_eI._){return new T3(0,_eG,_1M,_eH);}else{var _eJ=E(_eI.a),_eK=_eJ.a,_eL=_eJ.b,_eM=E(_eI.b);if(!_eM._){return new T3(0,new T(function(){return B(_95(_eK,_eL,_eG));}),_1M,_eH);}else{var _eN=_eM.b,_eO=E(_eM.a),_eP=_eO.b,_eQ=E(_eK),_eR=E(_eO.a),_eS=_eR.b,_eT=E(_eQ.a),_eU=E(_eR.a);if(_eT>=_eU){if(_eT!=_eU){return new T3(0,_eG,_1M,_eI);}else{var _eV=E(_eS);if(E(_eQ.b)<_eV){var _eW=B(_dZ(_ez>>1,_eU,_eV,_eP,_eN));return new T3(0,new T(function(){return B(_ay(_eQ,_eL,_eG,_eW.a));}),_eW.b,_eW.c);}else{return new T3(0,_eG,_1M,_eI);}}}else{var _eX=B(_et(_ez>>1,_eU,_eS,_eP,_eN));return new T3(0,new T(function(){return B(_ay(_eQ,_eL,_eG,_eX.a));}),_eX.b,_eX.c);}}}}},_eY=function(_eZ,_f0,_f1,_f2,_f3){var _f4=E(_f3);if(!_f4._){var _f5=_f4.c,_f6=_f4.d,_f7=_f4.e,_f8=E(_f4.b),_f9=E(_f8.a);if(_eZ>=_f9){if(_eZ!=_f9){return new F(function(){return _8n(_f8,_f5,_f6,B(_eY(_eZ,_,_f1,_f2,_f7)));});}else{var _fa=E(_f8.b);if(_f1>=_fa){if(_f1!=_fa){return new F(function(){return _8n(_f8,_f5,_f6,B(_eY(_eZ,_,_f1,_f2,_f7)));});}else{return new T5(0,_f4.a,E(new T2(0,_eZ,_f1)),_f2,E(_f6),E(_f7));}}else{return new F(function(){return _9e(_f8,_f5,B(_eY(_eZ,_,_f1,_f2,_f6)),_f7);});}}}else{return new F(function(){return _9e(_f8,_f5,B(_eY(_eZ,_,_f1,_f2,_f6)),_f7);});}}else{return new T5(0,1,E(new T2(0,_eZ,_f1)),_f2,E(_8i),E(_8i));}},_fb=function(_fc,_fd,_fe,_ff,_fg){var _fh=E(_fg);if(!_fh._){var _fi=_fh.c,_fj=_fh.d,_fk=_fh.e,_fl=E(_fh.b),_fm=E(_fl.a);if(_fc>=_fm){if(_fc!=_fm){return new F(function(){return _8n(_fl,_fi,_fj,B(_fb(_fc,_,_fe,_ff,_fk)));});}else{var _fn=E(_fe),_fo=E(_fl.b);if(_fn>=_fo){if(_fn!=_fo){return new F(function(){return _8n(_fl,_fi,_fj,B(_eY(_fc,_,_fn,_ff,_fk)));});}else{return new T5(0,_fh.a,E(new T2(0,_fc,_fn)),_ff,E(_fj),E(_fk));}}else{return new F(function(){return _9e(_fl,_fi,B(_eY(_fc,_,_fn,_ff,_fj)),_fk);});}}}else{return new F(function(){return _9e(_fl,_fi,B(_fb(_fc,_,_fe,_ff,_fj)),_fk);});}}else{return new T5(0,1,E(new T2(0,_fc,_fe)),_ff,E(_8i),E(_8i));}},_fp=function(_fq,_fr,_fs,_ft){var _fu=E(_ft);if(!_fu._){var _fv=_fu.c,_fw=_fu.d,_fx=_fu.e,_fy=E(_fu.b),_fz=E(_fq),_fA=E(_fy.a);if(_fz>=_fA){if(_fz!=_fA){return new F(function(){return _8n(_fy,_fv,_fw,B(_fb(_fz,_,_fr,_fs,_fx)));});}else{var _fB=E(_fr),_fC=E(_fy.b);if(_fB>=_fC){if(_fB!=_fC){return new F(function(){return _8n(_fy,_fv,_fw,B(_eY(_fz,_,_fB,_fs,_fx)));});}else{return new T5(0,_fu.a,E(new T2(0,_fz,_fB)),_fs,E(_fw),E(_fx));}}else{return new F(function(){return _9e(_fy,_fv,B(_eY(_fz,_,_fB,_fs,_fw)),_fx);});}}}else{return new F(function(){return _9e(_fy,_fv,B(_fb(_fz,_,_fr,_fs,_fw)),_fx);});}}else{return new T5(0,1,E(new T2(0,_fq,_fr)),_fs,E(_8i),E(_8i));}},_fD=function(_fE,_fF){while(1){var _fG=E(_fF);if(!_fG._){return E(_fE);}else{var _fH=E(_fG.a),_fI=E(_fH.a),_fJ=B(_fp(_fI.a,_fI.b,_fH.b,_fE));_fE=_fJ;_fF=_fG.b;continue;}}},_fK=function(_fL,_fM,_fN,_fO,_fP){return new F(function(){return _fD(B(_fp(_fM,_fN,_fO,_fL)),_fP);});},_fQ=function(_fR,_fS,_fT){var _fU=E(_fS),_fV=E(_fU.a);return new F(function(){return _fD(B(_fp(_fV.a,_fV.b,_fU.b,_fR)),_fT);});},_fW=function(_fX,_fY,_fZ){var _g0=E(_fZ);if(!_g0._){return E(_fY);}else{var _g1=E(_g0.a),_g2=_g1.a,_g3=_g1.b,_g4=E(_g0.b);if(!_g4._){return new F(function(){return _95(_g2,_g3,_fY);});}else{var _g5=E(_g4.a),_g6=E(_g2),_g7=_g6.b,_g8=E(_g5.a),_g9=_g8.b,_ga=E(_g6.a),_gb=E(_g8.a),_gc=function(_gd){var _ge=B(_et(_fX,_gb,_g9,_g5.b,_g4.b)),_gf=_ge.a,_gg=E(_ge.c);if(!_gg._){return new F(function(){return _fW(_fX<<1,B(_ay(_g6,_g3,_fY,_gf)),_ge.b);});}else{return new F(function(){return _fQ(B(_ay(_g6,_g3,_fY,_gf)),_gg.a,_gg.b);});}};if(_ga>=_gb){if(_ga!=_gb){return new F(function(){return _fK(_fY,_ga,_g7,_g3,_g4);});}else{var _gh=E(_g7);if(_gh<E(_g9)){return new F(function(){return _gc(_);});}else{return new F(function(){return _fK(_fY,_ga,_gh,_g3,_g4);});}}}else{return new F(function(){return _gc(_);});}}}},_gi=function(_gj,_gk,_gl,_gm,_gn,_go){var _gp=E(_go);if(!_gp._){return new F(function(){return _95(new T2(0,_gl,_gm),_gn,_gk);});}else{var _gq=E(_gp.a),_gr=E(_gq.a),_gs=_gr.b,_gt=E(_gl),_gu=E(_gr.a),_gv=function(_gw){var _gx=B(_et(_gj,_gu,_gs,_gq.b,_gp.b)),_gy=_gx.a,_gz=E(_gx.c);if(!_gz._){return new F(function(){return _fW(_gj<<1,B(_ay(new T2(0,_gt,_gm),_gn,_gk,_gy)),_gx.b);});}else{return new F(function(){return _fQ(B(_ay(new T2(0,_gt,_gm),_gn,_gk,_gy)),_gz.a,_gz.b);});}};if(_gt>=_gu){if(_gt!=_gu){return new F(function(){return _fK(_gk,_gt,_gm,_gn,_gp);});}else{var _gA=E(_gm);if(_gA<E(_gs)){return new F(function(){return _gv(_);});}else{return new F(function(){return _fK(_gk,_gt,_gA,_gn,_gp);});}}}else{return new F(function(){return _gv(_);});}}},_gB=function(_gC,_gD,_gE,_gF,_gG,_gH){var _gI=E(_gH);if(!_gI._){return new F(function(){return _95(new T2(0,_gE,_gF),_gG,_gD);});}else{var _gJ=E(_gI.a),_gK=E(_gJ.a),_gL=_gK.b,_gM=E(_gE),_gN=E(_gK.a),_gO=function(_gP){var _gQ=B(_et(_gC,_gN,_gL,_gJ.b,_gI.b)),_gR=_gQ.a,_gS=E(_gQ.c);if(!_gS._){return new F(function(){return _fW(_gC<<1,B(_ay(new T2(0,_gM,_gF),_gG,_gD,_gR)),_gQ.b);});}else{return new F(function(){return _fQ(B(_ay(new T2(0,_gM,_gF),_gG,_gD,_gR)),_gS.a,_gS.b);});}};if(_gM>=_gN){if(_gM!=_gN){return new F(function(){return _fK(_gD,_gM,_gF,_gG,_gI);});}else{if(_gF<E(_gL)){return new F(function(){return _gO(_);});}else{return new F(function(){return _fK(_gD,_gM,_gF,_gG,_gI);});}}}else{return new F(function(){return _gO(_);});}}},_gT=function(_gU){var _gV=E(_gU);if(!_gV._){return new T0(1);}else{var _gW=E(_gV.a),_gX=_gW.a,_gY=_gW.b,_gZ=E(_gV.b);if(!_gZ._){return new T5(0,1,E(_gX),_gY,E(_8i),E(_8i));}else{var _h0=_gZ.b,_h1=E(_gZ.a),_h2=_h1.b,_h3=E(_gX),_h4=E(_h1.a),_h5=_h4.b,_h6=E(_h3.a),_h7=E(_h4.a);if(_h6>=_h7){if(_h6!=_h7){return new F(function(){return _fK(new T5(0,1,E(_h3),_gY,E(_8i),E(_8i)),_h7,_h5,_h2,_h0);});}else{var _h8=E(_h5);if(E(_h3.b)<_h8){return new F(function(){return _gB(1,new T5(0,1,E(_h3),_gY,E(_8i),E(_8i)),_h7,_h8,_h2,_h0);});}else{return new F(function(){return _fK(new T5(0,1,E(_h3),_gY,E(_8i),E(_8i)),_h7,_h8,_h2,_h0);});}}}else{return new F(function(){return _gi(1,new T5(0,1,E(_h3),_gY,E(_8i),E(_8i)),_h7,_h5,_h2,_h0);});}}}},_h9=0,_ha=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_hb=new T(function(){return B(err(_ha));}),_hc=function(_hd,_he){while(1){var _hf=B((function(_hg,_hh){var _hi=E(_hh);if(!_hi._){_hd=new T2(1,new T2(0,_hi.b,_hi.c),new T(function(){return B(_hc(_hg,_hi.e));}));_he=_hi.d;return __continue;}else{return E(_hg);}})(_hd,_he));if(_hf!=__continue){return _hf;}}},_hj=44,_hk=function(_hl,_hm,_hn){return new F(function(){return A1(_hl,new T2(1,_hj,new T(function(){return B(A1(_hm,_hn));})));});},_ho=new T(function(){return B(unCStr("CC "));}),_hp=new T(function(){return B(unCStr("IdentCC "));}),_hq=function(_hr,_hs){var _ht=E(_hr);return (_ht._==0)?E(_hs):new T2(1,_ht.a,new T(function(){return B(_hq(_ht.b,_hs));}));},_hu=function(_hv,_hw){var _hx=jsShowI(_hv);return new F(function(){return _hq(fromJSStr(_hx),_hw);});},_hy=41,_hz=40,_hA=function(_hB,_hC,_hD){if(_hC>=0){return new F(function(){return _hu(_hC,_hD);});}else{if(_hB<=6){return new F(function(){return _hu(_hC,_hD);});}else{return new T2(1,_hz,new T(function(){var _hE=jsShowI(_hC);return B(_hq(fromJSStr(_hE),new T2(1,_hy,_hD)));}));}}},_hF=function(_hG,_hH,_hI){if(_hG<11){return new F(function(){return _hq(_hp,new T(function(){return B(_hA(11,E(_hH),_hI));},1));});}else{var _hJ=new T(function(){return B(_hq(_hp,new T(function(){return B(_hA(11,E(_hH),new T2(1,_hy,_hI)));},1)));});return new T2(1,_hz,_hJ);}},_hK=32,_hL=function(_hM,_hN,_hO,_hP,_hQ,_hR){var _hS=function(_hT){var _hU=new T(function(){var _hV=new T(function(){return B(_hA(11,E(_hP),new T2(1,_hK,new T(function(){return B(_hA(11,E(_hQ),_hT));}))));});return B(_hA(11,E(_hO),new T2(1,_hK,_hV)));});return new F(function(){return _hF(11,_hN,new T2(1,_hK,_hU));});};if(_hM<11){return new F(function(){return _hq(_ho,new T(function(){return B(_hS(_hR));},1));});}else{var _hW=new T(function(){return B(_hq(_ho,new T(function(){return B(_hS(new T2(1,_hy,_hR)));},1)));});return new T2(1,_hz,_hW);}},_hX=function(_hY,_hZ){var _i0=E(_hY);return new F(function(){return _hL(0,_i0.a,_i0.b,_i0.c,_i0.d,_hZ);});},_i1=new T(function(){return B(unCStr("RC "));}),_i2=function(_i3,_i4,_i5,_i6,_i7){var _i8=function(_i9){var _ia=new T(function(){var _ib=new T(function(){return B(_hA(11,E(_i5),new T2(1,_hK,new T(function(){return B(_hA(11,E(_i6),_i9));}))));});return B(_hF(11,_i4,new T2(1,_hK,_ib)));},1);return new F(function(){return _hq(_i1,_ia);});};if(_i3<11){return new F(function(){return _i8(_i7);});}else{return new T2(1,_hz,new T(function(){return B(_i8(new T2(1,_hy,_i7)));}));}},_ic=function(_id,_ie){var _if=E(_id);return new F(function(){return _i2(0,_if.a,_if.b,_if.c,_ie);});},_ig=new T(function(){return B(unCStr("IdentPay "));}),_ih=function(_ii,_ij,_ik){if(_ii<11){return new F(function(){return _hq(_ig,new T(function(){return B(_hA(11,E(_ij),_ik));},1));});}else{var _il=new T(function(){return B(_hq(_ig,new T(function(){return B(_hA(11,E(_ij),new T2(1,_hy,_ik)));},1)));});return new T2(1,_hz,_il);}},_im=new T(function(){return B(unCStr(": empty list"));}),_in=new T(function(){return B(unCStr("Prelude."));}),_io=function(_ip){return new F(function(){return err(B(_hq(_in,new T(function(){return B(_hq(_ip,_im));},1))));});},_iq=new T(function(){return B(unCStr("foldr1"));}),_ir=new T(function(){return B(_io(_iq));}),_is=function(_it,_iu){var _iv=E(_iu);if(!_iv._){return E(_ir);}else{var _iw=_iv.a,_ix=E(_iv.b);if(!_ix._){return E(_iw);}else{return new F(function(){return A2(_it,_iw,new T(function(){return B(_is(_it,_ix));}));});}}},_iy=function(_iz,_iA,_iB){var _iC=new T(function(){var _iD=function(_iE){var _iF=E(_iz),_iG=new T(function(){return B(A3(_is,_hk,new T2(1,function(_iH){return new F(function(){return _ih(0,_iF.a,_iH);});},new T2(1,function(_iI){return new F(function(){return _hA(0,E(_iF.b),_iI);});},_1M)),new T2(1,_hy,_iE)));});return new T2(1,_hz,_iG);};return B(A3(_is,_hk,new T2(1,_iD,new T2(1,function(_iJ){return new F(function(){return _hA(0,E(_iA),_iJ);});},_1M)),new T2(1,_hy,_iB)));});return new T2(0,_hz,_iC);},_iK=function(_iL,_iM){var _iN=E(_iL),_iO=B(_iy(_iN.a,_iN.b,_iM));return new T2(1,_iO.a,_iO.b);},_iP=93,_iQ=91,_iR=function(_iS,_iT,_iU){var _iV=E(_iT);if(!_iV._){return new F(function(){return unAppCStr("[]",_iU);});}else{var _iW=new T(function(){var _iX=new T(function(){var _iY=function(_iZ){var _j0=E(_iZ);if(!_j0._){return E(new T2(1,_iP,_iU));}else{var _j1=new T(function(){return B(A2(_iS,_j0.a,new T(function(){return B(_iY(_j0.b));})));});return new T2(1,_hj,_j1);}};return B(_iY(_iV.b));});return B(A2(_iS,_iV.a,_iX));});return new T2(1,_iQ,_iW);}},_j2=function(_j3,_j4){return new F(function(){return _iR(_iK,_j3,_j4);});},_j5=new T(function(){return B(unCStr("IdentChoice "));}),_j6=function(_j7,_j8,_j9){if(_j7<11){return new F(function(){return _hq(_j5,new T(function(){return B(_hA(11,E(_j8),_j9));},1));});}else{var _ja=new T(function(){return B(_hq(_j5,new T(function(){return B(_hA(11,E(_j8),new T2(1,_hy,_j9)));},1)));});return new T2(1,_hz,_ja);}},_jb=function(_jc,_jd,_je){var _jf=new T(function(){var _jg=function(_jh){var _ji=E(_jc),_jj=new T(function(){return B(A3(_is,_hk,new T2(1,function(_jk){return new F(function(){return _j6(0,_ji.a,_jk);});},new T2(1,function(_jl){return new F(function(){return _hA(0,E(_ji.b),_jl);});},_1M)),new T2(1,_hy,_jh)));});return new T2(1,_hz,_jj);};return B(A3(_is,_hk,new T2(1,_jg,new T2(1,function(_jm){return new F(function(){return _hA(0,E(_jd),_jm);});},_1M)),new T2(1,_hy,_je)));});return new T2(0,_hz,_jf);},_jn=function(_jo,_jp){var _jq=E(_jo),_jr=B(_jb(_jq.a,_jq.b,_jp));return new T2(1,_jr.a,_jr.b);},_js=function(_jt,_ju){return new F(function(){return _iR(_jn,_jt,_ju);});},_jv=new T2(1,_hy,_1M),_jw=function(_jx,_jy){while(1){var _jz=B((function(_jA,_jB){var _jC=E(_jB);if(!_jC._){_jx=new T2(1,_jC.b,new T(function(){return B(_jw(_jA,_jC.d));}));_jy=_jC.c;return __continue;}else{return E(_jA);}})(_jx,_jy));if(_jz!=__continue){return _jz;}}},_jD=function(_jE,_jF,_jG,_jH){var _jI=new T(function(){var _jJ=new T(function(){return B(_hc(_1M,_jH));}),_jK=new T(function(){return B(_hc(_1M,_jG));}),_jL=new T(function(){return B(_jw(_1M,_jF));}),_jM=new T(function(){return B(_jw(_1M,_jE));});return B(A3(_is,_hk,new T2(1,function(_jN){return new F(function(){return _iR(_hX,_jM,_jN);});},new T2(1,function(_jO){return new F(function(){return _iR(_ic,_jL,_jO);});},new T2(1,function(_jP){return new F(function(){return _j2(_jK,_jP);});},new T2(1,function(_jQ){return new F(function(){return _js(_jJ,_jQ);});},_1M)))),_jv));});return new T2(0,_hz,_jI);},_jR=new T(function(){return B(err(_ha));}),_jS=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_jT=new T(function(){return B(err(_jS));}),_jU=new T0(2),_jV=function(_jW){return new T2(3,_jW,_jU);},_jX=new T(function(){return B(unCStr("base"));}),_jY=new T(function(){return B(unCStr("Control.Exception.Base"));}),_jZ=new T(function(){return B(unCStr("PatternMatchFail"));}),_k0=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_jX,_jY,_jZ),_k1=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_k0,_1M,_1M),_k2=function(_k3){return E(_k1);},_k4=function(_k5){return E(E(_k5).a);},_k6=function(_k7,_k8,_k9){var _ka=B(A1(_k7,_)),_kb=B(A1(_k8,_)),_kc=hs_eqWord64(_ka.a,_kb.a);if(!_kc){return __Z;}else{var _kd=hs_eqWord64(_ka.b,_kb.b);return (!_kd)?__Z:new T1(1,_k9);}},_ke=function(_kf){var _kg=E(_kf);return new F(function(){return _k6(B(_k4(_kg.a)),_k2,_kg.b);});},_kh=function(_ki){return E(E(_ki).a);},_kj=function(_kk){return new T2(0,_kl,_kk);},_km=function(_kn,_ko){return new F(function(){return _hq(E(_kn).a,_ko);});},_kp=function(_kq,_kr){return new F(function(){return _iR(_km,_kq,_kr);});},_ks=function(_kt,_ku,_kv){return new F(function(){return _hq(E(_ku).a,_kv);});},_kw=new T3(0,_ks,_kh,_kp),_kl=new T(function(){return new T5(0,_k2,_kw,_kj,_ke,_kh);}),_kx=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_ky=function(_kz){return E(E(_kz).c);},_kA=function(_kB,_kC){return new F(function(){return die(new T(function(){return B(A2(_ky,_kC,_kB));}));});},_kD=function(_kE,_kF){return new F(function(){return _kA(_kE,_kF);});},_kG=function(_kH,_kI){var _kJ=E(_kI);if(!_kJ._){return new T2(0,_1M,_1M);}else{var _kK=_kJ.a;if(!B(A1(_kH,_kK))){return new T2(0,_1M,_kJ);}else{var _kL=new T(function(){var _kM=B(_kG(_kH,_kJ.b));return new T2(0,_kM.a,_kM.b);});return new T2(0,new T2(1,_kK,new T(function(){return E(E(_kL).a);})),new T(function(){return E(E(_kL).b);}));}}},_kN=32,_kO=new T(function(){return B(unCStr("\n"));}),_kP=function(_kQ){return (E(_kQ)==124)?false:true;},_kR=function(_kS,_kT){var _kU=B(_kG(_kP,B(unCStr(_kS)))),_kV=_kU.a,_kW=function(_kX,_kY){var _kZ=new T(function(){var _l0=new T(function(){return B(_hq(_kT,new T(function(){return B(_hq(_kY,_kO));},1)));});return B(unAppCStr(": ",_l0));},1);return new F(function(){return _hq(_kX,_kZ);});},_l1=E(_kU.b);if(!_l1._){return new F(function(){return _kW(_kV,_1M);});}else{if(E(_l1.a)==124){return new F(function(){return _kW(_kV,new T2(1,_kN,_l1.b));});}else{return new F(function(){return _kW(_kV,_1M);});}}},_l2=function(_l3){return new F(function(){return _kD(new T1(0,new T(function(){return B(_kR(_l3,_kx));})),_kl);});},_l4=new T(function(){return B(_l2("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_l5=function(_l6,_l7){while(1){var _l8=B((function(_l9,_la){var _lb=E(_l9);switch(_lb._){case 0:var _lc=E(_la);if(!_lc._){return __Z;}else{_l6=B(A1(_lb.a,_lc.a));_l7=_lc.b;return __continue;}break;case 1:var _ld=B(A1(_lb.a,_la)),_le=_la;_l6=_ld;_l7=_le;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_lb.a,_la),new T(function(){return B(_l5(_lb.b,_la));}));default:return E(_lb.a);}})(_l6,_l7));if(_l8!=__continue){return _l8;}}},_lf=function(_lg,_lh){var _li=function(_lj){var _lk=E(_lh);if(_lk._==3){return new T2(3,_lk.a,new T(function(){return B(_lf(_lg,_lk.b));}));}else{var _ll=E(_lg);if(_ll._==2){return E(_lk);}else{var _lm=E(_lk);if(_lm._==2){return E(_ll);}else{var _ln=function(_lo){var _lp=E(_lm);if(_lp._==4){var _lq=function(_lr){return new T1(4,new T(function(){return B(_hq(B(_l5(_ll,_lr)),_lp.a));}));};return new T1(1,_lq);}else{var _ls=E(_ll);if(_ls._==1){var _lt=_ls.a,_lu=E(_lp);if(!_lu._){return new T1(1,function(_lv){return new F(function(){return _lf(B(A1(_lt,_lv)),_lu);});});}else{var _lw=function(_lx){return new F(function(){return _lf(B(A1(_lt,_lx)),new T(function(){return B(A1(_lu.a,_lx));}));});};return new T1(1,_lw);}}else{var _ly=E(_lp);if(!_ly._){return E(_l4);}else{var _lz=function(_lA){return new F(function(){return _lf(_ls,new T(function(){return B(A1(_ly.a,_lA));}));});};return new T1(1,_lz);}}}},_lB=E(_ll);switch(_lB._){case 1:var _lC=E(_lm);if(_lC._==4){var _lD=function(_lE){return new T1(4,new T(function(){return B(_hq(B(_l5(B(A1(_lB.a,_lE)),_lE)),_lC.a));}));};return new T1(1,_lD);}else{return new F(function(){return _ln(_);});}break;case 4:var _lF=_lB.a,_lG=E(_lm);switch(_lG._){case 0:var _lH=function(_lI){var _lJ=new T(function(){return B(_hq(_lF,new T(function(){return B(_l5(_lG,_lI));},1)));});return new T1(4,_lJ);};return new T1(1,_lH);case 1:var _lK=function(_lL){var _lM=new T(function(){return B(_hq(_lF,new T(function(){return B(_l5(B(A1(_lG.a,_lL)),_lL));},1)));});return new T1(4,_lM);};return new T1(1,_lK);default:return new T1(4,new T(function(){return B(_hq(_lF,_lG.a));}));}break;default:return new F(function(){return _ln(_);});}}}}},_lN=E(_lg);switch(_lN._){case 0:var _lO=E(_lh);if(!_lO._){var _lP=function(_lQ){return new F(function(){return _lf(B(A1(_lN.a,_lQ)),new T(function(){return B(A1(_lO.a,_lQ));}));});};return new T1(0,_lP);}else{return new F(function(){return _li(_);});}break;case 3:return new T2(3,_lN.a,new T(function(){return B(_lf(_lN.b,_lh));}));default:return new F(function(){return _li(_);});}},_lR=new T(function(){return B(unCStr("("));}),_lS=new T(function(){return B(unCStr(")"));}),_lT=function(_lU,_lV){while(1){var _lW=E(_lU);if(!_lW._){return (E(_lV)._==0)?true:false;}else{var _lX=E(_lV);if(!_lX._){return false;}else{if(E(_lW.a)!=E(_lX.a)){return false;}else{_lU=_lW.b;_lV=_lX.b;continue;}}}}},_lY=function(_lZ,_m0){return E(_lZ)!=E(_m0);},_m1=function(_m2,_m3){return E(_m2)==E(_m3);},_m4=new T2(0,_m1,_lY),_m5=function(_m6,_m7){while(1){var _m8=E(_m6);if(!_m8._){return (E(_m7)._==0)?true:false;}else{var _m9=E(_m7);if(!_m9._){return false;}else{if(E(_m8.a)!=E(_m9.a)){return false;}else{_m6=_m8.b;_m7=_m9.b;continue;}}}}},_ma=function(_mb,_mc){return (!B(_m5(_mb,_mc)))?true:false;},_md=new T2(0,_m5,_ma),_me=function(_mf,_mg){var _mh=E(_mf);switch(_mh._){case 0:return new T1(0,function(_mi){return new F(function(){return _me(B(A1(_mh.a,_mi)),_mg);});});case 1:return new T1(1,function(_mj){return new F(function(){return _me(B(A1(_mh.a,_mj)),_mg);});});case 2:return new T0(2);case 3:return new F(function(){return _lf(B(A1(_mg,_mh.a)),new T(function(){return B(_me(_mh.b,_mg));}));});break;default:var _mk=function(_ml){var _mm=E(_ml);if(!_mm._){return __Z;}else{var _mn=E(_mm.a);return new F(function(){return _hq(B(_l5(B(A1(_mg,_mn.a)),_mn.b)),new T(function(){return B(_mk(_mm.b));},1));});}},_mo=B(_mk(_mh.a));return (_mo._==0)?new T0(2):new T1(4,_mo);}},_mp=function(_mq,_mr){var _ms=E(_mq);if(!_ms){return new F(function(){return A1(_mr,_h9);});}else{var _mt=new T(function(){return B(_mp(_ms-1|0,_mr));});return new T1(0,function(_mu){return E(_mt);});}},_mv=function(_mw,_mx,_my){var _mz=new T(function(){return B(A1(_mw,_jV));}),_mA=function(_mB,_mC,_mD,_mE){while(1){var _mF=B((function(_mG,_mH,_mI,_mJ){var _mK=E(_mG);switch(_mK._){case 0:var _mL=E(_mH);if(!_mL._){return new F(function(){return A1(_mx,_mJ);});}else{var _mM=_mI+1|0,_mN=_mJ;_mB=B(A1(_mK.a,_mL.a));_mC=_mL.b;_mD=_mM;_mE=_mN;return __continue;}break;case 1:var _mO=B(A1(_mK.a,_mH)),_mP=_mH,_mM=_mI,_mN=_mJ;_mB=_mO;_mC=_mP;_mD=_mM;_mE=_mN;return __continue;case 2:return new F(function(){return A1(_mx,_mJ);});break;case 3:var _mQ=new T(function(){return B(_me(_mK,_mJ));});return new F(function(){return _mp(_mI,function(_mR){return E(_mQ);});});break;default:return new F(function(){return _me(_mK,_mJ);});}})(_mB,_mC,_mD,_mE));if(_mF!=__continue){return _mF;}}};return function(_mS){return new F(function(){return _mA(_mz,_mS,0,_my);});};},_mT=function(_mU){return new F(function(){return A1(_mU,_1M);});},_mV=function(_mW,_mX){var _mY=function(_mZ){var _n0=E(_mZ);if(!_n0._){return E(_mT);}else{var _n1=_n0.a;if(!B(A1(_mW,_n1))){return E(_mT);}else{var _n2=new T(function(){return B(_mY(_n0.b));}),_n3=function(_n4){var _n5=new T(function(){return B(A1(_n2,function(_n6){return new F(function(){return A1(_n4,new T2(1,_n1,_n6));});}));});return new T1(0,function(_n7){return E(_n5);});};return E(_n3);}}};return function(_n8){return new F(function(){return A2(_mY,_n8,_mX);});};},_n9=new T0(6),_na=function(_nb){return E(_nb);},_nc=new T(function(){return B(unCStr("valDig: Bad base"));}),_nd=new T(function(){return B(err(_nc));}),_ne=function(_nf,_ng){var _nh=function(_ni,_nj){var _nk=E(_ni);if(!_nk._){var _nl=new T(function(){return B(A1(_nj,_1M));});return function(_nm){return new F(function(){return A1(_nm,_nl);});};}else{var _nn=E(_nk.a),_no=function(_np){var _nq=new T(function(){return B(_nh(_nk.b,function(_nr){return new F(function(){return A1(_nj,new T2(1,_np,_nr));});}));}),_ns=function(_nt){var _nu=new T(function(){return B(A1(_nq,_nt));});return new T1(0,function(_nv){return E(_nu);});};return E(_ns);};switch(E(_nf)){case 8:if(48>_nn){var _nw=new T(function(){return B(A1(_nj,_1M));});return function(_nx){return new F(function(){return A1(_nx,_nw);});};}else{if(_nn>55){var _ny=new T(function(){return B(A1(_nj,_1M));});return function(_nz){return new F(function(){return A1(_nz,_ny);});};}else{return new F(function(){return _no(_nn-48|0);});}}break;case 10:if(48>_nn){var _nA=new T(function(){return B(A1(_nj,_1M));});return function(_nB){return new F(function(){return A1(_nB,_nA);});};}else{if(_nn>57){var _nC=new T(function(){return B(A1(_nj,_1M));});return function(_nD){return new F(function(){return A1(_nD,_nC);});};}else{return new F(function(){return _no(_nn-48|0);});}}break;case 16:if(48>_nn){if(97>_nn){if(65>_nn){var _nE=new T(function(){return B(A1(_nj,_1M));});return function(_nF){return new F(function(){return A1(_nF,_nE);});};}else{if(_nn>70){var _nG=new T(function(){return B(A1(_nj,_1M));});return function(_nH){return new F(function(){return A1(_nH,_nG);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{if(_nn>102){if(65>_nn){var _nI=new T(function(){return B(A1(_nj,_1M));});return function(_nJ){return new F(function(){return A1(_nJ,_nI);});};}else{if(_nn>70){var _nK=new T(function(){return B(A1(_nj,_1M));});return function(_nL){return new F(function(){return A1(_nL,_nK);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{return new F(function(){return _no((_nn-97|0)+10|0);});}}}else{if(_nn>57){if(97>_nn){if(65>_nn){var _nM=new T(function(){return B(A1(_nj,_1M));});return function(_nN){return new F(function(){return A1(_nN,_nM);});};}else{if(_nn>70){var _nO=new T(function(){return B(A1(_nj,_1M));});return function(_nP){return new F(function(){return A1(_nP,_nO);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{if(_nn>102){if(65>_nn){var _nQ=new T(function(){return B(A1(_nj,_1M));});return function(_nR){return new F(function(){return A1(_nR,_nQ);});};}else{if(_nn>70){var _nS=new T(function(){return B(A1(_nj,_1M));});return function(_nT){return new F(function(){return A1(_nT,_nS);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{return new F(function(){return _no((_nn-97|0)+10|0);});}}}else{return new F(function(){return _no(_nn-48|0);});}}break;default:return E(_nd);}}},_nU=function(_nV){var _nW=E(_nV);if(!_nW._){return new T0(2);}else{return new F(function(){return A1(_ng,_nW);});}};return function(_nX){return new F(function(){return A3(_nh,_nX,_na,_nU);});};},_nY=16,_nZ=8,_o0=function(_o1){var _o2=function(_o3){return new F(function(){return A1(_o1,new T1(5,new T2(0,_nZ,_o3)));});},_o4=function(_o5){return new F(function(){return A1(_o1,new T1(5,new T2(0,_nY,_o5)));});},_o6=function(_o7){switch(E(_o7)){case 79:return new T1(1,B(_ne(_nZ,_o2)));case 88:return new T1(1,B(_ne(_nY,_o4)));case 111:return new T1(1,B(_ne(_nZ,_o2)));case 120:return new T1(1,B(_ne(_nY,_o4)));default:return new T0(2);}};return function(_o8){return (E(_o8)==48)?E(new T1(0,_o6)):new T0(2);};},_o9=function(_oa){return new T1(0,B(_o0(_oa)));},_ob=__Z,_oc=function(_od){return new F(function(){return A1(_od,_ob);});},_oe=function(_of){return new F(function(){return A1(_of,_ob);});},_og=10,_oh=new T1(0,1),_oi=new T1(0,2147483647),_oj=function(_ok,_ol){while(1){var _om=E(_ok);if(!_om._){var _on=_om.a,_oo=E(_ol);if(!_oo._){var _op=_oo.a,_oq=addC(_on,_op);if(!E(_oq.b)){return new T1(0,_oq.a);}else{_ok=new T1(1,I_fromInt(_on));_ol=new T1(1,I_fromInt(_op));continue;}}else{_ok=new T1(1,I_fromInt(_on));_ol=_oo;continue;}}else{var _or=E(_ol);if(!_or._){_ok=_om;_ol=new T1(1,I_fromInt(_or.a));continue;}else{return new T1(1,I_add(_om.a,_or.a));}}}},_os=new T(function(){return B(_oj(_oi,_oh));}),_ot=function(_ou){var _ov=E(_ou);if(!_ov._){var _ow=E(_ov.a);return (_ow==( -2147483648))?E(_os):new T1(0, -_ow);}else{return new T1(1,I_negate(_ov.a));}},_ox=new T1(0,10),_oy=function(_oz,_oA){while(1){var _oB=E(_oz);if(!_oB._){return E(_oA);}else{var _oC=_oA+1|0;_oz=_oB.b;_oA=_oC;continue;}}},_oD=function(_oE,_oF){var _oG=E(_oF);return (_oG._==0)?__Z:new T2(1,new T(function(){return B(A1(_oE,_oG.a));}),new T(function(){return B(_oD(_oE,_oG.b));}));},_oH=function(_oI){return new T1(0,_oI);},_oJ=function(_oK){return new F(function(){return _oH(E(_oK));});},_oL=new T(function(){return B(unCStr("this should not happen"));}),_oM=new T(function(){return B(err(_oL));}),_oN=function(_oO,_oP){while(1){var _oQ=E(_oO);if(!_oQ._){var _oR=_oQ.a,_oS=E(_oP);if(!_oS._){var _oT=_oS.a;if(!(imul(_oR,_oT)|0)){return new T1(0,imul(_oR,_oT)|0);}else{_oO=new T1(1,I_fromInt(_oR));_oP=new T1(1,I_fromInt(_oT));continue;}}else{_oO=new T1(1,I_fromInt(_oR));_oP=_oS;continue;}}else{var _oU=E(_oP);if(!_oU._){_oO=_oQ;_oP=new T1(1,I_fromInt(_oU.a));continue;}else{return new T1(1,I_mul(_oQ.a,_oU.a));}}}},_oV=function(_oW,_oX){var _oY=E(_oX);if(!_oY._){return __Z;}else{var _oZ=E(_oY.b);return (_oZ._==0)?E(_oM):new T2(1,B(_oj(B(_oN(_oY.a,_oW)),_oZ.a)),new T(function(){return B(_oV(_oW,_oZ.b));}));}},_p0=new T1(0,0),_p1=function(_p2,_p3,_p4){while(1){var _p5=B((function(_p6,_p7,_p8){var _p9=E(_p8);if(!_p9._){return E(_p0);}else{if(!E(_p9.b)._){return E(_p9.a);}else{var _pa=E(_p7);if(_pa<=40){var _pb=function(_pc,_pd){while(1){var _pe=E(_pd);if(!_pe._){return E(_pc);}else{var _pf=B(_oj(B(_oN(_pc,_p6)),_pe.a));_pc=_pf;_pd=_pe.b;continue;}}};return new F(function(){return _pb(_p0,_p9);});}else{var _pg=B(_oN(_p6,_p6));if(!(_pa%2)){var _ph=B(_oV(_p6,_p9));_p2=_pg;_p3=quot(_pa+1|0,2);_p4=_ph;return __continue;}else{var _ph=B(_oV(_p6,new T2(1,_p0,_p9)));_p2=_pg;_p3=quot(_pa+1|0,2);_p4=_ph;return __continue;}}}}})(_p2,_p3,_p4));if(_p5!=__continue){return _p5;}}},_pi=function(_pj,_pk){return new F(function(){return _p1(_pj,new T(function(){return B(_oy(_pk,0));},1),B(_oD(_oJ,_pk)));});},_pl=function(_pm){var _pn=new T(function(){var _po=new T(function(){var _pp=function(_pq){return new F(function(){return A1(_pm,new T1(1,new T(function(){return B(_pi(_ox,_pq));})));});};return new T1(1,B(_ne(_og,_pp)));}),_pr=function(_ps){if(E(_ps)==43){var _pt=function(_pu){return new F(function(){return A1(_pm,new T1(1,new T(function(){return B(_pi(_ox,_pu));})));});};return new T1(1,B(_ne(_og,_pt)));}else{return new T0(2);}},_pv=function(_pw){if(E(_pw)==45){var _px=function(_py){return new F(function(){return A1(_pm,new T1(1,new T(function(){return B(_ot(B(_pi(_ox,_py))));})));});};return new T1(1,B(_ne(_og,_px)));}else{return new T0(2);}};return B(_lf(B(_lf(new T1(0,_pv),new T1(0,_pr))),_po));});return new F(function(){return _lf(new T1(0,function(_pz){return (E(_pz)==101)?E(_pn):new T0(2);}),new T1(0,function(_pA){return (E(_pA)==69)?E(_pn):new T0(2);}));});},_pB=function(_pC){var _pD=function(_pE){return new F(function(){return A1(_pC,new T1(1,_pE));});};return function(_pF){return (E(_pF)==46)?new T1(1,B(_ne(_og,_pD))):new T0(2);};},_pG=function(_pH){return new T1(0,B(_pB(_pH)));},_pI=function(_pJ){var _pK=function(_pL){var _pM=function(_pN){return new T1(1,B(_mv(_pl,_oc,function(_pO){return new F(function(){return A1(_pJ,new T1(5,new T3(1,_pL,_pN,_pO)));});})));};return new T1(1,B(_mv(_pG,_oe,_pM)));};return new F(function(){return _ne(_og,_pK);});},_pP=function(_pQ){return new T1(1,B(_pI(_pQ)));},_pR=function(_pS){return E(E(_pS).a);},_pT=function(_pU,_pV,_pW){while(1){var _pX=E(_pW);if(!_pX._){return false;}else{if(!B(A3(_pR,_pU,_pV,_pX.a))){_pW=_pX.b;continue;}else{return true;}}}},_pY=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_pZ=function(_q0){return new F(function(){return _pT(_m4,_q0,_pY);});},_q1=false,_q2=true,_q3=function(_q4){var _q5=new T(function(){return B(A1(_q4,_nZ));}),_q6=new T(function(){return B(A1(_q4,_nY));});return function(_q7){switch(E(_q7)){case 79:return E(_q5);case 88:return E(_q6);case 111:return E(_q5);case 120:return E(_q6);default:return new T0(2);}};},_q8=function(_q9){return new T1(0,B(_q3(_q9)));},_qa=function(_qb){return new F(function(){return A1(_qb,_og);});},_qc=function(_qd){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_hA(9,_qd,_1M));}))));});},_qe=function(_qf){var _qg=E(_qf);if(!_qg._){return E(_qg.a);}else{return new F(function(){return I_toInt(_qg.a);});}},_qh=function(_qi,_qj){var _qk=E(_qi);if(!_qk._){var _ql=_qk.a,_qm=E(_qj);return (_qm._==0)?_ql<=_qm.a:I_compareInt(_qm.a,_ql)>=0;}else{var _qn=_qk.a,_qo=E(_qj);return (_qo._==0)?I_compareInt(_qn,_qo.a)<=0:I_compare(_qn,_qo.a)<=0;}},_qp=function(_qq){return new T0(2);},_qr=function(_qs){var _qt=E(_qs);if(!_qt._){return E(_qp);}else{var _qu=_qt.a,_qv=E(_qt.b);if(!_qv._){return E(_qu);}else{var _qw=new T(function(){return B(_qr(_qv));}),_qx=function(_qy){return new F(function(){return _lf(B(A1(_qu,_qy)),new T(function(){return B(A1(_qw,_qy));}));});};return E(_qx);}}},_qz=function(_qA,_qB){var _qC=function(_qD,_qE,_qF){var _qG=E(_qD);if(!_qG._){return new F(function(){return A1(_qF,_qA);});}else{var _qH=E(_qE);if(!_qH._){return new T0(2);}else{if(E(_qG.a)!=E(_qH.a)){return new T0(2);}else{var _qI=new T(function(){return B(_qC(_qG.b,_qH.b,_qF));});return new T1(0,function(_qJ){return E(_qI);});}}}};return function(_qK){return new F(function(){return _qC(_qA,_qK,_qB);});};},_qL=new T(function(){return B(unCStr("SO"));}),_qM=14,_qN=function(_qO){var _qP=new T(function(){return B(A1(_qO,_qM));});return new T1(1,B(_qz(_qL,function(_qQ){return E(_qP);})));},_qR=new T(function(){return B(unCStr("SOH"));}),_qS=1,_qT=function(_qU){var _qV=new T(function(){return B(A1(_qU,_qS));});return new T1(1,B(_qz(_qR,function(_qW){return E(_qV);})));},_qX=function(_qY){return new T1(1,B(_mv(_qT,_qN,_qY)));},_qZ=new T(function(){return B(unCStr("NUL"));}),_r0=0,_r1=function(_r2){var _r3=new T(function(){return B(A1(_r2,_r0));});return new T1(1,B(_qz(_qZ,function(_r4){return E(_r3);})));},_r5=new T(function(){return B(unCStr("STX"));}),_r6=2,_r7=function(_r8){var _r9=new T(function(){return B(A1(_r8,_r6));});return new T1(1,B(_qz(_r5,function(_ra){return E(_r9);})));},_rb=new T(function(){return B(unCStr("ETX"));}),_rc=3,_rd=function(_re){var _rf=new T(function(){return B(A1(_re,_rc));});return new T1(1,B(_qz(_rb,function(_rg){return E(_rf);})));},_rh=new T(function(){return B(unCStr("EOT"));}),_ri=4,_rj=function(_rk){var _rl=new T(function(){return B(A1(_rk,_ri));});return new T1(1,B(_qz(_rh,function(_rm){return E(_rl);})));},_rn=new T(function(){return B(unCStr("ENQ"));}),_ro=5,_rp=function(_rq){var _rr=new T(function(){return B(A1(_rq,_ro));});return new T1(1,B(_qz(_rn,function(_rs){return E(_rr);})));},_rt=new T(function(){return B(unCStr("ACK"));}),_ru=6,_rv=function(_rw){var _rx=new T(function(){return B(A1(_rw,_ru));});return new T1(1,B(_qz(_rt,function(_ry){return E(_rx);})));},_rz=new T(function(){return B(unCStr("BEL"));}),_rA=7,_rB=function(_rC){var _rD=new T(function(){return B(A1(_rC,_rA));});return new T1(1,B(_qz(_rz,function(_rE){return E(_rD);})));},_rF=new T(function(){return B(unCStr("BS"));}),_rG=8,_rH=function(_rI){var _rJ=new T(function(){return B(A1(_rI,_rG));});return new T1(1,B(_qz(_rF,function(_rK){return E(_rJ);})));},_rL=new T(function(){return B(unCStr("HT"));}),_rM=9,_rN=function(_rO){var _rP=new T(function(){return B(A1(_rO,_rM));});return new T1(1,B(_qz(_rL,function(_rQ){return E(_rP);})));},_rR=new T(function(){return B(unCStr("LF"));}),_rS=10,_rT=function(_rU){var _rV=new T(function(){return B(A1(_rU,_rS));});return new T1(1,B(_qz(_rR,function(_rW){return E(_rV);})));},_rX=new T(function(){return B(unCStr("VT"));}),_rY=11,_rZ=function(_s0){var _s1=new T(function(){return B(A1(_s0,_rY));});return new T1(1,B(_qz(_rX,function(_s2){return E(_s1);})));},_s3=new T(function(){return B(unCStr("FF"));}),_s4=12,_s5=function(_s6){var _s7=new T(function(){return B(A1(_s6,_s4));});return new T1(1,B(_qz(_s3,function(_s8){return E(_s7);})));},_s9=new T(function(){return B(unCStr("CR"));}),_sa=13,_sb=function(_sc){var _sd=new T(function(){return B(A1(_sc,_sa));});return new T1(1,B(_qz(_s9,function(_se){return E(_sd);})));},_sf=new T(function(){return B(unCStr("SI"));}),_sg=15,_sh=function(_si){var _sj=new T(function(){return B(A1(_si,_sg));});return new T1(1,B(_qz(_sf,function(_sk){return E(_sj);})));},_sl=new T(function(){return B(unCStr("DLE"));}),_sm=16,_sn=function(_so){var _sp=new T(function(){return B(A1(_so,_sm));});return new T1(1,B(_qz(_sl,function(_sq){return E(_sp);})));},_sr=new T(function(){return B(unCStr("DC1"));}),_ss=17,_st=function(_su){var _sv=new T(function(){return B(A1(_su,_ss));});return new T1(1,B(_qz(_sr,function(_sw){return E(_sv);})));},_sx=new T(function(){return B(unCStr("DC2"));}),_sy=18,_sz=function(_sA){var _sB=new T(function(){return B(A1(_sA,_sy));});return new T1(1,B(_qz(_sx,function(_sC){return E(_sB);})));},_sD=new T(function(){return B(unCStr("DC3"));}),_sE=19,_sF=function(_sG){var _sH=new T(function(){return B(A1(_sG,_sE));});return new T1(1,B(_qz(_sD,function(_sI){return E(_sH);})));},_sJ=new T(function(){return B(unCStr("DC4"));}),_sK=20,_sL=function(_sM){var _sN=new T(function(){return B(A1(_sM,_sK));});return new T1(1,B(_qz(_sJ,function(_sO){return E(_sN);})));},_sP=new T(function(){return B(unCStr("NAK"));}),_sQ=21,_sR=function(_sS){var _sT=new T(function(){return B(A1(_sS,_sQ));});return new T1(1,B(_qz(_sP,function(_sU){return E(_sT);})));},_sV=new T(function(){return B(unCStr("SYN"));}),_sW=22,_sX=function(_sY){var _sZ=new T(function(){return B(A1(_sY,_sW));});return new T1(1,B(_qz(_sV,function(_t0){return E(_sZ);})));},_t1=new T(function(){return B(unCStr("ETB"));}),_t2=23,_t3=function(_t4){var _t5=new T(function(){return B(A1(_t4,_t2));});return new T1(1,B(_qz(_t1,function(_t6){return E(_t5);})));},_t7=new T(function(){return B(unCStr("CAN"));}),_t8=24,_t9=function(_ta){var _tb=new T(function(){return B(A1(_ta,_t8));});return new T1(1,B(_qz(_t7,function(_tc){return E(_tb);})));},_td=new T(function(){return B(unCStr("EM"));}),_te=25,_tf=function(_tg){var _th=new T(function(){return B(A1(_tg,_te));});return new T1(1,B(_qz(_td,function(_ti){return E(_th);})));},_tj=new T(function(){return B(unCStr("SUB"));}),_tk=26,_tl=function(_tm){var _tn=new T(function(){return B(A1(_tm,_tk));});return new T1(1,B(_qz(_tj,function(_to){return E(_tn);})));},_tp=new T(function(){return B(unCStr("ESC"));}),_tq=27,_tr=function(_ts){var _tt=new T(function(){return B(A1(_ts,_tq));});return new T1(1,B(_qz(_tp,function(_tu){return E(_tt);})));},_tv=new T(function(){return B(unCStr("FS"));}),_tw=28,_tx=function(_ty){var _tz=new T(function(){return B(A1(_ty,_tw));});return new T1(1,B(_qz(_tv,function(_tA){return E(_tz);})));},_tB=new T(function(){return B(unCStr("GS"));}),_tC=29,_tD=function(_tE){var _tF=new T(function(){return B(A1(_tE,_tC));});return new T1(1,B(_qz(_tB,function(_tG){return E(_tF);})));},_tH=new T(function(){return B(unCStr("RS"));}),_tI=30,_tJ=function(_tK){var _tL=new T(function(){return B(A1(_tK,_tI));});return new T1(1,B(_qz(_tH,function(_tM){return E(_tL);})));},_tN=new T(function(){return B(unCStr("US"));}),_tO=31,_tP=function(_tQ){var _tR=new T(function(){return B(A1(_tQ,_tO));});return new T1(1,B(_qz(_tN,function(_tS){return E(_tR);})));},_tT=new T(function(){return B(unCStr("SP"));}),_tU=32,_tV=function(_tW){var _tX=new T(function(){return B(A1(_tW,_tU));});return new T1(1,B(_qz(_tT,function(_tY){return E(_tX);})));},_tZ=new T(function(){return B(unCStr("DEL"));}),_u0=127,_u1=function(_u2){var _u3=new T(function(){return B(A1(_u2,_u0));});return new T1(1,B(_qz(_tZ,function(_u4){return E(_u3);})));},_u5=new T2(1,_u1,_1M),_u6=new T2(1,_tV,_u5),_u7=new T2(1,_tP,_u6),_u8=new T2(1,_tJ,_u7),_u9=new T2(1,_tD,_u8),_ua=new T2(1,_tx,_u9),_ub=new T2(1,_tr,_ua),_uc=new T2(1,_tl,_ub),_ud=new T2(1,_tf,_uc),_ue=new T2(1,_t9,_ud),_uf=new T2(1,_t3,_ue),_ug=new T2(1,_sX,_uf),_uh=new T2(1,_sR,_ug),_ui=new T2(1,_sL,_uh),_uj=new T2(1,_sF,_ui),_uk=new T2(1,_sz,_uj),_ul=new T2(1,_st,_uk),_um=new T2(1,_sn,_ul),_un=new T2(1,_sh,_um),_uo=new T2(1,_sb,_un),_up=new T2(1,_s5,_uo),_uq=new T2(1,_rZ,_up),_ur=new T2(1,_rT,_uq),_us=new T2(1,_rN,_ur),_ut=new T2(1,_rH,_us),_uu=new T2(1,_rB,_ut),_uv=new T2(1,_rv,_uu),_uw=new T2(1,_rp,_uv),_ux=new T2(1,_rj,_uw),_uy=new T2(1,_rd,_ux),_uz=new T2(1,_r7,_uy),_uA=new T2(1,_r1,_uz),_uB=new T2(1,_qX,_uA),_uC=new T(function(){return B(_qr(_uB));}),_uD=34,_uE=new T1(0,1114111),_uF=92,_uG=39,_uH=function(_uI){var _uJ=new T(function(){return B(A1(_uI,_rA));}),_uK=new T(function(){return B(A1(_uI,_rG));}),_uL=new T(function(){return B(A1(_uI,_rM));}),_uM=new T(function(){return B(A1(_uI,_rS));}),_uN=new T(function(){return B(A1(_uI,_rY));}),_uO=new T(function(){return B(A1(_uI,_s4));}),_uP=new T(function(){return B(A1(_uI,_sa));}),_uQ=new T(function(){return B(A1(_uI,_uF));}),_uR=new T(function(){return B(A1(_uI,_uG));}),_uS=new T(function(){return B(A1(_uI,_uD));}),_uT=new T(function(){var _uU=function(_uV){var _uW=new T(function(){return B(_oH(E(_uV)));}),_uX=function(_uY){var _uZ=B(_pi(_uW,_uY));if(!B(_qh(_uZ,_uE))){return new T0(2);}else{return new F(function(){return A1(_uI,new T(function(){var _v0=B(_qe(_uZ));if(_v0>>>0>1114111){return B(_qc(_v0));}else{return _v0;}}));});}};return new T1(1,B(_ne(_uV,_uX)));},_v1=new T(function(){var _v2=new T(function(){return B(A1(_uI,_tO));}),_v3=new T(function(){return B(A1(_uI,_tI));}),_v4=new T(function(){return B(A1(_uI,_tC));}),_v5=new T(function(){return B(A1(_uI,_tw));}),_v6=new T(function(){return B(A1(_uI,_tq));}),_v7=new T(function(){return B(A1(_uI,_tk));}),_v8=new T(function(){return B(A1(_uI,_te));}),_v9=new T(function(){return B(A1(_uI,_t8));}),_va=new T(function(){return B(A1(_uI,_t2));}),_vb=new T(function(){return B(A1(_uI,_sW));}),_vc=new T(function(){return B(A1(_uI,_sQ));}),_vd=new T(function(){return B(A1(_uI,_sK));}),_ve=new T(function(){return B(A1(_uI,_sE));}),_vf=new T(function(){return B(A1(_uI,_sy));}),_vg=new T(function(){return B(A1(_uI,_ss));}),_vh=new T(function(){return B(A1(_uI,_sm));}),_vi=new T(function(){return B(A1(_uI,_sg));}),_vj=new T(function(){return B(A1(_uI,_qM));}),_vk=new T(function(){return B(A1(_uI,_ru));}),_vl=new T(function(){return B(A1(_uI,_ro));}),_vm=new T(function(){return B(A1(_uI,_ri));}),_vn=new T(function(){return B(A1(_uI,_rc));}),_vo=new T(function(){return B(A1(_uI,_r6));}),_vp=new T(function(){return B(A1(_uI,_qS));}),_vq=new T(function(){return B(A1(_uI,_r0));}),_vr=function(_vs){switch(E(_vs)){case 64:return E(_vq);case 65:return E(_vp);case 66:return E(_vo);case 67:return E(_vn);case 68:return E(_vm);case 69:return E(_vl);case 70:return E(_vk);case 71:return E(_uJ);case 72:return E(_uK);case 73:return E(_uL);case 74:return E(_uM);case 75:return E(_uN);case 76:return E(_uO);case 77:return E(_uP);case 78:return E(_vj);case 79:return E(_vi);case 80:return E(_vh);case 81:return E(_vg);case 82:return E(_vf);case 83:return E(_ve);case 84:return E(_vd);case 85:return E(_vc);case 86:return E(_vb);case 87:return E(_va);case 88:return E(_v9);case 89:return E(_v8);case 90:return E(_v7);case 91:return E(_v6);case 92:return E(_v5);case 93:return E(_v4);case 94:return E(_v3);case 95:return E(_v2);default:return new T0(2);}};return B(_lf(new T1(0,function(_vt){return (E(_vt)==94)?E(new T1(0,_vr)):new T0(2);}),new T(function(){return B(A1(_uC,_uI));})));});return B(_lf(new T1(1,B(_mv(_q8,_qa,_uU))),_v1));});return new F(function(){return _lf(new T1(0,function(_vu){switch(E(_vu)){case 34:return E(_uS);case 39:return E(_uR);case 92:return E(_uQ);case 97:return E(_uJ);case 98:return E(_uK);case 102:return E(_uO);case 110:return E(_uM);case 114:return E(_uP);case 116:return E(_uL);case 118:return E(_uN);default:return new T0(2);}}),_uT);});},_vv=function(_vw){return new F(function(){return A1(_vw,_h9);});},_vx=function(_vy){var _vz=E(_vy);if(!_vz._){return E(_vv);}else{var _vA=E(_vz.a),_vB=_vA>>>0,_vC=new T(function(){return B(_vx(_vz.b));});if(_vB>887){var _vD=u_iswspace(_vA);if(!E(_vD)){return E(_vv);}else{var _vE=function(_vF){var _vG=new T(function(){return B(A1(_vC,_vF));});return new T1(0,function(_vH){return E(_vG);});};return E(_vE);}}else{var _vI=E(_vB);if(_vI==32){var _vJ=function(_vK){var _vL=new T(function(){return B(A1(_vC,_vK));});return new T1(0,function(_vM){return E(_vL);});};return E(_vJ);}else{if(_vI-9>>>0>4){if(E(_vI)==160){var _vN=function(_vO){var _vP=new T(function(){return B(A1(_vC,_vO));});return new T1(0,function(_vQ){return E(_vP);});};return E(_vN);}else{return E(_vv);}}else{var _vR=function(_vS){var _vT=new T(function(){return B(A1(_vC,_vS));});return new T1(0,function(_vU){return E(_vT);});};return E(_vR);}}}}},_vV=function(_vW){var _vX=new T(function(){return B(_vV(_vW));}),_vY=function(_vZ){return (E(_vZ)==92)?E(_vX):new T0(2);},_w0=function(_w1){return E(new T1(0,_vY));},_w2=new T1(1,function(_w3){return new F(function(){return A2(_vx,_w3,_w0);});}),_w4=new T(function(){return B(_uH(function(_w5){return new F(function(){return A1(_vW,new T2(0,_w5,_q2));});}));}),_w6=function(_w7){var _w8=E(_w7);if(_w8==38){return E(_vX);}else{var _w9=_w8>>>0;if(_w9>887){var _wa=u_iswspace(_w8);return (E(_wa)==0)?new T0(2):E(_w2);}else{var _wb=E(_w9);return (_wb==32)?E(_w2):(_wb-9>>>0>4)?(E(_wb)==160)?E(_w2):new T0(2):E(_w2);}}};return new F(function(){return _lf(new T1(0,function(_wc){return (E(_wc)==92)?E(new T1(0,_w6)):new T0(2);}),new T1(0,function(_wd){var _we=E(_wd);if(E(_we)==92){return E(_w4);}else{return new F(function(){return A1(_vW,new T2(0,_we,_q1));});}}));});},_wf=function(_wg,_wh){var _wi=new T(function(){return B(A1(_wh,new T1(1,new T(function(){return B(A1(_wg,_1M));}))));}),_wj=function(_wk){var _wl=E(_wk),_wm=E(_wl.a);if(E(_wm)==34){if(!E(_wl.b)){return E(_wi);}else{return new F(function(){return _wf(function(_wn){return new F(function(){return A1(_wg,new T2(1,_wm,_wn));});},_wh);});}}else{return new F(function(){return _wf(function(_wo){return new F(function(){return A1(_wg,new T2(1,_wm,_wo));});},_wh);});}};return new F(function(){return _vV(_wj);});},_wp=new T(function(){return B(unCStr("_\'"));}),_wq=function(_wr){var _ws=u_iswalnum(_wr);if(!E(_ws)){return new F(function(){return _pT(_m4,_wr,_wp);});}else{return true;}},_wt=function(_wu){return new F(function(){return _wq(E(_wu));});},_wv=new T(function(){return B(unCStr(",;()[]{}`"));}),_ww=new T(function(){return B(unCStr("=>"));}),_wx=new T2(1,_ww,_1M),_wy=new T(function(){return B(unCStr("~"));}),_wz=new T2(1,_wy,_wx),_wA=new T(function(){return B(unCStr("@"));}),_wB=new T2(1,_wA,_wz),_wC=new T(function(){return B(unCStr("->"));}),_wD=new T2(1,_wC,_wB),_wE=new T(function(){return B(unCStr("<-"));}),_wF=new T2(1,_wE,_wD),_wG=new T(function(){return B(unCStr("|"));}),_wH=new T2(1,_wG,_wF),_wI=new T(function(){return B(unCStr("\\"));}),_wJ=new T2(1,_wI,_wH),_wK=new T(function(){return B(unCStr("="));}),_wL=new T2(1,_wK,_wJ),_wM=new T(function(){return B(unCStr("::"));}),_wN=new T2(1,_wM,_wL),_wO=new T(function(){return B(unCStr(".."));}),_wP=new T2(1,_wO,_wN),_wQ=function(_wR){var _wS=new T(function(){return B(A1(_wR,_n9));}),_wT=new T(function(){var _wU=new T(function(){var _wV=function(_wW){var _wX=new T(function(){return B(A1(_wR,new T1(0,_wW)));});return new T1(0,function(_wY){return (E(_wY)==39)?E(_wX):new T0(2);});};return B(_uH(_wV));}),_wZ=function(_x0){var _x1=E(_x0);switch(E(_x1)){case 39:return new T0(2);case 92:return E(_wU);default:var _x2=new T(function(){return B(A1(_wR,new T1(0,_x1)));});return new T1(0,function(_x3){return (E(_x3)==39)?E(_x2):new T0(2);});}},_x4=new T(function(){var _x5=new T(function(){return B(_wf(_na,_wR));}),_x6=new T(function(){var _x7=new T(function(){var _x8=new T(function(){var _x9=function(_xa){var _xb=E(_xa),_xc=u_iswalpha(_xb);return (E(_xc)==0)?(E(_xb)==95)?new T1(1,B(_mV(_wt,function(_xd){return new F(function(){return A1(_wR,new T1(3,new T2(1,_xb,_xd)));});}))):new T0(2):new T1(1,B(_mV(_wt,function(_xe){return new F(function(){return A1(_wR,new T1(3,new T2(1,_xb,_xe)));});})));};return B(_lf(new T1(0,_x9),new T(function(){return new T1(1,B(_mv(_o9,_pP,_wR)));})));}),_xf=function(_xg){return (!B(_pT(_m4,_xg,_pY)))?new T0(2):new T1(1,B(_mV(_pZ,function(_xh){var _xi=new T2(1,_xg,_xh);if(!B(_pT(_md,_xi,_wP))){return new F(function(){return A1(_wR,new T1(4,_xi));});}else{return new F(function(){return A1(_wR,new T1(2,_xi));});}})));};return B(_lf(new T1(0,_xf),_x8));});return B(_lf(new T1(0,function(_xj){if(!B(_pT(_m4,_xj,_wv))){return new T0(2);}else{return new F(function(){return A1(_wR,new T1(2,new T2(1,_xj,_1M)));});}}),_x7));});return B(_lf(new T1(0,function(_xk){return (E(_xk)==34)?E(_x5):new T0(2);}),_x6));});return B(_lf(new T1(0,function(_xl){return (E(_xl)==39)?E(new T1(0,_wZ)):new T0(2);}),_x4));});return new F(function(){return _lf(new T1(1,function(_xm){return (E(_xm)._==0)?E(_wS):new T0(2);}),_wT);});},_xn=0,_xo=function(_xp,_xq){var _xr=new T(function(){var _xs=new T(function(){var _xt=function(_xu){var _xv=new T(function(){var _xw=new T(function(){return B(A1(_xq,_xu));});return B(_wQ(function(_xx){var _xy=E(_xx);return (_xy._==2)?(!B(_lT(_xy.a,_lS)))?new T0(2):E(_xw):new T0(2);}));}),_xz=function(_xA){return E(_xv);};return new T1(1,function(_xB){return new F(function(){return A2(_vx,_xB,_xz);});});};return B(A2(_xp,_xn,_xt));});return B(_wQ(function(_xC){var _xD=E(_xC);return (_xD._==2)?(!B(_lT(_xD.a,_lR)))?new T0(2):E(_xs):new T0(2);}));}),_xE=function(_xF){return E(_xr);};return function(_xG){return new F(function(){return A2(_vx,_xG,_xE);});};},_xH=function(_xI,_xJ){var _xK=function(_xL){var _xM=new T(function(){return B(A1(_xI,_xL));}),_xN=function(_xO){return new F(function(){return _lf(B(A1(_xM,_xO)),new T(function(){return new T1(1,B(_xo(_xK,_xO)));}));});};return E(_xN);},_xP=new T(function(){return B(A1(_xI,_xJ));}),_xQ=function(_xR){return new F(function(){return _lf(B(A1(_xP,_xR)),new T(function(){return new T1(1,B(_xo(_xK,_xR)));}));});};return E(_xQ);},_xS=function(_xT,_xU){var _xV=function(_xW,_xX){var _xY=function(_xZ){return new F(function(){return A1(_xX,new T(function(){return  -E(_xZ);}));});},_y0=new T(function(){return B(_wQ(function(_y1){return new F(function(){return A3(_xT,_y1,_xW,_xY);});}));}),_y2=function(_y3){return E(_y0);},_y4=function(_y5){return new F(function(){return A2(_vx,_y5,_y2);});},_y6=new T(function(){return B(_wQ(function(_y7){var _y8=E(_y7);if(_y8._==4){var _y9=E(_y8.a);if(!_y9._){return new F(function(){return A3(_xT,_y8,_xW,_xX);});}else{if(E(_y9.a)==45){if(!E(_y9.b)._){return E(new T1(1,_y4));}else{return new F(function(){return A3(_xT,_y8,_xW,_xX);});}}else{return new F(function(){return A3(_xT,_y8,_xW,_xX);});}}}else{return new F(function(){return A3(_xT,_y8,_xW,_xX);});}}));}),_ya=function(_yb){return E(_y6);};return new T1(1,function(_yc){return new F(function(){return A2(_vx,_yc,_ya);});});};return new F(function(){return _xH(_xV,_xU);});},_yd=function(_ye){var _yf=E(_ye);if(!_yf._){var _yg=_yf.b,_yh=new T(function(){return B(_p1(new T(function(){return B(_oH(E(_yf.a)));}),new T(function(){return B(_oy(_yg,0));},1),B(_oD(_oJ,_yg))));});return new T1(1,_yh);}else{return (E(_yf.b)._==0)?(E(_yf.c)._==0)?new T1(1,new T(function(){return B(_pi(_ox,_yf.a));})):__Z:__Z;}},_yi=function(_yj,_yk){return new T0(2);},_yl=function(_ym){var _yn=E(_ym);if(_yn._==5){var _yo=B(_yd(_yn.a));if(!_yo._){return E(_yi);}else{var _yp=new T(function(){return B(_qe(_yo.a));});return function(_yq,_yr){return new F(function(){return A1(_yr,_yp);});};}}else{return E(_yi);}},_ys=function(_yt){return new F(function(){return _xS(_yl,_yt);});},_yu=new T(function(){return B(unCStr("["));}),_yv=function(_yw,_yx){var _yy=function(_yz,_yA){var _yB=new T(function(){return B(A1(_yA,_1M));}),_yC=new T(function(){var _yD=function(_yE){return new F(function(){return _yy(_q2,function(_yF){return new F(function(){return A1(_yA,new T2(1,_yE,_yF));});});});};return B(A2(_yw,_xn,_yD));}),_yG=new T(function(){return B(_wQ(function(_yH){var _yI=E(_yH);if(_yI._==2){var _yJ=E(_yI.a);if(!_yJ._){return new T0(2);}else{var _yK=_yJ.b;switch(E(_yJ.a)){case 44:return (E(_yK)._==0)?(!E(_yz))?new T0(2):E(_yC):new T0(2);case 93:return (E(_yK)._==0)?E(_yB):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_yL=function(_yM){return E(_yG);};return new T1(1,function(_yN){return new F(function(){return A2(_vx,_yN,_yL);});});},_yO=function(_yP,_yQ){return new F(function(){return _yR(_yQ);});},_yR=function(_yS){var _yT=new T(function(){var _yU=new T(function(){var _yV=new T(function(){var _yW=function(_yX){return new F(function(){return _yy(_q2,function(_yY){return new F(function(){return A1(_yS,new T2(1,_yX,_yY));});});});};return B(A2(_yw,_xn,_yW));});return B(_lf(B(_yy(_q1,_yS)),_yV));});return B(_wQ(function(_yZ){var _z0=E(_yZ);return (_z0._==2)?(!B(_lT(_z0.a,_yu)))?new T0(2):E(_yU):new T0(2);}));}),_z1=function(_z2){return E(_yT);};return new F(function(){return _lf(new T1(1,function(_z3){return new F(function(){return A2(_vx,_z3,_z1);});}),new T(function(){return new T1(1,B(_xo(_yO,_yS)));}));});};return new F(function(){return _yR(_yx);});},_z4=function(_z5,_z6){return new F(function(){return _yv(_ys,_z6);});},_z7=new T(function(){return B(_yv(_ys,_jV));}),_z8=function(_yt){return new F(function(){return _l5(_z7,_yt);});},_z9=function(_za){var _zb=new T(function(){return B(A3(_xS,_yl,_za,_jV));});return function(_zc){return new F(function(){return _l5(_zb,_zc);});};},_zd=new T4(0,_z9,_z8,_ys,_z4),_ze=11,_zf=new T(function(){return B(unCStr("IdentChoice"));}),_zg=function(_zh,_zi){if(_zh>10){return new T0(2);}else{var _zj=new T(function(){var _zk=new T(function(){return B(A3(_xS,_yl,_ze,function(_zl){return new F(function(){return A1(_zi,_zl);});}));});return B(_wQ(function(_zm){var _zn=E(_zm);return (_zn._==3)?(!B(_lT(_zn.a,_zf)))?new T0(2):E(_zk):new T0(2);}));}),_zo=function(_zp){return E(_zj);};return new T1(1,function(_zq){return new F(function(){return A2(_vx,_zq,_zo);});});}},_zr=function(_zs,_zt){return new F(function(){return _zg(E(_zs),_zt);});},_zu=function(_zv){return new F(function(){return _xH(_zr,_zv);});},_zw=function(_zx,_zy){return new F(function(){return _yv(_zu,_zy);});},_zz=new T(function(){return B(_yv(_zu,_jV));}),_zA=function(_zv){return new F(function(){return _l5(_zz,_zv);});},_zB=function(_zC){var _zD=new T(function(){return B(A3(_xH,_zr,_zC,_jV));});return function(_zc){return new F(function(){return _l5(_zD,_zc);});};},_zE=new T4(0,_zB,_zA,_zu,_zw),_zF=new T(function(){return B(unCStr(","));}),_zG=function(_zH){return E(E(_zH).c);},_zI=function(_zJ,_zK,_zL){var _zM=new T(function(){return B(_zG(_zK));}),_zN=new T(function(){return B(A2(_zG,_zJ,_zL));}),_zO=function(_zP){var _zQ=function(_zR){var _zS=new T(function(){var _zT=new T(function(){return B(A2(_zM,_zL,function(_zU){return new F(function(){return A1(_zP,new T2(0,_zR,_zU));});}));});return B(_wQ(function(_zV){var _zW=E(_zV);return (_zW._==2)?(!B(_lT(_zW.a,_zF)))?new T0(2):E(_zT):new T0(2);}));}),_zX=function(_zY){return E(_zS);};return new T1(1,function(_zZ){return new F(function(){return A2(_vx,_zZ,_zX);});});};return new F(function(){return A1(_zN,_zQ);});};return E(_zO);},_A0=function(_A1,_A2,_A3){var _A4=function(_yt){return new F(function(){return _zI(_A1,_A2,_yt);});},_A5=function(_A6,_A7){return new F(function(){return _A8(_A7);});},_A8=function(_A9){return new F(function(){return _lf(new T1(1,B(_xo(_A4,_A9))),new T(function(){return new T1(1,B(_xo(_A5,_A9)));}));});};return new F(function(){return _A8(_A3);});},_Aa=function(_Ab,_Ac){return new F(function(){return _A0(_zE,_zd,_Ac);});},_Ad=new T(function(){return B(_yv(_Aa,_jV));}),_Ae=function(_zv){return new F(function(){return _l5(_Ad,_zv);});},_Af=new T(function(){return B(_A0(_zE,_zd,_jV));}),_Ag=function(_zv){return new F(function(){return _l5(_Af,_zv);});},_Ah=function(_Ai,_zv){return new F(function(){return _Ag(_zv);});},_Aj=function(_Ak,_Al){return new F(function(){return _yv(_Aa,_Al);});},_Am=new T4(0,_Ah,_Ae,_Aa,_Aj),_An=function(_Ao,_Ap){return new F(function(){return _A0(_Am,_zd,_Ap);});},_Aq=function(_Ar,_As){return new F(function(){return _yv(_An,_As);});},_At=new T(function(){return B(_yv(_Aq,_jV));}),_Au=function(_Av){return new F(function(){return _l5(_At,_Av);});},_Aw=function(_Ax){return new F(function(){return _yv(_Aq,_Ax);});},_Ay=function(_Az,_AA){return new F(function(){return _Aw(_AA);});},_AB=new T(function(){return B(_yv(_An,_jV));}),_AC=function(_Av){return new F(function(){return _l5(_AB,_Av);});},_AD=function(_AE,_Av){return new F(function(){return _AC(_Av);});},_AF=new T4(0,_AD,_Au,_Aq,_Ay),_AG=new T(function(){return B(unCStr("IdentPay"));}),_AH=function(_AI,_AJ){if(_AI>10){return new T0(2);}else{var _AK=new T(function(){var _AL=new T(function(){return B(A3(_xS,_yl,_ze,function(_AM){return new F(function(){return A1(_AJ,_AM);});}));});return B(_wQ(function(_AN){var _AO=E(_AN);return (_AO._==3)?(!B(_lT(_AO.a,_AG)))?new T0(2):E(_AL):new T0(2);}));}),_AP=function(_AQ){return E(_AK);};return new T1(1,function(_AR){return new F(function(){return A2(_vx,_AR,_AP);});});}},_AS=function(_AT,_AU){return new F(function(){return _AH(E(_AT),_AU);});},_AV=function(_zv){return new F(function(){return _xH(_AS,_zv);});},_AW=function(_AX,_AY){return new F(function(){return _yv(_AV,_AY);});},_AZ=new T(function(){return B(_yv(_AV,_jV));}),_B0=function(_zv){return new F(function(){return _l5(_AZ,_zv);});},_B1=function(_B2){var _B3=new T(function(){return B(A3(_xH,_AS,_B2,_jV));});return function(_zc){return new F(function(){return _l5(_B3,_zc);});};},_B4=new T4(0,_B1,_B0,_AV,_AW),_B5=function(_B6,_B7){return new F(function(){return _A0(_B4,_zd,_B7);});},_B8=new T(function(){return B(_yv(_B5,_jV));}),_B9=function(_zv){return new F(function(){return _l5(_B8,_zv);});},_Ba=new T(function(){return B(_A0(_B4,_zd,_jV));}),_Bb=function(_zv){return new F(function(){return _l5(_Ba,_zv);});},_Bc=function(_Bd,_zv){return new F(function(){return _Bb(_zv);});},_Be=function(_Bf,_Bg){return new F(function(){return _yv(_B5,_Bg);});},_Bh=new T4(0,_Bc,_B9,_B5,_Be),_Bi=function(_Bj,_Bk){return new F(function(){return _A0(_Bh,_zd,_Bk);});},_Bl=function(_Bm,_Bn){return new F(function(){return _yv(_Bi,_Bn);});},_Bo=new T(function(){return B(_yv(_Bl,_jV));}),_Bp=function(_Av){return new F(function(){return _l5(_Bo,_Av);});},_Bq=function(_Br){return new F(function(){return _yv(_Bl,_Br);});},_Bs=function(_Bt,_Bu){return new F(function(){return _Bq(_Bu);});},_Bv=new T(function(){return B(_yv(_Bi,_jV));}),_Bw=function(_Av){return new F(function(){return _l5(_Bv,_Av);});},_Bx=function(_By,_Av){return new F(function(){return _Bw(_Av);});},_Bz=new T4(0,_Bx,_Bp,_Bl,_Bs),_BA=new T(function(){return B(unCStr("IdentCC"));}),_BB=function(_BC,_BD){if(_BC>10){return new T0(2);}else{var _BE=new T(function(){var _BF=new T(function(){return B(A3(_xS,_yl,_ze,function(_BG){return new F(function(){return A1(_BD,_BG);});}));});return B(_wQ(function(_BH){var _BI=E(_BH);return (_BI._==3)?(!B(_lT(_BI.a,_BA)))?new T0(2):E(_BF):new T0(2);}));}),_BJ=function(_BK){return E(_BE);};return new T1(1,function(_BL){return new F(function(){return A2(_vx,_BL,_BJ);});});}},_BM=function(_BN,_BO){return new F(function(){return _BB(E(_BN),_BO);});},_BP=new T(function(){return B(unCStr("RC"));}),_BQ=function(_BR,_BS){if(_BR>10){return new T0(2);}else{var _BT=new T(function(){var _BU=new T(function(){var _BV=function(_BW){var _BX=function(_BY){return new F(function(){return A3(_xS,_yl,_ze,function(_BZ){return new F(function(){return A1(_BS,new T3(0,_BW,_BY,_BZ));});});});};return new F(function(){return A3(_xS,_yl,_ze,_BX);});};return B(A3(_xH,_BM,_ze,_BV));});return B(_wQ(function(_C0){var _C1=E(_C0);return (_C1._==3)?(!B(_lT(_C1.a,_BP)))?new T0(2):E(_BU):new T0(2);}));}),_C2=function(_C3){return E(_BT);};return new T1(1,function(_C4){return new F(function(){return A2(_vx,_C4,_C2);});});}},_C5=function(_C6,_C7){return new F(function(){return _BQ(E(_C6),_C7);});},_C8=function(_zv){return new F(function(){return _xH(_C5,_zv);});},_C9=function(_Ca,_Cb){return new F(function(){return _yv(_C8,_Cb);});},_Cc=new T(function(){return B(_yv(_C9,_jV));}),_Cd=function(_Av){return new F(function(){return _l5(_Cc,_Av);});},_Ce=new T(function(){return B(_yv(_C8,_jV));}),_Cf=function(_Av){return new F(function(){return _l5(_Ce,_Av);});},_Cg=function(_Ch,_Av){return new F(function(){return _Cf(_Av);});},_Ci=function(_Cj,_Ck){return new F(function(){return _yv(_C9,_Ck);});},_Cl=new T4(0,_Cg,_Cd,_C9,_Ci),_Cm=new T(function(){return B(unCStr("CC"));}),_Cn=function(_Co,_Cp){if(_Co>10){return new T0(2);}else{var _Cq=new T(function(){var _Cr=new T(function(){var _Cs=function(_Ct){var _Cu=function(_Cv){var _Cw=function(_Cx){return new F(function(){return A3(_xS,_yl,_ze,function(_Cy){return new F(function(){return A1(_Cp,new T4(0,_Ct,_Cv,_Cx,_Cy));});});});};return new F(function(){return A3(_xS,_yl,_ze,_Cw);});};return new F(function(){return A3(_xS,_yl,_ze,_Cu);});};return B(A3(_xH,_BM,_ze,_Cs));});return B(_wQ(function(_Cz){var _CA=E(_Cz);return (_CA._==3)?(!B(_lT(_CA.a,_Cm)))?new T0(2):E(_Cr):new T0(2);}));}),_CB=function(_CC){return E(_Cq);};return new T1(1,function(_CD){return new F(function(){return A2(_vx,_CD,_CB);});});}},_CE=function(_CF,_CG){return new F(function(){return _Cn(E(_CF),_CG);});},_CH=function(_zv){return new F(function(){return _xH(_CE,_zv);});},_CI=function(_CJ,_CK){return new F(function(){return _yv(_CH,_CK);});},_CL=new T(function(){return B(_yv(_CI,_jV));}),_CM=function(_Av){return new F(function(){return _l5(_CL,_Av);});},_CN=new T(function(){return B(_yv(_CH,_jV));}),_CO=function(_Av){return new F(function(){return _l5(_CN,_Av);});},_CP=function(_CQ,_Av){return new F(function(){return _CO(_Av);});},_CR=function(_CS,_CT){return new F(function(){return _yv(_CI,_CT);});},_CU=new T4(0,_CP,_CM,_CI,_CR),_CV=function(_CW,_CX,_CY,_CZ,_D0){var _D1=new T(function(){return B(_zI(_CW,_CX,_D0));}),_D2=new T(function(){return B(_zG(_CZ));}),_D3=function(_D4){var _D5=function(_D6){var _D7=E(_D6),_D8=new T(function(){var _D9=new T(function(){var _Da=function(_Db){var _Dc=new T(function(){var _Dd=new T(function(){return B(A2(_D2,_D0,function(_De){return new F(function(){return A1(_D4,new T4(0,_D7.a,_D7.b,_Db,_De));});}));});return B(_wQ(function(_Df){var _Dg=E(_Df);return (_Dg._==2)?(!B(_lT(_Dg.a,_zF)))?new T0(2):E(_Dd):new T0(2);}));}),_Dh=function(_Di){return E(_Dc);};return new T1(1,function(_Dj){return new F(function(){return A2(_vx,_Dj,_Dh);});});};return B(A3(_zG,_CY,_D0,_Da));});return B(_wQ(function(_Dk){var _Dl=E(_Dk);return (_Dl._==2)?(!B(_lT(_Dl.a,_zF)))?new T0(2):E(_D9):new T0(2);}));}),_Dm=function(_Dn){return E(_D8);};return new T1(1,function(_Do){return new F(function(){return A2(_vx,_Do,_Dm);});});};return new F(function(){return A1(_D1,_D5);});};return E(_D3);},_Dp=function(_Dq,_Dr,_Ds,_Dt,_Du){var _Dv=function(_yt){return new F(function(){return _CV(_Dq,_Dr,_Ds,_Dt,_yt);});},_Dw=function(_Dx,_Dy){return new F(function(){return _Dz(_Dy);});},_Dz=function(_DA){return new F(function(){return _lf(new T1(1,B(_xo(_Dv,_DA))),new T(function(){return new T1(1,B(_xo(_Dw,_DA)));}));});};return new F(function(){return _Dz(_Du);});},_DB=function(_DC){var _DD=function(_DE){return E(new T2(3,_DC,_jU));};return new T1(1,function(_DF){return new F(function(){return A2(_vx,_DF,_DD);});});},_DG=new T(function(){return B(_Dp(_CU,_Cl,_Bz,_AF,_DB));}),_DH=function(_DI,_DJ,_DK,_DL){var _DM=E(_DI);if(_DM==1){var _DN=E(_DL);if(!_DN._){return new T3(0,new T(function(){var _DO=E(_DJ);return new T5(0,1,E(_DO),_DK,E(_8i),E(_8i));}),_1M,_1M);}else{var _DP=E(_DJ);return (_DP<E(E(_DN.a).a))?new T3(0,new T5(0,1,E(_DP),_DK,E(_8i),E(_8i)),_DN,_1M):new T3(0,new T5(0,1,E(_DP),_DK,E(_8i),E(_8i)),_1M,_DN);}}else{var _DQ=B(_DH(_DM>>1,_DJ,_DK,_DL)),_DR=_DQ.a,_DS=_DQ.c,_DT=E(_DQ.b);if(!_DT._){return new T3(0,_DR,_1M,_DS);}else{var _DU=E(_DT.a),_DV=_DU.a,_DW=_DU.b,_DX=E(_DT.b);if(!_DX._){return new T3(0,new T(function(){return B(_95(_DV,_DW,_DR));}),_1M,_DS);}else{var _DY=E(_DX.a),_DZ=E(_DV),_E0=E(_DY.a);if(_DZ<_E0){var _E1=B(_DH(_DM>>1,_E0,_DY.b,_DX.b));return new T3(0,new T(function(){return B(_ay(_DZ,_DW,_DR,_E1.a));}),_E1.b,_E1.c);}else{return new T3(0,_DR,_1M,_DT);}}}}},_E2=function(_E3,_E4,_E5){var _E6=E(_E5);if(!_E6._){var _E7=_E6.c,_E8=_E6.d,_E9=_E6.e,_Ea=E(_E6.b);if(_E3>=_Ea){if(_E3!=_Ea){return new F(function(){return _8n(_Ea,_E7,_E8,B(_E2(_E3,_E4,_E9)));});}else{return new T5(0,_E6.a,E(_E3),_E4,E(_E8),E(_E9));}}else{return new F(function(){return _9e(_Ea,_E7,B(_E2(_E3,_E4,_E8)),_E9);});}}else{return new T5(0,1,E(_E3),_E4,E(_8i),E(_8i));}},_Eb=function(_Ec,_Ed){while(1){var _Ee=E(_Ed);if(!_Ee._){return E(_Ec);}else{var _Ef=E(_Ee.a),_Eg=B(_E2(E(_Ef.a),_Ef.b,_Ec));_Ec=_Eg;_Ed=_Ee.b;continue;}}},_Eh=function(_Ei,_Ej,_Ek,_El){return new F(function(){return _Eb(B(_E2(E(_Ej),_Ek,_Ei)),_El);});},_Em=function(_En,_Eo,_Ep){var _Eq=E(_Eo);return new F(function(){return _Eb(B(_E2(E(_Eq.a),_Eq.b,_En)),_Ep);});},_Er=function(_Es,_Et,_Eu){while(1){var _Ev=E(_Eu);if(!_Ev._){return E(_Et);}else{var _Ew=E(_Ev.a),_Ex=_Ew.a,_Ey=_Ew.b,_Ez=E(_Ev.b);if(!_Ez._){return new F(function(){return _95(_Ex,_Ey,_Et);});}else{var _EA=E(_Ez.a),_EB=E(_Ex),_EC=E(_EA.a);if(_EB<_EC){var _ED=B(_DH(_Es,_EC,_EA.b,_Ez.b)),_EE=_ED.a,_EF=E(_ED.c);if(!_EF._){var _EG=_Es<<1,_EH=B(_ay(_EB,_Ey,_Et,_EE));_Es=_EG;_Et=_EH;_Eu=_ED.b;continue;}else{return new F(function(){return _Em(B(_ay(_EB,_Ey,_Et,_EE)),_EF.a,_EF.b);});}}else{return new F(function(){return _Eh(_Et,_EB,_Ey,_Ez);});}}}}},_EI=function(_EJ,_EK,_EL,_EM,_EN){var _EO=E(_EN);if(!_EO._){return new F(function(){return _95(_EL,_EM,_EK);});}else{var _EP=E(_EO.a),_EQ=E(_EL),_ER=E(_EP.a);if(_EQ<_ER){var _ES=B(_DH(_EJ,_ER,_EP.b,_EO.b)),_ET=_ES.a,_EU=E(_ES.c);if(!_EU._){return new F(function(){return _Er(_EJ<<1,B(_ay(_EQ,_EM,_EK,_ET)),_ES.b);});}else{return new F(function(){return _Em(B(_ay(_EQ,_EM,_EK,_ET)),_EU.a,_EU.b);});}}else{return new F(function(){return _Eh(_EK,_EQ,_EM,_EO);});}}},_EV=function(_EW){var _EX=E(_EW);if(!_EX._){return new T0(1);}else{var _EY=E(_EX.a),_EZ=_EY.a,_F0=_EY.b,_F1=E(_EX.b);if(!_F1._){var _F2=E(_EZ);return new T5(0,1,E(_F2),_F0,E(_8i),E(_8i));}else{var _F3=_F1.b,_F4=E(_F1.a),_F5=_F4.b,_F6=E(_EZ),_F7=E(_F4.a);if(_F6<_F7){return new F(function(){return _EI(1,new T5(0,1,E(_F6),_F0,E(_8i),E(_8i)),_F7,_F5,_F3);});}else{return new F(function(){return _Eh(new T5(0,1,E(_F6),_F0,E(_8i),E(_8i)),_F7,_F5,_F3);});}}}},_F8=function(_){return _h9;},_F9=new T(function(){return B(unCStr(": Choose"));}),_Fa=new T(function(){return eval("(function (x, y, z) {var a = document.getElementById(\'actions\'); var r = a.insertRow(); var c1 = r.insertCell(); c1.appendChild(document.createTextNode(x + \' \')); var input = document.createElement(\'input\'); input.type = \'number\'; var ch = \'ibox\' + a.childNodes.length; input.id = ch; input.value = 0; input.style.setProperty(\'width\', \'5em\'); c1.appendChild(input); c1.appendChild(document.createTextNode(\' \' + y)); var c2 = r.insertCell(); var btn = document.createElement(\'button\'); c2.appendChild(btn); btn.appendChild(document.createTextNode(\'Add action\')); btn.style.setProperty(\'width\', \'100%\'); btn.onclick = function () {Haste.addActionWithNum(z, document.getElementById(ch).value);};})");}),_Fb=function(_Fc,_Fd,_){var _Fe=new T(function(){return B(A3(_is,_hk,new T2(1,function(_Ff){return new F(function(){return _j6(0,_Fc,_Ff);});},new T2(1,function(_Fg){return new F(function(){return _hA(0,E(_Fd),_Fg);});},_1M)),_jv));}),_Fh=__app3(E(_Fa),toJSStr(B(unAppCStr("P",new T(function(){return B(_hq(B(_hA(0,E(_Fd),_1M)),_F9));})))),toJSStr(B(unAppCStr("for choice with id ",new T(function(){return B(_hA(0,E(_Fc),_1M));})))),toJSStr(new T2(1,_hz,_Fe)));return new F(function(){return _F8(_);});},_Fi=function(_Fj,_Fk,_){while(1){var _Fl=B((function(_Fm,_Fn,_){var _Fo=E(_Fn);if(!_Fo._){var _Fp=E(_Fo.b);_Fj=function(_){var _Fq=B(_Fb(_Fp.a,_Fp.b,_));return new F(function(){return _Fi(_Fm,_Fo.e,_);});};_Fk=_Fo.d;return __continue;}else{return new F(function(){return A1(_Fm,_);});}})(_Fj,_Fk,_));if(_Fl!=__continue){return _Fl;}}},_Fr=new T(function(){return B(unCStr("SIP "));}),_Fs=new T(function(){return B(unCStr("SIRC "));}),_Ft=new T(function(){return B(unCStr("SICC "));}),_Fu=function(_Fv,_Fw,_Fx){var _Fy=E(_Fw);switch(_Fy._){case 0:var _Fz=function(_FA){var _FB=new T(function(){var _FC=new T(function(){return B(_hA(11,E(_Fy.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_Fy.d),_FA));}))));});return B(_hA(11,E(_Fy.b),new T2(1,_hK,_FC)));});return new F(function(){return _hF(11,_Fy.a,new T2(1,_hK,_FB));});};if(_Fv<11){return new F(function(){return _hq(_Ft,new T(function(){return B(_Fz(_Fx));},1));});}else{var _FD=new T(function(){return B(_hq(_Ft,new T(function(){return B(_Fz(new T2(1,_hy,_Fx)));},1)));});return new T2(1,_hz,_FD);}break;case 1:var _FE=function(_FF){var _FG=new T(function(){var _FH=new T(function(){return B(_hA(11,E(_Fy.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_Fy.c),_FF));}))));});return B(_hF(11,_Fy.a,new T2(1,_hK,_FH)));},1);return new F(function(){return _hq(_Fs,_FG);});};if(_Fv<11){return new F(function(){return _FE(_Fx);});}else{return new T2(1,_hz,new T(function(){return B(_FE(new T2(1,_hy,_Fx)));}));}break;default:var _FI=function(_FJ){var _FK=new T(function(){var _FL=new T(function(){return B(_hA(11,E(_Fy.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_Fy.c),_FJ));}))));});return B(_ih(11,_Fy.a,new T2(1,_hK,_FL)));},1);return new F(function(){return _hq(_Fr,_FK);});};if(_Fv<11){return new F(function(){return _FI(_Fx);});}else{return new T2(1,_hz,new T(function(){return B(_FI(new T2(1,_hy,_Fx)));}));}}},_FM=new T(function(){return B(unCStr(" ADA"));}),_FN=new T(function(){return eval("(function (x, y) {var r = document.getElementById(\'actions\').insertRow(); var c1 = r.insertCell(); c1.appendChild(document.createTextNode(x)); var c2 = r.insertCell(); var btn = document.createElement(\'button\'); c2.appendChild(btn); btn.appendChild(document.createTextNode(\'Add action\')); btn.style.setProperty(\'width\', \'100%\'); btn.onclick = function () {Haste.addAction(y);};})");}),_FO=function(_FP,_FQ,_FR,_){var _FS=new T(function(){var _FT=new T(function(){var _FU=new T(function(){var _FV=new T(function(){return B(unAppCStr(") of ",new T(function(){return B(_hq(B(_hA(0,E(_FR),_1M)),_FM));})));},1);return B(_hq(B(_hA(0,E(_FP),_1M)),_FV));});return B(unAppCStr(": Claim payment (with id: ",_FU));},1);return B(_hq(B(_hA(0,E(_FQ),_1M)),_FT));}),_FW=__app2(E(_FN),toJSStr(B(unAppCStr("P",_FS))),toJSStr(B(_Fu(0,new T3(2,_FP,_FQ,_FR),_1M))));return new F(function(){return _F8(_);});},_FX=function(_FY,_FZ,_){while(1){var _G0=B((function(_G1,_G2,_){var _G3=E(_G2);if(!_G3._){var _G4=E(_G3.b);_FY=function(_){var _G5=B(_FO(_G4.a,_G4.b,_G3.c,_));return new F(function(){return _FX(_G1,_G3.e,_);});};_FZ=_G3.d;return __continue;}else{return new F(function(){return A1(_G1,_);});}})(_FY,_FZ,_));if(_G0!=__continue){return _G0;}}},_G6=new T(function(){return B(unCStr(")"));}),_G7=function(_G8,_G9,_Ga,_){var _Gb=new T(function(){var _Gc=new T(function(){var _Gd=new T(function(){var _Ge=new T(function(){return B(unAppCStr(" ADA from commit (with id: ",new T(function(){return B(_hq(B(_hA(0,E(_G8),_1M)),_G6));})));},1);return B(_hq(B(_hA(0,E(_Ga),_1M)),_Ge));});return B(unAppCStr(": Redeem ",_Gd));},1);return B(_hq(B(_hA(0,E(_G9),_1M)),_Gc));}),_Gf=__app2(E(_FN),toJSStr(B(unAppCStr("P",_Gb))),toJSStr(B(_Fu(0,new T3(1,_G8,_G9,_Ga),_1M))));return new F(function(){return _F8(_);});},_Gg=function(_Gh,_Gi,_){while(1){var _Gj=B((function(_Gk,_Gl,_){var _Gm=E(_Gl);if(!_Gm._){var _Gn=E(_Gm.b);_Gh=function(_){var _Go=B(_G7(_Gn.a,_Gn.b,_Gn.c,_));return new F(function(){return _Gg(_Gk,_Gm.d,_);});};_Gi=_Gm.c;return __continue;}else{return new F(function(){return A1(_Gk,_);});}})(_Gh,_Gi,_));if(_Gj!=__continue){return _Gj;}}},_Gp=function(_){return _h9;},_Gq=function(_Gr,_Gs,_Gt,_Gu,_){var _Gv=new T(function(){var _Gw=new T(function(){var _Gx=new T(function(){var _Gy=new T(function(){var _Gz=new T(function(){var _GA=new T(function(){return B(unAppCStr(" ADA expiring on: ",new T(function(){return B(_hA(0,E(_Gu),_1M));})));},1);return B(_hq(B(_hA(0,E(_Gt),_1M)),_GA));});return B(unAppCStr(") of ",_Gz));},1);return B(_hq(B(_hA(0,E(_Gr),_1M)),_Gy));});return B(unAppCStr(": Make commit (with id: ",_Gx));},1);return B(_hq(B(_hA(0,E(_Gs),_1M)),_Gw));}),_GB=__app2(E(_FN),toJSStr(B(unAppCStr("P",_Gv))),toJSStr(B(_Fu(0,new T4(0,_Gr,_Gs,_Gt,_Gu),_1M))));return new F(function(){return _F8(_);});},_GC=function(_GD,_GE,_){while(1){var _GF=B((function(_GG,_GH,_){var _GI=E(_GH);if(!_GI._){var _GJ=E(_GI.b);_GD=function(_){var _GK=B(_Gq(_GJ.a,_GJ.b,_GJ.c,_GJ.d,_));return new F(function(){return _GC(_GG,_GI.d,_);});};_GE=_GI.c;return __continue;}else{return new F(function(){return A1(_GG,_);});}})(_GD,_GE,_));if(_GF!=__continue){return _GF;}}},_GL=function(_GM,_GN,_GO,_GP,_){var _GQ=B(_GC(_Gp,_GM,_)),_GR=B(_Gg(_Gp,_GN,_)),_GS=B(_FX(_Gp,_GO,_));return new F(function(){return _Fi(_Gp,_GP,_);});},_GT=function(_GU,_GV){var _GW=E(_GU),_GX=E(_GV);return (E(_GW.a)!=E(_GX.a))?true:(E(_GW.b)!=E(_GX.b))?true:(E(_GW.c)!=E(_GX.c))?true:(E(_GW.d)!=E(_GX.d))?true:false;},_GY=function(_GZ,_H0){return E(_GZ)==E(_H0);},_H1=function(_H2,_H3,_H4,_H5,_H6,_H7,_H8,_H9){if(_H2!=_H6){return false;}else{if(E(_H3)!=E(_H7)){return false;}else{if(E(_H4)!=E(_H8)){return false;}else{return new F(function(){return _GY(_H5,_H9);});}}}},_Ha=function(_Hb,_Hc){var _Hd=E(_Hb),_He=E(_Hc);return new F(function(){return _H1(E(_Hd.a),_Hd.b,_Hd.c,_Hd.d,E(_He.a),_He.b,_He.c,_He.d);});},_Hf=new T2(0,_Ha,_GT),_Hg=function(_Hh,_Hi){return E(_Hh)<E(_Hi);},_Hj=function(_Hk,_Hl,_Hm,_Hn,_Ho,_Hp,_Hq,_Hr){if(_Hk>=_Ho){if(_Hk!=_Ho){return false;}else{var _Hs=E(_Hl),_Ht=E(_Hp);if(_Hs>=_Ht){if(_Hs!=_Ht){return false;}else{var _Hu=E(_Hm),_Hv=E(_Hq);if(_Hu>=_Hv){if(_Hu!=_Hv){return false;}else{return new F(function(){return _Hg(_Hn,_Hr);});}}else{return true;}}}else{return true;}}}else{return true;}},_Hw=function(_Hx,_Hy){var _Hz=E(_Hx),_HA=E(_Hy);return new F(function(){return _Hj(E(_Hz.a),_Hz.b,_Hz.c,_Hz.d,E(_HA.a),_HA.b,_HA.c,_HA.d);});},_HB=function(_HC,_HD){return E(_HC)<=E(_HD);},_HE=function(_HF,_HG,_HH,_HI,_HJ,_HK,_HL,_HM){if(_HF>=_HJ){if(_HF!=_HJ){return false;}else{var _HN=E(_HG),_HO=E(_HK);if(_HN>=_HO){if(_HN!=_HO){return false;}else{var _HP=E(_HH),_HQ=E(_HL);if(_HP>=_HQ){if(_HP!=_HQ){return false;}else{return new F(function(){return _HB(_HI,_HM);});}}else{return true;}}}else{return true;}}}else{return true;}},_HR=function(_HS,_HT){var _HU=E(_HS),_HV=E(_HT);return new F(function(){return _HE(E(_HU.a),_HU.b,_HU.c,_HU.d,E(_HV.a),_HV.b,_HV.c,_HV.d);});},_HW=function(_HX,_HY){return E(_HX)>E(_HY);},_HZ=function(_I0,_I1,_I2,_I3,_I4,_I5,_I6,_I7){if(_I0>=_I4){if(_I0!=_I4){return true;}else{var _I8=E(_I1),_I9=E(_I5);if(_I8>=_I9){if(_I8!=_I9){return true;}else{var _Ia=E(_I2),_Ib=E(_I6);if(_Ia>=_Ib){if(_Ia!=_Ib){return true;}else{return new F(function(){return _HW(_I3,_I7);});}}else{return false;}}}else{return false;}}}else{return false;}},_Ic=function(_Id,_Ie){var _If=E(_Id),_Ig=E(_Ie);return new F(function(){return _HZ(E(_If.a),_If.b,_If.c,_If.d,E(_Ig.a),_Ig.b,_Ig.c,_Ig.d);});},_Ih=function(_Ii,_Ij){return E(_Ii)>=E(_Ij);},_Ik=function(_Il,_Im,_In,_Io,_Ip,_Iq,_Ir,_Is){if(_Il>=_Ip){if(_Il!=_Ip){return true;}else{var _It=E(_Im),_Iu=E(_Iq);if(_It>=_Iu){if(_It!=_Iu){return true;}else{var _Iv=E(_In),_Iw=E(_Ir);if(_Iv>=_Iw){if(_Iv!=_Iw){return true;}else{return new F(function(){return _Ih(_Io,_Is);});}}else{return false;}}}else{return false;}}}else{return false;}},_Ix=function(_Iy,_Iz){var _IA=E(_Iy),_IB=E(_Iz);return new F(function(){return _Ik(E(_IA.a),_IA.b,_IA.c,_IA.d,E(_IB.a),_IB.b,_IB.c,_IB.d);});},_IC=function(_ID,_IE){return (_ID>=_IE)?(_ID!=_IE)?2:1:0;},_IF=function(_IG,_IH){return new F(function(){return _IC(E(_IG),E(_IH));});},_II=function(_IJ,_IK,_IL,_IM,_IN,_IO,_IP,_IQ){if(_IJ>=_IN){if(_IJ!=_IN){return 2;}else{var _IR=E(_IK),_IS=E(_IO);if(_IR>=_IS){if(_IR!=_IS){return 2;}else{var _IT=E(_IL),_IU=E(_IP);if(_IT>=_IU){if(_IT!=_IU){return 2;}else{return new F(function(){return _IF(_IM,_IQ);});}}else{return 0;}}}else{return 0;}}}else{return 0;}},_IV=function(_IW,_IX){var _IY=E(_IW),_IZ=E(_IX);return new F(function(){return _II(E(_IY.a),_IY.b,_IY.c,_IY.d,E(_IZ.a),_IZ.b,_IZ.c,_IZ.d);});},_J0=function(_J1,_J2){var _J3=E(_J1),_J4=E(_J3.a),_J5=E(_J2),_J6=E(_J5.a);if(_J4>=_J6){if(_J4!=_J6){return E(_J3);}else{var _J7=E(_J3.b),_J8=E(_J5.b);if(_J7>=_J8){if(_J7!=_J8){return E(_J3);}else{var _J9=E(_J3.c),_Ja=E(_J5.c);return (_J9>=_Ja)?(_J9!=_Ja)?E(_J3):(E(_J3.d)>E(_J5.d))?E(_J3):E(_J5):E(_J5);}}else{return E(_J5);}}}else{return E(_J5);}},_Jb=function(_Jc,_Jd){var _Je=E(_Jc),_Jf=E(_Je.a),_Jg=E(_Jd),_Jh=E(_Jg.a);if(_Jf>=_Jh){if(_Jf!=_Jh){return E(_Jg);}else{var _Ji=E(_Je.b),_Jj=E(_Jg.b);if(_Ji>=_Jj){if(_Ji!=_Jj){return E(_Jg);}else{var _Jk=E(_Je.c),_Jl=E(_Jg.c);return (_Jk>=_Jl)?(_Jk!=_Jl)?E(_Jg):(E(_Je.d)>E(_Jg.d))?E(_Jg):E(_Je):E(_Je);}}else{return E(_Je);}}}else{return E(_Je);}},_Jm={_:0,a:_Hf,b:_IV,c:_Hw,d:_HR,e:_Ic,f:_Ix,g:_J0,h:_Jb},_Jn=function(_Jo,_Jp,_Jq,_Jr){if(_Jo!=_Jq){return false;}else{return new F(function(){return _GY(_Jp,_Jr);});}},_Js=function(_Jt,_Ju){var _Jv=E(_Jt),_Jw=E(_Ju);return new F(function(){return _Jn(E(_Jv.a),_Jv.b,E(_Jw.a),_Jw.b);});},_Jx=function(_Jy,_Jz,_JA,_JB){return (_Jy!=_JA)?true:(E(_Jz)!=E(_JB))?true:false;},_JC=function(_JD,_JE){var _JF=E(_JD),_JG=E(_JE);return new F(function(){return _Jx(E(_JF.a),_JF.b,E(_JG.a),_JG.b);});},_JH=new T2(0,_Js,_JC),_JI=function(_JJ,_JK,_JL,_JM){if(_JJ>=_JL){if(_JJ!=_JL){return 2;}else{return new F(function(){return _IF(_JK,_JM);});}}else{return 0;}},_JN=function(_JO,_JP){var _JQ=E(_JO),_JR=E(_JP);return new F(function(){return _JI(E(_JQ.a),_JQ.b,E(_JR.a),_JR.b);});},_JS=function(_JT,_JU,_JV,_JW){if(_JT>=_JV){if(_JT!=_JV){return false;}else{return new F(function(){return _Hg(_JU,_JW);});}}else{return true;}},_JX=function(_JY,_JZ){var _K0=E(_JY),_K1=E(_JZ);return new F(function(){return _JS(E(_K0.a),_K0.b,E(_K1.a),_K1.b);});},_K2=function(_K3,_K4,_K5,_K6){if(_K3>=_K5){if(_K3!=_K5){return false;}else{return new F(function(){return _HB(_K4,_K6);});}}else{return true;}},_K7=function(_K8,_K9){var _Ka=E(_K8),_Kb=E(_K9);return new F(function(){return _K2(E(_Ka.a),_Ka.b,E(_Kb.a),_Kb.b);});},_Kc=function(_Kd,_Ke,_Kf,_Kg){if(_Kd>=_Kf){if(_Kd!=_Kf){return true;}else{return new F(function(){return _HW(_Ke,_Kg);});}}else{return false;}},_Kh=function(_Ki,_Kj){var _Kk=E(_Ki),_Kl=E(_Kj);return new F(function(){return _Kc(E(_Kk.a),_Kk.b,E(_Kl.a),_Kl.b);});},_Km=function(_Kn,_Ko,_Kp,_Kq){if(_Kn>=_Kp){if(_Kn!=_Kp){return true;}else{return new F(function(){return _Ih(_Ko,_Kq);});}}else{return false;}},_Kr=function(_Ks,_Kt){var _Ku=E(_Ks),_Kv=E(_Kt);return new F(function(){return _Km(E(_Ku.a),_Ku.b,E(_Kv.a),_Kv.b);});},_Kw=function(_Kx,_Ky){var _Kz=E(_Kx),_KA=_Kz.b,_KB=E(_Kz.a),_KC=E(_Ky),_KD=_KC.b,_KE=E(_KC.a);if(_KB>=_KE){if(_KB!=_KE){return new T2(0,_KB,_KA);}else{var _KF=E(_KA),_KG=E(_KD);return (_KF>_KG)?new T2(0,_KB,_KF):new T2(0,_KE,_KG);}}else{return new T2(0,_KE,_KD);}},_KH=function(_KI,_KJ){var _KK=E(_KI),_KL=_KK.b,_KM=E(_KK.a),_KN=E(_KJ),_KO=_KN.b,_KP=E(_KN.a);if(_KM>=_KP){if(_KM!=_KP){return new T2(0,_KP,_KO);}else{var _KQ=E(_KL),_KR=E(_KO);return (_KQ>_KR)?new T2(0,_KP,_KR):new T2(0,_KM,_KQ);}}else{return new T2(0,_KM,_KL);}},_KS={_:0,a:_JH,b:_JN,c:_JX,d:_K7,e:_Kh,f:_Kr,g:_Kw,h:_KH},_KT=function(_KU,_KV,_KW,_KX){if(_KU!=_KW){return false;}else{return new F(function(){return _GY(_KV,_KX);});}},_KY=function(_KZ,_L0){var _L1=E(_KZ),_L2=E(_L0);return new F(function(){return _KT(E(_L1.a),_L1.b,E(_L2.a),_L2.b);});},_L3=function(_L4,_L5,_L6,_L7){return (_L4!=_L6)?true:(E(_L5)!=E(_L7))?true:false;},_L8=function(_L9,_La){var _Lb=E(_L9),_Lc=E(_La);return new F(function(){return _L3(E(_Lb.a),_Lb.b,E(_Lc.a),_Lc.b);});},_Ld=new T2(0,_KY,_L8),_Le=function(_Lf,_Lg,_Lh,_Li){if(_Lf>=_Lh){if(_Lf!=_Lh){return 2;}else{return new F(function(){return _IF(_Lg,_Li);});}}else{return 0;}},_Lj=function(_Lk,_Ll){var _Lm=E(_Lk),_Ln=E(_Ll);return new F(function(){return _Le(E(_Lm.a),_Lm.b,E(_Ln.a),_Ln.b);});},_Lo=function(_Lp,_Lq,_Lr,_Ls){if(_Lp>=_Lr){if(_Lp!=_Lr){return false;}else{return new F(function(){return _Hg(_Lq,_Ls);});}}else{return true;}},_Lt=function(_Lu,_Lv){var _Lw=E(_Lu),_Lx=E(_Lv);return new F(function(){return _Lo(E(_Lw.a),_Lw.b,E(_Lx.a),_Lx.b);});},_Ly=function(_Lz,_LA,_LB,_LC){if(_Lz>=_LB){if(_Lz!=_LB){return false;}else{return new F(function(){return _HB(_LA,_LC);});}}else{return true;}},_LD=function(_LE,_LF){var _LG=E(_LE),_LH=E(_LF);return new F(function(){return _Ly(E(_LG.a),_LG.b,E(_LH.a),_LH.b);});},_LI=function(_LJ,_LK,_LL,_LM){if(_LJ>=_LL){if(_LJ!=_LL){return true;}else{return new F(function(){return _HW(_LK,_LM);});}}else{return false;}},_LN=function(_LO,_LP){var _LQ=E(_LO),_LR=E(_LP);return new F(function(){return _LI(E(_LQ.a),_LQ.b,E(_LR.a),_LR.b);});},_LS=function(_LT,_LU,_LV,_LW){if(_LT>=_LV){if(_LT!=_LV){return true;}else{return new F(function(){return _Ih(_LU,_LW);});}}else{return false;}},_LX=function(_LY,_LZ){var _M0=E(_LY),_M1=E(_LZ);return new F(function(){return _LS(E(_M0.a),_M0.b,E(_M1.a),_M1.b);});},_M2=function(_M3,_M4){var _M5=E(_M3),_M6=_M5.b,_M7=E(_M5.a),_M8=E(_M4),_M9=_M8.b,_Ma=E(_M8.a);if(_M7>=_Ma){if(_M7!=_Ma){return new T2(0,_M7,_M6);}else{var _Mb=E(_M6),_Mc=E(_M9);return (_Mb>_Mc)?new T2(0,_M7,_Mb):new T2(0,_Ma,_Mc);}}else{return new T2(0,_Ma,_M9);}},_Md=function(_Me,_Mf){var _Mg=E(_Me),_Mh=_Mg.b,_Mi=E(_Mg.a),_Mj=E(_Mf),_Mk=_Mj.b,_Ml=E(_Mj.a);if(_Mi>=_Ml){if(_Mi!=_Ml){return new T2(0,_Ml,_Mk);}else{var _Mm=E(_Mh),_Mn=E(_Mk);return (_Mm>_Mn)?new T2(0,_Ml,_Mn):new T2(0,_Mi,_Mm);}}else{return new T2(0,_Mi,_Mh);}},_Mo={_:0,a:_Ld,b:_Lj,c:_Lt,d:_LD,e:_LN,f:_LX,g:_M2,h:_Md},_Mp=function(_Mq,_Mr){var _Ms=E(_Mq),_Mt=E(_Mr);return (E(_Ms.a)!=E(_Mt.a))?true:(E(_Ms.b)!=E(_Mt.b))?true:(E(_Ms.c)!=E(_Mt.c))?true:false;},_Mu=function(_Mv,_Mw,_Mx,_My,_Mz,_MA){if(_Mv!=_My){return false;}else{if(E(_Mw)!=E(_Mz)){return false;}else{return new F(function(){return _GY(_Mx,_MA);});}}},_MB=function(_MC,_MD){var _ME=E(_MC),_MF=E(_MD);return new F(function(){return _Mu(E(_ME.a),_ME.b,_ME.c,E(_MF.a),_MF.b,_MF.c);});},_MG=new T2(0,_MB,_Mp),_MH=function(_MI,_MJ,_MK,_ML,_MM,_MN){if(_MI>=_ML){if(_MI!=_ML){return false;}else{var _MO=E(_MJ),_MP=E(_MM);if(_MO>=_MP){if(_MO!=_MP){return false;}else{return new F(function(){return _Hg(_MK,_MN);});}}else{return true;}}}else{return true;}},_MQ=function(_MR,_MS){var _MT=E(_MR),_MU=E(_MS);return new F(function(){return _MH(E(_MT.a),_MT.b,_MT.c,E(_MU.a),_MU.b,_MU.c);});},_MV=function(_MW,_MX,_MY,_MZ,_N0,_N1){if(_MW>=_MZ){if(_MW!=_MZ){return false;}else{var _N2=E(_MX),_N3=E(_N0);if(_N2>=_N3){if(_N2!=_N3){return false;}else{return new F(function(){return _HB(_MY,_N1);});}}else{return true;}}}else{return true;}},_N4=function(_N5,_N6){var _N7=E(_N5),_N8=E(_N6);return new F(function(){return _MV(E(_N7.a),_N7.b,_N7.c,E(_N8.a),_N8.b,_N8.c);});},_N9=function(_Na,_Nb,_Nc,_Nd,_Ne,_Nf){if(_Na>=_Nd){if(_Na!=_Nd){return true;}else{var _Ng=E(_Nb),_Nh=E(_Ne);if(_Ng>=_Nh){if(_Ng!=_Nh){return true;}else{return new F(function(){return _HW(_Nc,_Nf);});}}else{return false;}}}else{return false;}},_Ni=function(_Nj,_Nk){var _Nl=E(_Nj),_Nm=E(_Nk);return new F(function(){return _N9(E(_Nl.a),_Nl.b,_Nl.c,E(_Nm.a),_Nm.b,_Nm.c);});},_Nn=function(_No,_Np,_Nq,_Nr,_Ns,_Nt){if(_No>=_Nr){if(_No!=_Nr){return true;}else{var _Nu=E(_Np),_Nv=E(_Ns);if(_Nu>=_Nv){if(_Nu!=_Nv){return true;}else{return new F(function(){return _Ih(_Nq,_Nt);});}}else{return false;}}}else{return false;}},_Nw=function(_Nx,_Ny){var _Nz=E(_Nx),_NA=E(_Ny);return new F(function(){return _Nn(E(_Nz.a),_Nz.b,_Nz.c,E(_NA.a),_NA.b,_NA.c);});},_NB=function(_NC,_ND,_NE,_NF,_NG,_NH){if(_NC>=_NF){if(_NC!=_NF){return 2;}else{var _NI=E(_ND),_NJ=E(_NG);if(_NI>=_NJ){if(_NI!=_NJ){return 2;}else{return new F(function(){return _IF(_NE,_NH);});}}else{return 0;}}}else{return 0;}},_NK=function(_NL,_NM){var _NN=E(_NL),_NO=E(_NM);return new F(function(){return _NB(E(_NN.a),_NN.b,_NN.c,E(_NO.a),_NO.b,_NO.c);});},_NP=function(_NQ,_NR){var _NS=E(_NQ),_NT=E(_NS.a),_NU=E(_NR),_NV=E(_NU.a);if(_NT>=_NV){if(_NT!=_NV){return E(_NS);}else{var _NW=E(_NS.b),_NX=E(_NU.b);return (_NW>=_NX)?(_NW!=_NX)?E(_NS):(E(_NS.c)>E(_NU.c))?E(_NS):E(_NU):E(_NU);}}else{return E(_NU);}},_NY=function(_NZ,_O0){var _O1=E(_NZ),_O2=E(_O1.a),_O3=E(_O0),_O4=E(_O3.a);if(_O2>=_O4){if(_O2!=_O4){return E(_O3);}else{var _O5=E(_O1.b),_O6=E(_O3.b);return (_O5>=_O6)?(_O5!=_O6)?E(_O3):(E(_O1.c)>E(_O3.c))?E(_O3):E(_O1):E(_O1);}}else{return E(_O1);}},_O7={_:0,a:_MG,b:_NK,c:_MQ,d:_N4,e:_Ni,f:_Nw,g:_NP,h:_NY},_O8=__Z,_O9=__Z,_Oa=function(_Ob){return E(E(_Ob).b);},_Oc=function(_Od,_Oe,_Of){var _Og=E(_Oe);if(!_Og._){return E(_Of);}else{var _Oh=function(_Oi,_Oj){while(1){var _Ok=E(_Oj);if(!_Ok._){var _Ol=_Ok.b,_Om=_Ok.e;switch(B(A3(_Oa,_Od,_Oi,_Ol))){case 0:return new F(function(){return _ay(_Ol,_Ok.c,B(_Oh(_Oi,_Ok.d)),_Om);});break;case 1:return E(_Om);default:_Oj=_Om;continue;}}else{return new T0(1);}}};return new F(function(){return _Oh(_Og.a,_Of);});}},_On=function(_Oo,_Op,_Oq){var _Or=E(_Op);if(!_Or._){return E(_Oq);}else{var _Os=function(_Ot,_Ou){while(1){var _Ov=E(_Ou);if(!_Ov._){var _Ow=_Ov.b,_Ox=_Ov.d;switch(B(A3(_Oa,_Oo,_Ow,_Ot))){case 0:return new F(function(){return _ay(_Ow,_Ov.c,_Ox,B(_Os(_Ot,_Ov.e)));});break;case 1:return E(_Ox);default:_Ou=_Ox;continue;}}else{return new T0(1);}}};return new F(function(){return _Os(_Or.a,_Oq);});}},_Oy=function(_Oz,_OA,_OB,_OC){var _OD=E(_OA),_OE=E(_OC);if(!_OE._){var _OF=_OE.b,_OG=_OE.c,_OH=_OE.d,_OI=_OE.e;switch(B(A3(_Oa,_Oz,_OD,_OF))){case 0:return new F(function(){return _9e(_OF,_OG,B(_Oy(_Oz,_OD,_OB,_OH)),_OI);});break;case 1:return E(_OE);default:return new F(function(){return _8n(_OF,_OG,_OH,B(_Oy(_Oz,_OD,_OB,_OI)));});}}else{return new T5(0,1,E(_OD),_OB,E(_8i),E(_8i));}},_OJ=function(_OK,_OL,_OM,_ON){return new F(function(){return _Oy(_OK,_OL,_OM,_ON);});},_OO=function(_OP){return E(E(_OP).d);},_OQ=function(_OR){return E(E(_OR).f);},_OS=function(_OT,_OU,_OV,_OW){var _OX=E(_OU);if(!_OX._){var _OY=E(_OV);if(!_OY._){return E(_OW);}else{var _OZ=function(_P0,_P1){while(1){var _P2=E(_P1);if(!_P2._){if(!B(A3(_OQ,_OT,_P2.b,_P0))){return E(_P2);}else{_P1=_P2.d;continue;}}else{return new T0(1);}}};return new F(function(){return _OZ(_OY.a,_OW);});}}else{var _P3=_OX.a,_P4=E(_OV);if(!_P4._){var _P5=function(_P6,_P7){while(1){var _P8=E(_P7);if(!_P8._){if(!B(A3(_OO,_OT,_P8.b,_P6))){return E(_P8);}else{_P7=_P8.e;continue;}}else{return new T0(1);}}};return new F(function(){return _P5(_P3,_OW);});}else{var _P9=function(_Pa,_Pb,_Pc){while(1){var _Pd=E(_Pc);if(!_Pd._){var _Pe=_Pd.b;if(!B(A3(_OO,_OT,_Pe,_Pa))){if(!B(A3(_OQ,_OT,_Pe,_Pb))){return E(_Pd);}else{_Pc=_Pd.d;continue;}}else{_Pc=_Pd.e;continue;}}else{return new T0(1);}}};return new F(function(){return _P9(_P3,_P4.a,_OW);});}}},_Pf=function(_Pg,_Ph,_Pi,_Pj,_Pk){var _Pl=E(_Pk);if(!_Pl._){var _Pm=_Pl.b,_Pn=_Pl.c,_Po=_Pl.d,_Pp=_Pl.e,_Pq=E(_Pj);if(!_Pq._){var _Pr=_Pq.b,_Ps=function(_Pt){var _Pu=new T1(1,E(_Pr));return new F(function(){return _ay(_Pr,_Pq.c,B(_Pf(_Pg,_Ph,_Pu,_Pq.d,B(_OS(_Pg,_Ph,_Pu,_Pl)))),B(_Pf(_Pg,_Pu,_Pi,_Pq.e,B(_OS(_Pg,_Pu,_Pi,_Pl)))));});};if(!E(_Po)._){return new F(function(){return _Ps(_);});}else{if(!E(_Pp)._){return new F(function(){return _Ps(_);});}else{return new F(function(){return _OJ(_Pg,_Pm,_Pn,_Pq);});}}}else{return new F(function(){return _ay(_Pm,_Pn,B(_Oc(_Pg,_Ph,_Po)),B(_On(_Pg,_Pi,_Pp)));});}}else{return E(_Pj);}},_Pv=function(_Pw,_Px,_Py,_Pz,_PA,_PB,_PC,_PD,_PE,_PF,_PG,_PH,_PI){var _PJ=function(_PK){var _PL=new T1(1,E(_PA));return new F(function(){return _ay(_PA,_PB,B(_Pf(_Pw,_Px,_PL,_PC,B(_OS(_Pw,_Px,_PL,new T5(0,_PE,E(_PF),_PG,E(_PH),E(_PI)))))),B(_Pf(_Pw,_PL,_Py,_PD,B(_OS(_Pw,_PL,_Py,new T5(0,_PE,E(_PF),_PG,E(_PH),E(_PI)))))));});};if(!E(_PH)._){return new F(function(){return _PJ(_);});}else{if(!E(_PI)._){return new F(function(){return _PJ(_);});}else{return new F(function(){return _OJ(_Pw,_PF,_PG,new T5(0,_Pz,E(_PA),_PB,E(_PC),E(_PD)));});}}},_PM=function(_PN,_PO,_PP){var _PQ=E(_PO);if(!_PQ._){return E(_PP);}else{var _PR=function(_PS,_PT){while(1){var _PU=E(_PT);if(!_PU._){var _PV=_PU.b,_PW=_PU.d;switch(B(A3(_Oa,_PN,_PS,_PV))){case 0:return new F(function(){return _2x(_PV,B(_PR(_PS,_PU.c)),_PW);});break;case 1:return E(_PW);default:_PT=_PW;continue;}}else{return new T0(1);}}};return new F(function(){return _PR(_PQ.a,_PP);});}},_PX=function(_PY,_PZ,_Q0){var _Q1=E(_PZ);if(!_Q1._){return E(_Q0);}else{var _Q2=function(_Q3,_Q4){while(1){var _Q5=E(_Q4);if(!_Q5._){var _Q6=_Q5.b,_Q7=_Q5.c;switch(B(A3(_Oa,_PY,_Q6,_Q3))){case 0:return new F(function(){return _2x(_Q6,_Q7,B(_Q2(_Q3,_Q5.d)));});break;case 1:return E(_Q7);default:_Q4=_Q7;continue;}}else{return new T0(1);}}};return new F(function(){return _Q2(_Q1.a,_Q0);});}},_Q8=function(_Q9,_Qa,_Qb){var _Qc=E(_Qa),_Qd=E(_Qb);if(!_Qd._){var _Qe=_Qd.b,_Qf=_Qd.c,_Qg=_Qd.d;switch(B(A3(_Oa,_Q9,_Qc,_Qe))){case 0:return new F(function(){return _5(_Qe,B(_Q8(_Q9,_Qc,_Qf)),_Qg);});break;case 1:return E(_Qd);default:return new F(function(){return _H(_Qe,_Qf,B(_Q8(_Q9,_Qc,_Qg)));});}}else{return new T4(0,1,E(_Qc),E(_0),E(_0));}},_Qh=function(_Qi,_Qj,_Qk){return new F(function(){return _Q8(_Qi,_Qj,_Qk);});},_Ql=function(_Qm,_Qn,_Qo,_Qp){var _Qq=E(_Qn);if(!_Qq._){var _Qr=E(_Qo);if(!_Qr._){return E(_Qp);}else{var _Qs=function(_Qt,_Qu){while(1){var _Qv=E(_Qu);if(!_Qv._){if(!B(A3(_OQ,_Qm,_Qv.b,_Qt))){return E(_Qv);}else{_Qu=_Qv.c;continue;}}else{return new T0(1);}}};return new F(function(){return _Qs(_Qr.a,_Qp);});}}else{var _Qw=_Qq.a,_Qx=E(_Qo);if(!_Qx._){var _Qy=function(_Qz,_QA){while(1){var _QB=E(_QA);if(!_QB._){if(!B(A3(_OO,_Qm,_QB.b,_Qz))){return E(_QB);}else{_QA=_QB.d;continue;}}else{return new T0(1);}}};return new F(function(){return _Qy(_Qw,_Qp);});}else{var _QC=function(_QD,_QE,_QF){while(1){var _QG=E(_QF);if(!_QG._){var _QH=_QG.b;if(!B(A3(_OO,_Qm,_QH,_QD))){if(!B(A3(_OQ,_Qm,_QH,_QE))){return E(_QG);}else{_QF=_QG.c;continue;}}else{_QF=_QG.d;continue;}}else{return new T0(1);}}};return new F(function(){return _QC(_Qw,_Qx.a,_Qp);});}}},_QI=function(_QJ,_QK,_QL,_QM,_QN){var _QO=E(_QN);if(!_QO._){var _QP=_QO.b,_QQ=_QO.c,_QR=_QO.d,_QS=E(_QM);if(!_QS._){var _QT=_QS.b,_QU=function(_QV){var _QW=new T1(1,E(_QT));return new F(function(){return _2x(_QT,B(_QI(_QJ,_QK,_QW,_QS.c,B(_Ql(_QJ,_QK,_QW,_QO)))),B(_QI(_QJ,_QW,_QL,_QS.d,B(_Ql(_QJ,_QW,_QL,_QO)))));});};if(!E(_QQ)._){return new F(function(){return _QU(_);});}else{if(!E(_QR)._){return new F(function(){return _QU(_);});}else{return new F(function(){return _Qh(_QJ,_QP,_QS);});}}}else{return new F(function(){return _2x(_QP,B(_PM(_QJ,_QK,_QQ)),B(_PX(_QJ,_QL,_QR)));});}}else{return E(_QM);}},_QX=function(_QY,_QZ,_R0,_R1,_R2,_R3,_R4,_R5,_R6,_R7,_R8){var _R9=function(_Ra){var _Rb=new T1(1,E(_R2));return new F(function(){return _2x(_R2,B(_QI(_QY,_QZ,_Rb,_R3,B(_Ql(_QY,_QZ,_Rb,new T4(0,_R5,E(_R6),E(_R7),E(_R8)))))),B(_QI(_QY,_Rb,_R0,_R4,B(_Ql(_QY,_Rb,_R0,new T4(0,_R5,E(_R6),E(_R7),E(_R8)))))));});};if(!E(_R7)._){return new F(function(){return _R9(_);});}else{if(!E(_R8)._){return new F(function(){return _R9(_);});}else{return new F(function(){return _Qh(_QY,_R6,new T4(0,_R1,E(_R2),E(_R3),E(_R4)));});}}},_Rc=function(_Rd,_Re,_Rf,_Rg,_Rh,_Ri,_Rj,_Rk){return new T4(0,new T(function(){var _Rl=E(_Rd);if(!_Rl._){var _Rm=E(_Rh);if(!_Rm._){return B(_QX(_Jm,_O9,_O9,_Rl.a,_Rl.b,_Rl.c,_Rl.d,_Rm.a,_Rm.b,_Rm.c,_Rm.d));}else{return E(_Rl);}}else{return E(_Rh);}}),new T(function(){var _Rn=E(_Re);if(!_Rn._){var _Ro=E(_Ri);if(!_Ro._){return B(_QX(_O7,_O9,_O9,_Rn.a,_Rn.b,_Rn.c,_Rn.d,_Ro.a,_Ro.b,_Ro.c,_Ro.d));}else{return E(_Rn);}}else{return E(_Ri);}}),new T(function(){var _Rp=E(_Rf);if(!_Rp._){var _Rq=E(_Rj);if(!_Rq._){return B(_Pv(_Mo,_O8,_O8,_Rp.a,_Rp.b,_Rp.c,_Rp.d,_Rp.e,_Rq.a,_Rq.b,_Rq.c,_Rq.d,_Rq.e));}else{return E(_Rp);}}else{return E(_Rj);}}),new T(function(){var _Rr=E(_Rg);if(!_Rr._){var _Rs=E(_Rk);if(!_Rs._){return B(_Pv(_KS,_O8,_O8,_Rr.a,_Rr.b,_Rr.c,_Rr.d,_Rr.e,_Rs.a,_Rs.b,_Rs.c,_Rs.d,_Rs.e));}else{return E(_Rr);}}else{return E(_Rk);}}));},_Rt=0,_Ru=function(_Rv,_Rw,_Rx,_Ry){while(1){var _Rz=E(_Ry);if(!_Rz._){var _RA=_Rz.d,_RB=_Rz.e,_RC=E(_Rz.b),_RD=E(_RC.a);if(_Rv>=_RD){if(_Rv!=_RD){_Rw=_;_Ry=_RB;continue;}else{var _RE=E(_RC.b);if(_Rx>=_RE){if(_Rx!=_RE){_Rw=_;_Ry=_RB;continue;}else{return new T1(1,_Rz.c);}}else{_Rw=_;_Ry=_RA;continue;}}}else{_Rw=_;_Ry=_RA;continue;}}else{return __Z;}}},_RF=function(_RG,_RH,_RI,_RJ){while(1){var _RK=E(_RJ);if(!_RK._){var _RL=_RK.d,_RM=_RK.e,_RN=E(_RK.b),_RO=E(_RN.a);if(_RG>=_RO){if(_RG!=_RO){_RH=_;_RJ=_RM;continue;}else{var _RP=E(_RI),_RQ=E(_RN.b);if(_RP>=_RQ){if(_RP!=_RQ){return new F(function(){return _Ru(_RG,_,_RP,_RM);});}else{return new T1(1,_RK.c);}}else{return new F(function(){return _Ru(_RG,_,_RP,_RL);});}}}else{_RH=_;_RJ=_RL;continue;}}else{return __Z;}}},_RR=function(_RS,_RT){while(1){var _RU=E(_RT);if(!_RU._){var _RV=E(_RU.b);if(_RS>=_RV){if(_RS!=_RV){_RT=_RU.e;continue;}else{return new T1(1,_RU.c);}}else{_RT=_RU.d;continue;}}else{return __Z;}}},_RW=function(_RX,_RY,_RZ){while(1){var _S0=E(_RZ);switch(_S0._){case 0:var _S1=B(_RR(E(_S0.a),_RX));if(!_S1._){return E(_Rt);}else{var _S2=E(E(_S1.a).b);return (_S2._==0)?E(_S2.a):E(_Rt);}break;case 1:return B(_RW(_RX,_RY,_S0.a))+B(_RW(_RX,_RY,_S0.b))|0;case 2:return E(_S0.a);default:var _S3=_S0.b,_S4=_S0.c,_S5=E(_RY);if(!_S5._){var _S6=_S5.d,_S7=_S5.e,_S8=E(_S5.b),_S9=E(_S0.a),_Sa=E(_S8.a);if(_S9>=_Sa){if(_S9!=_Sa){var _Sb=B(_RF(_S9,_,_S3,_S7));if(!_Sb._){_RY=_S5;_RZ=_S4;continue;}else{return E(_Sb.a);}}else{var _Sc=E(_S3),_Sd=E(_S8.b);if(_Sc>=_Sd){if(_Sc!=_Sd){var _Se=B(_Ru(_S9,_,_Sc,_S7));if(!_Se._){_RY=_S5;_RZ=_S4;continue;}else{return E(_Se.a);}}else{return E(_S5.c);}}else{var _Sf=B(_Ru(_S9,_,_Sc,_S6));if(!_Sf._){_RY=_S5;_RZ=_S4;continue;}else{return E(_Sf.a);}}}}else{var _Sg=B(_RF(_S9,_,_S3,_S6));if(!_Sg._){_RY=_S5;_RZ=_S4;continue;}else{return E(_Sg.a);}}}else{_RY=_8i;_RZ=_S4;continue;}}}},_Sh=function(_Si,_Sj){while(1){var _Sk=E(_Sj);if(!_Sk._){var _Sl=E(_Sk.b);if(_Si>=_Sl){if(_Si!=_Sl){_Sj=_Sk.e;continue;}else{return true;}}else{_Sj=_Sk.d;continue;}}else{return false;}}},_Sm=function(_Sn,_So){while(1){var _Sp=E(_So);if(!_Sp._){var _Sq=E(_Sp.b);if(_Sn>=_Sq){if(_Sn!=_Sq){_So=_Sp.e;continue;}else{return new T1(1,_Sp.c);}}else{_So=_Sp.d;continue;}}else{return __Z;}}},_Sr=function(_Ss,_St){var _Su=E(_Ss);return new F(function(){return _RW(_Su.a,_Su.b,_St);});},_Sv=function(_Sw,_Sx){while(1){var _Sy=B((function(_Sz,_SA){var _SB=E(_Sz);switch(_SB._){case 1:var _SC=E(_SA),_SD=_SC.a,_SE=E(_SB.a);return (!B(_Sh(_SE,_SD)))?new T4(0,new T4(0,1,E(new T4(0,_SE,_SB.b,new T(function(){return B(_RW(_SD,_SC.b,_SB.c));}),_SB.e)),E(_0),E(_0)),_0,_8i,_8i):new T4(0,_0,_0,_8i,_8i);case 2:var _SF=E(_SB.a),_SG=B(_Sm(_SF,E(_SA).a));if(!_SG._){return new T4(0,_0,_0,_8i,_8i);}else{var _SH=E(_SG.a),_SI=E(_SH.b);return (_SI._==0)?new T4(0,_0,new T4(0,1,E(new T3(0,_SF,_SH.a,_SI.a)),E(_0),E(_0)),_8i,_8i):new T4(0,_0,_0,_8i,_8i);}break;case 3:return new T4(0,_0,_0,new T5(0,1,E(new T2(0,_SB.a,_SB.c)),new T(function(){return B(_Sr(_SA,_SB.d));}),E(_8i),E(_8i)),_8i);case 4:var _SJ=B(_Sv(_SB.a,_SA)),_SK=B(_Sv(_SB.b,_SA));return new F(function(){return _Rc(_SJ.a,_SJ.b,_SJ.c,_SJ.d,_SK.a,_SK.b,_SK.c,_SK.d);});break;case 8:var _SL=_SA;_Sw=_SB.c;_Sx=_SL;return __continue;case 9:var _SL=_SA;_Sw=_SB.b;_Sx=_SL;return __continue;case 10:var _SL=_SA;_Sw=_SB.b;_Sx=_SL;return __continue;case 11:var _SL=_SA;_Sw=_SB.c;_Sx=_SL;return __continue;default:return new T4(0,_0,_0,_8i,_8i);}})(_Sw,_Sx));if(_Sy!=__continue){return _Sy;}}},_SM=function(_SN,_SO){var _SP=new T(function(){var _SQ=function(_SR,_SS){while(1){var _ST=B((function(_SU,_SV){var _SW=E(_SV);if(!_SW._){var _SX=_SW.e,_SY=new T(function(){var _SZ=E(_SW.c),_T0=E(_SZ.b);if(!_T0._){var _T1=E(E(_SN).b);if(E(_T0.b)>_T1){var _T2=function(_T3,_T4){while(1){var _T5=B((function(_T6,_T7){var _T8=E(_T7);if(!_T8._){var _T9=_T8.e,_Ta=new T(function(){var _Tb=E(_T8.c),_Tc=E(_Tb.b);if(!_Tc._){if(E(_Tc.b)>_T1){return B(_T2(_T6,_T9));}else{return new T2(1,new T3(0,_T8.b,_Tb.a,_Tc.a),new T(function(){return B(_T2(_T6,_T9));}));}}else{return B(_T2(_T6,_T9));}},1);_T3=_Ta;_T4=_T8.d;return __continue;}else{return E(_T6);}})(_T3,_T4));if(_T5!=__continue){return _T5;}}};return B(_T2(_SU,_SX));}else{var _Td=new T(function(){var _Te=function(_Tf,_Tg){while(1){var _Th=B((function(_Ti,_Tj){var _Tk=E(_Tj);if(!_Tk._){var _Tl=_Tk.e,_Tm=new T(function(){var _Tn=E(_Tk.c),_To=E(_Tn.b);if(!_To._){if(E(_To.b)>_T1){return B(_Te(_Ti,_Tl));}else{return new T2(1,new T3(0,_Tk.b,_Tn.a,_To.a),new T(function(){return B(_Te(_Ti,_Tl));}));}}else{return B(_Te(_Ti,_Tl));}},1);_Tf=_Tm;_Tg=_Tk.d;return __continue;}else{return E(_Ti);}})(_Tf,_Tg));if(_Th!=__continue){return _Th;}}};return B(_Te(_SU,_SX));});return new T2(1,new T3(0,_SW.b,_SZ.a,_T0.a),_Td);}}else{return B(_SQ(_SU,_SX));}},1);_SR=_SY;_SS=_SW.d;return __continue;}else{return E(_SU);}})(_SR,_SS));if(_ST!=__continue){return _ST;}}};return B(_83(B(_SQ(_1M,_SO))));});return new T4(0,_0,_SP,_8i,_8i);},_Tp=function(_Tq,_Tr,_Ts,_Tt,_Tu){while(1){var _Tv=E(_Tq);if(!_Tv._){return new T4(0,_Tr,_Ts,_Tt,_Tu);}else{var _Tw=E(_Tv.a),_Tx=B(_Rc(_Tr,_Ts,_Tt,_Tu,_Tw.a,_Tw.b,_Tw.c,_Tw.d));_Tq=_Tv.b;_Tr=_Tx.a;_Ts=_Tx.b;_Tt=_Tx.c;_Tu=_Tx.d;continue;}}},_Ty=function(_Tz,_TA,_TB,_TC,_TD,_TE){var _TF=E(_Tz),_TG=B(_Rc(_TB,_TC,_TD,_TE,_TF.a,_TF.b,_TF.c,_TF.d));return new F(function(){return _Tp(_TA,_TG.a,_TG.b,_TG.c,_TG.d);});},_TH=0,_TI=function(_TJ){var _TK=E(_TJ);switch(_TK._){case 1:var _TL=B(_TI(_TK.a));return new F(function(){return _Ty(new T(function(){var _TM=B(_TI(_TK.b));return new T4(0,_TM.a,_TM.b,_TM.c,_TM.d);}),_1M,_TL.a,_TL.b,_TL.c,_TL.d);});break;case 3:var _TN=B(_TI(_TK.c));return new F(function(){return _Rc(_0,_0,_8i,new T5(0,1,E(new T2(0,_TK.a,_TK.b)),_TH,E(_8i),E(_8i)),_TN.a,_TN.b,_TN.c,_TN.d);});break;default:return new T4(0,_0,_0,_8i,_8i);}},_TO=function(_TP,_TQ,_TR,_TS){while(1){var _TT=E(_TS);if(!_TT._){var _TU=_TT.d,_TV=_TT.e,_TW=E(_TT.b),_TX=E(_TW.a);if(_TP>=_TX){if(_TP!=_TX){_TQ=_;_TS=_TV;continue;}else{var _TY=E(_TW.b);if(_TR>=_TY){if(_TR!=_TY){_TQ=_;_TS=_TV;continue;}else{return true;}}else{_TQ=_;_TS=_TU;continue;}}}else{_TQ=_;_TS=_TU;continue;}}else{return false;}}},_TZ=function(_U0,_U1,_U2,_U3){while(1){var _U4=E(_U3);if(!_U4._){var _U5=_U4.d,_U6=_U4.e,_U7=E(_U4.b),_U8=E(_U7.a);if(_U0>=_U8){if(_U0!=_U8){_U1=_;_U3=_U6;continue;}else{var _U9=E(_U2),_Ua=E(_U7.b);if(_U9>=_Ua){if(_U9!=_Ua){return new F(function(){return _TO(_U0,_,_U9,_U6);});}else{return true;}}else{return new F(function(){return _TO(_U0,_,_U9,_U5);});}}}else{_U1=_;_U3=_U5;continue;}}else{return false;}}},_Ub=function(_Uc,_Ud,_Ue,_Uf,_Ug){while(1){var _Uh=E(_Uc);if(!_Uh._){return new T4(0,_Ud,_Ue,_Uf,_Ug);}else{var _Ui=E(_Uh.a),_Uj=B(_Rc(_Ud,_Ue,_Uf,_Ug,_Ui.a,_Ui.b,_Ui.c,_Ui.d));_Uc=_Uh.b;_Ud=_Uj.a;_Ue=_Uj.b;_Uf=_Uj.c;_Ug=_Uj.d;continue;}}},_Uk=function(_Ul,_Um,_Un,_Uo,_Up){while(1){var _Uq=E(_Ul);if(!_Uq._){return new T4(0,_Um,_Un,_Uo,_Up);}else{var _Ur=E(_Uq.a),_Us=B(_Rc(_Um,_Un,_Uo,_Up,_Ur.a,_Ur.b,_Ur.c,_Ur.d));_Ul=_Uq.b;_Um=_Us.a;_Un=_Us.b;_Uo=_Us.c;_Up=_Us.d;continue;}}},_Ut=function(_Uu,_Uv,_Uw,_Ux,_Uy){while(1){var _Uz=E(_Uu);if(!_Uz._){return new T4(0,_Uv,_Uw,_Ux,_Uy);}else{var _UA=E(_Uz.a),_UB=B(_Rc(_Uv,_Uw,_Ux,_Uy,_UA.a,_UA.b,_UA.c,_UA.d));_Uu=_Uz.b;_Uv=_UB.a;_Uw=_UB.b;_Ux=_UB.c;_Uy=_UB.d;continue;}}},_UC=function(_UD,_UE){var _UF=B(_TI(_UE));return new T4(0,_UF.a,_UF.b,_UF.c,_UF.d);},_UG=function(_UH,_UI){var _UJ=B(_UK(_UH,_UI));return new T4(0,_UJ.a,_UJ.b,_UJ.c,_UJ.d);},_UK=function(_UL,_UM){while(1){var _UN=B((function(_UO,_UP){var _UQ=E(_UP);switch(_UQ._){case 1:var _UR=B(_UK(_UO,_UQ.a));return new F(function(){return _Ut(new T2(1,new T(function(){return B(_UG(_UO,_UQ.b));}),_1M),_UR.a,_UR.b,_UR.c,_UR.d);});break;case 2:var _US=B(_UK(_UO,_UQ.a));return new F(function(){return _Uk(new T2(1,new T(function(){return B(_UG(_UO,_UQ.b));}),_1M),_US.a,_US.b,_US.c,_US.d);});break;case 3:var _UT=_UO;_UL=_UT;_UM=_UQ.a;return __continue;case 4:var _UU=_UQ.a,_UV=_UQ.b,_UW=E(E(_UO).b);if(!_UW._){var _UX=_UW.d,_UY=_UW.e,_UZ=E(_UW.b),_V0=E(_UU),_V1=E(_UZ.a);if(_V0>=_V1){if(_V0!=_V1){return (!B(_TZ(_V0,_,_UV,_UY)))?new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_V0,_UV)),_TH,E(_8i),E(_8i))):new T4(0,_0,_0,_8i,_8i);}else{var _V2=E(_UV),_V3=E(_UZ.b);return (_V2>=_V3)?(_V2!=_V3)?(!B(_TO(_V0,_,_V2,_UY)))?new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_V0,_V2)),_TH,E(_8i),E(_8i))):new T4(0,_0,_0,_8i,_8i):new T4(0,_0,_0,_8i,_8i):(!B(_TO(_V0,_,_V2,_UX)))?new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_V0,_V2)),_TH,E(_8i),E(_8i))):new T4(0,_0,_0,_8i,_8i);}}else{return (!B(_TZ(_V0,_,_UV,_UX)))?new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_V0,_UV)),_TH,E(_8i),E(_8i))):new T4(0,_0,_0,_8i,_8i);}}else{return new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_UU,_UV)),_TH,E(_8i),E(_8i)));}break;case 5:var _V4=_UQ.a,_V5=_UQ.b,_V6=E(E(_UO).b);if(!_V6._){var _V7=_V6.d,_V8=_V6.e,_V9=E(_V6.b),_Va=E(_V4),_Vb=E(_V9.a);if(_Va>=_Vb){if(_Va!=_Vb){return (!B(_TZ(_Va,_,_V5,_V8)))?new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_Va,_V5)),_TH,E(_8i),E(_8i))):new T4(0,_0,_0,_8i,_8i);}else{var _Vc=E(_V5),_Vd=E(_V9.b);return (_Vc>=_Vd)?(_Vc!=_Vd)?(!B(_TO(_Va,_,_Vc,_V8)))?new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_Va,_Vc)),_TH,E(_8i),E(_8i))):new T4(0,_0,_0,_8i,_8i):new T4(0,_0,_0,_8i,_8i):(!B(_TO(_Va,_,_Vc,_V7)))?new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_Va,_Vc)),_TH,E(_8i),E(_8i))):new T4(0,_0,_0,_8i,_8i);}}else{return (!B(_TZ(_Va,_,_V5,_V7)))?new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_Va,_V5)),_TH,E(_8i),E(_8i))):new T4(0,_0,_0,_8i,_8i);}}else{return new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_V4,_V5)),_TH,E(_8i),E(_8i)));}break;case 6:var _Ve=B(_TI(_UQ.a));return new F(function(){return _Ub(new T2(1,new T(function(){return B(_UC(_UO,_UQ.b));}),_1M),_Ve.a,_Ve.b,_Ve.c,_Ve.d);});break;default:return new T4(0,_0,_0,_8i,_8i);}})(_UL,_UM));if(_UN!=__continue){return _UN;}}},_Vf=function(_Vg,_Vh,_Vi,_Vj,_Vk){while(1){var _Vl=E(_Vg);if(!_Vl._){return new T4(0,_Vh,_Vi,_Vj,_Vk);}else{var _Vm=E(_Vl.a),_Vn=B(_Rc(_Vh,_Vi,_Vj,_Vk,_Vm.a,_Vm.b,_Vm.c,_Vm.d));_Vg=_Vl.b;_Vh=_Vn.a;_Vi=_Vn.b;_Vj=_Vn.c;_Vk=_Vn.d;continue;}}},_Vo=function(_Vp,_Vq,_Vr,_Vs,_Vt){while(1){var _Vu=E(_Vp);if(!_Vu._){return new T4(0,_Vq,_Vr,_Vs,_Vt);}else{var _Vv=E(_Vu.a),_Vw=B(_Rc(_Vq,_Vr,_Vs,_Vt,_Vv.a,_Vv.b,_Vv.c,_Vv.d));_Vp=_Vu.b;_Vq=_Vw.a;_Vr=_Vw.b;_Vs=_Vw.c;_Vt=_Vw.d;continue;}}},_Vx=function(_Vy,_Vz){var _VA=B(_VB(_Vy,_Vz));return new T4(0,_VA.a,_VA.b,_VA.c,_VA.d);},_VB=function(_VC,_VD){while(1){var _VE=B((function(_VF,_VG){var _VH=E(_VG);switch(_VH._){case 1:var _VI=B(_TI(_VH.c)),_VJ=B(_VB(_VF,_VH.f)),_VK=B(_Rc(_VI.a,_VI.b,_VI.c,_VI.d,_VJ.a,_VJ.b,_VJ.c,_VJ.d)),_VL=B(_VB(_VF,_VH.g));return new F(function(){return _Rc(_VK.a,_VK.b,_VK.c,_VK.d,_VL.a,_VL.b,_VL.c,_VL.d);});break;case 2:var _VM=_VF;_VC=_VM;_VD=_VH.b;return __continue;case 3:var _VN=B(_TI(_VH.d)),_VO=B(_VB(_VF,_VH.f));return new F(function(){return _Rc(_VN.a,_VN.b,_VN.c,_VN.d,_VO.a,_VO.b,_VO.c,_VO.d);});break;case 4:var _VP=B(_VB(_VF,_VH.a));return new F(function(){return _Vo(new T2(1,new T(function(){return B(_Vx(_VF,_VH.b));}),_1M),_VP.a,_VP.b,_VP.c,_VP.d);});break;case 5:var _VQ=B(_UK(_VF,_VH.a)),_VR=B(_VB(_VF,_VH.b)),_VS=B(_Rc(_VQ.a,_VQ.b,_VQ.c,_VQ.d,_VR.a,_VR.b,_VR.c,_VR.d)),_VT=B(_VB(_VF,_VH.c));return new F(function(){return _Rc(_VS.a,_VS.b,_VS.c,_VS.d,_VT.a,_VT.b,_VT.c,_VT.d);});break;case 6:var _VU=B(_UK(_VF,_VH.a)),_VV=B(_VB(_VF,_VH.c)),_VW=B(_Rc(_VU.a,_VU.b,_VU.c,_VU.d,_VV.a,_VV.b,_VV.c,_VV.d)),_VX=B(_VB(_VF,_VH.d));return new F(function(){return _Rc(_VW.a,_VW.b,_VW.c,_VW.d,_VX.a,_VX.b,_VX.c,_VX.d);});break;case 8:var _VY=B(_VB(_VF,_VH.b));return new F(function(){return _Vf(new T2(1,new T(function(){return B(_Vx(_VF,_VH.c));}),_1M),_VY.a,_VY.b,_VY.c,_VY.d);});break;case 9:var _VM=_VF;_VC=_VM;_VD=_VH.b;return __continue;case 10:var _VM=_VF;_VC=_VM;_VD=_VH.b;return __continue;case 11:var _VZ=B(_UK(_VF,_VH.b)),_W0=B(_VB(_VF,_VH.c));return new F(function(){return _Rc(_VZ.a,_VZ.b,_VZ.c,_VZ.d,_W0.a,_W0.b,_W0.c,_W0.d);});break;default:return new T4(0,_0,_0,_8i,_8i);}})(_VC,_VD));if(_VE!=__continue){return _VE;}}},_W1=function(_W2,_W3){return E(_W2)!=E(_W3);},_W4=new T2(0,_GY,_W1),_W5=function(_W6,_W7){var _W8=E(_W6),_W9=E(_W7);return (_W8>_W9)?E(_W8):E(_W9);},_Wa=function(_Wb,_Wc){var _Wd=E(_Wb),_We=E(_Wc);return (_Wd>_We)?E(_We):E(_Wd);},_Wf={_:0,a:_W4,b:_IF,c:_Hg,d:_HB,e:_HW,f:_Ih,g:_W5,h:_Wa},_Wg=function(_Wh,_Wi,_Wj,_Wk,_Wl){while(1){var _Wm=E(_Wl);if(!_Wm._){var _Wn=_Wm.c,_Wo=_Wm.d,_Wp=E(_Wm.b),_Wq=E(_Wp.a);if(_Wh>=_Wq){if(_Wh!=_Wq){_Wi=_;_Wl=_Wo;continue;}else{var _Wr=E(_Wp.b);if(_Wj>=_Wr){if(_Wj!=_Wr){_Wi=_;_Wl=_Wo;continue;}else{var _Ws=E(_Wp.c);if(_Wk>=_Ws){if(_Wk!=_Ws){_Wi=_;_Wl=_Wo;continue;}else{return true;}}else{_Wi=_;_Wl=_Wn;continue;}}}else{_Wi=_;_Wl=_Wn;continue;}}}else{_Wi=_;_Wl=_Wn;continue;}}else{return false;}}},_Wt=function(_Wu,_Wv,_Ww,_Wx,_Wy){while(1){var _Wz=E(_Wy);if(!_Wz._){var _WA=_Wz.c,_WB=_Wz.d,_WC=E(_Wz.b),_WD=E(_WC.a);if(_Wu>=_WD){if(_Wu!=_WD){_Wv=_;_Wy=_WB;continue;}else{var _WE=E(_WC.b);if(_Ww>=_WE){if(_Ww!=_WE){_Wv=_;_Wy=_WB;continue;}else{var _WF=E(_Wx),_WG=E(_WC.c);if(_WF>=_WG){if(_WF!=_WG){return new F(function(){return _Wg(_Wu,_,_Ww,_WF,_WB);});}else{return true;}}else{return new F(function(){return _Wg(_Wu,_,_Ww,_WF,_WA);});}}}else{_Wv=_;_Wy=_WA;continue;}}}else{_Wv=_;_Wy=_WA;continue;}}else{return false;}}},_WH=function(_WI,_WJ,_WK,_WL,_WM){while(1){var _WN=E(_WM);if(!_WN._){var _WO=_WN.c,_WP=_WN.d,_WQ=E(_WN.b),_WR=E(_WQ.a);if(_WI>=_WR){if(_WI!=_WR){_WJ=_;_WM=_WP;continue;}else{var _WS=E(_WK),_WT=E(_WQ.b);if(_WS>=_WT){if(_WS!=_WT){return new F(function(){return _Wt(_WI,_,_WS,_WL,_WP);});}else{var _WU=E(_WL),_WV=E(_WQ.c);if(_WU>=_WV){if(_WU!=_WV){return new F(function(){return _Wg(_WI,_,_WS,_WU,_WP);});}else{return true;}}else{return new F(function(){return _Wg(_WI,_,_WS,_WU,_WO);});}}}else{return new F(function(){return _Wt(_WI,_,_WS,_WL,_WO);});}}}else{_WJ=_;_WM=_WO;continue;}}else{return false;}}},_WW=function(_WX,_WY,_WZ,_X0){var _X1=E(_X0);if(!_X1._){var _X2=_X1.c,_X3=_X1.d,_X4=E(_X1.b),_X5=E(_WX),_X6=E(_X4.a);if(_X5>=_X6){if(_X5!=_X6){return new F(function(){return _WH(_X5,_,_WY,_WZ,_X3);});}else{var _X7=E(_WY),_X8=E(_X4.b);if(_X7>=_X8){if(_X7!=_X8){return new F(function(){return _Wt(_X5,_,_X7,_WZ,_X3);});}else{var _X9=E(_WZ),_Xa=E(_X4.c);if(_X9>=_Xa){if(_X9!=_Xa){return new F(function(){return _Wg(_X5,_,_X7,_X9,_X3);});}else{return true;}}else{return new F(function(){return _Wg(_X5,_,_X7,_X9,_X2);});}}}else{return new F(function(){return _Wt(_X5,_,_X7,_WZ,_X2);});}}}else{return new F(function(){return _WH(_X5,_,_WY,_WZ,_X2);});}}else{return false;}},_Xb=function(_Xc,_Xd,_Xe,_Xf,_Xg){var _Xh=E(_Xg);if(!_Xh._){if(E(_Xh.b)>E(_Xd)){return false;}else{return new F(function(){return _WW(_Xe,_Xf,_Xh.a,E(_Xc).b);});}}else{return false;}},_Xi=function(_Xj,_Xk,_Xl,_Xm,_Xn){var _Xo=E(_Xn);if(!_Xo._){var _Xp=new T(function(){var _Xq=B(_Xi(_Xo.a,_Xo.b,_Xo.c,_Xo.d,_Xo.e));return new T2(0,_Xq.a,_Xq.b);});return new T2(0,new T(function(){return E(E(_Xp).a);}),new T(function(){return B(_9e(_Xk,_Xl,_Xm,E(_Xp).b));}));}else{return new T2(0,new T2(0,_Xk,_Xl),_Xm);}},_Xr=function(_Xs,_Xt,_Xu,_Xv,_Xw){var _Xx=E(_Xv);if(!_Xx._){var _Xy=new T(function(){var _Xz=B(_Xr(_Xx.a,_Xx.b,_Xx.c,_Xx.d,_Xx.e));return new T2(0,_Xz.a,_Xz.b);});return new T2(0,new T(function(){return E(E(_Xy).a);}),new T(function(){return B(_8n(_Xt,_Xu,E(_Xy).b,_Xw));}));}else{return new T2(0,new T2(0,_Xt,_Xu),_Xw);}},_XA=function(_XB,_XC){var _XD=E(_XB);if(!_XD._){var _XE=_XD.a,_XF=E(_XC);if(!_XF._){var _XG=_XF.a;if(_XE<=_XG){var _XH=B(_Xr(_XG,_XF.b,_XF.c,_XF.d,_XF.e)),_XI=E(_XH.a);return new F(function(){return _9e(_XI.a,_XI.b,_XD,_XH.b);});}else{var _XJ=B(_Xi(_XE,_XD.b,_XD.c,_XD.d,_XD.e)),_XK=E(_XJ.a);return new F(function(){return _8n(_XK.a,_XK.b,_XJ.b,_XF);});}}else{return E(_XD);}}else{return E(_XC);}},_XL=function(_XM,_XN,_XO,_XP,_XQ,_XR){var _XS=E(_XM);if(!_XS._){var _XT=_XS.a,_XU=_XS.b,_XV=_XS.c,_XW=_XS.d,_XX=_XS.e;if((imul(3,_XT)|0)>=_XN){if((imul(3,_XN)|0)>=_XT){return new F(function(){return _XA(_XS,new T5(0,_XN,E(_XO),_XP,E(_XQ),E(_XR)));});}else{return new F(function(){return _8n(_XU,_XV,_XW,B(_XL(_XX,_XN,_XO,_XP,_XQ,_XR)));});}}else{return new F(function(){return _9e(_XO,_XP,B(_XY(_XT,_XU,_XV,_XW,_XX,_XQ)),_XR);});}}else{return new T5(0,_XN,E(_XO),_XP,E(_XQ),E(_XR));}},_XY=function(_XZ,_Y0,_Y1,_Y2,_Y3,_Y4){var _Y5=E(_Y4);if(!_Y5._){var _Y6=_Y5.a,_Y7=_Y5.b,_Y8=_Y5.c,_Y9=_Y5.d,_Ya=_Y5.e;if((imul(3,_XZ)|0)>=_Y6){if((imul(3,_Y6)|0)>=_XZ){return new F(function(){return _XA(new T5(0,_XZ,E(_Y0),_Y1,E(_Y2),E(_Y3)),_Y5);});}else{return new F(function(){return _8n(_Y0,_Y1,_Y2,B(_XL(_Y3,_Y6,_Y7,_Y8,_Y9,_Ya)));});}}else{return new F(function(){return _9e(_Y7,_Y8,B(_XY(_XZ,_Y0,_Y1,_Y2,_Y3,_Y9)),_Ya);});}}else{return new T5(0,_XZ,E(_Y0),_Y1,E(_Y2),E(_Y3));}},_Yb=function(_Yc,_Yd){var _Ye=E(_Yc);if(!_Ye._){var _Yf=_Ye.a,_Yg=_Ye.b,_Yh=_Ye.c,_Yi=_Ye.d,_Yj=_Ye.e,_Yk=E(_Yd);if(!_Yk._){var _Yl=_Yk.a,_Ym=_Yk.b,_Yn=_Yk.c,_Yo=_Yk.d,_Yp=_Yk.e;if((imul(3,_Yf)|0)>=_Yl){if((imul(3,_Yl)|0)>=_Yf){return new F(function(){return _XA(_Ye,_Yk);});}else{return new F(function(){return _8n(_Yg,_Yh,_Yi,B(_XL(_Yj,_Yl,_Ym,_Yn,_Yo,_Yp)));});}}else{return new F(function(){return _9e(_Ym,_Yn,B(_XY(_Yf,_Yg,_Yh,_Yi,_Yj,_Yo)),_Yp);});}}else{return E(_Ye);}}else{return E(_Yd);}},_Yq=function(_Yr,_Ys){var _Yt=E(_Ys);if(!_Yt._){var _Yu=_Yt.b,_Yv=_Yt.c,_Yw=B(_Yq(_Yr,_Yt.d)),_Yx=_Yw.a,_Yy=_Yw.b,_Yz=B(_Yq(_Yr,_Yt.e)),_YA=_Yz.a,_YB=_Yz.b;return (!B(A2(_Yr,_Yu,_Yv)))?new T2(0,B(_Yb(_Yx,_YA)),B(_ay(_Yu,_Yv,_Yy,_YB))):new T2(0,B(_ay(_Yu,_Yv,_Yx,_YA)),B(_Yb(_Yy,_YB)));}else{return new T2(0,_8i,_8i);}},_YC=function(_YD,_YE){while(1){var _YF=B((function(_YG,_YH){var _YI=E(_YH);if(!_YI._){var _YJ=_YI.e,_YK=new T(function(){var _YL=E(_YI.c),_YM=E(_YL.b);if(!_YM._){return new T2(1,new T3(5,_YI.b,_YL.a,_YM.a),new T(function(){return B(_YC(_YG,_YJ));}));}else{return B(_YC(_YG,_YJ));}},1);_YD=_YK;_YE=_YI.d;return __continue;}else{return E(_YG);}})(_YD,_YE));if(_YF!=__continue){return _YF;}}},_YN=function(_YO,_YP){var _YQ=E(_YP);return (_YQ._==0)?new T5(0,_YQ.a,E(_YQ.b),new T(function(){return B(A1(_YO,_YQ.c));}),E(B(_YN(_YO,_YQ.d))),E(B(_YN(_YO,_YQ.e)))):new T0(1);},_YR=new T0(1),_YS=function(_YT){var _YU=E(_YT),_YV=E(_YU.b);return new T2(0,_YU.a,_YR);},_YW=function(_YX,_YY,_YZ){var _Z0=new T(function(){var _Z1=new T(function(){return E(E(_YZ).b);}),_Z2=B(_Yq(function(_Z3,_Z4){var _Z5=E(_Z4);return new F(function(){return _Xb(_YX,_Z1,_Z3,_Z5.a,_Z5.b);});},_YY));return new T2(0,_Z2.a,_Z2.b);}),_Z6=new T(function(){return E(E(_Z0).a);});return new T2(0,new T(function(){var _Z7=B(_YN(_YS,_Z6));if(!_Z7._){var _Z8=E(E(_Z0).b);if(!_Z8._){return B(_Pv(_Wf,_O8,_O8,_Z7.a,_Z7.b,_Z7.c,_Z7.d,_Z7.e,_Z8.a,_Z8.b,_Z8.c,_Z8.d,_Z8.e));}else{return E(_Z7);}}else{return E(E(_Z0).b);}}),new T(function(){return B(_YC(_1M,_Z6));}));},_Z9=function(_Za,_Zb,_Zc,_Zd){while(1){var _Ze=E(_Zd);if(!_Ze._){var _Zf=_Ze.d,_Zg=_Ze.e,_Zh=E(_Ze.b),_Zi=E(_Zh.a);if(_Za>=_Zi){if(_Za!=_Zi){_Zb=_;_Zd=_Zg;continue;}else{var _Zj=E(_Zh.b);if(_Zc>=_Zj){if(_Zc!=_Zj){_Zb=_;_Zd=_Zg;continue;}else{return true;}}else{_Zb=_;_Zd=_Zf;continue;}}}else{_Zb=_;_Zd=_Zf;continue;}}else{return false;}}},_Zk=function(_Zl,_Zm,_Zn,_Zo){while(1){var _Zp=E(_Zo);if(!_Zp._){var _Zq=_Zp.d,_Zr=_Zp.e,_Zs=E(_Zp.b),_Zt=E(_Zs.a);if(_Zl>=_Zt){if(_Zl!=_Zt){_Zm=_;_Zo=_Zr;continue;}else{var _Zu=E(_Zn),_Zv=E(_Zs.b);if(_Zu>=_Zv){if(_Zu!=_Zv){return new F(function(){return _Z9(_Zl,_,_Zu,_Zr);});}else{return true;}}else{return new F(function(){return _Z9(_Zl,_,_Zu,_Zq);});}}}else{_Zm=_;_Zo=_Zq;continue;}}else{return false;}}},_Zw=function(_Zx,_Zy,_Zz,_ZA,_ZB){var _ZC=E(_ZB);if(!_ZC._){var _ZD=_ZC.c,_ZE=_ZC.d,_ZF=_ZC.e,_ZG=E(_ZC.b),_ZH=E(_ZG.a);if(_Zx>=_ZH){if(_Zx!=_ZH){return new F(function(){return _8n(_ZG,_ZD,_ZE,B(_Zw(_Zx,_,_Zz,_ZA,_ZF)));});}else{var _ZI=E(_ZG.b);if(_Zz>=_ZI){if(_Zz!=_ZI){return new F(function(){return _8n(_ZG,_ZD,_ZE,B(_Zw(_Zx,_,_Zz,_ZA,_ZF)));});}else{return new T5(0,_ZC.a,E(new T2(0,_Zx,_Zz)),_ZA,E(_ZE),E(_ZF));}}else{return new F(function(){return _9e(_ZG,_ZD,B(_Zw(_Zx,_,_Zz,_ZA,_ZE)),_ZF);});}}}else{return new F(function(){return _9e(_ZG,_ZD,B(_Zw(_Zx,_,_Zz,_ZA,_ZE)),_ZF);});}}else{return new T5(0,1,E(new T2(0,_Zx,_Zz)),_ZA,E(_8i),E(_8i));}},_ZJ=function(_ZK,_ZL,_ZM,_ZN,_ZO){var _ZP=E(_ZO);if(!_ZP._){var _ZQ=_ZP.c,_ZR=_ZP.d,_ZS=_ZP.e,_ZT=E(_ZP.b),_ZU=E(_ZT.a);if(_ZK>=_ZU){if(_ZK!=_ZU){return new F(function(){return _8n(_ZT,_ZQ,_ZR,B(_ZJ(_ZK,_,_ZM,_ZN,_ZS)));});}else{var _ZV=E(_ZM),_ZW=E(_ZT.b);if(_ZV>=_ZW){if(_ZV!=_ZW){return new F(function(){return _8n(_ZT,_ZQ,_ZR,B(_Zw(_ZK,_,_ZV,_ZN,_ZS)));});}else{return new T5(0,_ZP.a,E(new T2(0,_ZK,_ZV)),_ZN,E(_ZR),E(_ZS));}}else{return new F(function(){return _9e(_ZT,_ZQ,B(_Zw(_ZK,_,_ZV,_ZN,_ZR)),_ZS);});}}}else{return new F(function(){return _9e(_ZT,_ZQ,B(_ZJ(_ZK,_,_ZM,_ZN,_ZR)),_ZS);});}}else{return new T5(0,1,E(new T2(0,_ZK,_ZM)),_ZN,E(_8i),E(_8i));}},_ZX=function(_ZY,_ZZ,_100,_101){var _102=E(_101);if(!_102._){var _103=_102.c,_104=_102.d,_105=_102.e,_106=E(_102.b),_107=E(_ZY),_108=E(_106.a);if(_107>=_108){if(_107!=_108){return new F(function(){return _8n(_106,_103,_104,B(_ZJ(_107,_,_ZZ,_100,_105)));});}else{var _109=E(_ZZ),_10a=E(_106.b);if(_109>=_10a){if(_109!=_10a){return new F(function(){return _8n(_106,_103,_104,B(_Zw(_107,_,_109,_100,_105)));});}else{return new T5(0,_102.a,E(new T2(0,_107,_109)),_100,E(_104),E(_105));}}else{return new F(function(){return _9e(_106,_103,B(_Zw(_107,_,_109,_100,_104)),_105);});}}}else{return new F(function(){return _9e(_106,_103,B(_ZJ(_107,_,_ZZ,_100,_104)),_105);});}}else{return new T5(0,1,E(new T2(0,_ZY,_ZZ)),_100,E(_8i),E(_8i));}},_10b=function(_10c,_10d,_10e){while(1){var _10f=B((function(_10g,_10h,_10i){var _10j=E(_10i);if(!_10j._){var _10k=_10j.c,_10l=_10j.e,_10m=E(_10j.b),_10n=_10m.a,_10o=_10m.b,_10p=B(_10b(_10g,_10h,_10j.d)),_10q=_10p.a,_10r=_10p.b,_10s=function(_10t){return new F(function(){return _10b(new T(function(){return B(_ZX(_10n,_10o,_10k,_10q));}),new T2(1,new T3(7,_10n,_10o,_10k),_10r),_10l);});},_10u=E(_10q);if(!_10u._){var _10v=_10u.d,_10w=_10u.e,_10x=E(_10u.b),_10y=E(_10n),_10z=E(_10x.a);if(_10y>=_10z){if(_10y!=_10z){if(!B(_Zk(_10y,_,_10o,_10w))){return new F(function(){return _10s(_);});}else{_10c=_10u;_10d=_10r;_10e=_10l;return __continue;}}else{var _10A=E(_10o),_10B=E(_10x.b);if(_10A>=_10B){if(_10A!=_10B){if(!B(_Z9(_10y,_,_10A,_10w))){return new F(function(){return _10s(_);});}else{_10c=_10u;_10d=_10r;_10e=_10l;return __continue;}}else{_10c=_10u;_10d=_10r;_10e=_10l;return __continue;}}else{if(!B(_Z9(_10y,_,_10A,_10v))){return new F(function(){return _10s(_);});}else{_10c=_10u;_10d=_10r;_10e=_10l;return __continue;}}}}else{if(!B(_Zk(_10y,_,_10o,_10v))){return new F(function(){return _10s(_);});}else{_10c=_10u;_10d=_10r;_10e=_10l;return __continue;}}}else{return new F(function(){return _10s(_);});}}else{return new T2(0,_10g,_10h);}})(_10c,_10d,_10e));if(_10f!=__continue){return _10f;}}},_10C=function(_10D,_10E){while(1){var _10F=E(_10D);switch(_10F._){case 0:var _10G=E(_10E);if(!_10G._){return new F(function(){return _GY(_10F.a,_10G.a);});}else{return false;}break;case 1:var _10H=E(_10E);if(_10H._==1){if(!B(_10C(_10F.a,_10H.a))){return false;}else{_10D=_10F.b;_10E=_10H.b;continue;}}else{return false;}break;case 2:var _10I=E(_10E);if(_10I._==2){return new F(function(){return _GY(_10F.a,_10I.a);});}else{return false;}break;default:var _10J=E(_10E);if(_10J._==3){if(E(_10F.a)!=E(_10J.a)){return false;}else{if(E(_10F.b)!=E(_10J.b)){return false;}else{_10D=_10F.c;_10E=_10J.c;continue;}}}else{return false;}}}},_10K=function(_10L,_10M){while(1){var _10N=E(_10L);switch(_10N._){case 0:var _10O=E(_10M);if(!_10O._){return new F(function(){return _GY(_10N.a,_10O.a);});}else{return false;}break;case 1:var _10P=E(_10M);if(_10P._==1){if(!B(_10K(_10N.a,_10P.a))){return false;}else{_10L=_10N.b;_10M=_10P.b;continue;}}else{return false;}break;case 2:var _10Q=E(_10M);if(_10Q._==2){if(!B(_10K(_10N.a,_10Q.a))){return false;}else{_10L=_10N.b;_10M=_10Q.b;continue;}}else{return false;}break;case 3:var _10R=E(_10M);if(_10R._==3){_10L=_10N.a;_10M=_10R.a;continue;}else{return false;}break;case 4:var _10S=E(_10M);if(_10S._==4){if(E(_10N.a)!=E(_10S.a)){return false;}else{if(E(_10N.b)!=E(_10S.b)){return false;}else{return new F(function(){return _GY(_10N.c,_10S.c);});}}}else{return false;}break;case 5:var _10T=E(_10M);if(_10T._==5){if(E(_10N.a)!=E(_10T.a)){return false;}else{return new F(function(){return _GY(_10N.b,_10T.b);});}}else{return false;}break;case 6:var _10U=E(_10M);if(_10U._==6){if(!B(_10C(_10N.a,_10U.a))){return false;}else{return new F(function(){return _10C(_10N.b,_10U.b);});}}else{return false;}break;case 7:return (E(_10M)._==7)?true:false;case 8:return (E(_10M)._==8)?true:false;default:var _10V=E(_10M);if(_10V._==9){return new F(function(){return _GY(_10N.a,_10V.a);});}else{return false;}}}},_10W=function(_10X,_10Y){while(1){var _10Z=E(_10X);switch(_10Z._){case 0:return (E(_10Y)._==0)?true:false;case 1:var _110=E(_10Y);if(_110._==1){if(E(_10Z.a)!=E(_110.a)){return false;}else{if(E(_10Z.b)!=E(_110.b)){return false;}else{if(!B(_10C(_10Z.c,_110.c))){return false;}else{if(E(_10Z.d)!=E(_110.d)){return false;}else{if(E(_10Z.e)!=E(_110.e)){return false;}else{if(!B(_10W(_10Z.f,_110.f))){return false;}else{_10X=_10Z.g;_10Y=_110.g;continue;}}}}}}}else{return false;}break;case 2:var _111=E(_10Y);if(_111._==2){if(E(_10Z.a)!=E(_111.a)){return false;}else{_10X=_10Z.b;_10Y=_111.b;continue;}}else{return false;}break;case 3:var _112=E(_10Y);if(_112._==3){if(E(_10Z.a)!=E(_112.a)){return false;}else{if(E(_10Z.b)!=E(_112.b)){return false;}else{if(E(_10Z.c)!=E(_112.c)){return false;}else{if(!B(_10C(_10Z.d,_112.d))){return false;}else{if(E(_10Z.e)!=E(_112.e)){return false;}else{_10X=_10Z.f;_10Y=_112.f;continue;}}}}}}else{return false;}break;case 4:var _113=E(_10Y);if(_113._==4){if(!B(_10W(_10Z.a,_113.a))){return false;}else{_10X=_10Z.b;_10Y=_113.b;continue;}}else{return false;}break;case 5:var _114=E(_10Y);if(_114._==5){if(!B(_10K(_10Z.a,_114.a))){return false;}else{if(!B(_10W(_10Z.b,_114.b))){return false;}else{_10X=_10Z.c;_10Y=_114.c;continue;}}}else{return false;}break;case 6:var _115=E(_10Y);if(_115._==6){if(!B(_10K(_10Z.a,_115.a))){return false;}else{if(E(_10Z.b)!=E(_115.b)){return false;}else{if(!B(_10W(_10Z.c,_115.c))){return false;}else{_10X=_10Z.d;_10Y=_115.d;continue;}}}}else{return false;}break;case 7:var _116=E(_10Y);if(_116._==7){return new F(function(){return _GY(_10Z.a,_116.a);});}else{return false;}break;case 8:var _117=E(_10Y);if(_117._==8){if(E(_10Z.a)!=E(_117.a)){return false;}else{if(!B(_10W(_10Z.b,_117.b))){return false;}else{_10X=_10Z.c;_10Y=_117.c;continue;}}}else{return false;}break;case 9:var _118=E(_10Y);if(_118._==9){if(E(_10Z.a)!=E(_118.a)){return false;}else{_10X=_10Z.b;_10Y=_118.b;continue;}}else{return false;}break;case 10:var _119=E(_10Y);if(_119._==10){if(E(_10Z.a)!=E(_119.a)){return false;}else{_10X=_10Z.b;_10Y=_119.b;continue;}}else{return false;}break;default:var _11a=E(_10Y);if(_11a._==11){if(E(_10Z.a)!=E(_11a.a)){return false;}else{if(!B(_10K(_10Z.b,_11a.b))){return false;}else{_10X=_10Z.c;_10Y=_11a.c;continue;}}}else{return false;}}}},_11b=new T2(0,_GY,_W1),_11c=function(_11d,_11e,_11f,_11g,_11h,_11i){return (!B(A3(_pR,_11d,_11f,_11h)))?true:(!B(A3(_pR,_11e,_11g,_11i)))?true:false;},_11j=function(_11k,_11l,_11m,_11n){var _11o=E(_11m),_11p=E(_11n);return new F(function(){return _11c(_11k,_11l,_11o.a,_11o.b,_11p.a,_11p.b);});},_11q=function(_11r,_11s,_11t,_11u,_11v,_11w){if(!B(A3(_pR,_11r,_11t,_11v))){return false;}else{return new F(function(){return A3(_pR,_11s,_11u,_11w);});}},_11x=function(_11y,_11z,_11A,_11B){var _11C=E(_11A),_11D=E(_11B);return new F(function(){return _11q(_11y,_11z,_11C.a,_11C.b,_11D.a,_11D.b);});},_11E=function(_11F,_11G){return new T2(0,function(_11H,_11I){return new F(function(){return _11x(_11F,_11G,_11H,_11I);});},function(_11H,_11I){return new F(function(){return _11j(_11F,_11G,_11H,_11I);});});},_11J=function(_11K,_11L,_11M){while(1){var _11N=E(_11L);if(!_11N._){return (E(_11M)._==0)?true:false;}else{var _11O=E(_11M);if(!_11O._){return false;}else{if(!B(A3(_pR,_11K,_11N.a,_11O.a))){return false;}else{_11L=_11N.b;_11M=_11O.b;continue;}}}}},_11P=function(_11Q,_11R){var _11S=new T(function(){return B(_11E(_11Q,_11R));}),_11T=function(_11U,_11V){var _11W=function(_11X){var _11Y=function(_11Z){if(_11X!=_11Z){return false;}else{return new F(function(){return _11J(_11S,B(_hc(_1M,_11U)),B(_hc(_1M,_11V)));});}},_120=E(_11V);if(!_120._){return new F(function(){return _11Y(_120.a);});}else{return new F(function(){return _11Y(0);});}},_121=E(_11U);if(!_121._){return new F(function(){return _11W(_121.a);});}else{return new F(function(){return _11W(0);});}};return E(_11T);},_122=new T(function(){return B(_11P(_JH,_11b));}),_123=function(_124,_125){var _126=E(_124);if(!_126._){var _127=E(_125);if(!_127._){if(E(_126.a)!=E(_127.a)){return false;}else{return new F(function(){return _GY(_126.b,_127.b);});}}else{return false;}}else{return (E(_125)._==0)?false:true;}},_128=function(_129,_12a,_12b,_12c){if(_129!=_12b){return false;}else{return new F(function(){return _123(_12a,_12c);});}},_12d=function(_12e,_12f){var _12g=E(_12e),_12h=E(_12f);return new F(function(){return _128(E(_12g.a),_12g.b,E(_12h.a),_12h.b);});},_12i=function(_12j,_12k,_12l,_12m){if(_12j!=_12l){return true;}else{var _12n=E(_12k);if(!_12n._){var _12o=E(_12m);return (_12o._==0)?(E(_12n.a)!=E(_12o.a))?true:(E(_12n.b)!=E(_12o.b))?true:false:true;}else{return (E(_12m)._==0)?true:false;}}},_12p=function(_12q,_12r){var _12s=E(_12q),_12t=E(_12r);return new F(function(){return _12i(E(_12s.a),_12s.b,E(_12t.a),_12t.b);});},_12u=new T2(0,_12d,_12p),_12v=new T(function(){return B(_11P(_W4,_12u));}),_12w=new T2(0,_GY,_W1),_12x={_:0,a:_12w,b:_IF,c:_Hg,d:_HB,e:_HW,f:_Ih,g:_W5,h:_Wa},_12y=new T2(0,_GY,_W1),_12z={_:0,a:_12y,b:_IF,c:_Hg,d:_HB,e:_HW,f:_Ih,g:_W5,h:_Wa},_12A=function(_12B,_12C,_12D,_12E){while(1){var _12F=E(_12E);if(!_12F._){var _12G=_12F.d,_12H=_12F.e,_12I=E(_12F.b),_12J=E(_12I.a);if(_12B>=_12J){if(_12B!=_12J){_12C=_;_12E=_12H;continue;}else{var _12K=E(_12I.b);if(_12D>=_12K){if(_12D!=_12K){_12C=_;_12E=_12H;continue;}else{return new T1(1,_12F.c);}}else{_12C=_;_12E=_12G;continue;}}}else{_12C=_;_12E=_12G;continue;}}else{return __Z;}}},_12L=function(_12M,_12N,_12O,_12P){while(1){var _12Q=E(_12P);if(!_12Q._){var _12R=_12Q.d,_12S=_12Q.e,_12T=E(_12Q.b),_12U=E(_12T.a);if(_12M>=_12U){if(_12M!=_12U){_12N=_;_12P=_12S;continue;}else{var _12V=E(_12O),_12W=E(_12T.b);if(_12V>=_12W){if(_12V!=_12W){return new F(function(){return _12A(_12M,_,_12V,_12S);});}else{return new T1(1,_12Q.c);}}else{return new F(function(){return _12A(_12M,_,_12V,_12R);});}}}else{_12N=_;_12P=_12R;continue;}}else{return __Z;}}},_12X=function(_12Y,_12Z,_130,_131,_132){while(1){var _133=E(_132);if(!_133._){var _134=_133.c,_135=_133.d,_136=E(_133.b),_137=E(_12Y),_138=E(_136.a);if(_137>=_138){if(_137!=_138){_12Y=_137;_132=_135;continue;}else{var _139=E(_12Z),_13a=E(_136.b);if(_139>=_13a){if(_139!=_13a){_12Y=_137;_12Z=_139;_132=_135;continue;}else{var _13b=E(_130),_13c=E(_136.c);if(_13b>=_13c){if(_13b!=_13c){_12Y=_137;_12Z=_139;_130=_13b;_132=_135;continue;}else{var _13d=E(_136.d);if(_131>=_13d){if(_131!=_13d){_12Y=_137;_12Z=_139;_130=_13b;_132=_135;continue;}else{return true;}}else{_12Y=_137;_12Z=_139;_130=_13b;_132=_134;continue;}}}else{_12Y=_137;_12Z=_139;_130=_13b;_132=_134;continue;}}}else{_12Y=_137;_12Z=_139;_132=_134;continue;}}}else{_12Y=_137;_132=_134;continue;}}else{return false;}}},_13e=function(_13f,_13g){var _13h=E(_13g);if(!_13h._){var _13i=_13h.c,_13j=_13h.d,_13k=_13h.e,_13l=E(_13h.b);if(_13f>=_13l){if(_13f!=_13l){return new F(function(){return _9e(_13l,_13i,_13j,B(_13e(_13f,_13k)));});}else{return new F(function(){return _XA(_13j,_13k);});}}else{return new F(function(){return _8n(_13l,_13i,B(_13e(_13f,_13j)),_13k);});}}else{return new T0(1);}},_13m=function(_13n,_13o){var _13p=E(_13o);if(!_13p._){var _13q=_13p.c,_13r=_13p.d,_13s=_13p.e,_13t=E(_13p.b);if(_13n>=_13t){if(_13n!=_13t){return new F(function(){return _9e(_13t,_13q,_13r,B(_13m(_13n,_13s)));});}else{return new F(function(){return _XA(_13r,_13s);});}}else{return new F(function(){return _8n(_13t,_13q,B(_13m(_13n,_13r)),_13s);});}}else{return new T0(1);}},_13u=function(_13v,_13w,_13x){var _13y=E(_13x);if(!_13y._){var _13z=_13y.c,_13A=_13y.d,_13B=_13y.e,_13C=E(_13y.b);if(_13v>=_13C){if(_13v!=_13C){return new F(function(){return _8n(_13C,_13z,_13A,B(_13u(_13v,_13w,_13B)));});}else{return new T5(0,_13y.a,E(_13v),_13w,E(_13A),E(_13B));}}else{return new F(function(){return _9e(_13C,_13z,B(_13u(_13v,_13w,_13A)),_13B);});}}else{return new T5(0,1,E(_13v),_13w,E(_8i),E(_8i));}},_13D=function(_13E,_13F,_13G){var _13H=E(_13G);if(!_13H._){var _13I=_13H.c,_13J=_13H.d,_13K=_13H.e,_13L=E(_13H.b);if(_13E>=_13L){if(_13E!=_13L){return new F(function(){return _8n(_13L,_13I,_13J,B(_13D(_13E,_13F,_13K)));});}else{return new T5(0,_13H.a,E(_13E),_13F,E(_13J),E(_13K));}}else{return new F(function(){return _9e(_13L,_13I,B(_13D(_13E,_13F,_13J)),_13K);});}}else{return new T5(0,1,E(_13E),_13F,E(_8i),E(_8i));}},_13M=function(_13N,_13O){return E(_13N)+E(_13O)|0;},_13P=function(_13Q,_13R,_13S){var _13T=function(_13U,_13V){while(1){var _13W=B((function(_13X,_13Y){var _13Z=E(_13Y);if(!_13Z._){var _140=new T(function(){return B(_13T(_13X,_13Z.e));}),_141=function(_142){var _143=E(_13Z.c),_144=E(_143.b);if(!_144._){if(E(_143.a)!=E(_13R)){return new F(function(){return A1(_140,_142);});}else{if(E(_144.b)>E(_13S)){return new F(function(){return A1(_140,new T(function(){return B(_13M(_142,_144.a));}));});}else{return new F(function(){return A1(_140,_142);});}}}else{return new F(function(){return A1(_140,_142);});}};_13U=_141;_13V=_13Z.d;return __continue;}else{return E(_13X);}})(_13U,_13V));if(_13W!=__continue){return _13W;}}};return new F(function(){return A3(_13T,_na,_13Q,_Rt);});},_145=function(_146,_147,_148,_149){var _14a=E(_147),_14b=E(_149);if(!_14b._){var _14c=_14b.b,_14d=_14b.c,_14e=_14b.d,_14f=_14b.e;switch(B(A3(_Oa,_146,_14a,_14c))){case 0:return new F(function(){return _9e(_14c,_14d,B(_145(_146,_14a,_148,_14e)),_14f);});break;case 1:return new T5(0,_14b.a,E(_14a),_148,E(_14e),E(_14f));default:return new F(function(){return _8n(_14c,_14d,_14e,B(_145(_146,_14a,_148,_14f)));});}}else{return new T5(0,1,E(_14a),_148,E(_8i),E(_8i));}},_14g=function(_14h,_14i,_14j,_14k){return new F(function(){return _145(_14h,_14i,_14j,_14k);});},_14l=function(_14m,_14n,_14o){var _14p=function(_14q,_14r){while(1){var _14s=E(_14q),_14t=E(_14r);if(!_14t._){switch(B(A3(_Oa,_14m,_14s,_14t.b))){case 0:_14q=_14s;_14r=_14t.d;continue;case 1:return new T1(1,_14t.c);default:_14q=_14s;_14r=_14t.e;continue;}}else{return __Z;}}};return new F(function(){return _14p(_14n,_14o);});},_14u=function(_14v,_14w,_14x,_14y){var _14z=B(_14l(_14v,_14w,_14y));return (_14z._==0)?new T(function(){return B(_14g(_14v,_14w,new T2(1,_14x,_1M),_14y));}):new T(function(){return B(_14g(_14v,_14w,new T2(1,_14x,_14z.a),_14y));});},_14A=function(_14B,_14C){while(1){var _14D=E(_14C);if(!_14D._){var _14E=E(_14D.b);if(_14B>=_14E){if(_14B!=_14E){_14C=_14D.e;continue;}else{return new T1(1,_14D.c);}}else{_14C=_14D.d;continue;}}else{return __Z;}}},_14F=function(_14G,_14H){while(1){var _14I=E(_14H);if(!_14I._){var _14J=E(_14I.b);if(_14G>=_14J){if(_14G!=_14J){_14H=_14I.e;continue;}else{return new T1(1,_14I.c);}}else{_14H=_14I.d;continue;}}else{return __Z;}}},_14K=__Z,_14L=new T(function(){return B(unCStr("attempt to discount when insufficient cash available"));}),_14M=new T(function(){return B(err(_14L));}),_14N=function(_14O,_14P){var _14Q=E(_14P);if(!_14Q._){return (E(_14O)==0)?__Z:E(_14M);}else{var _14R=_14Q.b,_14S=E(_14Q.a),_14T=_14S.a,_14U=E(_14S.b),_14V=_14U.a,_14W=E(_14U.b);if(!_14W._){var _14X=_14W.b,_14Y=E(_14W.a);return (_14O>_14Y)?(_14Y>=_14O)?E(_14R):new T2(1,new T2(0,_14T,new T2(0,_14V,new T2(0,_Rt,_14X))),new T(function(){return B(_14N(_14O-_14Y|0,_14R));})):new T2(1,new T2(0,_14T,new T2(0,_14V,new T2(0,_14Y-_14O|0,_14X))),_1M);}else{return E(_14R);}}},_14Z=function(_150,_151){var _152=E(_151);if(!_152._){return (E(_150)==0)?__Z:E(_14M);}else{var _153=_152.b,_154=E(_152.a),_155=_154.a,_156=E(_154.b),_157=_156.a,_158=E(_156.b);if(!_158._){var _159=_158.b,_15a=E(_150),_15b=E(_158.a);return (_15a>_15b)?(_15b>=_15a)?E(_153):new T2(1,new T2(0,_155,new T2(0,_157,new T2(0,_Rt,_159))),new T(function(){return B(_14N(_15a-_15b|0,_153));})):new T2(1,new T2(0,_155,new T2(0,_157,new T2(0,_15b-_15a|0,_159))),_1M);}else{return E(_153);}}},_15c=function(_15d,_15e){var _15f=E(_15e);if(!_15f._){var _15g=_15f.b,_15h=_15f.c,_15i=_15f.d,_15j=_15f.e;if(!B(A2(_15d,_15g,_15h))){return new F(function(){return _Yb(B(_15c(_15d,_15i)),B(_15c(_15d,_15j)));});}else{return new F(function(){return _ay(_15g,_15h,B(_15c(_15d,_15i)),B(_15c(_15d,_15j)));});}}else{return new T0(1);}},_15k=function(_15l,_15m){var _15n=E(_15l);if(!_15n._){var _15o=E(_15m);if(!_15o._){return new F(function(){return _IF(_15n.b,_15o.b);});}else{return 0;}}else{return (E(_15m)._==0)?2:1;}},_15p=function(_15q,_15r){return new F(function(){return _15k(E(E(_15q).b).b,E(E(_15r).b).b);});},_15s=new T2(1,_1M,_1M),_15t=function(_15u,_15v){var _15w=function(_15x,_15y){var _15z=E(_15x);if(!_15z._){return E(_15y);}else{var _15A=_15z.a,_15B=E(_15y);if(!_15B._){return E(_15z);}else{var _15C=_15B.a;return (B(A2(_15u,_15A,_15C))==2)?new T2(1,_15C,new T(function(){return B(_15w(_15z,_15B.b));})):new T2(1,_15A,new T(function(){return B(_15w(_15z.b,_15B));}));}}},_15D=function(_15E){var _15F=E(_15E);if(!_15F._){return __Z;}else{var _15G=E(_15F.b);return (_15G._==0)?E(_15F):new T2(1,new T(function(){return B(_15w(_15F.a,_15G.a));}),new T(function(){return B(_15D(_15G.b));}));}},_15H=new T(function(){return B(_15I(B(_15D(_1M))));}),_15I=function(_15J){while(1){var _15K=E(_15J);if(!_15K._){return E(_15H);}else{if(!E(_15K.b)._){return E(_15K.a);}else{_15J=B(_15D(_15K));continue;}}}},_15L=new T(function(){return B(_15M(_1M));}),_15N=function(_15O,_15P,_15Q){while(1){var _15R=B((function(_15S,_15T,_15U){var _15V=E(_15U);if(!_15V._){return new T2(1,new T2(1,_15S,_15T),_15L);}else{var _15W=_15V.a;if(B(A2(_15u,_15S,_15W))==2){var _15X=new T2(1,_15S,_15T);_15O=_15W;_15P=_15X;_15Q=_15V.b;return __continue;}else{return new T2(1,new T2(1,_15S,_15T),new T(function(){return B(_15M(_15V));}));}}})(_15O,_15P,_15Q));if(_15R!=__continue){return _15R;}}},_15Y=function(_15Z,_160,_161){while(1){var _162=B((function(_163,_164,_165){var _166=E(_165);if(!_166._){return new T2(1,new T(function(){return B(A1(_164,new T2(1,_163,_1M)));}),_15L);}else{var _167=_166.a,_168=_166.b;switch(B(A2(_15u,_163,_167))){case 0:_15Z=_167;_160=function(_169){return new F(function(){return A1(_164,new T2(1,_163,_169));});};_161=_168;return __continue;case 1:_15Z=_167;_160=function(_16a){return new F(function(){return A1(_164,new T2(1,_163,_16a));});};_161=_168;return __continue;default:return new T2(1,new T(function(){return B(A1(_164,new T2(1,_163,_1M)));}),new T(function(){return B(_15M(_166));}));}}})(_15Z,_160,_161));if(_162!=__continue){return _162;}}},_15M=function(_16b){var _16c=E(_16b);if(!_16c._){return E(_15s);}else{var _16d=_16c.a,_16e=E(_16c.b);if(!_16e._){return new T2(1,_16c,_1M);}else{var _16f=_16e.a,_16g=_16e.b;if(B(A2(_15u,_16d,_16f))==2){return new F(function(){return _15N(_16f,new T2(1,_16d,_1M),_16g);});}else{return new F(function(){return _15Y(_16f,function(_16h){return new T2(1,_16d,_16h);},_16g);});}}}};return new F(function(){return _15I(B(_15M(_15v)));});},_16i=function(_16j,_16k,_16l){var _16m=B(_EV(B(_14Z(_16k,B(_15t(_15p,B(_hc(_1M,B(_15c(function(_16n,_16o){return new F(function(){return A1(_16j,_16o);});},_16l))))))))));if(!_16m._){var _16p=E(_16l);if(!_16p._){return new F(function(){return _Pv(_Wf,_O8,_O8,_16m.a,_16m.b,_16m.c,_16m.d,_16m.e,_16p.a,_16p.b,_16p.c,_16p.d,_16p.e);});}else{return E(_16m);}}else{return E(_16l);}},_16q=function(_16r,_16s,_16t){var _16u=E(_16t);if(!_16u._){var _16v=_16u.d,_16w=_16u.e,_16x=E(_16u.b),_16y=E(_16r),_16z=E(_16x.a);if(_16y>=_16z){if(_16y!=_16z){return new F(function(){return _Zk(_16y,_,_16s,_16w);});}else{var _16A=E(_16s),_16B=E(_16x.b);if(_16A>=_16B){if(_16A!=_16B){return new F(function(){return _Z9(_16y,_,_16A,_16w);});}else{return true;}}else{return new F(function(){return _Z9(_16y,_,_16A,_16v);});}}}else{return new F(function(){return _Zk(_16y,_,_16s,_16v);});}}else{return false;}},_16C=function(_16D,_16E){return (!E(_16D))?false:E(_16E);},_16F=new T(function(){return B(unCStr("IStack is corrupt!"));}),_16G=new T(function(){return B(err(_16F));}),_16H=new T1(0,_q1),_16I=new T1(0,_q2),_16J=function(_16K){return (!E(_16K))?true:false;},_16L=function(_16M,_16N){return (!E(_16M))?E(_16N):true;},_16O=function(_16P,_16Q,_16R,_16S,_16T){while(1){var _16U=B((function(_16V,_16W,_16X,_16Y,_16Z){var _170=E(_16Y);switch(_170._){case 0:return new T1(0,new T(function(){if(E(_170.a)>E(E(_16Z).b)){return true;}else{return false;}}));case 1:var _171=_170.b,_172=B(_16O(_16V,_16W,_16X,_170.a,_16Z));if(!_172._){var _173=B(_16O(_16V,_16W,_16X,_171,_16Z));return (_173._==0)?new T1(0,new T(function(){return B(_16C(_172.a,_173.a));})):E(_173);}else{var _174=B(_16O(_16V,_16W,_16X,_171,_16Z));return (_174._==0)?E(_172):new T1(1,new T(function(){return B(_hq(_172.a,_174.a));}));}break;case 2:var _175=_170.b,_176=B(_16O(_16V,_16W,_16X,_170.a,_16Z));if(!_176._){var _177=B(_16O(_16V,_16W,_16X,_175,_16Z));return (_177._==0)?new T1(0,new T(function(){return B(_16L(_176.a,_177.a));})):E(_177);}else{var _178=B(_16O(_16V,_16W,_16X,_175,_16Z));return (_178._==0)?E(_176):new T1(1,new T(function(){return B(_hq(_176.a,_178.a));}));}break;case 3:var _179=B(_16O(_16V,_16W,_16X,_170.a,_16Z));return (_179._==0)?new T1(0,new T(function(){return B(_16J(_179.a));})):E(_179);case 4:var _17a=_170.b,_17b=_170.c,_17c=E(E(_16V).b);if(!_17c._){var _17d=_17c.d,_17e=_17c.e,_17f=E(_17c.b),_17g=E(_170.a),_17h=E(_17f.a);if(_17g>=_17h){if(_17g!=_17h){var _17i=B(_RF(_17g,_,_17a,_17e));return (_17i._==0)?E(_16H):new T1(0,new T(function(){return B(_GY(_17i.a,_17b));}));}else{var _17j=E(_17a),_17k=E(_17f.b);if(_17j>=_17k){if(_17j!=_17k){var _17l=B(_Ru(_17g,_,_17j,_17e));return (_17l._==0)?E(_16H):new T1(0,new T(function(){return B(_GY(_17l.a,_17b));}));}else{return new T1(0,new T(function(){return B(_GY(_17c.c,_17b));}));}}else{var _17m=B(_Ru(_17g,_,_17j,_17d));return (_17m._==0)?E(_16H):new T1(0,new T(function(){return B(_GY(_17m.a,_17b));}));}}}else{var _17n=B(_RF(_17g,_,_17a,_17d));return (_17n._==0)?E(_16H):new T1(0,new T(function(){return B(_GY(_17n.a,_17b));}));}}else{return E(_16H);}break;case 5:return new T1(0,new T(function(){return B(_16q(_170.a,_170.b,E(_16V).b));}));case 6:return new T1(0,new T(function(){var _17o=E(_16V),_17p=_17o.a,_17q=_17o.b;return B(_RW(_17p,_17q,_170.a))>=B(_RW(_17p,_17q,_170.b));}));case 7:return E(_16I);case 8:return E(_16H);default:var _17r=E(_16X).a,_17s=E(_170.a),_17t=B(_14A(_17s,_17r));if(!_17t._){return new T1(1,new T2(1,new T1(9,_17s),_1M));}else{var _17u=E(_17t.a);if(!_17u._){return E(_16G);}else{var _17v=new T(function(){var _17w=E(_17u.b);if(!_17w._){return new T1(0,new T(function(){return B(_13e(_17s,_17r));}));}else{return new T1(0,new T(function(){return B(_13D(_17s,_17w,_17r));}));}}),_17x=_16V,_17y=_16W,_17z=_16Z;_16P=_17x;_16Q=_17y;_16R=_17v;_16S=_17u.a;_16T=_17z;return __continue;}}}})(_16P,_16Q,_16R,_16S,_16T));if(_16U!=__continue){return _16U;}}},_17A=function(_17B,_17C,_17D,_17E){var _17F=E(_17D);switch(_17F._){case 0:return new T1(0,new T(function(){if(E(_17F.a)>E(E(_17E).b)){return true;}else{return false;}}));case 1:var _17G=_17F.b,_17H=B(_17A(_17B,_17C,_17F.a,_17E));if(!_17H._){var _17I=B(_17A(_17B,_17C,_17G,_17E));return (_17I._==0)?new T1(0,new T(function(){return B(_16C(_17H.a,_17I.a));})):E(_17I);}else{var _17J=B(_17A(_17B,_17C,_17G,_17E));return (_17J._==0)?E(_17H):new T1(1,new T(function(){return B(_hq(_17H.a,_17J.a));}));}break;case 2:var _17K=_17F.b,_17L=B(_17A(_17B,_17C,_17F.a,_17E));if(!_17L._){var _17M=B(_17A(_17B,_17C,_17K,_17E));return (_17M._==0)?new T1(0,new T(function(){return B(_16L(_17L.a,_17M.a));})):E(_17M);}else{var _17N=B(_17A(_17B,_17C,_17K,_17E));return (_17N._==0)?E(_17L):new T1(1,new T(function(){return B(_hq(_17L.a,_17N.a));}));}break;case 3:var _17O=B(_17A(_17B,_17C,_17F.a,_17E));return (_17O._==0)?new T1(0,new T(function(){return B(_16J(_17O.a));})):E(_17O);case 4:var _17P=_17F.b,_17Q=_17F.c,_17R=E(E(_17B).b);if(!_17R._){var _17S=_17R.d,_17T=_17R.e,_17U=E(_17R.b),_17V=E(_17F.a),_17W=E(_17U.a);if(_17V>=_17W){if(_17V!=_17W){var _17X=B(_RF(_17V,_,_17P,_17T));return (_17X._==0)?E(_16H):new T1(0,new T(function(){return B(_GY(_17X.a,_17Q));}));}else{var _17Y=E(_17P),_17Z=E(_17U.b);if(_17Y>=_17Z){if(_17Y!=_17Z){var _180=B(_Ru(_17V,_,_17Y,_17T));return (_180._==0)?E(_16H):new T1(0,new T(function(){return B(_GY(_180.a,_17Q));}));}else{return new T1(0,new T(function(){return B(_GY(_17R.c,_17Q));}));}}else{var _181=B(_Ru(_17V,_,_17Y,_17S));return (_181._==0)?E(_16H):new T1(0,new T(function(){return B(_GY(_181.a,_17Q));}));}}}else{var _182=B(_RF(_17V,_,_17P,_17S));return (_182._==0)?E(_16H):new T1(0,new T(function(){return B(_GY(_182.a,_17Q));}));}}else{return E(_16H);}break;case 5:return new T1(0,new T(function(){return B(_16q(_17F.a,_17F.b,E(_17B).b));}));case 6:return new T1(0,new T(function(){var _183=E(_17B),_184=_183.a,_185=_183.b;return B(_RW(_184,_185,_17F.a))>=B(_RW(_184,_185,_17F.b));}));case 7:return E(_16I);case 8:return E(_16H);default:var _186=E(_17C),_187=E(_186.b).a,_188=E(_17F.a),_189=B(_14A(_188,_187));if(!_189._){return new T1(1,new T2(1,new T1(9,_188),_1M));}else{var _18a=E(_189.a);if(!_18a._){return E(_16G);}else{var _18b=new T(function(){var _18c=E(_18a.b);if(!_18c._){return new T1(0,new T(function(){return B(_13e(_188,_187));}));}else{return new T1(0,new T(function(){return B(_13D(_188,_18c,_187));}));}});return new F(function(){return _16O(_17B,_186.a,_18b,_18a.a,_17E);});}}}},_18d=function(_18e,_18f,_18g,_18h,_18i){var _18j=E(_18h);switch(_18j._){case 0:return new T3(0,_18f,_14K,_1M);case 1:var _18k=_18j.a,_18l=_18j.b,_18m=_18j.g,_18n=E(_18j.e),_18o=E(E(_18i).b),_18p=_18n<=_18o,_18q=new T(function(){var _18r=E(_18f);return B(_RW(_18r.a,_18r.b,_18j.c));}),_18s=new T(function(){return E(_18j.d)<=_18o;}),_18t=new T(function(){return B(_E2(E(_18k),new T2(0,_18l,new T(function(){if(!E(_18p)){if(!E(_18s)){return new T2(0,_18q,_18n);}else{return new T0(1);}}else{return new T0(1);}})),E(_18f).a));});return (!E(_18p))?(!E(_18s))?(!B(_12X(_18k,_18l,_18q,_18n,E(_18e).a)))?new T3(0,_18f,_18j,_1M):new T3(0,new T(function(){return new T2(0,_18t,E(_18f).b);}),_18j.f,new T2(1,new T3(3,_18k,_18l,_18q),_1M)):new T3(0,new T(function(){return new T2(0,_18t,E(_18f).b);}),_18m,_1M):new T3(0,new T(function(){return new T2(0,_18t,E(_18f).b);}),_18m,_1M);case 2:var _18u=_18j.b,_18v=E(_18f),_18w=_18v.a,_18x=E(_18j.a),_18y=B(_RR(_18x,_18w));if(!_18y._){return new T3(0,_18v,_18j,_1M);}else{var _18z=E(_18y.a),_18A=_18z.a,_18B=E(_18z.b);if(!_18B._){var _18C=_18B.a;return (!B(_WH(_18x,_,_18A,_18C,E(_18e).b)))?new T3(0,_18v,_18j,_1M):new T3(0,new T2(0,new T(function(){return B(_E2(_18x,new T2(0,_18A,_YR),_18w));}),_18v.b),_18u,new T2(1,new T3(4,_18x,_18A,_18C),_1M));}else{return new T3(0,_18v,_18u,new T2(1,new T2(6,_18x,_18A),_1M));}}break;case 3:var _18D=_18j.a,_18E=_18j.b,_18F=_18j.c,_18G=_18j.d,_18H=_18j.f,_18I=E(E(_18i).b);if(E(_18j.e)>_18I){var _18J=function(_18K){var _18L=E(_18f),_18M=_18L.a,_18N=_18L.b,_18O=B(_RW(_18M,_18N,_18G));if(E(_18K)!=_18O){return new T3(0,_18L,_18j,_1M);}else{if(B(_13P(_18M,_18E,_18I))<_18O){return new T3(0,_18L,_18H,new T2(1,new T4(2,_18D,_18E,_18F,_18O),_1M));}else{var _18P=new T(function(){return B(_16i(function(_18Q){var _18R=E(_18Q),_18S=E(_18R.b);return (_18S._==0)?(E(_18R.a)!=E(_18E))?false:(E(_18S.b)>_18I)?true:false:false;},_18O,_18M));});return new T3(0,new T2(0,_18P,_18N),_18H,new T2(1,new T4(0,_18D,_18E,_18F,_18O),_1M));}}},_18T=E(E(_18e).c);if(!_18T._){var _18U=_18T.d,_18V=_18T.e,_18W=E(_18T.b),_18X=E(_18D),_18Y=E(_18W.a);if(_18X>=_18Y){if(_18X!=_18Y){var _18Z=B(_12L(_18X,_,_18F,_18V));if(!_18Z._){return new T3(0,_18f,_18j,_1M);}else{return new F(function(){return _18J(_18Z.a);});}}else{var _190=E(_18F),_191=E(_18W.b);if(_190>=_191){if(_190!=_191){var _192=B(_12A(_18X,_,_190,_18V));if(!_192._){return new T3(0,_18f,_18j,_1M);}else{return new F(function(){return _18J(_192.a);});}}else{return new F(function(){return _18J(_18T.c);});}}else{var _193=B(_12A(_18X,_,_190,_18U));if(!_193._){return new T3(0,_18f,_18j,_1M);}else{return new F(function(){return _18J(_193.a);});}}}}else{var _194=B(_12L(_18X,_,_18F,_18U));if(!_194._){return new T3(0,_18f,_18j,_1M);}else{return new F(function(){return _18J(_194.a);});}}}else{return new T3(0,_18f,_18j,_1M);}}else{return new T3(0,_18f,_18H,new T2(1,new T4(1,_18D,_18E,_18F,new T(function(){return B(_Sr(_18f,_18G));})),_1M));}break;case 4:var _195=new T(function(){var _196=B(_18d(_18e,_18f,_18g,_18j.a,_18i));return new T3(0,_196.a,_196.b,_196.c);}),_197=new T(function(){var _198=B(_18d(_18e,new T(function(){return E(E(_195).a);}),_18g,_18j.b,_18i));return new T3(0,_198.a,_198.b,_198.c);}),_199=new T(function(){return B(_hq(E(_195).c,new T(function(){return E(E(_197).c);},1)));}),_19a=new T(function(){var _19b=E(_195).b,_19c=E(_197).b,_19d=function(_19e){var _19f=E(_19c);switch(_19f._){case 0:return E(_19b);case 1:return new T2(4,_19b,_19f);case 2:return new T2(4,_19b,_19f);case 3:return new T2(4,_19b,_19f);case 4:return new T2(4,_19b,_19f);case 5:return new T2(4,_19b,_19f);case 6:return new T2(4,_19b,_19f);case 7:return new T2(4,_19b,_19f);case 8:return new T2(4,_19b,_19f);case 9:return new T2(4,_19b,_19f);case 10:return new T2(4,_19b,_19f);default:return new T2(4,_19b,_19f);}};switch(E(_19b)._){case 0:return E(_19c);break;case 1:return B(_19d(_));break;case 2:return B(_19d(_));break;case 3:return B(_19d(_));break;case 4:return B(_19d(_));break;case 5:return B(_19d(_));break;case 6:return B(_19d(_));break;case 7:return B(_19d(_));break;case 8:return B(_19d(_));break;case 9:return B(_19d(_));break;case 10:return B(_19d(_));break;default:return B(_19d(_));}});return new T3(0,new T(function(){return E(E(_197).a);}),_19a,_199);case 5:var _19g=B(_17A(_18f,_18g,_18j.a,_18i));return (_19g._==0)?(!E(_19g.a))?new T3(0,_18f,_18j.c,_1M):new T3(0,_18f,_18j.b,_1M):new T3(0,_18f,_14K,_19g.a);case 6:var _19h=E(_18i);if(E(_18j.b)>E(_19h.b)){var _19i=B(_17A(_18f,_18g,_18j.a,_19h));return (_19i._==0)?(!E(_19i.a))?new T3(0,_18f,_18j,_1M):new T3(0,_18f,_18j.c,_1M):new T3(0,_18f,_14K,_19i.a);}else{return new T3(0,_18f,_18j.d,_1M);}break;case 7:var _19j=E(_18j.a),_19k=B(_14F(_19j,E(E(_18g).a).a));if(!_19k._){return new T3(0,_18f,_14K,new T2(1,new T1(8,_19j),_1M));}else{var _19l=E(_19k.a);return (_19l._==0)?E(_16G):new T3(0,_18f,new T2(9,_19j,_19l.a),_1M);}break;case 8:var _19m=_18j.a,_19n=_18j.b,_19o=new T(function(){var _19p=new T(function(){var _19q=E(_18g);return new T2(0,new T(function(){return new T1(0,B(_14u(_12x,_19m,_19n,E(_19q.a).a)));}),_19q.b);}),_19r=B(_18d(_18e,_18f,_19p,_18j.c,_18i));return new T3(0,_19r.a,_19r.b,_19r.c);});return new T3(0,new T(function(){return E(E(_19o).a);}),new T3(8,_19m,_19n,new T(function(){return E(E(_19o).b);})),new T(function(){return E(E(_19o).c);}));case 9:var _19s=E(_18g),_19t=E(_19s.a).a,_19u=E(_18j.a),_19v=B(_14F(_19u,_19t));if(!_19v._){return new T3(0,_18f,_14K,new T2(1,new T1(10,_19u),_1M));}else{var _19w=E(_19v.a);if(!_19w._){return E(_16G);}else{var _19x=new T(function(){var _19y=new T(function(){var _19z=E(_19w.b);if(!_19z._){return new T1(0,new T(function(){return B(_13m(_19u,_19t));}));}else{return new T1(0,new T(function(){return B(_13u(_19u,_19z,_19t));}));}}),_19A=B(_18d(_18e,_18f,new T2(0,_19y,_19s.b),_18j.b,_18i));return new T3(0,_19A.a,_19A.b,_19A.c);});return new T3(0,new T(function(){return E(E(_19x).a);}),new T2(9,_19u,new T(function(){return E(E(_19x).b);})),new T(function(){return E(E(_19x).c);}));}}break;case 10:var _19B=E(_18g),_19C=E(_19B.b).a,_19D=E(_18j.a),_19E=B(_14A(_19D,_19C));if(!_19E._){return new T3(0,_18f,_14K,new T2(1,new T1(11,_19D),_1M));}else{var _19F=E(_19E.a);if(!_19F._){return E(_16G);}else{var _19G=new T(function(){var _19H=new T(function(){var _19I=E(_19F.b);if(!_19I._){return new T1(0,new T(function(){return B(_13e(_19D,_19C));}));}else{return new T1(0,new T(function(){return B(_13D(_19D,_19I,_19C));}));}}),_19J=B(_18d(_18e,_18f,new T2(0,_19B.a,_19H),_18j.b,_18i));return new T3(0,_19J.a,_19J.b,_19J.c);});return new T3(0,new T(function(){return E(E(_19G).a);}),new T2(10,_19D,new T(function(){return E(E(_19G).b);})),new T(function(){return E(E(_19G).c);}));}}break;default:var _19K=_18j.a,_19L=_18j.b,_19M=new T(function(){var _19N=new T(function(){var _19O=E(_18g);return new T2(0,_19O.a,new T(function(){return new T1(0,B(_14u(_12z,_19K,_19L,E(_19O.b).a)));}));}),_19P=B(_18d(_18e,_18f,_19N,_18j.c,_18i));return new T3(0,_19P.a,_19P.b,_19P.c);});return new T3(0,new T(function(){return E(E(_19M).a);}),new T3(11,_19K,_19L,new T(function(){return E(E(_19M).b);})),new T(function(){return E(E(_19M).c);}));}},_19Q=new T1(0,_8i),_19R=new T2(0,_19Q,_19Q),_19S=function(_19T,_19U,_19V,_19W,_19X,_19Y){var _19Z=new T2(0,_19U,_19V),_1a0=B(_18d(_19T,_19Z,_19R,_19W,_19X)),_1a1=_1a0.b,_1a2=_1a0.c,_1a3=E(_1a0.a),_1a4=_1a3.a,_1a5=_1a3.b,_1a6=function(_1a7){return new F(function(){return _19S(_19T,_1a4,_1a5,_1a1,_19X,new T(function(){return B(_hq(_1a2,_19Y));}));});};if(!B(A2(_12v,_1a4,_19U))){return new F(function(){return _1a6(_);});}else{if(!B(A2(_122,_1a5,_19V))){return new F(function(){return _1a6(_);});}else{if(!B(_10W(_1a1,_19W))){return new F(function(){return _1a6(_);});}else{if(!E(_1a2)._){return new T3(0,_19Z,_19W,_19Y);}else{return new F(function(){return _1a6(_);});}}}}},_1a8=function(_1a9,_1aa,_1ab,_1ac){var _1ad=new T(function(){var _1ae=B(_YW(_1a9,new T(function(){return E(E(_1aa).a);},1),_1ac));return new T2(0,_1ae.a,_1ae.b);}),_1af=new T(function(){var _1ag=B(_10b(new T(function(){return E(E(_1aa).b);}),_1M,E(_1a9).d));return new T2(0,_1ag.a,_1ag.b);}),_1ah=new T(function(){var _1ai=E(_1aa),_1aj=B(_19S(_1a9,new T(function(){return E(E(_1ad).a);}),new T(function(){return E(E(_1af).a);}),_1ab,_1ac,_1M));return new T3(0,_1aj.a,_1aj.b,_1aj.c);}),_1ak=new T(function(){var _1al=new T(function(){return B(_hq(E(_1ad).b,new T(function(){return E(E(_1ah).c);},1)));},1);return B(_hq(E(_1af).b,_1al));});return new T3(0,new T(function(){return E(E(_1ah).a);}),new T(function(){return E(E(_1ah).b);}),_1ak);},_1am=function(_1an,_1ao,_1ap,_1aq,_1ar){while(1){var _1as=E(_1an);if(!_1as._){return new T4(0,_1ao,_1ap,_1aq,_1ar);}else{var _1at=E(_1as.a),_1au=B(_Rc(_1ao,_1ap,_1aq,_1ar,_1at.a,_1at.b,_1at.c,_1at.d));_1an=_1as.b;_1ao=_1au.a;_1ap=_1au.b;_1aq=_1au.c;_1ar=_1au.d;continue;}}},_1av=function(_1aw,_1ax,_1ay,_1az,_1aA,_1aB){var _1aC=E(_1aw),_1aD=B(_Rc(_1ay,_1az,_1aA,_1aB,_1aC.a,_1aC.b,_1aC.c,_1aC.d));return new F(function(){return _1am(_1ax,_1aD.a,_1aD.b,_1aD.c,_1aD.d);});},_1aE=function(_1aF,_1aG,_1aH,_1aI){var _1aJ=B(_1a8(_1aG,_1aI,_1aH,_1aF)),_1aK=_1aJ.a,_1aL=_1aJ.b,_1aM=B(_Sv(_1aL,_1aK));return new F(function(){return _1av(new T(function(){var _1aN=B(_SM(_1aF,E(_1aK).a));return new T4(0,_1aN.a,_1aN.b,_1aN.c,_1aN.d);}),new T2(1,new T(function(){var _1aO=B(_VB(_1aK,_1aL));return new T4(0,_1aO.a,_1aO.b,_1aO.c,_1aO.d);}),_1M),_1aM.a,_1aM.b,_1aM.c,_1aM.d);});},_1aP="(function (t) {return document.getElementById(t).value})",_1aQ=new T(function(){return eval("(function () {return Blockly.Marlowe.workspaceToCode(demoWorkspace);})");}),_1aR=new T(function(){return B(unCStr("contractState"));}),_1aS=new T(function(){return B(unCStr("currBlock"));}),_1aT=new T(function(){return eval("(function (x) { var node = document.getElementById(x); while (node.hasChildNodes()) { node.removeChild(node.lastChild); } })");}),_1aU=new T(function(){return B(err(_ha));}),_1aV=new T(function(){return B(err(_jS));}),_1aW=new T(function(){return B(A3(_xS,_yl,_xn,_DB));}),_1aX=new T(function(){return B(err(_ha));}),_1aY=new T(function(){return B(err(_jS));}),_1aZ=function(_zv){return new F(function(){return _xH(_BM,_zv);});},_1b0=function(_1b1,_1b2){return new F(function(){return _yv(_1aZ,_1b2);});},_1b3=new T(function(){return B(_yv(_1aZ,_jV));}),_1b4=function(_zv){return new F(function(){return _l5(_1b3,_zv);});},_1b5=function(_1b6){var _1b7=new T(function(){return B(A3(_xH,_BM,_1b6,_jV));});return function(_zc){return new F(function(){return _l5(_1b7,_zc);});};},_1b8=new T4(0,_1b5,_1b4,_1aZ,_1b0),_1b9=new T(function(){return B(unCStr("NotRedeemed"));}),_1ba=new T(function(){return B(unCStr("ManuallyRedeemed"));}),_1bb=function(_1bc,_1bd){var _1be=new T(function(){var _1bf=new T(function(){return B(A1(_1bd,_YR));});return B(_wQ(function(_1bg){var _1bh=E(_1bg);return (_1bh._==3)?(!B(_lT(_1bh.a,_1ba)))?new T0(2):E(_1bf):new T0(2);}));}),_1bi=function(_1bj){return E(_1be);},_1bk=new T(function(){if(E(_1bc)>10){return new T0(2);}else{var _1bl=new T(function(){var _1bm=new T(function(){var _1bn=function(_1bo){return new F(function(){return A3(_xS,_yl,_ze,function(_1bp){return new F(function(){return A1(_1bd,new T2(0,_1bo,_1bp));});});});};return B(A3(_xS,_yl,_ze,_1bn));});return B(_wQ(function(_1bq){var _1br=E(_1bq);return (_1br._==3)?(!B(_lT(_1br.a,_1b9)))?new T0(2):E(_1bm):new T0(2);}));}),_1bs=function(_1bt){return E(_1bl);};return new T1(1,function(_1bu){return new F(function(){return A2(_vx,_1bu,_1bs);});});}});return new F(function(){return _lf(new T1(1,function(_1bv){return new F(function(){return A2(_vx,_1bv,_1bi);});}),_1bk);});},_1bw=function(_zv){return new F(function(){return _xH(_1bb,_zv);});},_1bx=function(_1by,_1bz){return new F(function(){return _yv(_1bw,_1bz);});},_1bA=new T(function(){return B(_yv(_1bw,_jV));}),_1bB=function(_zv){return new F(function(){return _l5(_1bA,_zv);});},_1bC=function(_1bD){var _1bE=new T(function(){return B(A3(_xH,_1bb,_1bD,_jV));});return function(_zc){return new F(function(){return _l5(_1bE,_zc);});};},_1bF=new T4(0,_1bC,_1bB,_1bw,_1bx),_1bG=function(_1bH,_1bI){return new F(function(){return _A0(_zd,_1bF,_1bI);});},_1bJ=new T(function(){return B(_yv(_1bG,_jV));}),_1bK=function(_zv){return new F(function(){return _l5(_1bJ,_zv);});},_1bL=new T(function(){return B(_A0(_zd,_1bF,_jV));}),_1bM=function(_zv){return new F(function(){return _l5(_1bL,_zv);});},_1bN=function(_1bO,_zv){return new F(function(){return _1bM(_zv);});},_1bP=function(_1bQ,_1bR){return new F(function(){return _yv(_1bG,_1bR);});},_1bS=new T4(0,_1bN,_1bK,_1bG,_1bP),_1bT=function(_1bU,_1bV){return new F(function(){return _A0(_1b8,_1bS,_1bV);});},_1bW=function(_1bX,_1bY){return new F(function(){return _yv(_1bT,_1bY);});},_1bZ=new T(function(){return B(_yv(_1bW,_jV));}),_1c0=function(_Av){return new F(function(){return _l5(_1bZ,_Av);});},_1c1=function(_1c2){return new F(function(){return _yv(_1bW,_1c2);});},_1c3=function(_1c4,_1c5){return new F(function(){return _1c1(_1c5);});},_1c6=new T(function(){return B(_yv(_1bT,_jV));}),_1c7=function(_Av){return new F(function(){return _l5(_1c6,_Av);});},_1c8=function(_1c9,_Av){return new F(function(){return _1c7(_Av);});},_1ca=new T4(0,_1c8,_1c0,_1bW,_1c3),_1cb=new T(function(){return B(_A0(_1ca,_AF,_DB));}),_1cc=42,_1cd=new T(function(){return B(unCStr("actions"));}),_1ce=function(_1cf){while(1){var _1cg=B((function(_1ch){var _1ci=E(_1ch);if(!_1ci._){return __Z;}else{var _1cj=_1ci.b,_1ck=E(_1ci.a);if(!E(_1ck.b)._){return new T2(1,_1ck.a,new T(function(){return B(_1ce(_1cj));}));}else{_1cf=_1cj;return __continue;}}})(_1cf));if(_1cg!=__continue){return _1cg;}}},_1cl=new T(function(){return B(err(_ha));}),_1cm=new T(function(){return B(err(_jS));}),_1cn=new T(function(){return B(unCStr("IdentCBind"));}),_1co=function(_1cp,_1cq){if(_1cp>10){return new T0(2);}else{var _1cr=new T(function(){var _1cs=new T(function(){return B(A3(_xS,_yl,_ze,function(_1ct){return new F(function(){return A1(_1cq,_1ct);});}));});return B(_wQ(function(_1cu){var _1cv=E(_1cu);return (_1cv._==3)?(!B(_lT(_1cv.a,_1cn)))?new T0(2):E(_1cs):new T0(2);}));}),_1cw=function(_1cx){return E(_1cr);};return new T1(1,function(_1cy){return new F(function(){return A2(_vx,_1cy,_1cw);});});}},_1cz=function(_1cA,_1cB){return new F(function(){return _1co(E(_1cA),_1cB);});},_1cC=new T(function(){return B(unCStr("IdentOBind"));}),_1cD=function(_1cE,_1cF){if(_1cE>10){return new T0(2);}else{var _1cG=new T(function(){var _1cH=new T(function(){return B(A3(_xS,_yl,_ze,function(_1cI){return new F(function(){return A1(_1cF,_1cI);});}));});return B(_wQ(function(_1cJ){var _1cK=E(_1cJ);return (_1cK._==3)?(!B(_lT(_1cK.a,_1cC)))?new T0(2):E(_1cH):new T0(2);}));}),_1cL=function(_1cM){return E(_1cG);};return new T1(1,function(_1cN){return new F(function(){return A2(_vx,_1cN,_1cL);});});}},_1cO=function(_1cP,_1cQ){return new F(function(){return _1cD(E(_1cP),_1cQ);});},_1cR=new T(function(){return B(unCStr("ConstMoney"));}),_1cS=new T(function(){return B(unCStr("AvailableMoney"));}),_1cT=new T(function(){return B(unCStr("AddMoney"));}),_1cU=new T(function(){return B(unCStr("MoneyFromChoice"));}),_1cV=function(_1cW,_1cX){var _1cY=new T(function(){var _1cZ=new T(function(){var _1d0=new T(function(){if(_1cW>10){return new T0(2);}else{var _1d1=new T(function(){var _1d2=new T(function(){var _1d3=function(_1d4){var _1d5=function(_1d6){return new F(function(){return A3(_xH,_1d7,_ze,function(_1d8){return new F(function(){return A1(_1cX,new T3(3,_1d4,_1d6,_1d8));});});});};return new F(function(){return A3(_xS,_yl,_ze,_1d5);});};return B(A3(_xH,_zr,_ze,_1d3));});return B(_wQ(function(_1d9){var _1da=E(_1d9);return (_1da._==3)?(!B(_lT(_1da.a,_1cU)))?new T0(2):E(_1d2):new T0(2);}));}),_1db=function(_1dc){return E(_1d1);};return new T1(1,function(_1dd){return new F(function(){return A2(_vx,_1dd,_1db);});});}});if(_1cW>10){return B(_lf(_jU,_1d0));}else{var _1de=new T(function(){var _1df=new T(function(){return B(A3(_xS,_yl,_ze,function(_1dg){return new F(function(){return A1(_1cX,new T1(2,_1dg));});}));});return B(_wQ(function(_1dh){var _1di=E(_1dh);return (_1di._==3)?(!B(_lT(_1di.a,_1cR)))?new T0(2):E(_1df):new T0(2);}));}),_1dj=function(_1dk){return E(_1de);};return B(_lf(new T1(1,function(_1dl){return new F(function(){return A2(_vx,_1dl,_1dj);});}),_1d0));}});if(_1cW>10){return B(_lf(_jU,_1cZ));}else{var _1dm=new T(function(){var _1dn=new T(function(){var _1do=function(_1dp){return new F(function(){return A3(_xH,_1d7,_ze,function(_1dq){return new F(function(){return A1(_1cX,new T2(1,_1dp,_1dq));});});});};return B(A3(_xH,_1d7,_ze,_1do));});return B(_wQ(function(_1dr){var _1ds=E(_1dr);return (_1ds._==3)?(!B(_lT(_1ds.a,_1cT)))?new T0(2):E(_1dn):new T0(2);}));}),_1dt=function(_1du){return E(_1dm);};return B(_lf(new T1(1,function(_1dv){return new F(function(){return A2(_vx,_1dv,_1dt);});}),_1cZ));}});if(_1cW>10){return new F(function(){return _lf(_jU,_1cY);});}else{var _1dw=new T(function(){var _1dx=new T(function(){return B(A3(_xH,_BM,_ze,function(_1dy){return new F(function(){return A1(_1cX,new T1(0,_1dy));});}));});return B(_wQ(function(_1dz){var _1dA=E(_1dz);return (_1dA._==3)?(!B(_lT(_1dA.a,_1cS)))?new T0(2):E(_1dx):new T0(2);}));}),_1dB=function(_1dC){return E(_1dw);};return new F(function(){return _lf(new T1(1,function(_1dD){return new F(function(){return A2(_vx,_1dD,_1dB);});}),_1cY);});}},_1d7=function(_1dE,_1dF){return new F(function(){return _1cV(E(_1dE),_1dF);});},_1dG=new T0(7),_1dH=function(_1dI,_1dJ){return new F(function(){return A1(_1dJ,_1dG);});},_1dK=new T(function(){return B(unCStr("TrueObs"));}),_1dL=new T2(0,_1dK,_1dH),_1dM=new T0(8),_1dN=function(_1dO,_1dP){return new F(function(){return A1(_1dP,_1dM);});},_1dQ=new T(function(){return B(unCStr("FalseObs"));}),_1dR=new T2(0,_1dQ,_1dN),_1dS=new T2(1,_1dR,_1M),_1dT=new T2(1,_1dL,_1dS),_1dU=function(_1dV,_1dW,_1dX){var _1dY=E(_1dV);if(!_1dY._){return new T0(2);}else{var _1dZ=E(_1dY.a),_1e0=_1dZ.a,_1e1=new T(function(){return B(A2(_1dZ.b,_1dW,_1dX));}),_1e2=new T(function(){return B(_wQ(function(_1e3){var _1e4=E(_1e3);switch(_1e4._){case 3:return (!B(_lT(_1e0,_1e4.a)))?new T0(2):E(_1e1);case 4:return (!B(_lT(_1e0,_1e4.a)))?new T0(2):E(_1e1);default:return new T0(2);}}));}),_1e5=function(_1e6){return E(_1e2);};return new F(function(){return _lf(new T1(1,function(_1e7){return new F(function(){return A2(_vx,_1e7,_1e5);});}),new T(function(){return B(_1dU(_1dY.b,_1dW,_1dX));}));});}},_1e8=new T(function(){return B(unCStr("OReplace"));}),_1e9=new T(function(){return B(unCStr("ValueGE"));}),_1ea=new T(function(){return B(unCStr("PersonChoseSomething"));}),_1eb=new T(function(){return B(unCStr("PersonChoseThis"));}),_1ec=new T(function(){return B(unCStr("BelowTimeout"));}),_1ed=new T(function(){return B(unCStr("AndObs"));}),_1ee=new T(function(){return B(unCStr("OrObs"));}),_1ef=new T(function(){return B(unCStr("NotObs"));}),_1eg=function(_1eh,_1ei){var _1ej=new T(function(){var _1ek=E(_1eh),_1el=new T(function(){var _1em=new T(function(){var _1en=new T(function(){var _1eo=new T(function(){var _1ep=new T(function(){var _1eq=new T(function(){var _1er=new T(function(){if(_1ek>10){return new T0(2);}else{var _1es=new T(function(){var _1et=new T(function(){return B(A3(_xH,_1cO,_ze,function(_1eu){return new F(function(){return A1(_1ei,new T1(9,_1eu));});}));});return B(_wQ(function(_1ev){var _1ew=E(_1ev);return (_1ew._==3)?(!B(_lT(_1ew.a,_1e8)))?new T0(2):E(_1et):new T0(2);}));}),_1ex=function(_1ey){return E(_1es);};return new T1(1,function(_1ez){return new F(function(){return A2(_vx,_1ez,_1ex);});});}});if(_1ek>10){return B(_lf(_jU,_1er));}else{var _1eA=new T(function(){var _1eB=new T(function(){var _1eC=function(_1eD){return new F(function(){return A3(_xH,_1d7,_ze,function(_1eE){return new F(function(){return A1(_1ei,new T2(6,_1eD,_1eE));});});});};return B(A3(_xH,_1d7,_ze,_1eC));});return B(_wQ(function(_1eF){var _1eG=E(_1eF);return (_1eG._==3)?(!B(_lT(_1eG.a,_1e9)))?new T0(2):E(_1eB):new T0(2);}));}),_1eH=function(_1eI){return E(_1eA);};return B(_lf(new T1(1,function(_1eJ){return new F(function(){return A2(_vx,_1eJ,_1eH);});}),_1er));}});if(_1ek>10){return B(_lf(_jU,_1eq));}else{var _1eK=new T(function(){var _1eL=new T(function(){var _1eM=function(_1eN){return new F(function(){return A3(_xS,_yl,_ze,function(_1eO){return new F(function(){return A1(_1ei,new T2(5,_1eN,_1eO));});});});};return B(A3(_xH,_zr,_ze,_1eM));});return B(_wQ(function(_1eP){var _1eQ=E(_1eP);return (_1eQ._==3)?(!B(_lT(_1eQ.a,_1ea)))?new T0(2):E(_1eL):new T0(2);}));}),_1eR=function(_1eS){return E(_1eK);};return B(_lf(new T1(1,function(_1eT){return new F(function(){return A2(_vx,_1eT,_1eR);});}),_1eq));}});if(_1ek>10){return B(_lf(_jU,_1ep));}else{var _1eU=new T(function(){var _1eV=new T(function(){var _1eW=function(_1eX){var _1eY=function(_1eZ){return new F(function(){return A3(_xS,_yl,_ze,function(_1f0){return new F(function(){return A1(_1ei,new T3(4,_1eX,_1eZ,_1f0));});});});};return new F(function(){return A3(_xS,_yl,_ze,_1eY);});};return B(A3(_xH,_zr,_ze,_1eW));});return B(_wQ(function(_1f1){var _1f2=E(_1f1);return (_1f2._==3)?(!B(_lT(_1f2.a,_1eb)))?new T0(2):E(_1eV):new T0(2);}));}),_1f3=function(_1f4){return E(_1eU);};return B(_lf(new T1(1,function(_1f5){return new F(function(){return A2(_vx,_1f5,_1f3);});}),_1ep));}});if(_1ek>10){return B(_lf(_jU,_1eo));}else{var _1f6=new T(function(){var _1f7=new T(function(){return B(A3(_xH,_1eg,_ze,function(_1f8){return new F(function(){return A1(_1ei,new T1(3,_1f8));});}));});return B(_wQ(function(_1f9){var _1fa=E(_1f9);return (_1fa._==3)?(!B(_lT(_1fa.a,_1ef)))?new T0(2):E(_1f7):new T0(2);}));}),_1fb=function(_1fc){return E(_1f6);};return B(_lf(new T1(1,function(_1fd){return new F(function(){return A2(_vx,_1fd,_1fb);});}),_1eo));}});if(_1ek>10){return B(_lf(_jU,_1en));}else{var _1fe=new T(function(){var _1ff=new T(function(){var _1fg=function(_1fh){return new F(function(){return A3(_xH,_1eg,_ze,function(_1fi){return new F(function(){return A1(_1ei,new T2(2,_1fh,_1fi));});});});};return B(A3(_xH,_1eg,_ze,_1fg));});return B(_wQ(function(_1fj){var _1fk=E(_1fj);return (_1fk._==3)?(!B(_lT(_1fk.a,_1ee)))?new T0(2):E(_1ff):new T0(2);}));}),_1fl=function(_1fm){return E(_1fe);};return B(_lf(new T1(1,function(_1fn){return new F(function(){return A2(_vx,_1fn,_1fl);});}),_1en));}});if(_1ek>10){return B(_lf(_jU,_1em));}else{var _1fo=new T(function(){var _1fp=new T(function(){var _1fq=function(_1fr){return new F(function(){return A3(_xH,_1eg,_ze,function(_1fs){return new F(function(){return A1(_1ei,new T2(1,_1fr,_1fs));});});});};return B(A3(_xH,_1eg,_ze,_1fq));});return B(_wQ(function(_1ft){var _1fu=E(_1ft);return (_1fu._==3)?(!B(_lT(_1fu.a,_1ed)))?new T0(2):E(_1fp):new T0(2);}));}),_1fv=function(_1fw){return E(_1fo);};return B(_lf(new T1(1,function(_1fx){return new F(function(){return A2(_vx,_1fx,_1fv);});}),_1em));}});if(_1ek>10){return B(_lf(_jU,_1el));}else{var _1fy=new T(function(){var _1fz=new T(function(){return B(A3(_xS,_yl,_ze,function(_1fA){return new F(function(){return A1(_1ei,new T1(0,_1fA));});}));});return B(_wQ(function(_1fB){var _1fC=E(_1fB);return (_1fC._==3)?(!B(_lT(_1fC.a,_1ec)))?new T0(2):E(_1fz):new T0(2);}));}),_1fD=function(_1fE){return E(_1fy);};return B(_lf(new T1(1,function(_1fF){return new F(function(){return A2(_vx,_1fF,_1fD);});}),_1el));}});return new F(function(){return _lf(B(_1dU(_1dT,_1eh,_1ei)),_1ej);});},_1fG=new T(function(){return B(unCStr("CReplace"));}),_1fH=new T(function(){return B(unCStr("Null"));}),_1fI=new T(function(){return B(unCStr("CommitCash"));}),_1fJ=new T(function(){return B(unCStr("RedeemCC"));}),_1fK=new T(function(){return B(unCStr("Pay"));}),_1fL=new T(function(){return B(unCStr("Both"));}),_1fM=new T(function(){return B(unCStr("Choice"));}),_1fN=new T(function(){return B(unCStr("When"));}),_1fO=new T(function(){return B(unCStr("CBind"));}),_1fP=new T(function(){return B(unCStr("CUnbind"));}),_1fQ=new T(function(){return B(unCStr("OUnbind"));}),_1fR=new T(function(){return B(unCStr("OBind"));}),_1fS=function(_1fT,_1fU){var _1fV=new T(function(){var _1fW=new T(function(){return B(A1(_1fU,_14K));});return B(_wQ(function(_1fX){var _1fY=E(_1fX);return (_1fY._==3)?(!B(_lT(_1fY.a,_1fH)))?new T0(2):E(_1fW):new T0(2);}));}),_1fZ=function(_1g0){return E(_1fV);},_1g1=new T(function(){var _1g2=E(_1fT),_1g3=new T(function(){var _1g4=new T(function(){var _1g5=new T(function(){var _1g6=new T(function(){var _1g7=new T(function(){var _1g8=new T(function(){var _1g9=new T(function(){var _1ga=new T(function(){var _1gb=new T(function(){var _1gc=new T(function(){if(_1g2>10){return new T0(2);}else{var _1gd=new T(function(){var _1ge=new T(function(){var _1gf=function(_1gg){var _1gh=function(_1gi){return new F(function(){return A3(_xH,_1fS,_ze,function(_1gj){return new F(function(){return A1(_1fU,new T3(11,_1gg,_1gi,_1gj));});});});};return new F(function(){return A3(_xH,_1eg,_ze,_1gh);});};return B(A3(_xH,_1cO,_ze,_1gf));});return B(_wQ(function(_1gk){var _1gl=E(_1gk);return (_1gl._==3)?(!B(_lT(_1gl.a,_1fR)))?new T0(2):E(_1ge):new T0(2);}));}),_1gm=function(_1gn){return E(_1gd);};return new T1(1,function(_1go){return new F(function(){return A2(_vx,_1go,_1gm);});});}});if(_1g2>10){return B(_lf(_jU,_1gc));}else{var _1gp=new T(function(){var _1gq=new T(function(){var _1gr=function(_1gs){return new F(function(){return A3(_xH,_1fS,_ze,function(_1gt){return new F(function(){return A1(_1fU,new T2(10,_1gs,_1gt));});});});};return B(A3(_xH,_1cO,_ze,_1gr));});return B(_wQ(function(_1gu){var _1gv=E(_1gu);return (_1gv._==3)?(!B(_lT(_1gv.a,_1fQ)))?new T0(2):E(_1gq):new T0(2);}));}),_1gw=function(_1gx){return E(_1gp);};return B(_lf(new T1(1,function(_1gy){return new F(function(){return A2(_vx,_1gy,_1gw);});}),_1gc));}});if(_1g2>10){return B(_lf(_jU,_1gb));}else{var _1gz=new T(function(){var _1gA=new T(function(){var _1gB=function(_1gC){return new F(function(){return A3(_xH,_1fS,_ze,function(_1gD){return new F(function(){return A1(_1fU,new T2(9,_1gC,_1gD));});});});};return B(A3(_xH,_1cz,_ze,_1gB));});return B(_wQ(function(_1gE){var _1gF=E(_1gE);return (_1gF._==3)?(!B(_lT(_1gF.a,_1fP)))?new T0(2):E(_1gA):new T0(2);}));}),_1gG=function(_1gH){return E(_1gz);};return B(_lf(new T1(1,function(_1gI){return new F(function(){return A2(_vx,_1gI,_1gG);});}),_1gb));}});if(_1g2>10){return B(_lf(_jU,_1ga));}else{var _1gJ=new T(function(){var _1gK=new T(function(){var _1gL=function(_1gM){var _1gN=function(_1gO){return new F(function(){return A3(_xH,_1fS,_ze,function(_1gP){return new F(function(){return A1(_1fU,new T3(8,_1gM,_1gO,_1gP));});});});};return new F(function(){return A3(_xH,_1fS,_ze,_1gN);});};return B(A3(_xH,_1cz,_ze,_1gL));});return B(_wQ(function(_1gQ){var _1gR=E(_1gQ);return (_1gR._==3)?(!B(_lT(_1gR.a,_1fO)))?new T0(2):E(_1gK):new T0(2);}));}),_1gS=function(_1gT){return E(_1gJ);};return B(_lf(new T1(1,function(_1gU){return new F(function(){return A2(_vx,_1gU,_1gS);});}),_1ga));}});if(_1g2>10){return B(_lf(_jU,_1g9));}else{var _1gV=new T(function(){var _1gW=new T(function(){return B(A3(_xH,_1cz,_ze,function(_1gX){return new F(function(){return A1(_1fU,new T1(7,_1gX));});}));});return B(_wQ(function(_1gY){var _1gZ=E(_1gY);return (_1gZ._==3)?(!B(_lT(_1gZ.a,_1fG)))?new T0(2):E(_1gW):new T0(2);}));}),_1h0=function(_1h1){return E(_1gV);};return B(_lf(new T1(1,function(_1h2){return new F(function(){return A2(_vx,_1h2,_1h0);});}),_1g9));}});if(_1g2>10){return B(_lf(_jU,_1g8));}else{var _1h3=new T(function(){var _1h4=new T(function(){var _1h5=function(_1h6){var _1h7=function(_1h8){var _1h9=function(_1ha){return new F(function(){return A3(_xH,_1fS,_ze,function(_1hb){return new F(function(){return A1(_1fU,new T4(6,_1h6,_1h8,_1ha,_1hb));});});});};return new F(function(){return A3(_xH,_1fS,_ze,_1h9);});};return new F(function(){return A3(_xS,_yl,_ze,_1h7);});};return B(A3(_xH,_1eg,_ze,_1h5));});return B(_wQ(function(_1hc){var _1hd=E(_1hc);return (_1hd._==3)?(!B(_lT(_1hd.a,_1fN)))?new T0(2):E(_1h4):new T0(2);}));}),_1he=function(_1hf){return E(_1h3);};return B(_lf(new T1(1,function(_1hg){return new F(function(){return A2(_vx,_1hg,_1he);});}),_1g8));}});if(_1g2>10){return B(_lf(_jU,_1g7));}else{var _1hh=new T(function(){var _1hi=new T(function(){var _1hj=function(_1hk){var _1hl=function(_1hm){return new F(function(){return A3(_xH,_1fS,_ze,function(_1hn){return new F(function(){return A1(_1fU,new T3(5,_1hk,_1hm,_1hn));});});});};return new F(function(){return A3(_xH,_1fS,_ze,_1hl);});};return B(A3(_xH,_1eg,_ze,_1hj));});return B(_wQ(function(_1ho){var _1hp=E(_1ho);return (_1hp._==3)?(!B(_lT(_1hp.a,_1fM)))?new T0(2):E(_1hi):new T0(2);}));}),_1hq=function(_1hr){return E(_1hh);};return B(_lf(new T1(1,function(_1hs){return new F(function(){return A2(_vx,_1hs,_1hq);});}),_1g7));}});if(_1g2>10){return B(_lf(_jU,_1g6));}else{var _1ht=new T(function(){var _1hu=new T(function(){var _1hv=function(_1hw){return new F(function(){return A3(_xH,_1fS,_ze,function(_1hx){return new F(function(){return A1(_1fU,new T2(4,_1hw,_1hx));});});});};return B(A3(_xH,_1fS,_ze,_1hv));});return B(_wQ(function(_1hy){var _1hz=E(_1hy);return (_1hz._==3)?(!B(_lT(_1hz.a,_1fL)))?new T0(2):E(_1hu):new T0(2);}));}),_1hA=function(_1hB){return E(_1ht);};return B(_lf(new T1(1,function(_1hC){return new F(function(){return A2(_vx,_1hC,_1hA);});}),_1g6));}});if(_1g2>10){return B(_lf(_jU,_1g5));}else{var _1hD=new T(function(){var _1hE=new T(function(){var _1hF=function(_1hG){var _1hH=function(_1hI){var _1hJ=function(_1hK){var _1hL=function(_1hM){var _1hN=function(_1hO){return new F(function(){return A3(_xH,_1fS,_ze,function(_1hP){return new F(function(){return A1(_1fU,new T6(3,_1hG,_1hI,_1hK,_1hM,_1hO,_1hP));});});});};return new F(function(){return A3(_xS,_yl,_ze,_1hN);});};return new F(function(){return A3(_xH,_1d7,_ze,_1hL);});};return new F(function(){return A3(_xS,_yl,_ze,_1hJ);});};return new F(function(){return A3(_xS,_yl,_ze,_1hH);});};return B(A3(_xH,_AS,_ze,_1hF));});return B(_wQ(function(_1hQ){var _1hR=E(_1hQ);return (_1hR._==3)?(!B(_lT(_1hR.a,_1fK)))?new T0(2):E(_1hE):new T0(2);}));}),_1hS=function(_1hT){return E(_1hD);};return B(_lf(new T1(1,function(_1hU){return new F(function(){return A2(_vx,_1hU,_1hS);});}),_1g5));}});if(_1g2>10){return B(_lf(_jU,_1g4));}else{var _1hV=new T(function(){var _1hW=new T(function(){var _1hX=function(_1hY){return new F(function(){return A3(_xH,_1fS,_ze,function(_1hZ){return new F(function(){return A1(_1fU,new T2(2,_1hY,_1hZ));});});});};return B(A3(_xH,_BM,_ze,_1hX));});return B(_wQ(function(_1i0){var _1i1=E(_1i0);return (_1i1._==3)?(!B(_lT(_1i1.a,_1fJ)))?new T0(2):E(_1hW):new T0(2);}));}),_1i2=function(_1i3){return E(_1hV);};return B(_lf(new T1(1,function(_1i4){return new F(function(){return A2(_vx,_1i4,_1i2);});}),_1g4));}});if(_1g2>10){return B(_lf(_jU,_1g3));}else{var _1i5=new T(function(){var _1i6=new T(function(){var _1i7=function(_1i8){var _1i9=function(_1ia){var _1ib=function(_1ic){var _1id=function(_1ie){var _1if=function(_1ig){var _1ih=function(_1ii){return new F(function(){return A3(_xH,_1fS,_ze,function(_1ij){return new F(function(){return A1(_1fU,{_:1,a:_1i8,b:_1ia,c:_1ic,d:_1ie,e:_1ig,f:_1ii,g:_1ij});});});});};return new F(function(){return A3(_xH,_1fS,_ze,_1ih);});};return new F(function(){return A3(_xS,_yl,_ze,_1if);});};return new F(function(){return A3(_xS,_yl,_ze,_1id);});};return new F(function(){return A3(_xH,_1d7,_ze,_1ib);});};return new F(function(){return A3(_xS,_yl,_ze,_1i9);});};return B(A3(_xH,_BM,_ze,_1i7));});return B(_wQ(function(_1ik){var _1il=E(_1ik);return (_1il._==3)?(!B(_lT(_1il.a,_1fI)))?new T0(2):E(_1i6):new T0(2);}));}),_1im=function(_1in){return E(_1i5);};return B(_lf(new T1(1,function(_1io){return new F(function(){return A2(_vx,_1io,_1im);});}),_1g3));}});return new F(function(){return _lf(new T1(1,function(_1ip){return new F(function(){return A2(_vx,_1ip,_1fZ);});}),_1g1);});},_1iq=new T(function(){return B(A3(_xH,_1fS,_xn,_DB));}),_1ir=function(_1is,_){var _1it=__app0(E(_1aQ)),_1iu=eval(E(_1aP)),_1iv=__app1(E(_1iu),toJSStr(E(_1aS))),_1iw=__app1(E(_1iu),toJSStr(E(_1aR))),_1ix=__app1(E(_1aT),toJSStr(_1cd)),_1iy=new T(function(){var _1iz=B(_1ce(B(_l5(_1cb,new T(function(){var _1iA=String(_1iw);return fromJSStr(_1iA);})))));if(!_1iz._){return E(_1aY);}else{if(!E(_1iz.b)._){var _1iB=E(_1iz.a);return new T2(0,new T(function(){return B(_EV(_1iB.a));}),new T(function(){return B(_dJ(_1iB.b));}));}else{return E(_1aX);}}}),_1iC=new T(function(){var _1iD=B(_1ce(B(_l5(_1iq,new T(function(){var _1iE=String(_1it);return fromJSStr(_1iE);})))));if(!_1iD._){return E(_1cm);}else{if(!E(_1iD.b)._){return E(_1iD.a);}else{return E(_1cl);}}}),_1iF=new T(function(){var _1iG=B(_1ce(B(_l5(_1aW,new T(function(){var _1iH=String(_1iv);return fromJSStr(_1iH);})))));if(!_1iG._){return E(_1aV);}else{if(!E(_1iG.b)._){return E(_1iG.a);}else{return E(_1aU);}}}),_1iI=B(_1aE(new T2(0,_1cc,_1iF),_1is,_1iC,_1iy));return new F(function(){return _GL(_1iI.a,_1iI.b,_1iI.c,_1iI.d,_);});},_1iJ=new T(function(){return B(unCStr("contractInput"));}),_1iK="(function (t, s) {document.getElementById(t).value = s})",_1iL=function(_1iM,_1iN,_){var _1iO=eval(E(_1iK)),_1iP=__app2(E(_1iO),toJSStr(E(_1iM)),toJSStr(E(_1iN)));return new F(function(){return _F8(_);});},_1iQ=function(_1iR,_1iS,_1iT,_){var _1iU=E(_1iJ),_1iV=toJSStr(_1iU),_1iW=eval(E(_1aP)),_1iX=__app1(E(_1iW),_1iV),_1iY=B(_1ce(B(_l5(_DG,new T(function(){var _1iZ=String(_1iX);return fromJSStr(_1iZ);})))));if(!_1iY._){return E(_jT);}else{if(!E(_1iY.b)._){var _1j0=E(_1iY.a),_1j1=B(_jD(new T(function(){return B(_3G(_1j0.a));},1),new T(function(){return B(_83(_1j0.b));},1),new T(function(){return B(_fp(_1iT,_1iR,_1iS,B(_gT(_1j0.c))));},1),new T(function(){return B(_dJ(_1j0.d));},1))),_1j2=B(_1iL(_1iU,new T2(1,_1j1.a,_1j1.b),_)),_1j3=__app1(E(_1iW),_1iV),_1j4=new T(function(){var _1j5=B(_1ce(B(_l5(_DG,new T(function(){var _1j6=String(_1j3);return fromJSStr(_1j6);})))));if(!_1j5._){return E(_jT);}else{if(!E(_1j5.b)._){var _1j7=E(_1j5.a);return new T4(0,new T(function(){return B(_3G(_1j7.a));}),new T(function(){return B(_83(_1j7.b));}),new T(function(){return B(_gT(_1j7.c));}),new T(function(){return B(_dJ(_1j7.d));}));}else{return E(_jR);}}});return new F(function(){return _1ir(_1j4,_);});}else{return E(_jR);}}},_1j8=function(_1j9,_1ja,_1jb,_1jc,_1jd){var _1je=E(_1jd);if(!_1je._){var _1jf=_1je.c,_1jg=_1je.d,_1jh=E(_1je.b),_1ji=E(_1jh.a);if(_1j9>=_1ji){if(_1j9!=_1ji){return new F(function(){return _H(_1jh,_1jf,B(_1j8(_1j9,_,_1jb,_1jc,_1jg)));});}else{var _1jj=E(_1jh.b);if(_1jb>=_1jj){if(_1jb!=_1jj){return new F(function(){return _H(_1jh,_1jf,B(_1j8(_1j9,_,_1jb,_1jc,_1jg)));});}else{var _1jk=E(_1jh.c);if(_1jc>=_1jk){if(_1jc!=_1jk){return new F(function(){return _H(_1jh,_1jf,B(_1j8(_1j9,_,_1jb,_1jc,_1jg)));});}else{return new T4(0,_1je.a,E(new T3(0,_1j9,_1jb,_1jc)),E(_1jf),E(_1jg));}}else{return new F(function(){return _5(_1jh,B(_1j8(_1j9,_,_1jb,_1jc,_1jf)),_1jg);});}}}else{return new F(function(){return _5(_1jh,B(_1j8(_1j9,_,_1jb,_1jc,_1jf)),_1jg);});}}}else{return new F(function(){return _5(_1jh,B(_1j8(_1j9,_,_1jb,_1jc,_1jf)),_1jg);});}}else{return new T4(0,1,E(new T3(0,_1j9,_1jb,_1jc)),E(_0),E(_0));}},_1jl=function(_1jm,_1jn,_1jo,_1jp,_1jq){var _1jr=E(_1jq);if(!_1jr._){var _1js=_1jr.c,_1jt=_1jr.d,_1ju=E(_1jr.b),_1jv=E(_1ju.a);if(_1jm>=_1jv){if(_1jm!=_1jv){return new F(function(){return _H(_1ju,_1js,B(_1jl(_1jm,_,_1jo,_1jp,_1jt)));});}else{var _1jw=E(_1ju.b);if(_1jo>=_1jw){if(_1jo!=_1jw){return new F(function(){return _H(_1ju,_1js,B(_1jl(_1jm,_,_1jo,_1jp,_1jt)));});}else{var _1jx=E(_1jp),_1jy=E(_1ju.c);if(_1jx>=_1jy){if(_1jx!=_1jy){return new F(function(){return _H(_1ju,_1js,B(_1j8(_1jm,_,_1jo,_1jx,_1jt)));});}else{return new T4(0,_1jr.a,E(new T3(0,_1jm,_1jo,_1jx)),E(_1js),E(_1jt));}}else{return new F(function(){return _5(_1ju,B(_1j8(_1jm,_,_1jo,_1jx,_1js)),_1jt);});}}}else{return new F(function(){return _5(_1ju,B(_1jl(_1jm,_,_1jo,_1jp,_1js)),_1jt);});}}}else{return new F(function(){return _5(_1ju,B(_1jl(_1jm,_,_1jo,_1jp,_1js)),_1jt);});}}else{return new T4(0,1,E(new T3(0,_1jm,_1jo,_1jp)),E(_0),E(_0));}},_1jz=function(_1jA,_1jB,_1jC,_1jD,_1jE){var _1jF=E(_1jE);if(!_1jF._){var _1jG=_1jF.c,_1jH=_1jF.d,_1jI=E(_1jF.b),_1jJ=E(_1jI.a);if(_1jA>=_1jJ){if(_1jA!=_1jJ){return new F(function(){return _H(_1jI,_1jG,B(_1jz(_1jA,_,_1jC,_1jD,_1jH)));});}else{var _1jK=E(_1jC),_1jL=E(_1jI.b);if(_1jK>=_1jL){if(_1jK!=_1jL){return new F(function(){return _H(_1jI,_1jG,B(_1jl(_1jA,_,_1jK,_1jD,_1jH)));});}else{var _1jM=E(_1jD),_1jN=E(_1jI.c);if(_1jM>=_1jN){if(_1jM!=_1jN){return new F(function(){return _H(_1jI,_1jG,B(_1j8(_1jA,_,_1jK,_1jM,_1jH)));});}else{return new T4(0,_1jF.a,E(new T3(0,_1jA,_1jK,_1jM)),E(_1jG),E(_1jH));}}else{return new F(function(){return _5(_1jI,B(_1j8(_1jA,_,_1jK,_1jM,_1jG)),_1jH);});}}}else{return new F(function(){return _5(_1jI,B(_1jl(_1jA,_,_1jK,_1jD,_1jG)),_1jH);});}}}else{return new F(function(){return _5(_1jI,B(_1jz(_1jA,_,_1jC,_1jD,_1jG)),_1jH);});}}else{return new T4(0,1,E(new T3(0,_1jA,_1jC,_1jD)),E(_0),E(_0));}},_1jO=function(_1jP,_1jQ,_1jR,_1jS){var _1jT=E(_1jS);if(!_1jT._){var _1jU=_1jT.c,_1jV=_1jT.d,_1jW=E(_1jT.b),_1jX=E(_1jP),_1jY=E(_1jW.a);if(_1jX>=_1jY){if(_1jX!=_1jY){return new F(function(){return _H(_1jW,_1jU,B(_1jz(_1jX,_,_1jQ,_1jR,_1jV)));});}else{var _1jZ=E(_1jQ),_1k0=E(_1jW.b);if(_1jZ>=_1k0){if(_1jZ!=_1k0){return new F(function(){return _H(_1jW,_1jU,B(_1jl(_1jX,_,_1jZ,_1jR,_1jV)));});}else{var _1k1=E(_1jR),_1k2=E(_1jW.c);if(_1k1>=_1k2){if(_1k1!=_1k2){return new F(function(){return _H(_1jW,_1jU,B(_1j8(_1jX,_,_1jZ,_1k1,_1jV)));});}else{return new T4(0,_1jT.a,E(new T3(0,_1jX,_1jZ,_1k1)),E(_1jU),E(_1jV));}}else{return new F(function(){return _5(_1jW,B(_1j8(_1jX,_,_1jZ,_1k1,_1jU)),_1jV);});}}}else{return new F(function(){return _5(_1jW,B(_1jl(_1jX,_,_1jZ,_1jR,_1jU)),_1jV);});}}}else{return new F(function(){return _5(_1jW,B(_1jz(_1jX,_,_1jQ,_1jR,_1jU)),_1jV);});}}else{return new T4(0,1,E(new T3(0,_1jP,_1jQ,_1jR)),E(_0),E(_0));}},_1k3=function(_1k4,_1k5,_1k6,_){var _1k7=E(_1iJ),_1k8=toJSStr(_1k7),_1k9=eval(E(_1aP)),_1ka=__app1(E(_1k9),_1k8),_1kb=B(_1ce(B(_l5(_DG,new T(function(){var _1kc=String(_1ka);return fromJSStr(_1kc);})))));if(!_1kb._){return E(_jT);}else{if(!E(_1kb.b)._){var _1kd=E(_1kb.a),_1ke=B(_jD(new T(function(){return B(_3G(_1kd.a));},1),new T(function(){return B(_1jO(_1k6,_1k4,_1k5,B(_83(_1kd.b))));},1),new T(function(){return B(_gT(_1kd.c));},1),new T(function(){return B(_dJ(_1kd.d));},1))),_1kf=B(_1iL(_1k7,new T2(1,_1ke.a,_1ke.b),_)),_1kg=__app1(E(_1k9),_1k8),_1kh=new T(function(){var _1ki=B(_1ce(B(_l5(_DG,new T(function(){var _1kj=String(_1kg);return fromJSStr(_1kj);})))));if(!_1ki._){return E(_jT);}else{if(!E(_1ki.b)._){var _1kk=E(_1ki.a);return new T4(0,new T(function(){return B(_3G(_1kk.a));}),new T(function(){return B(_83(_1kk.b));}),new T(function(){return B(_gT(_1kk.c));}),new T(function(){return B(_dJ(_1kk.d));}));}else{return E(_jR);}}});return new F(function(){return _1ir(_1kh,_);});}else{return E(_jR);}}},_1kl=function(_1km,_1kn,_1ko,_1kp,_){var _1kq=E(_1iJ),_1kr=toJSStr(_1kq),_1ks=eval(E(_1aP)),_1kt=__app1(E(_1ks),_1kr),_1ku=B(_1ce(B(_l5(_DG,new T(function(){var _1kv=String(_1kt);return fromJSStr(_1kv);})))));if(!_1ku._){return E(_jT);}else{if(!E(_1ku.b)._){var _1kw=E(_1ku.a),_1kx=B(_jD(new T(function(){return B(_1h(_1ko,_1km,_1kn,_1kp,B(_3G(_1kw.a))));},1),new T(function(){return B(_83(_1kw.b));},1),new T(function(){return B(_gT(_1kw.c));},1),new T(function(){return B(_dJ(_1kw.d));},1))),_1ky=B(_1iL(_1kq,new T2(1,_1kx.a,_1kx.b),_)),_1kz=__app1(E(_1ks),_1kr),_1kA=new T(function(){var _1kB=B(_1ce(B(_l5(_DG,new T(function(){var _1kC=String(_1kz);return fromJSStr(_1kC);})))));if(!_1kB._){return E(_jT);}else{if(!E(_1kB.b)._){var _1kD=E(_1kB.a);return new T4(0,new T(function(){return B(_3G(_1kD.a));}),new T(function(){return B(_83(_1kD.b));}),new T(function(){return B(_gT(_1kD.c));}),new T(function(){return B(_dJ(_1kD.d));}));}else{return E(_jR);}}});return new F(function(){return _1ir(_1kA,_);});}else{return E(_jR);}}},_1kE=new T(function(){return B(err(_jS));}),_1kF=new T(function(){return B(unCStr("SICC"));}),_1kG=new T(function(){return B(unCStr("SIRC"));}),_1kH=new T(function(){return B(unCStr("SIP"));}),_1kI=11,_1kJ=function(_1kK,_1kL){var _1kM=new T(function(){var _1kN=new T(function(){if(_1kK>10){return new T0(2);}else{var _1kO=new T(function(){var _1kP=new T(function(){var _1kQ=function(_1kR){var _1kS=function(_1kT){return new F(function(){return A3(_xS,_yl,_1kI,function(_1kU){return new F(function(){return A1(_1kL,new T3(2,_1kR,_1kT,_1kU));});});});};return new F(function(){return A3(_xS,_yl,_1kI,_1kS);});};return B(A3(_xH,_AS,_1kI,_1kQ));});return B(_wQ(function(_1kV){var _1kW=E(_1kV);return (_1kW._==3)?(!B(_lT(_1kW.a,_1kH)))?new T0(2):E(_1kP):new T0(2);}));}),_1kX=function(_1kY){return E(_1kO);};return new T1(1,function(_1kZ){return new F(function(){return A2(_vx,_1kZ,_1kX);});});}});if(_1kK>10){return B(_lf(_jU,_1kN));}else{var _1l0=new T(function(){var _1l1=new T(function(){var _1l2=function(_1l3){var _1l4=function(_1l5){return new F(function(){return A3(_xS,_yl,_1kI,function(_1l6){return new F(function(){return A1(_1kL,new T3(1,_1l3,_1l5,_1l6));});});});};return new F(function(){return A3(_xS,_yl,_1kI,_1l4);});};return B(A3(_xH,_BM,_1kI,_1l2));});return B(_wQ(function(_1l7){var _1l8=E(_1l7);return (_1l8._==3)?(!B(_lT(_1l8.a,_1kG)))?new T0(2):E(_1l1):new T0(2);}));}),_1l9=function(_1la){return E(_1l0);};return B(_lf(new T1(1,function(_1lb){return new F(function(){return A2(_vx,_1lb,_1l9);});}),_1kN));}});if(_1kK>10){return new F(function(){return _lf(_jU,_1kM);});}else{var _1lc=new T(function(){var _1ld=new T(function(){var _1le=function(_1lf){var _1lg=function(_1lh){var _1li=function(_1lj){return new F(function(){return A3(_xS,_yl,_1kI,function(_1lk){return new F(function(){return A1(_1kL,new T4(0,_1lf,_1lh,_1lj,_1lk));});});});};return new F(function(){return A3(_xS,_yl,_1kI,_1li);});};return new F(function(){return A3(_xS,_yl,_1kI,_1lg);});};return B(A3(_xH,_BM,_1kI,_1le));});return B(_wQ(function(_1ll){var _1lm=E(_1ll);return (_1lm._==3)?(!B(_lT(_1lm.a,_1kF)))?new T0(2):E(_1ld):new T0(2);}));}),_1ln=function(_1lo){return E(_1lc);};return new F(function(){return _lf(new T1(1,function(_1lp){return new F(function(){return A2(_vx,_1lp,_1ln);});}),_1kM);});}},_1lq=function(_1lr,_1ls){return new F(function(){return _1kJ(E(_1lr),_1ls);});},_1lt=new T(function(){return B(A3(_xH,_1lq,_xn,_DB));}),_1lu=function(_1lv,_){var _1lw=B(_1ce(B(_l5(_1lt,_1lv))));if(!_1lw._){return E(_1kE);}else{if(!E(_1lw.b)._){var _1lx=E(_1lw.a);switch(_1lx._){case 0:return new F(function(){return _1kl(_1lx.b,_1lx.c,_1lx.a,_1lx.d,_);});break;case 1:return new F(function(){return _1k3(_1lx.b,_1lx.c,_1lx.a,_);});break;default:return new F(function(){return _1iQ(_1lx.b,_1lx.c,_1lx.a,_);});}}else{return E(_hb);}}},_1ly=function(_1lz,_1lA,_1lB,_){var _1lC=E(_1iJ),_1lD=toJSStr(_1lC),_1lE=eval(E(_1aP)),_1lF=__app1(E(_1lE),_1lD),_1lG=B(_1ce(B(_l5(_DG,new T(function(){var _1lH=String(_1lF);return fromJSStr(_1lH);})))));if(!_1lG._){return E(_jT);}else{if(!E(_1lG.b)._){var _1lI=E(_1lG.a),_1lJ=B(_jD(new T(function(){return B(_3G(_1lI.a));},1),new T(function(){return B(_83(_1lI.b));},1),new T(function(){return B(_gT(_1lI.c));},1),new T(function(){return B(_cf(_1lB,_1lz,_1lA,B(_dJ(_1lI.d))));},1))),_1lK=B(_1iL(_1lC,new T2(1,_1lJ.a,_1lJ.b),_)),_1lL=__app1(E(_1lE),_1lD),_1lM=new T(function(){var _1lN=B(_1ce(B(_l5(_DG,new T(function(){var _1lO=String(_1lL);return fromJSStr(_1lO);})))));if(!_1lN._){return E(_jT);}else{if(!E(_1lN.b)._){var _1lP=E(_1lN.a);return new T4(0,new T(function(){return B(_3G(_1lP.a));}),new T(function(){return B(_83(_1lP.b));}),new T(function(){return B(_gT(_1lP.c));}),new T(function(){return B(_dJ(_1lP.d));}));}else{return E(_jR);}}});return new F(function(){return _1ir(_1lM,_);});}else{return E(_jR);}}},_1lQ=new T(function(){return B(err(_ha));}),_1lR=new T(function(){return B(err(_jS));}),_1lS=new T(function(){return B(_A0(_zE,_zd,_DB));}),_1lT=function(_1lU,_1lV,_){var _1lW=new T(function(){var _1lX=B(_1ce(B(_l5(_1lS,_1lU))));if(!_1lX._){return E(_1lR);}else{if(!E(_1lX.b)._){var _1lY=E(_1lX.a);return new T2(0,_1lY.a,_1lY.b);}else{return E(_1lQ);}}});return new F(function(){return _1ly(new T(function(){return E(E(_1lW).b);}),_1lV,new T(function(){return E(E(_1lW).a);}),_);});},_1lZ=new T(function(){return B(unCStr("OBind"));}),_1m0=new T(function(){return B(unCStr("OUnbind"));}),_1m1=new T(function(){return B(unCStr("CUnbind"));}),_1m2=new T(function(){return B(unCStr("CBind"));}),_1m3=new T(function(){return B(unCStr("CReplace"));}),_1m4=new T(function(){return B(unCStr("When"));}),_1m5=new T(function(){return B(unCStr("Choice"));}),_1m6=new T(function(){return B(unCStr("Both"));}),_1m7=new T(function(){return B(unCStr("Pay"));}),_1m8=new T(function(){return B(unCStr("RedeemCC"));}),_1m9=new T(function(){return B(unCStr("CommitCash"));}),_1ma=new T(function(){return B(unCStr("Null"));}),_1mb=32,_1mc=new T2(1,_1mb,_1M),_1md=function(_1me){var _1mf=E(_1me);return (_1mf==1)?E(_1mc):new T2(1,_1mb,new T(function(){return B(_1md(_1mf-1|0));}));},_1mg=new T(function(){return B(unCStr("head"));}),_1mh=new T(function(){return B(_io(_1mg));}),_1mi=function(_1mj){return new F(function(){return _hA(0,E(_1mj),_1M);});},_1mk=new T(function(){return B(unCStr("IdentOBind"));}),_1ml=new T(function(){return B(unCStr("OReplace"));}),_1mm=new T(function(){return B(unCStr("FalseObs"));}),_1mn=new T(function(){return B(unCStr("TrueObs"));}),_1mo=new T(function(){return B(unCStr("ValueGE"));}),_1mp=new T(function(){return B(unCStr("PersonChoseSomething"));}),_1mq=new T(function(){return B(unCStr("PersonChoseThis"));}),_1mr=new T(function(){return B(unCStr("NotObs"));}),_1ms=new T(function(){return B(unCStr("OrObs"));}),_1mt=new T(function(){return B(unCStr("AndObs"));}),_1mu=new T(function(){return B(unCStr("BelowTimeout"));}),_1mv=new T(function(){return B(unCStr("IdentCBind"));}),_1mw=new T(function(){return B(unCStr("IdentPay"));}),_1mx=new T(function(){return B(unCStr("IdentChoice"));}),_1my=new T(function(){return B(unCStr("IdentCC"));}),_1mz=new T(function(){return B(unCStr("MoneyFromChoice"));}),_1mA=new T(function(){return B(unCStr("ConstMoney"));}),_1mB=new T(function(){return B(unCStr("AddMoney"));}),_1mC=new T(function(){return B(unCStr("AvailableMoney"));}),_1mD=function(_1mE){var _1mF=E(_1mE);switch(_1mF._){case 0:var _1mG=E(_1mF.a);switch(_1mG._){case 0:return new T2(0,_1ma,_1M);case 1:return new T2(0,_1m9,new T2(1,new T1(3,_1mG.a),new T2(1,new T1(8,_1mG.b),new T2(1,new T1(2,_1mG.c),new T2(1,new T1(8,_1mG.d),new T2(1,new T1(8,_1mG.e),new T2(1,new T1(0,_1mG.f),new T2(1,new T1(0,_1mG.g),_1M))))))));case 2:return new T2(0,_1m8,new T2(1,new T1(3,_1mG.a),new T2(1,new T1(0,_1mG.b),_1M)));case 3:return new T2(0,_1m7,new T2(1,new T1(5,_1mG.a),new T2(1,new T1(8,_1mG.b),new T2(1,new T1(8,_1mG.c),new T2(1,new T1(2,_1mG.d),new T2(1,new T1(8,_1mG.e),new T2(1,new T1(0,_1mG.f),_1M)))))));case 4:return new T2(0,_1m6,new T2(1,new T1(0,_1mG.a),new T2(1,new T1(0,_1mG.b),_1M)));case 5:return new T2(0,_1m5,new T2(1,new T1(1,_1mG.a),new T2(1,new T1(0,_1mG.b),new T2(1,new T1(0,_1mG.c),_1M))));case 6:return new T2(0,_1m4,new T2(1,new T1(1,_1mG.a),new T2(1,new T1(8,_1mG.b),new T2(1,new T1(0,_1mG.c),new T2(1,new T1(0,_1mG.d),_1M)))));case 7:return new T2(0,_1m3,new T2(1,new T1(6,_1mG.a),_1M));case 8:return new T2(0,_1m2,new T2(1,new T1(6,_1mG.a),new T2(1,new T1(0,_1mG.b),new T2(1,new T1(0,_1mG.c),_1M))));case 9:return new T2(0,_1m1,new T2(1,new T1(6,_1mG.a),new T2(1,new T1(0,_1mG.b),_1M)));case 10:return new T2(0,_1m0,new T2(1,new T1(7,_1mG.a),new T2(1,new T1(0,_1mG.b),_1M)));default:return new T2(0,_1lZ,new T2(1,new T1(7,_1mG.a),new T2(1,new T1(1,_1mG.b),new T2(1,new T1(0,_1mG.c),_1M))));}break;case 1:var _1mH=E(_1mF.a);switch(_1mH._){case 0:return new T2(0,_1mu,new T2(1,new T1(8,_1mH.a),_1M));case 1:return new T2(0,_1mt,new T2(1,new T1(1,_1mH.a),new T2(1,new T1(1,_1mH.b),_1M)));case 2:return new T2(0,_1ms,new T2(1,new T1(1,_1mH.a),new T2(1,new T1(1,_1mH.b),_1M)));case 3:return new T2(0,_1mr,new T2(1,new T1(1,_1mH.a),_1M));case 4:return new T2(0,_1mq,new T2(1,new T1(4,_1mH.a),new T2(1,new T1(8,_1mH.b),new T2(1,new T1(8,_1mH.c),_1M))));case 5:return new T2(0,_1mp,new T2(1,new T1(4,_1mH.a),new T2(1,new T1(8,_1mH.b),_1M)));case 6:return new T2(0,_1mo,new T2(1,new T1(2,_1mH.a),new T2(1,new T1(2,_1mH.b),_1M)));case 7:return new T2(0,_1mn,_1M);case 8:return new T2(0,_1mm,_1M);default:return new T2(0,_1ml,new T2(1,new T1(7,_1mH.a),_1M));}break;case 2:var _1mI=E(_1mF.a);switch(_1mI._){case 0:return new T2(0,_1mC,new T2(1,new T1(3,_1mI.a),_1M));case 1:return new T2(0,_1mB,new T2(1,new T1(2,_1mI.a),new T2(1,new T1(2,_1mI.b),_1M)));case 2:return new T2(0,_1mA,new T2(1,new T1(8,_1mI.a),_1M));default:return new T2(0,_1mz,new T2(1,new T1(4,_1mI.a),new T2(1,new T1(8,_1mI.b),new T2(1,new T1(2,_1mI.c),_1M))));}break;case 3:return new T2(0,_1my,new T2(1,new T1(8,_1mF.a),_1M));case 4:return new T2(0,_1mx,new T2(1,new T1(8,_1mF.a),_1M));case 5:return new T2(0,_1mw,new T2(1,new T1(8,_1mF.a),_1M));case 6:return new T2(0,_1mv,new T2(1,new T1(8,_1mF.a),_1M));case 7:return new T2(0,_1mk,new T2(1,new T1(8,_1mF.a),_1M));default:return new T2(0,new T(function(){return B(_1mi(_1mF.a));}),_1M);}},_1mJ=function(_1mK){var _1mL=B(_1mD(_1mK)),_1mM=_1mL.a,_1mN=E(_1mL.b);if(!_1mN._){return new T1(0,new T2(0,_1mM,_1M));}else{switch(E(_1mK)._){case 0:return new T1(2,new T2(0,_1mM,_1mN));case 1:return new T1(2,new T2(0,_1mM,_1mN));case 2:return new T1(2,new T2(0,_1mM,_1mN));default:return new T1(1,new T2(0,_1mM,_1mN));}}},_1mO=function(_1mP,_1mQ){var _1mR=E(_1mQ);if(!_1mR._){return __Z;}else{var _1mS=_1mR.a,_1mT=new T(function(){var _1mU=B(_kG(new T(function(){return B(A1(_1mP,_1mS));}),_1mR.b));return new T2(0,_1mU.a,_1mU.b);});return new T2(1,new T2(1,_1mS,new T(function(){return E(E(_1mT).a);})),new T(function(){return B(_1mO(_1mP,E(_1mT).b));}));}},_1mV=function(_1mW){var _1mX=E(_1mW);if(!_1mX._){return __Z;}else{return new F(function(){return _hq(_1mX.a,new T(function(){return B(_1mV(_1mX.b));},1));});}},_1mY=function(_1mZ,_1n0){return (E(_1mZ)._==2)?false:(E(_1n0)._==2)?false:true;},_1n1=function(_1n2,_1n3){var _1n4=E(_1n3);return (_1n4._==0)?__Z:new T2(1,_1n2,new T2(1,_1n4.a,new T(function(){return B(_1n1(_1n2,_1n4.b));})));},_1n5=new T(function(){return B(unCStr("\n"));}),_1n6=new T(function(){return B(unCStr("tail"));}),_1n7=new T(function(){return B(_io(_1n6));}),_1n8=function(_1n9,_1na,_1nb){var _1nc=E(_1nb);if(!_1nc._){return E(_1na);}else{var _1nd=new T(function(){return (E(_1n9)+B(_oy(_1na,0))|0)+1|0;}),_1ne=new T(function(){return B(_1mO(_1mY,B(_oD(_1mJ,_1nc))));}),_1nf=new T(function(){var _1ng=E(_1ne);if(!_1ng._){return E(_1n7);}else{var _1nh=new T(function(){var _1ni=E(_1nd);if(0>=_1ni){return __Z;}else{return B(_1md(_1ni));}}),_1nj=function(_1nk){var _1nl=new T(function(){var _1nm=function(_1nn){var _1no=E(_1nn);if(!_1no._){return __Z;}else{var _1np=new T(function(){return B(_hq(B(_1nq(_1nd,_1no.a)),new T(function(){return B(_1nm(_1no.b));},1)));});return new T2(1,_1mb,_1np);}},_1nr=B(_1nm(_1nk));if(!_1nr._){return __Z;}else{return E(_1nr.b);}},1);return new F(function(){return _hq(_1nh,_1nl);});};return B(_1n1(_1n5,B(_oD(_1nj,_1ng.b))));}}),_1ns=new T(function(){var _1nt=new T(function(){var _1nu=E(_1ne);if(!_1nu._){return E(_1mh);}else{var _1nv=function(_1nw){var _1nx=E(_1nw);if(!_1nx._){return __Z;}else{var _1ny=new T(function(){return B(_hq(B(_1nq(_1nd,_1nx.a)),new T(function(){return B(_1nv(_1nx.b));},1)));});return new T2(1,_1mb,_1ny);}};return B(_1nv(_1nu.a));}},1);return B(_hq(_1na,_1nt));});return new F(function(){return _1mV(new T2(1,_1ns,_1nf));});}},_1nz=new T(function(){return B(unCStr(")"));}),_1nq=function(_1nA,_1nB){var _1nC=E(_1nB);switch(_1nC._){case 0:var _1nD=E(_1nC.a);return new F(function(){return _1nE(0,_1nD.a,_1nD.b);});break;case 1:return new F(function(){return unAppCStr("(",new T(function(){var _1nF=E(_1nC.a);return B(_hq(B(_1nE(0,_1nF.a,_1nF.b)),_1nz));}));});break;default:var _1nG=new T(function(){var _1nH=E(_1nC.a);return B(_hq(B(_1n8(new T(function(){return E(_1nA)+1|0;},1),_1nH.a,_1nH.b)),_1nz));});return new F(function(){return unAppCStr("(",_1nG);});}},_1nE=function(_1nI,_1nJ,_1nK){var _1nL=E(_1nK);if(!_1nL._){return E(_1nJ);}else{var _1nM=new T(function(){return (_1nI+B(_oy(_1nJ,0))|0)+1|0;}),_1nN=new T(function(){return B(_1mO(_1mY,B(_oD(_1mJ,_1nL))));}),_1nO=new T(function(){var _1nP=E(_1nN);if(!_1nP._){return E(_1n7);}else{var _1nQ=new T(function(){var _1nR=E(_1nM);if(0>=_1nR){return __Z;}else{return B(_1md(_1nR));}}),_1nS=function(_1nT){var _1nU=new T(function(){var _1nV=function(_1nW){var _1nX=E(_1nW);if(!_1nX._){return __Z;}else{var _1nY=new T(function(){return B(_hq(B(_1nq(_1nM,_1nX.a)),new T(function(){return B(_1nV(_1nX.b));},1)));});return new T2(1,_1mb,_1nY);}},_1nZ=B(_1nV(_1nT));if(!_1nZ._){return __Z;}else{return E(_1nZ.b);}},1);return new F(function(){return _hq(_1nQ,_1nU);});};return B(_1n1(_1n5,B(_oD(_1nS,_1nP.b))));}}),_1o0=new T(function(){var _1o1=new T(function(){var _1o2=E(_1nN);if(!_1o2._){return E(_1mh);}else{var _1o3=function(_1o4){var _1o5=E(_1o4);if(!_1o5._){return __Z;}else{var _1o6=new T(function(){return B(_hq(B(_1nq(_1nM,_1o5.a)),new T(function(){return B(_1o3(_1o5.b));},1)));});return new T2(1,_1mb,_1o6);}};return B(_1o3(_1o2.a));}},1);return B(_hq(_1nJ,_1o1));});return new F(function(){return _1mV(new T2(1,_1o0,_1nO));});}},_1o7=new T(function(){return B(_1nE(0,_1ma,_1M));}),_1o8=function(_1o9,_){return new T(function(){var _1oa=B(_1ce(B(_l5(_1iq,_1o9))));if(!_1oa._){return E(_1cm);}else{if(!E(_1oa.b)._){var _1ob=E(_1oa.a);switch(_1ob._){case 0:return E(_1o7);break;case 1:return B(_1nE(0,_1m9,new T2(1,new T1(3,_1ob.a),new T2(1,new T1(8,_1ob.b),new T2(1,new T1(2,_1ob.c),new T2(1,new T1(8,_1ob.d),new T2(1,new T1(8,_1ob.e),new T2(1,new T1(0,_1ob.f),new T2(1,new T1(0,_1ob.g),_1M)))))))));break;case 2:return B(_1nE(0,_1m8,new T2(1,new T1(3,_1ob.a),new T2(1,new T1(0,_1ob.b),_1M))));break;case 3:return B(_1nE(0,_1m7,new T2(1,new T1(5,_1ob.a),new T2(1,new T1(8,_1ob.b),new T2(1,new T1(8,_1ob.c),new T2(1,new T1(2,_1ob.d),new T2(1,new T1(8,_1ob.e),new T2(1,new T1(0,_1ob.f),_1M))))))));break;case 4:return B(_1nE(0,_1m6,new T2(1,new T1(0,_1ob.a),new T2(1,new T1(0,_1ob.b),_1M))));break;case 5:return B(_1nE(0,_1m5,new T2(1,new T1(1,_1ob.a),new T2(1,new T1(0,_1ob.b),new T2(1,new T1(0,_1ob.c),_1M)))));break;case 6:return B(_1nE(0,_1m4,new T2(1,new T1(1,_1ob.a),new T2(1,new T1(8,_1ob.b),new T2(1,new T1(0,_1ob.c),new T2(1,new T1(0,_1ob.d),_1M))))));break;case 7:return B(_1nE(0,_1m3,new T2(1,new T1(6,_1ob.a),_1M)));break;case 8:return B(_1nE(0,_1m2,new T2(1,new T1(6,_1ob.a),new T2(1,new T1(0,_1ob.b),new T2(1,new T1(0,_1ob.c),_1M)))));break;case 9:return B(_1nE(0,_1m1,new T2(1,new T1(6,_1ob.a),new T2(1,new T1(0,_1ob.b),_1M))));break;case 10:return B(_1nE(0,_1m0,new T2(1,new T1(7,_1ob.a),new T2(1,new T1(0,_1ob.b),_1M))));break;default:return B(_1nE(0,_1lZ,new T2(1,new T1(7,_1ob.a),new T2(1,new T1(1,_1ob.b),new T2(1,new T1(0,_1ob.c),_1M)))));}}else{return E(_1cl);}}});},_1oc=new T(function(){return B(unCStr("codeArea"));}),_1od=function(_){var _1oe=__app0(E(_1aQ)),_1of=B(_1o8(new T(function(){var _1og=String(_1oe);return fromJSStr(_1og);}),_)),_1oh=B(_1iL(_1oc,_1of,_)),_1oi=eval(E(_1aP)),_1oj=__app1(E(_1oi),toJSStr(E(_1iJ))),_1ok=new T(function(){var _1ol=B(_1ce(B(_l5(_DG,new T(function(){var _1om=String(_1oj);return fromJSStr(_1om);})))));if(!_1ol._){return E(_jT);}else{if(!E(_1ol.b)._){var _1on=E(_1ol.a);return new T4(0,new T(function(){return B(_3G(_1on.a));}),new T(function(){return B(_83(_1on.b));}),new T(function(){return B(_gT(_1on.c));}),new T(function(){return B(_dJ(_1on.d));}));}else{return E(_jR);}}});return new F(function(){return _1ir(_1ok,_);});},_1oo="(function (b) { return (b.inputList.length); })",_1op="(function (b, x) { return (b.inputList[x]); })",_1oq=function(_1or,_1os,_){var _1ot=eval(E(_1op)),_1ou=__app2(E(_1ot),_1or,_1os);return new T1(0,_1ou);},_1ov=function(_1ow,_1ox,_1oy,_){var _1oz=E(_1oy);if(!_1oz._){return _1M;}else{var _1oA=B(_1oq(_1ow,E(_1oz.a),_)),_1oB=B(_1ov(_1ow,_,_1oz.b,_));return new T2(1,_1oA,_1oB);}},_1oC=function(_1oD,_1oE){if(_1oD<=_1oE){var _1oF=function(_1oG){return new T2(1,_1oG,new T(function(){if(_1oG!=_1oE){return B(_1oF(_1oG+1|0));}else{return __Z;}}));};return new F(function(){return _1oF(_1oD);});}else{return __Z;}},_1oH=function(_1oI,_){var _1oJ=eval(E(_1oo)),_1oK=__app1(E(_1oJ),_1oI),_1oL=Number(_1oK),_1oM=jsTrunc(_1oL);return new F(function(){return _1ov(_1oI,_,new T(function(){return B(_1oC(0,_1oM-1|0));}),_);});},_1oN="(function (y, ip) {y.previousConnection.connect(ip.connection);})",_1oO="(function (x) { return x.name; })",_1oP=new T(function(){return B(unCStr("\""));}),_1oQ=function(_1oR){return new F(function(){return err(B(unAppCStr("No input matches \"",new T(function(){return B(_hq(_1oR,_1oP));}))));});},_1oS=function(_1oT,_1oU,_){var _1oV=E(_1oU);if(!_1oV._){return new F(function(){return _1oQ(_1oT);});}else{var _1oW=E(_1oV.a),_1oX=E(_1oO),_1oY=eval(_1oX),_1oZ=__app1(E(_1oY),E(_1oW.a)),_1p0=String(_1oZ);if(!B(_lT(fromJSStr(_1p0),_1oT))){var _1p1=function(_1p2,_1p3,_){while(1){var _1p4=E(_1p3);if(!_1p4._){return new F(function(){return _1oQ(_1p2);});}else{var _1p5=E(_1p4.a),_1p6=eval(_1oX),_1p7=__app1(E(_1p6),E(_1p5.a)),_1p8=String(_1p7);if(!B(_lT(fromJSStr(_1p8),_1p2))){_1p3=_1p4.b;continue;}else{return _1p5;}}}};return new F(function(){return _1p1(_1oT,_1oV.b,_);});}else{return _1oW;}}},_1p9=function(_1pa,_1pb,_1pc,_){var _1pd=B(_1oH(_1pb,_)),_1pe=B(_1oS(_1pa,_1pd,_)),_1pf=eval(E(_1oN)),_1pg=__app2(E(_1pf),E(E(_1pc).a),E(E(_1pe).a));return new F(function(){return _F8(_);});},_1ph="(function (y, ip) {y.outputConnection.connect(ip.connection);})",_1pi=function(_1pj,_1pk,_1pl,_){var _1pm=B(_1oH(_1pk,_)),_1pn=B(_1oS(_1pj,_1pm,_)),_1po=eval(E(_1ph)),_1pp=__app2(E(_1po),E(E(_1pl).a),E(E(_1pn).a));return new F(function(){return _F8(_);});},_1pq=function(_1pr){return new F(function(){return err(B(unAppCStr("No fieldrow matches \"",new T(function(){return B(_hq(_1pr,_1oP));}))));});},_1ps=function(_1pt,_1pu,_){var _1pv=E(_1pu);if(!_1pv._){return new F(function(){return _1pq(_1pt);});}else{var _1pw=E(_1pv.a),_1px=E(_1oO),_1py=eval(_1px),_1pz=__app1(E(_1py),E(_1pw.a)),_1pA=String(_1pz);if(!B(_lT(fromJSStr(_1pA),_1pt))){var _1pB=function(_1pC,_1pD,_){while(1){var _1pE=E(_1pD);if(!_1pE._){return new F(function(){return _1pq(_1pC);});}else{var _1pF=E(_1pE.a),_1pG=eval(_1px),_1pH=__app1(E(_1pG),E(_1pF.a)),_1pI=String(_1pH);if(!B(_lT(fromJSStr(_1pI),_1pC))){_1pD=_1pE.b;continue;}else{return _1pF;}}}};return new F(function(){return _1pB(_1pt,_1pv.b,_);});}else{return _1pw;}}},_1pJ="(function (b) { return (b.fieldRow.length); })",_1pK="(function (b, x) { return (b.fieldRow[x]); })",_1pL=function(_1pM,_1pN,_){var _1pO=eval(E(_1pK)),_1pP=__app2(E(_1pO),_1pM,_1pN);return new T1(0,_1pP);},_1pQ=function(_1pR,_1pS,_1pT,_){var _1pU=E(_1pT);if(!_1pU._){return _1M;}else{var _1pV=B(_1pL(_1pR,E(_1pU.a),_)),_1pW=B(_1pQ(_1pR,_,_1pU.b,_));return new T2(1,_1pV,_1pW);}},_1pX=function(_1pY,_){var _1pZ=eval(E(_1pJ)),_1q0=__app1(E(_1pZ),_1pY),_1q1=Number(_1q0),_1q2=jsTrunc(_1q1);return new F(function(){return _1pQ(_1pY,_,new T(function(){return B(_1oC(0,_1q2-1|0));}),_);});},_1q3=function(_1q4,_){var _1q5=E(_1q4);if(!_1q5._){return _1M;}else{var _1q6=B(_1pX(E(E(_1q5.a).a),_)),_1q7=B(_1q3(_1q5.b,_));return new T2(1,_1q6,_1q7);}},_1q8=function(_1q9){var _1qa=E(_1q9);if(!_1qa._){return __Z;}else{return new F(function(){return _hq(_1qa.a,new T(function(){return B(_1q8(_1qa.b));},1));});}},_1qb=function(_1qc,_1qd,_){var _1qe=B(_1oH(_1qd,_)),_1qf=B(_1q3(_1qe,_));return new F(function(){return _1ps(_1qc,B(_1q8(_1qf)),_);});},_1qg=function(_1qh,_1qi,_1qj,_){var _1qk=B(_1oH(_1qi,_)),_1ql=B(_1oS(_1qh,_1qk,_)),_1qm=eval(E(_1ph)),_1qn=__app2(E(_1qm),E(E(_1qj).a),E(E(_1ql).a));return new F(function(){return _F8(_);});},_1qo=new T(function(){return B(unCStr("contract_commitcash"));}),_1qp=new T(function(){return B(unCStr("contract_redeemcc"));}),_1qq=new T(function(){return B(unCStr("contract_bindobservation"));}),_1qr=new T(function(){return B(unCStr("contract_pay"));}),_1qs=new T(function(){return B(unCStr("contract_both"));}),_1qt=new T(function(){return B(unCStr("contract_choice"));}),_1qu=new T(function(){return B(unCStr("contract_when"));}),_1qv=new T(function(){return B(unCStr("contract_replacecontractbind"));}),_1qw=new T(function(){return B(unCStr("contract_bindcontract"));}),_1qx=new T(function(){return B(unCStr("contract_unbindcontract"));}),_1qy=new T(function(){return B(unCStr("contract_unbindobservation"));}),_1qz="(function (x) {var c = demoWorkspace.newBlock(x); c.initSvg(); return c;})",_1qA=function(_1qB,_){var _1qC=eval(E(_1qz)),_1qD=__app1(E(_1qC),toJSStr(E(_1qB)));return new T1(0,_1qD);},_1qE=new T(function(){return B(unCStr("ammount"));}),_1qF=new T(function(){return B(unCStr("payee_id"));}),_1qG=new T(function(){return B(unCStr("payer_id"));}),_1qH=new T(function(){return B(unCStr("pay_id"));}),_1qI=new T(function(){return B(unCStr("ccommit_id"));}),_1qJ=new T(function(){return B(unCStr("end_expiration"));}),_1qK=new T(function(){return B(unCStr("start_expiration"));}),_1qL=new T(function(){return B(unCStr("person_id"));}),_1qM=new T(function(){return B(unCStr("contract_null"));}),_1qN=new T(function(){return B(unCStr("contract"));}),_1qO=new T(function(){return B(unCStr("observation"));}),_1qP=new T(function(){return B(unCStr("obind_id"));}),_1qQ=new T(function(){return B(unCStr("cbind_id"));}),_1qR=new T(function(){return B(unCStr("contract2"));}),_1qS=new T(function(){return B(unCStr("contract1"));}),_1qT=new T(function(){return B(unCStr("timeout"));}),_1qU=new T(function(){return B(unCStr("expiration"));}),_1qV=new T(function(){return B(unCStr("value_available_money"));}),_1qW=new T(function(){return B(unCStr("value_add_money"));}),_1qX=new T(function(){return B(unCStr("value_const_money"));}),_1qY=new T(function(){return B(unCStr("money_from_choice"));}),_1qZ=new T(function(){return B(unCStr("value2"));}),_1r0=new T(function(){return B(unCStr("value1"));}),_1r1=new T(function(){return B(unCStr("choice_id"));}),_1r2=new T(function(){return B(unCStr("default"));}),_1r3=new T(function(){return B(unCStr("money"));}),_1r4=new T(function(){return B(unCStr("commit_id"));}),_1r5="(function (b, s) { return (b.setText(s)); })",_1r6=function(_1r7,_){var _1r8=E(_1r7);switch(_1r8._){case 0:var _1r9=B(_1qA(_1qV,_)),_1ra=E(_1r9),_1rb=B(_1qb(_1r4,E(_1ra.a),_)),_1rc=eval(E(_1r5)),_1rd=__app2(E(_1rc),E(E(_1rb).a),toJSStr(B(_hA(0,E(_1r8.a),_1M))));return _1ra;case 1:var _1re=B(_1r6(_1r8.a,_)),_1rf=B(_1r6(_1r8.b,_)),_1rg=B(_1qA(_1qW,_)),_1rh=E(_1rg),_1ri=E(_1rh.a),_1rj=B(_1pi(_1r0,_1ri,_1re,_)),_1rk=B(_1pi(_1qZ,_1ri,_1rf,_));return _1rh;case 2:var _1rl=B(_1qA(_1qX,_)),_1rm=E(_1rl),_1rn=B(_1qb(_1r3,E(_1rm.a),_)),_1ro=eval(E(_1r5)),_1rp=__app2(E(_1ro),E(E(_1rn).a),toJSStr(B(_hA(0,E(_1r8.a),_1M))));return _1rm;default:var _1rq=B(_1r6(_1r8.c,_)),_1rr=B(_1qA(_1qY,_)),_1rs=E(_1rr),_1rt=E(_1rs.a),_1ru=B(_1qb(_1r1,_1rt,_)),_1rv=eval(E(_1r5)),_1rw=__app2(E(_1rv),E(E(_1ru).a),toJSStr(B(_hA(0,E(_1r8.a),_1M)))),_1rx=B(_1qb(_1qL,_1rt,_)),_1ry=__app2(E(_1rv),E(E(_1rx).a),toJSStr(B(_hA(0,E(_1r8.b),_1M)))),_1rz=B(_1pi(_1r2,_1rt,_1rq,_));return _1rs;}},_1rA=new T(function(){return B(unCStr("observation_belowtimeout"));}),_1rB=new T(function(){return B(unCStr("observation_andobs"));}),_1rC=new T(function(){return B(unCStr("observation_orobs"));}),_1rD=new T(function(){return B(unCStr("observation_notobs"));}),_1rE=new T(function(){return B(unCStr("observation_personchosethis"));}),_1rF=new T(function(){return B(unCStr("observation_personchosesomething"));}),_1rG=new T(function(){return B(unCStr("observation_value_ge"));}),_1rH=new T(function(){return B(unCStr("observation_trueobs"));}),_1rI=new T(function(){return B(unCStr("observation_falseobs"));}),_1rJ=new T(function(){return B(unCStr("observation_replaceobservationbind"));}),_1rK=new T(function(){return B(unCStr("person"));}),_1rL=new T(function(){return B(unCStr("choice_value"));}),_1rM=new T(function(){return B(unCStr("observation2"));}),_1rN=new T(function(){return B(unCStr("observation1"));}),_1rO=new T(function(){return B(unCStr("block_number"));}),_1rP=function(_1rQ,_){var _1rR=E(_1rQ);switch(_1rR._){case 0:var _1rS=B(_1qA(_1rA,_)),_1rT=E(_1rS),_1rU=B(_1qb(_1rO,E(_1rT.a),_)),_1rV=eval(E(_1r5)),_1rW=__app2(E(_1rV),E(E(_1rU).a),toJSStr(B(_hA(0,E(_1rR.a),_1M))));return _1rT;case 1:var _1rX=B(_1rP(_1rR.a,_)),_1rY=B(_1rP(_1rR.b,_)),_1rZ=B(_1qA(_1rB,_)),_1s0=E(_1rZ),_1s1=E(_1s0.a),_1s2=B(_1qg(_1rN,_1s1,_1rX,_)),_1s3=B(_1qg(_1rM,_1s1,_1rY,_));return _1s0;case 2:var _1s4=B(_1rP(_1rR.a,_)),_1s5=B(_1rP(_1rR.b,_)),_1s6=B(_1qA(_1rC,_)),_1s7=E(_1s6),_1s8=E(_1s7.a),_1s9=B(_1qg(_1rN,_1s8,_1s4,_)),_1sa=B(_1qg(_1rM,_1s8,_1s5,_));return _1s7;case 3:var _1sb=B(_1rP(_1rR.a,_)),_1sc=B(_1qA(_1rD,_)),_1sd=E(_1sc),_1se=B(_1qg(_1qO,E(_1sd.a),_1sb,_));return _1sd;case 4:var _1sf=B(_1qA(_1rE,_)),_1sg=E(_1sf),_1sh=E(_1sg.a),_1si=B(_1qb(_1r1,_1sh,_)),_1sj=eval(E(_1r5)),_1sk=__app2(E(_1sj),E(E(_1si).a),toJSStr(B(_hA(0,E(_1rR.a),_1M)))),_1sl=B(_1qb(_1rK,_1sh,_)),_1sm=__app2(E(_1sj),E(E(_1sl).a),toJSStr(B(_hA(0,E(_1rR.b),_1M)))),_1sn=B(_1qb(_1rL,_1sh,_)),_1so=__app2(E(_1sj),E(E(_1sn).a),toJSStr(B(_hA(0,E(_1rR.c),_1M))));return _1sg;case 5:var _1sp=B(_1qA(_1rF,_)),_1sq=E(_1sp),_1sr=E(_1sq.a),_1ss=B(_1qb(_1r1,_1sr,_)),_1st=eval(E(_1r5)),_1su=__app2(E(_1st),E(E(_1ss).a),toJSStr(B(_hA(0,E(_1rR.a),_1M)))),_1sv=B(_1qb(_1rK,_1sr,_)),_1sw=__app2(E(_1st),E(E(_1sv).a),toJSStr(B(_hA(0,E(_1rR.b),_1M))));return _1sq;case 6:var _1sx=B(_1r6(_1rR.a,_)),_1sy=B(_1r6(_1rR.b,_)),_1sz=B(_1qA(_1rG,_)),_1sA=E(_1sz),_1sB=E(_1sA.a),_1sC=B(_1pi(_1r0,_1sB,_1sx,_)),_1sD=B(_1pi(_1qZ,_1sB,_1sy,_));return _1sA;case 7:return new F(function(){return _1qA(_1rH,_);});break;case 8:return new F(function(){return _1qA(_1rI,_);});break;default:var _1sE=B(_1qA(_1rJ,_)),_1sF=E(_1sE),_1sG=B(_1qb(_1qP,E(_1sF.a),_)),_1sH=eval(E(_1r5)),_1sI=__app2(E(_1sH),E(E(_1sG).a),toJSStr(B(_hA(0,E(_1rR.a),_1M))));return _1sF;}},_1sJ=function(_1sK,_){var _1sL=E(_1sK);switch(_1sL._){case 0:return new F(function(){return _1qA(_1qM,_);});break;case 1:var _1sM=B(_1sJ(_1sL.f,_)),_1sN=B(_1sJ(_1sL.g,_)),_1sO=B(_1r6(_1sL.c,_)),_1sP=B(_1qA(_1qo,_)),_1sQ=E(_1sP),_1sR=E(_1sQ.a),_1sS=B(_1qb(_1qI,_1sR,_)),_1sT=eval(E(_1r5)),_1sU=__app2(E(_1sT),E(E(_1sS).a),toJSStr(B(_hA(0,E(_1sL.a),_1M)))),_1sV=B(_1qb(_1qL,_1sR,_)),_1sW=__app2(E(_1sT),E(E(_1sV).a),toJSStr(B(_hA(0,E(_1sL.b),_1M)))),_1sX=B(_1pi(_1qE,_1sR,_1sO,_)),_1sY=B(_1qb(_1qK,_1sR,_)),_1sZ=__app2(E(_1sT),E(E(_1sY).a),toJSStr(B(_hA(0,E(_1sL.d),_1M)))),_1t0=B(_1qb(_1qJ,_1sR,_)),_1t1=__app2(E(_1sT),E(E(_1t0).a),toJSStr(B(_hA(0,E(_1sL.e),_1M)))),_1t2=B(_1p9(_1qS,_1sR,_1sM,_)),_1t3=B(_1p9(_1qR,_1sR,_1sN,_));return _1sQ;case 2:var _1t4=B(_1sJ(_1sL.b,_)),_1t5=B(_1qA(_1qp,_)),_1t6=E(_1t5),_1t7=E(_1t6.a),_1t8=B(_1qb(_1qI,_1t7,_)),_1t9=eval(E(_1r5)),_1ta=__app2(E(_1t9),E(E(_1t8).a),toJSStr(B(_hA(0,E(_1sL.a),_1M)))),_1tb=B(_1p9(_1qN,_1t7,_1t4,_));return _1t6;case 3:var _1tc=B(_1sJ(_1sL.f,_)),_1td=B(_1qA(_1qr,_)),_1te=B(_1r6(_1sL.d,_)),_1tf=E(_1td),_1tg=E(_1tf.a),_1th=B(_1qb(_1qH,_1tg,_)),_1ti=eval(E(_1r5)),_1tj=__app2(E(_1ti),E(E(_1th).a),toJSStr(B(_hA(0,E(_1sL.a),_1M)))),_1tk=B(_1qb(_1qG,_1tg,_)),_1tl=__app2(E(_1ti),E(E(_1tk).a),toJSStr(B(_hA(0,E(_1sL.b),_1M)))),_1tm=B(_1qb(_1qF,_1tg,_)),_1tn=__app2(E(_1ti),E(E(_1tm).a),toJSStr(B(_hA(0,E(_1sL.c),_1M)))),_1to=B(_1pi(_1qE,_1tg,_1te,_)),_1tp=B(_1qb(_1qU,_1tg,_)),_1tq=__app2(E(_1ti),E(E(_1tp).a),toJSStr(B(_hA(0,E(_1sL.e),_1M)))),_1tr=B(_1p9(_1qN,_1tg,_1tc,_));return _1tf;case 4:var _1ts=B(_1sJ(_1sL.a,_)),_1tt=B(_1sJ(_1sL.b,_)),_1tu=B(_1qA(_1qs,_)),_1tv=E(_1tu),_1tw=E(_1tv.a),_1tx=B(_1p9(_1qS,_1tw,_1ts,_)),_1ty=B(_1p9(_1qR,_1tw,_1tt,_));return _1tv;case 5:var _1tz=B(_1rP(_1sL.a,_)),_1tA=B(_1sJ(_1sL.b,_)),_1tB=B(_1sJ(_1sL.c,_)),_1tC=B(_1qA(_1qt,_)),_1tD=E(_1tC),_1tE=E(_1tD.a),_1tF=B(_1qg(_1qO,_1tE,_1tz,_)),_1tG=B(_1p9(_1qS,_1tE,_1tA,_)),_1tH=B(_1p9(_1qR,_1tE,_1tB,_));return _1tD;case 6:var _1tI=B(_1rP(_1sL.a,_)),_1tJ=B(_1sJ(_1sL.c,_)),_1tK=B(_1sJ(_1sL.d,_)),_1tL=B(_1qA(_1qu,_)),_1tM=E(_1tL),_1tN=E(_1tM.a),_1tO=B(_1qb(_1qT,_1tN,_)),_1tP=eval(E(_1r5)),_1tQ=__app2(E(_1tP),E(E(_1tO).a),toJSStr(B(_hA(0,E(_1sL.b),_1M)))),_1tR=B(_1qg(_1qO,_1tN,_1tI,_)),_1tS=B(_1p9(_1qS,_1tN,_1tJ,_)),_1tT=B(_1p9(_1qR,_1tN,_1tK,_));return _1tM;case 7:var _1tU=B(_1qA(_1qv,_)),_1tV=E(_1tU),_1tW=B(_1qb(_1qP,E(_1tV.a),_)),_1tX=eval(E(_1r5)),_1tY=__app2(E(_1tX),E(E(_1tW).a),toJSStr(B(_hA(0,E(_1sL.a),_1M))));return _1tV;case 8:var _1tZ=B(_1sJ(_1sL.b,_)),_1u0=B(_1sJ(_1sL.c,_)),_1u1=B(_1qA(_1qw,_)),_1u2=E(_1u1),_1u3=E(_1u2.a),_1u4=B(_1qb(_1qQ,_1u3,_)),_1u5=eval(E(_1r5)),_1u6=__app2(E(_1u5),E(E(_1u4).a),toJSStr(B(_hA(0,E(_1sL.a),_1M)))),_1u7=B(_1p9(_1qS,_1u3,_1tZ,_)),_1u8=B(_1p9(_1qR,_1u3,_1u0,_));return _1u2;case 9:var _1u9=B(_1sJ(_1sL.b,_)),_1ua=B(_1qA(_1qx,_)),_1ub=E(_1ua),_1uc=E(_1ub.a),_1ud=B(_1qb(_1qQ,_1uc,_)),_1ue=eval(E(_1r5)),_1uf=__app2(E(_1ue),E(E(_1ud).a),toJSStr(B(_hA(0,E(_1sL.a),_1M)))),_1ug=B(_1p9(_1qN,_1uc,_1u9,_));return _1ub;case 10:var _1uh=B(_1sJ(_1sL.b,_)),_1ui=B(_1qA(_1qy,_)),_1uj=E(_1ui),_1uk=E(_1uj.a),_1ul=B(_1qb(_1qP,_1uk,_)),_1um=eval(E(_1r5)),_1un=__app2(E(_1um),E(E(_1ul).a),toJSStr(B(_hA(0,E(_1sL.a),_1M)))),_1uo=B(_1p9(_1qN,_1uk,_1uh,_));return _1uj;default:var _1up=B(_1rP(_1sL.b,_)),_1uq=B(_1sJ(_1sL.c,_)),_1ur=B(_1qA(_1qq,_)),_1us=E(_1ur),_1ut=E(_1us.a),_1uu=B(_1qb(_1qP,_1ut,_)),_1uv=eval(E(_1r5)),_1uw=__app2(E(_1uv),E(E(_1uu).a),toJSStr(B(_hA(0,E(_1sL.a),_1M)))),_1ux=B(_1pi(_1qO,_1ut,_1up,_)),_1uy=B(_1p9(_1qN,_1ut,_1uq,_));return _1us;}},_1uz=new T(function(){return eval("(function () {var i; var b = demoWorkspace.getAllBlocks(); for (i = b.length - 1; i > 0; --i) { if (b[i] !== undefined) { b[i].dispose() } };})");}),_1uA=new T(function(){return eval("(function() {return (demoWorkspace.getAllBlocks()[0]);})");}),_1uB=new T(function(){return B(unCStr("base_contract"));}),_1uC=new T(function(){return eval("(function() { demoWorkspace.render(); onresize(); })");}),_1uD=function(_1uE,_){var _1uF=__app0(E(_1uz)),_1uG=__app0(E(_1uA)),_1uH=B(_1ce(B(_l5(_1iq,_1uE))));if(!_1uH._){return E(_1cm);}else{if(!E(_1uH.b)._){var _1uI=B(_1sJ(_1uH.a,_)),_1uJ=B(_1p9(_1uB,_1uG,_1uI,_)),_1uK=__app0(E(_1uC)),_1uL=eval(E(_1aP)),_1uM=__app1(E(_1uL),toJSStr(E(_1iJ))),_1uN=new T(function(){var _1uO=B(_1ce(B(_l5(_DG,new T(function(){var _1uP=String(_1uM);return fromJSStr(_1uP);})))));if(!_1uO._){return E(_jT);}else{if(!E(_1uO.b)._){var _1uQ=E(_1uO.a);return new T4(0,new T(function(){return B(_3G(_1uQ.a));}),new T(function(){return B(_83(_1uQ.b));}),new T(function(){return B(_gT(_1uQ.c));}),new T(function(){return B(_dJ(_1uQ.d));}));}else{return E(_jR);}}});return new F(function(){return _1ir(_1uN,_);});}else{return E(_1cl);}}},_1uR=function(_){var _1uS=eval(E(_1aP)),_1uT=__app1(E(_1uS),toJSStr(E(_1oc)));return new F(function(){return _1uD(new T(function(){var _1uU=String(_1uT);return fromJSStr(_1uU);}),_);});},_1uV=new T(function(){return B(unCStr("contractOutput"));}),_1uW=new T(function(){return B(unCStr("([], [], [], [])"));}),_1uX=new T(function(){return B(unCStr("([], [])"));}),_1uY=new T(function(){return B(_hA(0,0,_1M));}),_1uZ=function(_){var _1v0=__app0(E(_1uz)),_1v1=B(_1iL(_1oc,_1M,_)),_1v2=B(_1iL(_1aS,_1uY,_)),_1v3=B(_1iL(_1aR,_1uX,_)),_1v4=B(_1iL(_1iJ,_1uW,_));return new F(function(){return _1iL(_1uV,_1M,_);});},_1v5=1000,_1v6=new T1(2,_1v5),_1v7=0,_1v8=new T1(2,_1v7),_1v9=4,_1va=new T3(3,_1v9,_1v9,_1v8),_1vb=3,_1vc=new T3(3,_1vb,_1vb,_1v8),_1vd=new T2(1,_1vc,_1va),_1ve=2,_1vf=new T3(3,_1ve,_1ve,_1v8),_1vg=1,_1vh=new T3(3,_1vg,_1vg,_1v8),_1vi=new T2(1,_1vh,_1vf),_1vj=new T2(1,_1vi,_1vd),_1vk=new T2(6,_1vj,_1v6),_1vl=new T1(0,_1ve),_1vm=20,_1vn=5,_1vo=new T6(3,_1ve,_1ve,_1vn,_1vl,_1vm,_14K),_1vp=new T1(0,_1vg),_1vq=new T6(3,_1vg,_1vg,_1vn,_1vp,_1vm,_14K),_1vr=new T2(4,_1vq,_1vo),_1vs=new T1(0,_1vb),_1vt=new T6(3,_1vb,_1vb,_1vn,_1vs,_1vm,_14K),_1vu=new T1(0,_1v9),_1vv=new T6(3,_1v9,_1v9,_1vn,_1vu,_1vm,_14K),_1vw=new T2(4,_1vt,_1vv),_1vx=new T2(4,_1vr,_1vw),_1vy=new T3(5,_1vk,_1vx,_14K),_1vz=10,_1vA=new T4(6,_1dM,_1vz,_14K,_1vy),_1vB=new T1(0,_1vA),_1vC=new T2(1,_1vB,_1M),_1vD={_:1,a:_1v9,b:_1v9,c:_1va,d:_1vz,e:_1vm,f:_14K,g:_14K},_1vE=new T1(2,_1vg),_1vF=new T2(6,_1va,_1vE),_1vG=new T2(5,_1v9,_1v9),_1vH=new T2(1,_1vG,_1vF),_1vI=new T4(6,_1vH,_1vz,_1vD,_14K),_1vJ={_:1,a:_1vb,b:_1vb,c:_1vc,d:_1vz,e:_1vm,f:_14K,g:_14K},_1vK=new T2(6,_1vc,_1vE),_1vL=new T2(5,_1vb,_1vb),_1vM=new T2(1,_1vL,_1vK),_1vN=new T4(6,_1vM,_1vz,_1vJ,_14K),_1vO=new T2(4,_1vN,_1vI),_1vP={_:1,a:_1ve,b:_1ve,c:_1vf,d:_1vz,e:_1vm,f:_14K,g:_14K},_1vQ=new T2(6,_1vf,_1vE),_1vR=new T2(5,_1ve,_1ve),_1vS=new T2(1,_1vR,_1vQ),_1vT=new T4(6,_1vS,_1vz,_1vP,_14K),_1vU={_:1,a:_1vg,b:_1vg,c:_1vh,d:_1vz,e:_1vm,f:_14K,g:_14K},_1vV=new T2(6,_1vh,_1vE),_1vW=new T2(5,_1vg,_1vg),_1vX=new T2(1,_1vW,_1vV),_1vY=new T4(6,_1vX,_1vz,_1vU,_14K),_1vZ=new T2(4,_1vY,_1vT),_1w0=new T2(4,_1vZ,_1vO),_1w1=new T1(0,_1w0),_1w2=new T2(1,_1w1,_1vC),_1w3=new T(function(){return B(_1nE(0,_1m6,_1w2));}),_1w4=function(_){var _1w5=B(_1uZ(_)),_1w6=B(_1iL(_1oc,_1w3,_)),_1w7=eval(E(_1aP)),_1w8=__app1(E(_1w7),toJSStr(E(_1oc)));return new F(function(){return _1uD(new T(function(){var _1w9=String(_1w8);return fromJSStr(_1w9);}),_);});},_1wa=1,_1wb=new T1(3,_1wa),_1wc=new T1(8,_1wa),_1wd=100,_1we=new T1(2,_1wd),_1wf=new T1(2,_1we),_1wg=10,_1wh=new T1(8,_1wg),_1wi=200,_1wj=new T1(8,_1wi),_1wk=20,_1wl=new T1(2,_1wk),_1wm=new T2(2,_1wa,_14K),_1wn=new T2(5,_1wa,_1wa),_1wo=2,_1wp=new T2(2,_1wo,_14K),_1wq=new T2(4,_1wm,_1wp),_1wr=new T6(3,_1wa,_1wo,_1wa,_1wl,_1wi,_1wq),_1ws=new T4(6,_1wn,_1wd,_1wq,_1wr),_1wt={_:1,a:_1wo,b:_1wo,c:_1wl,d:_1wk,e:_1wi,f:_1ws,g:_1wm},_1wu=new T1(0,_1wt),_1wv=new T1(0,_14K),_1ww=new T2(1,_1wv,_1M),_1wx=new T2(1,_1wu,_1ww),_1wy=new T2(1,_1wj,_1wx),_1wz=new T2(1,_1wh,_1wy),_1wA=new T2(1,_1wf,_1wz),_1wB=new T2(1,_1wc,_1wA),_1wC=new T2(1,_1wb,_1wB),_1wD=new T(function(){return B(_1nE(0,_1m9,_1wC));}),_1wE=function(_){var _1wF=B(_1uZ(_)),_1wG=B(_1iL(_1oc,_1wD,_)),_1wH=eval(E(_1aP)),_1wI=__app1(E(_1wH),toJSStr(E(_1oc)));return new F(function(){return _1uD(new T(function(){var _1wJ=String(_1wI);return fromJSStr(_1wJ);}),_);});},_1wK=1,_1wL=new T1(3,_1wK),_1wM=new T1(8,_1wK),_1wN=450,_1wO=new T1(2,_1wN),_1wP=new T1(2,_1wO),_1wQ=10,_1wR=new T1(8,_1wQ),_1wS=100,_1wT=new T1(8,_1wS),_1wU=90,_1wV=3,_1wW=0,_1wX=new T3(4,_1wV,_1wV,_1wW),_1wY=2,_1wZ=new T3(4,_1wY,_1wY,_1wW),_1x0=new T2(1,_1wZ,_1wX),_1x1=new T2(2,_1wZ,_1wX),_1x2=new T3(4,_1wK,_1wK,_1wW),_1x3=new T2(1,_1x2,_1x1),_1x4=new T2(2,_1x3,_1x0),_1x5=new T3(4,_1wV,_1wV,_1wK),_1x6=new T3(4,_1wY,_1wY,_1wK),_1x7=new T2(1,_1x6,_1x5),_1x8=new T2(2,_1x6,_1x5),_1x9=new T3(4,_1wK,_1wK,_1wK),_1xa=new T2(1,_1x9,_1x8),_1xb=new T2(2,_1xa,_1x7),_1xc=new T2(2,_1x4,_1xb),_1xd=new T2(2,_1wK,_14K),_1xe=new T1(0,_1wK),_1xf=new T6(3,_1wK,_1wK,_1wY,_1xe,_1wS,_1xd),_1xg=new T3(5,_1xb,_1xf,_1xd),_1xh=new T4(6,_1xc,_1wU,_1xg,_1xd),_1xi=new T1(0,_1xh),_1xj=new T2(1,_1xi,_1ww),_1xk=new T2(1,_1wT,_1xj),_1xl=new T2(1,_1wR,_1xk),_1xm=new T2(1,_1wP,_1xl),_1xn=new T2(1,_1wM,_1xm),_1xo=new T2(1,_1wL,_1xn),_1xp=new T(function(){return B(_1nE(0,_1m9,_1xo));}),_1xq=function(_){var _1xr=B(_1uZ(_)),_1xs=B(_1iL(_1oc,_1xp,_)),_1xt=eval(E(_1aP)),_1xu=__app1(E(_1xt),toJSStr(E(_1oc)));return new F(function(){return _1uD(new T(function(){var _1xv=String(_1xu);return fromJSStr(_1xv);}),_);});},_1xw=new T(function(){return B(unCStr("NotRedeemed "));}),_1xx=function(_1xy,_1xz,_1xA){var _1xB=E(_1xz);if(!_1xB._){var _1xC=function(_1xD){return new F(function(){return _hA(11,E(_1xB.a),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1xB.b),_1xD));})));});};if(E(_1xy)<11){return new F(function(){return _hq(_1xw,new T(function(){return B(_1xC(_1xA));},1));});}else{var _1xE=new T(function(){return B(_hq(_1xw,new T(function(){return B(_1xC(new T2(1,_hy,_1xA)));},1)));});return new T2(1,_hz,_1xE);}}else{return new F(function(){return _hq(_1ba,_1xA);});}},_1xF=0,_1xG=function(_1xH,_1xI,_1xJ){var _1xK=new T(function(){var _1xL=function(_1xM){var _1xN=E(_1xI),_1xO=new T(function(){return B(A3(_is,_hk,new T2(1,function(_1xP){return new F(function(){return _hA(0,E(_1xN.a),_1xP);});},new T2(1,function(_Av){return new F(function(){return _1xx(_1xF,_1xN.b,_Av);});},_1M)),new T2(1,_hy,_1xM)));});return new T2(1,_hz,_1xO);};return B(A3(_is,_hk,new T2(1,function(_1xQ){return new F(function(){return _hF(0,_1xH,_1xQ);});},new T2(1,_1xL,_1M)),new T2(1,_hy,_1xJ)));});return new T2(0,_hz,_1xK);},_1xR=function(_1xS,_1xT){var _1xU=E(_1xS),_1xV=B(_1xG(_1xU.a,_1xU.b,_1xT));return new T2(1,_1xV.a,_1xV.b);},_1xW=function(_1xX,_1xY){return new F(function(){return _iR(_1xR,_1xX,_1xY);});},_1xZ=new T(function(){return B(unCStr("IdentOBind "));}),_1y0=function(_1y1,_1y2,_1y3){if(_1y1<11){return new F(function(){return _hq(_1xZ,new T(function(){return B(_hA(11,E(_1y2),_1y3));},1));});}else{var _1y4=new T(function(){return B(_hq(_1xZ,new T(function(){return B(_hA(11,E(_1y2),new T2(1,_hy,_1y3)));},1)));});return new T2(1,_hz,_1y4);}},_1y5=new T(function(){return B(unCStr("IdentCBind "));}),_1y6=function(_1y7,_1y8,_1y9){if(_1y7<11){return new F(function(){return _hq(_1y5,new T(function(){return B(_hA(11,E(_1y8),_1y9));},1));});}else{var _1ya=new T(function(){return B(_hq(_1y5,new T(function(){return B(_hA(11,E(_1y8),new T2(1,_hy,_1y9)));},1)));});return new T2(1,_hz,_1ya);}},_1yb=new T(function(){return B(unCStr("FailedOUnbind "));}),_1yc=new T(function(){return B(unCStr("FailedCUnbind "));}),_1yd=new T(function(){return B(unCStr("FailedOReplace "));}),_1ye=new T(function(){return B(unCStr("FailedCReplace "));}),_1yf=new T(function(){return B(unCStr("ChoiceMade "));}),_1yg=new T(function(){return B(unCStr("DuplicateRedeem "));}),_1yh=new T(function(){return B(unCStr("ExpiredCommitRedeemed "));}),_1yi=new T(function(){return B(unCStr("CommitRedeemed "));}),_1yj=new T(function(){return B(unCStr("SuccessfulCommit "));}),_1yk=new T(function(){return B(unCStr("FailedPay "));}),_1yl=new T(function(){return B(unCStr("ExpiredPay "));}),_1ym=new T(function(){return B(unCStr("SuccessfulPay "));}),_1yn=function(_1yo,_1yp,_1yq){var _1yr=E(_1yp);switch(_1yr._){case 0:var _1ys=function(_1yt){var _1yu=new T(function(){var _1yv=new T(function(){return B(_hA(11,E(_1yr.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1yr.d),_1yt));}))));});return B(_hA(11,E(_1yr.b),new T2(1,_hK,_1yv)));});return new F(function(){return _ih(11,_1yr.a,new T2(1,_hK,_1yu));});};if(_1yo<11){return new F(function(){return _hq(_1ym,new T(function(){return B(_1ys(_1yq));},1));});}else{var _1yw=new T(function(){return B(_hq(_1ym,new T(function(){return B(_1ys(new T2(1,_hy,_1yq)));},1)));});return new T2(1,_hz,_1yw);}break;case 1:var _1yx=function(_1yy){var _1yz=new T(function(){var _1yA=new T(function(){return B(_hA(11,E(_1yr.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1yr.d),_1yy));}))));});return B(_hA(11,E(_1yr.b),new T2(1,_hK,_1yA)));});return new F(function(){return _ih(11,_1yr.a,new T2(1,_hK,_1yz));});};if(_1yo<11){return new F(function(){return _hq(_1yl,new T(function(){return B(_1yx(_1yq));},1));});}else{var _1yB=new T(function(){return B(_hq(_1yl,new T(function(){return B(_1yx(new T2(1,_hy,_1yq)));},1)));});return new T2(1,_hz,_1yB);}break;case 2:var _1yC=function(_1yD){var _1yE=new T(function(){var _1yF=new T(function(){return B(_hA(11,E(_1yr.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1yr.d),_1yD));}))));});return B(_hA(11,E(_1yr.b),new T2(1,_hK,_1yF)));});return new F(function(){return _ih(11,_1yr.a,new T2(1,_hK,_1yE));});};if(_1yo<11){return new F(function(){return _hq(_1yk,new T(function(){return B(_1yC(_1yq));},1));});}else{var _1yG=new T(function(){return B(_hq(_1yk,new T(function(){return B(_1yC(new T2(1,_hy,_1yq)));},1)));});return new T2(1,_hz,_1yG);}break;case 3:var _1yH=function(_1yI){var _1yJ=new T(function(){var _1yK=new T(function(){return B(_hA(11,E(_1yr.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1yr.c),_1yI));}))));});return B(_hF(11,_1yr.a,new T2(1,_hK,_1yK)));},1);return new F(function(){return _hq(_1yj,_1yJ);});};if(_1yo<11){return new F(function(){return _1yH(_1yq);});}else{return new T2(1,_hz,new T(function(){return B(_1yH(new T2(1,_hy,_1yq)));}));}break;case 4:var _1yL=function(_1yM){var _1yN=new T(function(){var _1yO=new T(function(){return B(_hA(11,E(_1yr.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1yr.c),_1yM));}))));});return B(_hF(11,_1yr.a,new T2(1,_hK,_1yO)));},1);return new F(function(){return _hq(_1yi,_1yN);});};if(_1yo<11){return new F(function(){return _1yL(_1yq);});}else{return new T2(1,_hz,new T(function(){return B(_1yL(new T2(1,_hy,_1yq)));}));}break;case 5:var _1yP=function(_1yQ){var _1yR=new T(function(){var _1yS=new T(function(){return B(_hA(11,E(_1yr.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1yr.c),_1yQ));}))));});return B(_hF(11,_1yr.a,new T2(1,_hK,_1yS)));},1);return new F(function(){return _hq(_1yh,_1yR);});};if(_1yo<11){return new F(function(){return _1yP(_1yq);});}else{return new T2(1,_hz,new T(function(){return B(_1yP(new T2(1,_hy,_1yq)));}));}break;case 6:var _1yT=function(_1yU){return new F(function(){return _hF(11,_1yr.a,new T2(1,_hK,new T(function(){return B(_hA(11,E(_1yr.b),_1yU));})));});};if(_1yo<11){return new F(function(){return _hq(_1yg,new T(function(){return B(_1yT(_1yq));},1));});}else{var _1yV=new T(function(){return B(_hq(_1yg,new T(function(){return B(_1yT(new T2(1,_hy,_1yq)));},1)));});return new T2(1,_hz,_1yV);}break;case 7:var _1yW=function(_1yX){var _1yY=new T(function(){var _1yZ=new T(function(){return B(_hA(11,E(_1yr.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1yr.c),_1yX));}))));});return B(_j6(11,_1yr.a,new T2(1,_hK,_1yZ)));},1);return new F(function(){return _hq(_1yf,_1yY);});};if(_1yo<11){return new F(function(){return _1yW(_1yq);});}else{return new T2(1,_hz,new T(function(){return B(_1yW(new T2(1,_hy,_1yq)));}));}break;case 8:var _1z0=_1yr.a;if(_1yo<11){return new F(function(){return _hq(_1ye,new T(function(){return B(_1y6(11,_1z0,_1yq));},1));});}else{var _1z1=new T(function(){return B(_hq(_1ye,new T(function(){return B(_1y6(11,_1z0,new T2(1,_hy,_1yq)));},1)));});return new T2(1,_hz,_1z1);}break;case 9:var _1z2=_1yr.a;if(_1yo<11){return new F(function(){return _hq(_1yd,new T(function(){return B(_1y0(11,_1z2,_1yq));},1));});}else{var _1z3=new T(function(){return B(_hq(_1yd,new T(function(){return B(_1y0(11,_1z2,new T2(1,_hy,_1yq)));},1)));});return new T2(1,_hz,_1z3);}break;case 10:var _1z4=_1yr.a;if(_1yo<11){return new F(function(){return _hq(_1yc,new T(function(){return B(_1y6(11,_1z4,_1yq));},1));});}else{var _1z5=new T(function(){return B(_hq(_1yc,new T(function(){return B(_1y6(11,_1z4,new T2(1,_hy,_1yq)));},1)));});return new T2(1,_hz,_1z5);}break;default:var _1z6=_1yr.a;if(_1yo<11){return new F(function(){return _hq(_1yb,new T(function(){return B(_1y0(11,_1z6,_1yq));},1));});}else{var _1z7=new T(function(){return B(_hq(_1yb,new T(function(){return B(_1y0(11,_1z6,new T2(1,_hy,_1yq)));},1)));});return new T2(1,_hz,_1z7);}}},_1z8=new T(function(){return B(unAppCStr("[]",_1M));}),_1z9=new T2(1,_iP,_1M),_1za=function(_1zb){var _1zc=E(_1zb);if(!_1zc._){return E(_1z9);}else{var _1zd=new T(function(){return B(_1yn(0,_1zc.a,new T(function(){return B(_1za(_1zc.b));})));});return new T2(1,_hj,_1zd);}},_1ze=function(_){var _1zf=E(_1iJ),_1zg=toJSStr(_1zf),_1zh=eval(E(_1aP)),_1zi=_1zh,_1zj=__app1(E(_1zi),_1zg),_1zk=E(_1aR),_1zl=__app1(E(_1zi),toJSStr(_1zk)),_1zm=__app0(E(_1aQ)),_1zn=E(_1aS),_1zo=__app1(E(_1zi),toJSStr(_1zn)),_1zp=new T(function(){var _1zq=B(_1ce(B(_l5(_1aW,new T(function(){var _1zr=String(_1zo);return fromJSStr(_1zr);})))));if(!_1zq._){return E(_1aV);}else{if(!E(_1zq.b)._){return E(_1zq.a);}else{return E(_1aU);}}}),_1zs=new T(function(){var _1zt=B(_1ce(B(_l5(_1iq,new T(function(){var _1zu=String(_1zm);return fromJSStr(_1zu);})))));if(!_1zt._){return E(_1cm);}else{if(!E(_1zt.b)._){return E(_1zt.a);}else{return E(_1cl);}}}),_1zv=new T(function(){var _1zw=B(_1ce(B(_l5(_1cb,new T(function(){var _1zx=String(_1zl);return fromJSStr(_1zx);})))));if(!_1zw._){return E(_1aY);}else{if(!E(_1zw.b)._){var _1zy=E(_1zw.a);return new T2(0,new T(function(){return B(_EV(_1zy.a));}),new T(function(){return B(_dJ(_1zy.b));}));}else{return E(_1aX);}}}),_1zz=new T(function(){var _1zA=B(_1ce(B(_l5(_DG,new T(function(){var _1zB=String(_1zj);return fromJSStr(_1zB);})))));if(!_1zA._){return E(_jT);}else{if(!E(_1zA.b)._){var _1zC=E(_1zA.a);return new T4(0,new T(function(){return B(_3G(_1zC.a));}),new T(function(){return B(_83(_1zC.b));}),new T(function(){return B(_gT(_1zC.c));}),new T(function(){return B(_dJ(_1zC.d));}));}else{return E(_jR);}}}),_1zD=B(_1a8(_1zz,_1zv,_1zs,new T2(0,_1cc,_1zp))),_1zE=function(_,_1zF){var _1zG=function(_,_1zH){var _1zI=E(_1zD.a),_1zJ=new T(function(){var _1zK=new T(function(){return B(_hc(_1M,_1zI.b));}),_1zL=new T(function(){return B(_hc(_1M,_1zI.a));});return B(A3(_is,_hk,new T2(1,function(_1zM){return new F(function(){return _1xW(_1zL,_1zM);});},new T2(1,function(_1zN){return new F(function(){return _js(_1zK,_1zN);});},_1M)),_jv));}),_1zO=B(_1iL(_1zk,new T2(1,_hz,_1zJ),_)),_1zP=B(_1iL(_1zf,_1uW,_)),_1zQ=B(_1iL(_1zn,B(_hA(0,E(_1zp)+1|0,_1M)),_)),_1zR=__app1(E(_1zi),toJSStr(E(_1oc))),_1zS=B(_1uD(new T(function(){var _1zT=String(_1zR);return fromJSStr(_1zT);}),_)),_1zU=__app1(E(_1zi),_1zg),_1zV=new T(function(){var _1zW=B(_1ce(B(_l5(_DG,new T(function(){var _1zX=String(_1zU);return fromJSStr(_1zX);})))));if(!_1zW._){return E(_jT);}else{if(!E(_1zW.b)._){var _1zY=E(_1zW.a);return new T4(0,new T(function(){return B(_3G(_1zY.a));}),new T(function(){return B(_83(_1zY.b));}),new T(function(){return B(_gT(_1zY.c));}),new T(function(){return B(_dJ(_1zY.d));}));}else{return E(_jR);}}});return new F(function(){return _1ir(_1zV,_);});},_1zZ=E(_1zD.b);switch(_1zZ._){case 0:var _1A0=B(_1iL(_1oc,_1o7,_));return new F(function(){return _1zG(_,_1A0);});break;case 1:var _1A1=B(_1iL(_1oc,B(_1nE(0,_1m9,new T2(1,new T1(3,_1zZ.a),new T2(1,new T1(8,_1zZ.b),new T2(1,new T1(2,_1zZ.c),new T2(1,new T1(8,_1zZ.d),new T2(1,new T1(8,_1zZ.e),new T2(1,new T1(0,_1zZ.f),new T2(1,new T1(0,_1zZ.g),_1M))))))))),_));return new F(function(){return _1zG(_,_1A1);});break;case 2:var _1A2=B(_1iL(_1oc,B(_1nE(0,_1m8,new T2(1,new T1(3,_1zZ.a),new T2(1,new T1(0,_1zZ.b),_1M)))),_));return new F(function(){return _1zG(_,_1A2);});break;case 3:var _1A3=B(_1iL(_1oc,B(_1nE(0,_1m7,new T2(1,new T1(5,_1zZ.a),new T2(1,new T1(8,_1zZ.b),new T2(1,new T1(8,_1zZ.c),new T2(1,new T1(2,_1zZ.d),new T2(1,new T1(8,_1zZ.e),new T2(1,new T1(0,_1zZ.f),_1M)))))))),_));return new F(function(){return _1zG(_,_1A3);});break;case 4:var _1A4=B(_1iL(_1oc,B(_1nE(0,_1m6,new T2(1,new T1(0,_1zZ.a),new T2(1,new T1(0,_1zZ.b),_1M)))),_));return new F(function(){return _1zG(_,_1A4);});break;case 5:var _1A5=B(_1iL(_1oc,B(_1nE(0,_1m5,new T2(1,new T1(1,_1zZ.a),new T2(1,new T1(0,_1zZ.b),new T2(1,new T1(0,_1zZ.c),_1M))))),_));return new F(function(){return _1zG(_,_1A5);});break;case 6:var _1A6=B(_1iL(_1oc,B(_1nE(0,_1m4,new T2(1,new T1(1,_1zZ.a),new T2(1,new T1(8,_1zZ.b),new T2(1,new T1(0,_1zZ.c),new T2(1,new T1(0,_1zZ.d),_1M)))))),_));return new F(function(){return _1zG(_,_1A6);});break;case 7:var _1A7=B(_1iL(_1oc,B(_1nE(0,_1m3,new T2(1,new T1(6,_1zZ.a),_1M))),_));return new F(function(){return _1zG(_,_1A7);});break;case 8:var _1A8=B(_1iL(_1oc,B(_1nE(0,_1m2,new T2(1,new T1(6,_1zZ.a),new T2(1,new T1(0,_1zZ.b),new T2(1,new T1(0,_1zZ.c),_1M))))),_));return new F(function(){return _1zG(_,_1A8);});break;case 9:var _1A9=B(_1iL(_1oc,B(_1nE(0,_1m1,new T2(1,new T1(6,_1zZ.a),new T2(1,new T1(0,_1zZ.b),_1M)))),_));return new F(function(){return _1zG(_,_1A9);});break;case 10:var _1Aa=B(_1iL(_1oc,B(_1nE(0,_1m0,new T2(1,new T1(7,_1zZ.a),new T2(1,new T1(0,_1zZ.b),_1M)))),_));return new F(function(){return _1zG(_,_1Aa);});break;default:var _1Ab=B(_1iL(_1oc,B(_1nE(0,_1lZ,new T2(1,new T1(7,_1zZ.a),new T2(1,new T1(1,_1zZ.b),new T2(1,new T1(0,_1zZ.c),_1M))))),_));return new F(function(){return _1zG(_,_1Ab);});}},_1Ac=E(_1zD.c);if(!_1Ac._){var _1Ad=B(_1iL(_1uV,_1z8,_));return new F(function(){return _1zE(_,_1Ad);});}else{var _1Ae=new T(function(){return B(_1yn(0,_1Ac.a,new T(function(){return B(_1za(_1Ac.b));})));}),_1Af=B(_1iL(_1uV,new T2(1,_iQ,_1Ae),_));return new F(function(){return _1zE(_,_1Af);});}},_1Ag=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1Ah=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1Ai=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1Aj=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1Ak=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1Al=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1Am=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1An=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1Ao=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1Ap=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1Aq=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1Ar=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1As=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1At=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1Au=function(_){return new F(function(){return __jsNull();});},_1Av=function(_1Aw){var _1Ax=B(A1(_1Aw,_));return E(_1Ax);},_1Ay=new T(function(){return B(_1Av(_1Au));}),_1Az=new T(function(){return E(_1Ay);}),_1AA=function(_){var _1AB=eval(E(_1aP)),_1AC=__app1(E(_1AB),toJSStr(E(_1iJ))),_1AD=new T(function(){var _1AE=B(_1ce(B(_l5(_DG,new T(function(){var _1AF=String(_1AC);return fromJSStr(_1AF);})))));if(!_1AE._){return E(_jT);}else{if(!E(_1AE.b)._){var _1AG=E(_1AE.a);return new T4(0,new T(function(){return B(_3G(_1AG.a));}),new T(function(){return B(_83(_1AG.b));}),new T(function(){return B(_gT(_1AG.c));}),new T(function(){return B(_dJ(_1AG.d));}));}else{return E(_jR);}}});return new F(function(){return _1ir(_1AD,_);});},_1AH=function(_){var _1AI=eval(E(_1aP)),_1AJ=__app1(E(_1AI),toJSStr(E(_1oc))),_1AK=B(_1uD(new T(function(){var _1AL=String(_1AJ);return fromJSStr(_1AL);}),_)),_1AM=__createJSFunc(0,function(_){var _1AN=B(_1uZ(_));return _1Az;}),_1AO=__app2(E(_1Aq),"clear_workspace",_1AM),_1AP=__createJSFunc(0,function(_){var _1AQ=B(_1od(_));return _1Az;}),_1AR=__app2(E(_1Ap),"b2c",_1AP),_1AS=__createJSFunc(0,function(_){var _1AT=B(_1uR(_));return _1Az;}),_1AU=__app2(E(_1Ao),"c2b",_1AS),_1AV=function(_1AW){var _1AX=new T(function(){var _1AY=Number(E(_1AW));return jsTrunc(_1AY);}),_1AZ=function(_1B0){var _1B1=new T(function(){var _1B2=Number(E(_1B0));return jsTrunc(_1B2);}),_1B3=function(_1B4){var _1B5=new T(function(){var _1B6=Number(E(_1B4));return jsTrunc(_1B6);}),_1B7=function(_1B8,_){var _1B9=B(_1kl(_1AX,_1B1,_1B5,new T(function(){var _1Ba=Number(E(_1B8));return jsTrunc(_1Ba);}),_));return _1Az;};return E(_1B7);};return E(_1B3);};return E(_1AZ);},_1Bb=__createJSFunc(5,E(_1AV)),_1Bc=__app2(E(_1An),"commit",_1Bb),_1Bd=function(_1Be){var _1Bf=new T(function(){var _1Bg=Number(E(_1Be));return jsTrunc(_1Bg);}),_1Bh=function(_1Bi){var _1Bj=new T(function(){var _1Bk=Number(E(_1Bi));return jsTrunc(_1Bk);}),_1Bl=function(_1Bm,_){var _1Bn=B(_1k3(_1Bf,_1Bj,new T(function(){var _1Bo=Number(E(_1Bm));return jsTrunc(_1Bo);}),_));return _1Az;};return E(_1Bl);};return E(_1Bh);},_1Bp=__createJSFunc(4,E(_1Bd)),_1Bq=__app2(E(_1Am),"redeem",_1Bp),_1Br=function(_1Bs){var _1Bt=new T(function(){var _1Bu=Number(E(_1Bs));return jsTrunc(_1Bu);}),_1Bv=function(_1Bw){var _1Bx=new T(function(){var _1By=Number(E(_1Bw));return jsTrunc(_1By);}),_1Bz=function(_1BA,_){var _1BB=B(_1iQ(_1Bt,_1Bx,new T(function(){var _1BC=Number(E(_1BA));return jsTrunc(_1BC);}),_));return _1Az;};return E(_1Bz);};return E(_1Bv);},_1BD=__createJSFunc(4,E(_1Br)),_1BE=__app2(E(_1Al),"claim",_1BD),_1BF=function(_1BG){var _1BH=new T(function(){var _1BI=Number(E(_1BG));return jsTrunc(_1BI);}),_1BJ=function(_1BK){var _1BL=new T(function(){var _1BM=Number(E(_1BK));return jsTrunc(_1BM);}),_1BN=function(_1BO,_){var _1BP=B(_1ly(_1BH,_1BL,new T(function(){var _1BQ=Number(E(_1BO));return jsTrunc(_1BQ);}),_));return _1Az;};return E(_1BN);};return E(_1BJ);},_1BR=__createJSFunc(4,E(_1BF)),_1BS=__app2(E(_1Ak),"choose",_1BR),_1BT=__createJSFunc(0,function(_){var _1BU=B(_1ze(_));return _1Az;}),_1BV=__app2(E(_1Aj),"execute",_1BT),_1BW=__createJSFunc(0,function(_){var _1BX=B(_1AA(_));return _1Az;}),_1BY=__app2(E(_1Ai),"refreshActions",_1BW),_1BZ=function(_1C0,_){var _1C1=B(_1lu(new T(function(){var _1C2=String(E(_1C0));return fromJSStr(_1C2);}),_));return _1Az;},_1C3=__createJSFunc(2,E(_1BZ)),_1C4=__app2(E(_1Ah),"addAction",_1C3),_1C5=function(_1C6){var _1C7=new T(function(){var _1C8=String(E(_1C6));return fromJSStr(_1C8);}),_1C9=function(_1Ca,_){var _1Cb=B(_1lT(_1C7,new T(function(){var _1Cc=Number(E(_1Ca));return jsTrunc(_1Cc);}),_));return _1Az;};return E(_1C9);},_1Cd=__createJSFunc(3,E(_1C5)),_1Ce=__app2(E(_1Ag),"addActionWithNum",_1Cd),_1Cf=__createJSFunc(0,function(_){var _1Cg=B(_1wE(_));return _1Az;}),_1Ch=__app2(E(_1At),"depositIncentive",_1Cf),_1Ci=__createJSFunc(0,function(_){var _1Cj=B(_1w4(_));return _1Az;}),_1Ck=__app2(E(_1As),"crowdFunding",_1Ci),_1Cl=__createJSFunc(0,function(_){var _1Cm=B(_1xq(_));return _1Az;}),_1Cn=__app2(E(_1Ar),"escrow",_1Cl),_1Co=__app1(E(_1AI),toJSStr(E(_1iJ))),_1Cp=new T(function(){var _1Cq=B(_1ce(B(_l5(_DG,new T(function(){var _1Cr=String(_1Co);return fromJSStr(_1Cr);})))));if(!_1Cq._){return E(_jT);}else{if(!E(_1Cq.b)._){var _1Cs=E(_1Cq.a);return new T4(0,new T(function(){return B(_3G(_1Cs.a));}),new T(function(){return B(_83(_1Cs.b));}),new T(function(){return B(_gT(_1Cs.c));}),new T(function(){return B(_dJ(_1Cs.d));}));}else{return E(_jR);}}}),_1Ct=B(_1ir(_1Cp,_));return _h9;},_1Cu=function(_){return new F(function(){return _1AH(_);});};
var hasteMain = function() {B(A(_1Cu, [0]));};window.onload = hasteMain;
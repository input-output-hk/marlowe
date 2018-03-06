"use strict";
var __haste_prog_id = '2158c55f747d3ca3d2567d50b4af06fe3a6e8f4a2770f2229e724c873b0ee7e4';
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

var _0=0,_1=11,_2=new T(function(){return B(unCStr("IdentChoice "));}),_3=function(_4,_5){var _6=E(_4);return (_6._==0)?E(_5):new T2(1,_6.a,new T(function(){return B(_3(_6.b,_5));}));},_7=function(_8,_9){var _a=jsShowI(_8);return new F(function(){return _3(fromJSStr(_a),_9);});},_b=41,_c=40,_d=function(_e,_f,_g){if(_f>=0){return new F(function(){return _7(_f,_g);});}else{if(_e<=6){return new F(function(){return _7(_f,_g);});}else{return new T2(1,_c,new T(function(){var _h=jsShowI(_f);return B(_3(fromJSStr(_h),new T2(1,_b,_g)));}));}}},_i=function(_j,_k,_l){if(_j<11){return new F(function(){return _3(_2,new T(function(){return B(_d(11,E(_k),_l));},1));});}else{var _m=new T(function(){return B(_3(_2,new T(function(){return B(_d(11,E(_k),new T2(1,_b,_l)));},1)));});return new T2(1,_c,_m);}},_n=new T(function(){return B(unCStr("IdentCC "));}),_o=function(_p,_q,_r){if(_p<11){return new F(function(){return _3(_n,new T(function(){return B(_d(11,E(_q),_r));},1));});}else{var _s=new T(function(){return B(_3(_n,new T(function(){return B(_d(11,E(_q),new T2(1,_b,_r)));},1)));});return new T2(1,_c,_s);}},_t=new T(function(){return B(unCStr("ConstMoney "));}),_u=new T(function(){return B(unCStr("AddMoney "));}),_v=new T(function(){return B(unCStr("AvailableMoney "));}),_w=32,_x=function(_y,_z,_A){var _B=E(_z);switch(_B._){case 0:var _C=_B.a;if(_y<11){return new F(function(){return _3(_v,new T(function(){return B(_o(11,_C,_A));},1));});}else{var _D=new T(function(){return B(_3(_v,new T(function(){return B(_o(11,_C,new T2(1,_b,_A)));},1)));});return new T2(1,_c,_D);}break;case 1:var _E=function(_F){var _G=new T(function(){return B(_x(11,_B.a,new T2(1,_w,new T(function(){return B(_x(11,_B.b,_F));}))));},1);return new F(function(){return _3(_u,_G);});};if(_y<11){return new F(function(){return _E(_A);});}else{return new T2(1,_c,new T(function(){return B(_E(new T2(1,_b,_A)));}));}break;default:var _H=_B.a;if(_y<11){return new F(function(){return _3(_t,new T(function(){return B(_d(11,E(_H),_A));},1));});}else{var _I=new T(function(){return B(_3(_t,new T(function(){return B(_d(11,E(_H),new T2(1,_b,_A)));},1)));});return new T2(1,_c,_I);}}},_J=new T(function(){return B(unCStr("FalseObs"));}),_K=new T(function(){return B(unCStr("TrueObs"));}),_L=new T(function(){return B(unCStr("ValueGE "));}),_M=new T(function(){return B(unCStr("PersonChoseSomething "));}),_N=new T(function(){return B(unCStr("PersonChoseThis "));}),_O=new T(function(){return B(unCStr("NotObs "));}),_P=new T(function(){return B(unCStr("OrObs "));}),_Q=new T(function(){return B(unCStr("AndObs "));}),_R=new T(function(){return B(unCStr("BelowTimeout "));}),_S=function(_T,_U,_V){var _W=E(_U);switch(_W._){case 0:var _X=_W.a;if(_T<11){return new F(function(){return _3(_R,new T(function(){return B(_d(11,E(_X),_V));},1));});}else{var _Y=new T(function(){return B(_3(_R,new T(function(){return B(_d(11,E(_X),new T2(1,_b,_V)));},1)));});return new T2(1,_c,_Y);}break;case 1:var _Z=function(_10){var _11=new T(function(){return B(_S(11,_W.a,new T2(1,_w,new T(function(){return B(_S(11,_W.b,_10));}))));},1);return new F(function(){return _3(_Q,_11);});};if(_T<11){return new F(function(){return _Z(_V);});}else{return new T2(1,_c,new T(function(){return B(_Z(new T2(1,_b,_V)));}));}break;case 2:var _12=function(_13){var _14=new T(function(){return B(_S(11,_W.a,new T2(1,_w,new T(function(){return B(_S(11,_W.b,_13));}))));},1);return new F(function(){return _3(_P,_14);});};if(_T<11){return new F(function(){return _12(_V);});}else{return new T2(1,_c,new T(function(){return B(_12(new T2(1,_b,_V)));}));}break;case 3:var _15=_W.a;if(_T<11){return new F(function(){return _3(_O,new T(function(){return B(_S(11,_15,_V));},1));});}else{var _16=new T(function(){return B(_3(_O,new T(function(){return B(_S(11,_15,new T2(1,_b,_V)));},1)));});return new T2(1,_c,_16);}break;case 4:var _17=function(_18){var _19=new T(function(){var _1a=new T(function(){return B(_d(11,E(_W.b),new T2(1,_w,new T(function(){return B(_d(11,E(_W.c),_18));}))));});return B(_i(11,_W.a,new T2(1,_w,_1a)));},1);return new F(function(){return _3(_N,_19);});};if(_T<11){return new F(function(){return _17(_V);});}else{return new T2(1,_c,new T(function(){return B(_17(new T2(1,_b,_V)));}));}break;case 5:var _1b=function(_1c){return new F(function(){return _i(11,_W.a,new T2(1,_w,new T(function(){return B(_d(11,E(_W.b),_1c));})));});};if(_T<11){return new F(function(){return _3(_M,new T(function(){return B(_1b(_V));},1));});}else{var _1d=new T(function(){return B(_3(_M,new T(function(){return B(_1b(new T2(1,_b,_V)));},1)));});return new T2(1,_c,_1d);}break;case 6:var _1e=function(_1f){return new F(function(){return _x(11,_W.a,new T2(1,_w,new T(function(){return B(_x(11,_W.b,_1f));})));});};if(_T<11){return new F(function(){return _3(_L,new T(function(){return B(_1e(_V));},1));});}else{var _1g=new T(function(){return B(_3(_L,new T(function(){return B(_1e(new T2(1,_b,_V)));},1)));});return new T2(1,_c,_1g);}break;case 7:return new F(function(){return _3(_K,_V);});break;default:return new F(function(){return _3(_J,_V);});}},_1h=new T(function(){return B(unCStr("IdentPay "));}),_1i=function(_1j,_1k,_1l){if(_1j<11){return new F(function(){return _3(_1h,new T(function(){return B(_d(11,E(_1k),_1l));},1));});}else{var _1m=new T(function(){return B(_3(_1h,new T(function(){return B(_d(11,E(_1k),new T2(1,_b,_1l)));},1)));});return new T2(1,_c,_1m);}},_1n=new T(function(){return B(unCStr("Null"));}),_1o=new T(function(){return B(unCStr("When "));}),_1p=new T(function(){return B(unCStr("Choice "));}),_1q=new T(function(){return B(unCStr("Both "));}),_1r=new T(function(){return B(unCStr("Pay "));}),_1s=new T(function(){return B(unCStr("RedeemCC "));}),_1t=new T(function(){return B(unCStr("CommitCash "));}),_1u=function(_1v,_1w,_1x){var _1y=E(_1w);switch(_1y._){case 0:return new F(function(){return _3(_1n,_1x);});break;case 1:var _1z=function(_1A){var _1B=new T(function(){var _1C=new T(function(){var _1D=new T(function(){var _1E=new T(function(){var _1F=new T(function(){return B(_1u(_1,_1y.f,new T2(1,_w,new T(function(){return B(_1u(_1,_1y.g,_1A));}))));});return B(_d(11,E(_1y.e),new T2(1,_w,_1F)));});return B(_d(11,E(_1y.d),new T2(1,_w,_1E)));});return B(_d(11,E(_1y.c),new T2(1,_w,_1D)));});return B(_d(11,E(_1y.b),new T2(1,_w,_1C)));});return new F(function(){return _o(11,_1y.a,new T2(1,_w,_1B));});};if(E(_1v)<11){return new F(function(){return _3(_1t,new T(function(){return B(_1z(_1x));},1));});}else{var _1G=new T(function(){return B(_3(_1t,new T(function(){return B(_1z(new T2(1,_b,_1x)));},1)));});return new T2(1,_c,_1G);}break;case 2:var _1H=function(_1I){var _1J=new T(function(){return B(_o(11,_1y.a,new T2(1,_w,new T(function(){return B(_1u(_1,_1y.b,_1I));}))));},1);return new F(function(){return _3(_1s,_1J);});};if(E(_1v)<11){return new F(function(){return _1H(_1x);});}else{return new T2(1,_c,new T(function(){return B(_1H(new T2(1,_b,_1x)));}));}break;case 3:var _1K=function(_1L){var _1M=new T(function(){var _1N=new T(function(){var _1O=new T(function(){var _1P=new T(function(){var _1Q=new T(function(){return B(_d(11,E(_1y.e),new T2(1,_w,new T(function(){return B(_1u(_1,_1y.f,_1L));}))));});return B(_d(11,E(_1y.d),new T2(1,_w,_1Q)));});return B(_d(11,E(_1y.c),new T2(1,_w,_1P)));});return B(_d(11,E(_1y.b),new T2(1,_w,_1O)));});return B(_1i(11,_1y.a,new T2(1,_w,_1N)));},1);return new F(function(){return _3(_1r,_1M);});};if(E(_1v)<11){return new F(function(){return _1K(_1x);});}else{return new T2(1,_c,new T(function(){return B(_1K(new T2(1,_b,_1x)));}));}break;case 4:var _1R=function(_1S){var _1T=new T(function(){return B(_1u(_1,_1y.a,new T2(1,_w,new T(function(){return B(_1u(_1,_1y.b,_1S));}))));},1);return new F(function(){return _3(_1q,_1T);});};if(E(_1v)<11){return new F(function(){return _1R(_1x);});}else{return new T2(1,_c,new T(function(){return B(_1R(new T2(1,_b,_1x)));}));}break;case 5:var _1U=function(_1V){var _1W=new T(function(){return B(_1u(_1,_1y.b,new T2(1,_w,new T(function(){return B(_1u(_1,_1y.c,_1V));}))));});return new F(function(){return _S(11,_1y.a,new T2(1,_w,_1W));});};if(E(_1v)<11){return new F(function(){return _3(_1p,new T(function(){return B(_1U(_1x));},1));});}else{var _1X=new T(function(){return B(_3(_1p,new T(function(){return B(_1U(new T2(1,_b,_1x)));},1)));});return new T2(1,_c,_1X);}break;default:var _1Y=function(_1Z){var _20=new T(function(){var _21=new T(function(){var _22=new T(function(){return B(_1u(_1,_1y.c,new T2(1,_w,new T(function(){return B(_1u(_1,_1y.d,_1Z));}))));});return B(_d(11,E(_1y.b),new T2(1,_w,_22)));});return B(_S(11,_1y.a,new T2(1,_w,_21)));},1);return new F(function(){return _3(_1o,_20);});};if(E(_1v)<11){return new F(function(){return _1Y(_1x);});}else{return new T2(1,_c,new T(function(){return B(_1Y(new T2(1,_b,_1x)));}));}}},_23=__Z,_24=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_25=new T(function(){return B(err(_24));}),_26=new T(function(){return B(unCStr("codeArea"));}),_27=function(_){return _0;},_28="(function (t, s) {document.getElementById(t).value = s})",_29=function(_2a,_2b,_){var _2c=eval(E(_28)),_2d=__app2(E(_2c),toJSStr(E(_2a)),toJSStr(E(_2b)));return new F(function(){return _27(_);});},_2e=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_2f=new T(function(){return B(err(_2e));}),_2g=new T(function(){return B(unCStr("base"));}),_2h=new T(function(){return B(unCStr("Control.Exception.Base"));}),_2i=new T(function(){return B(unCStr("PatternMatchFail"));}),_2j=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_2g,_2h,_2i),_2k=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_2j,_23,_23),_2l=function(_2m){return E(_2k);},_2n=function(_2o){return E(E(_2o).a);},_2p=function(_2q,_2r,_2s){var _2t=B(A1(_2q,_)),_2u=B(A1(_2r,_)),_2v=hs_eqWord64(_2t.a,_2u.a);if(!_2v){return __Z;}else{var _2w=hs_eqWord64(_2t.b,_2u.b);return (!_2w)?__Z:new T1(1,_2s);}},_2x=function(_2y){var _2z=E(_2y);return new F(function(){return _2p(B(_2n(_2z.a)),_2l,_2z.b);});},_2A=function(_2B){return E(E(_2B).a);},_2C=function(_2D){return new T2(0,_2E,_2D);},_2F=function(_2G,_2H){return new F(function(){return _3(E(_2G).a,_2H);});},_2I=44,_2J=93,_2K=91,_2L=function(_2M,_2N,_2O){var _2P=E(_2N);if(!_2P._){return new F(function(){return unAppCStr("[]",_2O);});}else{var _2Q=new T(function(){var _2R=new T(function(){var _2S=function(_2T){var _2U=E(_2T);if(!_2U._){return E(new T2(1,_2J,_2O));}else{var _2V=new T(function(){return B(A2(_2M,_2U.a,new T(function(){return B(_2S(_2U.b));})));});return new T2(1,_2I,_2V);}};return B(_2S(_2P.b));});return B(A2(_2M,_2P.a,_2R));});return new T2(1,_2K,_2Q);}},_2W=function(_2X,_2Y){return new F(function(){return _2L(_2F,_2X,_2Y);});},_2Z=function(_30,_31,_32){return new F(function(){return _3(E(_31).a,_32);});},_33=new T3(0,_2Z,_2A,_2W),_2E=new T(function(){return new T5(0,_2l,_33,_2C,_2x,_2A);}),_34=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_35=function(_36){return E(E(_36).c);},_37=function(_38,_39){return new F(function(){return die(new T(function(){return B(A2(_35,_39,_38));}));});},_3a=function(_3b,_3c){return new F(function(){return _37(_3b,_3c);});},_3d=function(_3e,_3f){var _3g=E(_3f);if(!_3g._){return new T2(0,_23,_23);}else{var _3h=_3g.a;if(!B(A1(_3e,_3h))){return new T2(0,_23,_3g);}else{var _3i=new T(function(){var _3j=B(_3d(_3e,_3g.b));return new T2(0,_3j.a,_3j.b);});return new T2(0,new T2(1,_3h,new T(function(){return E(E(_3i).a);})),new T(function(){return E(E(_3i).b);}));}}},_3k=32,_3l=new T(function(){return B(unCStr("\n"));}),_3m=function(_3n){return (E(_3n)==124)?false:true;},_3o=function(_3p,_3q){var _3r=B(_3d(_3m,B(unCStr(_3p)))),_3s=_3r.a,_3t=function(_3u,_3v){var _3w=new T(function(){var _3x=new T(function(){return B(_3(_3q,new T(function(){return B(_3(_3v,_3l));},1)));});return B(unAppCStr(": ",_3x));},1);return new F(function(){return _3(_3u,_3w);});},_3y=E(_3r.b);if(!_3y._){return new F(function(){return _3t(_3s,_23);});}else{if(E(_3y.a)==124){return new F(function(){return _3t(_3s,new T2(1,_3k,_3y.b));});}else{return new F(function(){return _3t(_3s,_23);});}}},_3z=function(_3A){return new F(function(){return _3a(new T1(0,new T(function(){return B(_3o(_3A,_34));})),_2E);});},_3B=new T(function(){return B(_3z("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_3C=function(_3D,_3E){while(1){var _3F=B((function(_3G,_3H){var _3I=E(_3G);switch(_3I._){case 0:var _3J=E(_3H);if(!_3J._){return __Z;}else{_3D=B(A1(_3I.a,_3J.a));_3E=_3J.b;return __continue;}break;case 1:var _3K=B(A1(_3I.a,_3H)),_3L=_3H;_3D=_3K;_3E=_3L;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_3I.a,_3H),new T(function(){return B(_3C(_3I.b,_3H));}));default:return E(_3I.a);}})(_3D,_3E));if(_3F!=__continue){return _3F;}}},_3M=function(_3N,_3O){var _3P=function(_3Q){var _3R=E(_3O);if(_3R._==3){return new T2(3,_3R.a,new T(function(){return B(_3M(_3N,_3R.b));}));}else{var _3S=E(_3N);if(_3S._==2){return E(_3R);}else{var _3T=E(_3R);if(_3T._==2){return E(_3S);}else{var _3U=function(_3V){var _3W=E(_3T);if(_3W._==4){var _3X=function(_3Y){return new T1(4,new T(function(){return B(_3(B(_3C(_3S,_3Y)),_3W.a));}));};return new T1(1,_3X);}else{var _3Z=E(_3S);if(_3Z._==1){var _40=_3Z.a,_41=E(_3W);if(!_41._){return new T1(1,function(_42){return new F(function(){return _3M(B(A1(_40,_42)),_41);});});}else{var _43=function(_44){return new F(function(){return _3M(B(A1(_40,_44)),new T(function(){return B(A1(_41.a,_44));}));});};return new T1(1,_43);}}else{var _45=E(_3W);if(!_45._){return E(_3B);}else{var _46=function(_47){return new F(function(){return _3M(_3Z,new T(function(){return B(A1(_45.a,_47));}));});};return new T1(1,_46);}}}},_48=E(_3S);switch(_48._){case 1:var _49=E(_3T);if(_49._==4){var _4a=function(_4b){return new T1(4,new T(function(){return B(_3(B(_3C(B(A1(_48.a,_4b)),_4b)),_49.a));}));};return new T1(1,_4a);}else{return new F(function(){return _3U(_);});}break;case 4:var _4c=_48.a,_4d=E(_3T);switch(_4d._){case 0:var _4e=function(_4f){var _4g=new T(function(){return B(_3(_4c,new T(function(){return B(_3C(_4d,_4f));},1)));});return new T1(4,_4g);};return new T1(1,_4e);case 1:var _4h=function(_4i){var _4j=new T(function(){return B(_3(_4c,new T(function(){return B(_3C(B(A1(_4d.a,_4i)),_4i));},1)));});return new T1(4,_4j);};return new T1(1,_4h);default:return new T1(4,new T(function(){return B(_3(_4c,_4d.a));}));}break;default:return new F(function(){return _3U(_);});}}}}},_4k=E(_3N);switch(_4k._){case 0:var _4l=E(_3O);if(!_4l._){var _4m=function(_4n){return new F(function(){return _3M(B(A1(_4k.a,_4n)),new T(function(){return B(A1(_4l.a,_4n));}));});};return new T1(0,_4m);}else{return new F(function(){return _3P(_);});}break;case 3:return new T2(3,_4k.a,new T(function(){return B(_3M(_4k.b,_3O));}));default:return new F(function(){return _3P(_);});}},_4o=new T(function(){return B(unCStr("IdentCC"));}),_4p=new T(function(){return B(unCStr("("));}),_4q=new T(function(){return B(unCStr(")"));}),_4r=function(_4s,_4t){while(1){var _4u=E(_4s);if(!_4u._){return (E(_4t)._==0)?true:false;}else{var _4v=E(_4t);if(!_4v._){return false;}else{if(E(_4u.a)!=E(_4v.a)){return false;}else{_4s=_4u.b;_4t=_4v.b;continue;}}}}},_4w=function(_4x,_4y){return E(_4x)!=E(_4y);},_4z=function(_4A,_4B){return E(_4A)==E(_4B);},_4C=new T2(0,_4z,_4w),_4D=function(_4E,_4F){while(1){var _4G=E(_4E);if(!_4G._){return (E(_4F)._==0)?true:false;}else{var _4H=E(_4F);if(!_4H._){return false;}else{if(E(_4G.a)!=E(_4H.a)){return false;}else{_4E=_4G.b;_4F=_4H.b;continue;}}}}},_4I=function(_4J,_4K){return (!B(_4D(_4J,_4K)))?true:false;},_4L=new T2(0,_4D,_4I),_4M=function(_4N,_4O){var _4P=E(_4N);switch(_4P._){case 0:return new T1(0,function(_4Q){return new F(function(){return _4M(B(A1(_4P.a,_4Q)),_4O);});});case 1:return new T1(1,function(_4R){return new F(function(){return _4M(B(A1(_4P.a,_4R)),_4O);});});case 2:return new T0(2);case 3:return new F(function(){return _3M(B(A1(_4O,_4P.a)),new T(function(){return B(_4M(_4P.b,_4O));}));});break;default:var _4S=function(_4T){var _4U=E(_4T);if(!_4U._){return __Z;}else{var _4V=E(_4U.a);return new F(function(){return _3(B(_3C(B(A1(_4O,_4V.a)),_4V.b)),new T(function(){return B(_4S(_4U.b));},1));});}},_4W=B(_4S(_4P.a));return (_4W._==0)?new T0(2):new T1(4,_4W);}},_4X=new T0(2),_4Y=function(_4Z){return new T2(3,_4Z,_4X);},_50=function(_51,_52){var _53=E(_51);if(!_53){return new F(function(){return A1(_52,_0);});}else{var _54=new T(function(){return B(_50(_53-1|0,_52));});return new T1(0,function(_55){return E(_54);});}},_56=function(_57,_58,_59){var _5a=new T(function(){return B(A1(_57,_4Y));}),_5b=function(_5c,_5d,_5e,_5f){while(1){var _5g=B((function(_5h,_5i,_5j,_5k){var _5l=E(_5h);switch(_5l._){case 0:var _5m=E(_5i);if(!_5m._){return new F(function(){return A1(_58,_5k);});}else{var _5n=_5j+1|0,_5o=_5k;_5c=B(A1(_5l.a,_5m.a));_5d=_5m.b;_5e=_5n;_5f=_5o;return __continue;}break;case 1:var _5p=B(A1(_5l.a,_5i)),_5q=_5i,_5n=_5j,_5o=_5k;_5c=_5p;_5d=_5q;_5e=_5n;_5f=_5o;return __continue;case 2:return new F(function(){return A1(_58,_5k);});break;case 3:var _5r=new T(function(){return B(_4M(_5l,_5k));});return new F(function(){return _50(_5j,function(_5s){return E(_5r);});});break;default:return new F(function(){return _4M(_5l,_5k);});}})(_5c,_5d,_5e,_5f));if(_5g!=__continue){return _5g;}}};return function(_5t){return new F(function(){return _5b(_5a,_5t,0,_59);});};},_5u=function(_5v){return new F(function(){return A1(_5v,_23);});},_5w=function(_5x,_5y){var _5z=function(_5A){var _5B=E(_5A);if(!_5B._){return E(_5u);}else{var _5C=_5B.a;if(!B(A1(_5x,_5C))){return E(_5u);}else{var _5D=new T(function(){return B(_5z(_5B.b));}),_5E=function(_5F){var _5G=new T(function(){return B(A1(_5D,function(_5H){return new F(function(){return A1(_5F,new T2(1,_5C,_5H));});}));});return new T1(0,function(_5I){return E(_5G);});};return E(_5E);}}};return function(_5J){return new F(function(){return A2(_5z,_5J,_5y);});};},_5K=new T0(6),_5L=function(_5M){return E(_5M);},_5N=new T(function(){return B(unCStr("valDig: Bad base"));}),_5O=new T(function(){return B(err(_5N));}),_5P=function(_5Q,_5R){var _5S=function(_5T,_5U){var _5V=E(_5T);if(!_5V._){var _5W=new T(function(){return B(A1(_5U,_23));});return function(_5X){return new F(function(){return A1(_5X,_5W);});};}else{var _5Y=E(_5V.a),_5Z=function(_60){var _61=new T(function(){return B(_5S(_5V.b,function(_62){return new F(function(){return A1(_5U,new T2(1,_60,_62));});}));}),_63=function(_64){var _65=new T(function(){return B(A1(_61,_64));});return new T1(0,function(_66){return E(_65);});};return E(_63);};switch(E(_5Q)){case 8:if(48>_5Y){var _67=new T(function(){return B(A1(_5U,_23));});return function(_68){return new F(function(){return A1(_68,_67);});};}else{if(_5Y>55){var _69=new T(function(){return B(A1(_5U,_23));});return function(_6a){return new F(function(){return A1(_6a,_69);});};}else{return new F(function(){return _5Z(_5Y-48|0);});}}break;case 10:if(48>_5Y){var _6b=new T(function(){return B(A1(_5U,_23));});return function(_6c){return new F(function(){return A1(_6c,_6b);});};}else{if(_5Y>57){var _6d=new T(function(){return B(A1(_5U,_23));});return function(_6e){return new F(function(){return A1(_6e,_6d);});};}else{return new F(function(){return _5Z(_5Y-48|0);});}}break;case 16:if(48>_5Y){if(97>_5Y){if(65>_5Y){var _6f=new T(function(){return B(A1(_5U,_23));});return function(_6g){return new F(function(){return A1(_6g,_6f);});};}else{if(_5Y>70){var _6h=new T(function(){return B(A1(_5U,_23));});return function(_6i){return new F(function(){return A1(_6i,_6h);});};}else{return new F(function(){return _5Z((_5Y-65|0)+10|0);});}}}else{if(_5Y>102){if(65>_5Y){var _6j=new T(function(){return B(A1(_5U,_23));});return function(_6k){return new F(function(){return A1(_6k,_6j);});};}else{if(_5Y>70){var _6l=new T(function(){return B(A1(_5U,_23));});return function(_6m){return new F(function(){return A1(_6m,_6l);});};}else{return new F(function(){return _5Z((_5Y-65|0)+10|0);});}}}else{return new F(function(){return _5Z((_5Y-97|0)+10|0);});}}}else{if(_5Y>57){if(97>_5Y){if(65>_5Y){var _6n=new T(function(){return B(A1(_5U,_23));});return function(_6o){return new F(function(){return A1(_6o,_6n);});};}else{if(_5Y>70){var _6p=new T(function(){return B(A1(_5U,_23));});return function(_6q){return new F(function(){return A1(_6q,_6p);});};}else{return new F(function(){return _5Z((_5Y-65|0)+10|0);});}}}else{if(_5Y>102){if(65>_5Y){var _6r=new T(function(){return B(A1(_5U,_23));});return function(_6s){return new F(function(){return A1(_6s,_6r);});};}else{if(_5Y>70){var _6t=new T(function(){return B(A1(_5U,_23));});return function(_6u){return new F(function(){return A1(_6u,_6t);});};}else{return new F(function(){return _5Z((_5Y-65|0)+10|0);});}}}else{return new F(function(){return _5Z((_5Y-97|0)+10|0);});}}}else{return new F(function(){return _5Z(_5Y-48|0);});}}break;default:return E(_5O);}}},_6v=function(_6w){var _6x=E(_6w);if(!_6x._){return new T0(2);}else{return new F(function(){return A1(_5R,_6x);});}};return function(_6y){return new F(function(){return A3(_5S,_6y,_5L,_6v);});};},_6z=16,_6A=8,_6B=function(_6C){var _6D=function(_6E){return new F(function(){return A1(_6C,new T1(5,new T2(0,_6A,_6E)));});},_6F=function(_6G){return new F(function(){return A1(_6C,new T1(5,new T2(0,_6z,_6G)));});},_6H=function(_6I){switch(E(_6I)){case 79:return new T1(1,B(_5P(_6A,_6D)));case 88:return new T1(1,B(_5P(_6z,_6F)));case 111:return new T1(1,B(_5P(_6A,_6D)));case 120:return new T1(1,B(_5P(_6z,_6F)));default:return new T0(2);}};return function(_6J){return (E(_6J)==48)?E(new T1(0,_6H)):new T0(2);};},_6K=function(_6L){return new T1(0,B(_6B(_6L)));},_6M=__Z,_6N=function(_6O){return new F(function(){return A1(_6O,_6M);});},_6P=function(_6Q){return new F(function(){return A1(_6Q,_6M);});},_6R=10,_6S=new T1(0,1),_6T=new T1(0,2147483647),_6U=function(_6V,_6W){while(1){var _6X=E(_6V);if(!_6X._){var _6Y=_6X.a,_6Z=E(_6W);if(!_6Z._){var _70=_6Z.a,_71=addC(_6Y,_70);if(!E(_71.b)){return new T1(0,_71.a);}else{_6V=new T1(1,I_fromInt(_6Y));_6W=new T1(1,I_fromInt(_70));continue;}}else{_6V=new T1(1,I_fromInt(_6Y));_6W=_6Z;continue;}}else{var _72=E(_6W);if(!_72._){_6V=_6X;_6W=new T1(1,I_fromInt(_72.a));continue;}else{return new T1(1,I_add(_6X.a,_72.a));}}}},_73=new T(function(){return B(_6U(_6T,_6S));}),_74=function(_75){var _76=E(_75);if(!_76._){var _77=E(_76.a);return (_77==( -2147483648))?E(_73):new T1(0, -_77);}else{return new T1(1,I_negate(_76.a));}},_78=new T1(0,10),_79=function(_7a,_7b){while(1){var _7c=E(_7a);if(!_7c._){return E(_7b);}else{var _7d=_7b+1|0;_7a=_7c.b;_7b=_7d;continue;}}},_7e=function(_7f,_7g){var _7h=E(_7g);return (_7h._==0)?__Z:new T2(1,new T(function(){return B(A1(_7f,_7h.a));}),new T(function(){return B(_7e(_7f,_7h.b));}));},_7i=function(_7j){return new T1(0,_7j);},_7k=function(_7l){return new F(function(){return _7i(E(_7l));});},_7m=new T(function(){return B(unCStr("this should not happen"));}),_7n=new T(function(){return B(err(_7m));}),_7o=function(_7p,_7q){while(1){var _7r=E(_7p);if(!_7r._){var _7s=_7r.a,_7t=E(_7q);if(!_7t._){var _7u=_7t.a;if(!(imul(_7s,_7u)|0)){return new T1(0,imul(_7s,_7u)|0);}else{_7p=new T1(1,I_fromInt(_7s));_7q=new T1(1,I_fromInt(_7u));continue;}}else{_7p=new T1(1,I_fromInt(_7s));_7q=_7t;continue;}}else{var _7v=E(_7q);if(!_7v._){_7p=_7r;_7q=new T1(1,I_fromInt(_7v.a));continue;}else{return new T1(1,I_mul(_7r.a,_7v.a));}}}},_7w=function(_7x,_7y){var _7z=E(_7y);if(!_7z._){return __Z;}else{var _7A=E(_7z.b);return (_7A._==0)?E(_7n):new T2(1,B(_6U(B(_7o(_7z.a,_7x)),_7A.a)),new T(function(){return B(_7w(_7x,_7A.b));}));}},_7B=new T1(0,0),_7C=function(_7D,_7E,_7F){while(1){var _7G=B((function(_7H,_7I,_7J){var _7K=E(_7J);if(!_7K._){return E(_7B);}else{if(!E(_7K.b)._){return E(_7K.a);}else{var _7L=E(_7I);if(_7L<=40){var _7M=function(_7N,_7O){while(1){var _7P=E(_7O);if(!_7P._){return E(_7N);}else{var _7Q=B(_6U(B(_7o(_7N,_7H)),_7P.a));_7N=_7Q;_7O=_7P.b;continue;}}};return new F(function(){return _7M(_7B,_7K);});}else{var _7R=B(_7o(_7H,_7H));if(!(_7L%2)){var _7S=B(_7w(_7H,_7K));_7D=_7R;_7E=quot(_7L+1|0,2);_7F=_7S;return __continue;}else{var _7S=B(_7w(_7H,new T2(1,_7B,_7K)));_7D=_7R;_7E=quot(_7L+1|0,2);_7F=_7S;return __continue;}}}}})(_7D,_7E,_7F));if(_7G!=__continue){return _7G;}}},_7T=function(_7U,_7V){return new F(function(){return _7C(_7U,new T(function(){return B(_79(_7V,0));},1),B(_7e(_7k,_7V)));});},_7W=function(_7X){var _7Y=new T(function(){var _7Z=new T(function(){var _80=function(_81){return new F(function(){return A1(_7X,new T1(1,new T(function(){return B(_7T(_78,_81));})));});};return new T1(1,B(_5P(_6R,_80)));}),_82=function(_83){if(E(_83)==43){var _84=function(_85){return new F(function(){return A1(_7X,new T1(1,new T(function(){return B(_7T(_78,_85));})));});};return new T1(1,B(_5P(_6R,_84)));}else{return new T0(2);}},_86=function(_87){if(E(_87)==45){var _88=function(_89){return new F(function(){return A1(_7X,new T1(1,new T(function(){return B(_74(B(_7T(_78,_89))));})));});};return new T1(1,B(_5P(_6R,_88)));}else{return new T0(2);}};return B(_3M(B(_3M(new T1(0,_86),new T1(0,_82))),_7Z));});return new F(function(){return _3M(new T1(0,function(_8a){return (E(_8a)==101)?E(_7Y):new T0(2);}),new T1(0,function(_8b){return (E(_8b)==69)?E(_7Y):new T0(2);}));});},_8c=function(_8d){var _8e=function(_8f){return new F(function(){return A1(_8d,new T1(1,_8f));});};return function(_8g){return (E(_8g)==46)?new T1(1,B(_5P(_6R,_8e))):new T0(2);};},_8h=function(_8i){return new T1(0,B(_8c(_8i)));},_8j=function(_8k){var _8l=function(_8m){var _8n=function(_8o){return new T1(1,B(_56(_7W,_6N,function(_8p){return new F(function(){return A1(_8k,new T1(5,new T3(1,_8m,_8o,_8p)));});})));};return new T1(1,B(_56(_8h,_6P,_8n)));};return new F(function(){return _5P(_6R,_8l);});},_8q=function(_8r){return new T1(1,B(_8j(_8r)));},_8s=function(_8t){return E(E(_8t).a);},_8u=function(_8v,_8w,_8x){while(1){var _8y=E(_8x);if(!_8y._){return false;}else{if(!B(A3(_8s,_8v,_8w,_8y.a))){_8x=_8y.b;continue;}else{return true;}}}},_8z=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_8A=function(_8B){return new F(function(){return _8u(_4C,_8B,_8z);});},_8C=false,_8D=true,_8E=function(_8F){var _8G=new T(function(){return B(A1(_8F,_6A));}),_8H=new T(function(){return B(A1(_8F,_6z));});return function(_8I){switch(E(_8I)){case 79:return E(_8G);case 88:return E(_8H);case 111:return E(_8G);case 120:return E(_8H);default:return new T0(2);}};},_8J=function(_8K){return new T1(0,B(_8E(_8K)));},_8L=function(_8M){return new F(function(){return A1(_8M,_6R);});},_8N=function(_8O){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_d(9,_8O,_23));}))));});},_8P=function(_8Q){var _8R=E(_8Q);if(!_8R._){return E(_8R.a);}else{return new F(function(){return I_toInt(_8R.a);});}},_8S=function(_8T,_8U){var _8V=E(_8T);if(!_8V._){var _8W=_8V.a,_8X=E(_8U);return (_8X._==0)?_8W<=_8X.a:I_compareInt(_8X.a,_8W)>=0;}else{var _8Y=_8V.a,_8Z=E(_8U);return (_8Z._==0)?I_compareInt(_8Y,_8Z.a)<=0:I_compare(_8Y,_8Z.a)<=0;}},_90=function(_91){return new T0(2);},_92=function(_93){var _94=E(_93);if(!_94._){return E(_90);}else{var _95=_94.a,_96=E(_94.b);if(!_96._){return E(_95);}else{var _97=new T(function(){return B(_92(_96));}),_98=function(_99){return new F(function(){return _3M(B(A1(_95,_99)),new T(function(){return B(A1(_97,_99));}));});};return E(_98);}}},_9a=function(_9b,_9c){var _9d=function(_9e,_9f,_9g){var _9h=E(_9e);if(!_9h._){return new F(function(){return A1(_9g,_9b);});}else{var _9i=E(_9f);if(!_9i._){return new T0(2);}else{if(E(_9h.a)!=E(_9i.a)){return new T0(2);}else{var _9j=new T(function(){return B(_9d(_9h.b,_9i.b,_9g));});return new T1(0,function(_9k){return E(_9j);});}}}};return function(_9l){return new F(function(){return _9d(_9b,_9l,_9c);});};},_9m=new T(function(){return B(unCStr("SO"));}),_9n=14,_9o=function(_9p){var _9q=new T(function(){return B(A1(_9p,_9n));});return new T1(1,B(_9a(_9m,function(_9r){return E(_9q);})));},_9s=new T(function(){return B(unCStr("SOH"));}),_9t=1,_9u=function(_9v){var _9w=new T(function(){return B(A1(_9v,_9t));});return new T1(1,B(_9a(_9s,function(_9x){return E(_9w);})));},_9y=function(_9z){return new T1(1,B(_56(_9u,_9o,_9z)));},_9A=new T(function(){return B(unCStr("NUL"));}),_9B=0,_9C=function(_9D){var _9E=new T(function(){return B(A1(_9D,_9B));});return new T1(1,B(_9a(_9A,function(_9F){return E(_9E);})));},_9G=new T(function(){return B(unCStr("STX"));}),_9H=2,_9I=function(_9J){var _9K=new T(function(){return B(A1(_9J,_9H));});return new T1(1,B(_9a(_9G,function(_9L){return E(_9K);})));},_9M=new T(function(){return B(unCStr("ETX"));}),_9N=3,_9O=function(_9P){var _9Q=new T(function(){return B(A1(_9P,_9N));});return new T1(1,B(_9a(_9M,function(_9R){return E(_9Q);})));},_9S=new T(function(){return B(unCStr("EOT"));}),_9T=4,_9U=function(_9V){var _9W=new T(function(){return B(A1(_9V,_9T));});return new T1(1,B(_9a(_9S,function(_9X){return E(_9W);})));},_9Y=new T(function(){return B(unCStr("ENQ"));}),_9Z=5,_a0=function(_a1){var _a2=new T(function(){return B(A1(_a1,_9Z));});return new T1(1,B(_9a(_9Y,function(_a3){return E(_a2);})));},_a4=new T(function(){return B(unCStr("ACK"));}),_a5=6,_a6=function(_a7){var _a8=new T(function(){return B(A1(_a7,_a5));});return new T1(1,B(_9a(_a4,function(_a9){return E(_a8);})));},_aa=new T(function(){return B(unCStr("BEL"));}),_ab=7,_ac=function(_ad){var _ae=new T(function(){return B(A1(_ad,_ab));});return new T1(1,B(_9a(_aa,function(_af){return E(_ae);})));},_ag=new T(function(){return B(unCStr("BS"));}),_ah=8,_ai=function(_aj){var _ak=new T(function(){return B(A1(_aj,_ah));});return new T1(1,B(_9a(_ag,function(_al){return E(_ak);})));},_am=new T(function(){return B(unCStr("HT"));}),_an=9,_ao=function(_ap){var _aq=new T(function(){return B(A1(_ap,_an));});return new T1(1,B(_9a(_am,function(_ar){return E(_aq);})));},_as=new T(function(){return B(unCStr("LF"));}),_at=10,_au=function(_av){var _aw=new T(function(){return B(A1(_av,_at));});return new T1(1,B(_9a(_as,function(_ax){return E(_aw);})));},_ay=new T(function(){return B(unCStr("VT"));}),_az=11,_aA=function(_aB){var _aC=new T(function(){return B(A1(_aB,_az));});return new T1(1,B(_9a(_ay,function(_aD){return E(_aC);})));},_aE=new T(function(){return B(unCStr("FF"));}),_aF=12,_aG=function(_aH){var _aI=new T(function(){return B(A1(_aH,_aF));});return new T1(1,B(_9a(_aE,function(_aJ){return E(_aI);})));},_aK=new T(function(){return B(unCStr("CR"));}),_aL=13,_aM=function(_aN){var _aO=new T(function(){return B(A1(_aN,_aL));});return new T1(1,B(_9a(_aK,function(_aP){return E(_aO);})));},_aQ=new T(function(){return B(unCStr("SI"));}),_aR=15,_aS=function(_aT){var _aU=new T(function(){return B(A1(_aT,_aR));});return new T1(1,B(_9a(_aQ,function(_aV){return E(_aU);})));},_aW=new T(function(){return B(unCStr("DLE"));}),_aX=16,_aY=function(_aZ){var _b0=new T(function(){return B(A1(_aZ,_aX));});return new T1(1,B(_9a(_aW,function(_b1){return E(_b0);})));},_b2=new T(function(){return B(unCStr("DC1"));}),_b3=17,_b4=function(_b5){var _b6=new T(function(){return B(A1(_b5,_b3));});return new T1(1,B(_9a(_b2,function(_b7){return E(_b6);})));},_b8=new T(function(){return B(unCStr("DC2"));}),_b9=18,_ba=function(_bb){var _bc=new T(function(){return B(A1(_bb,_b9));});return new T1(1,B(_9a(_b8,function(_bd){return E(_bc);})));},_be=new T(function(){return B(unCStr("DC3"));}),_bf=19,_bg=function(_bh){var _bi=new T(function(){return B(A1(_bh,_bf));});return new T1(1,B(_9a(_be,function(_bj){return E(_bi);})));},_bk=new T(function(){return B(unCStr("DC4"));}),_bl=20,_bm=function(_bn){var _bo=new T(function(){return B(A1(_bn,_bl));});return new T1(1,B(_9a(_bk,function(_bp){return E(_bo);})));},_bq=new T(function(){return B(unCStr("NAK"));}),_br=21,_bs=function(_bt){var _bu=new T(function(){return B(A1(_bt,_br));});return new T1(1,B(_9a(_bq,function(_bv){return E(_bu);})));},_bw=new T(function(){return B(unCStr("SYN"));}),_bx=22,_by=function(_bz){var _bA=new T(function(){return B(A1(_bz,_bx));});return new T1(1,B(_9a(_bw,function(_bB){return E(_bA);})));},_bC=new T(function(){return B(unCStr("ETB"));}),_bD=23,_bE=function(_bF){var _bG=new T(function(){return B(A1(_bF,_bD));});return new T1(1,B(_9a(_bC,function(_bH){return E(_bG);})));},_bI=new T(function(){return B(unCStr("CAN"));}),_bJ=24,_bK=function(_bL){var _bM=new T(function(){return B(A1(_bL,_bJ));});return new T1(1,B(_9a(_bI,function(_bN){return E(_bM);})));},_bO=new T(function(){return B(unCStr("EM"));}),_bP=25,_bQ=function(_bR){var _bS=new T(function(){return B(A1(_bR,_bP));});return new T1(1,B(_9a(_bO,function(_bT){return E(_bS);})));},_bU=new T(function(){return B(unCStr("SUB"));}),_bV=26,_bW=function(_bX){var _bY=new T(function(){return B(A1(_bX,_bV));});return new T1(1,B(_9a(_bU,function(_bZ){return E(_bY);})));},_c0=new T(function(){return B(unCStr("ESC"));}),_c1=27,_c2=function(_c3){var _c4=new T(function(){return B(A1(_c3,_c1));});return new T1(1,B(_9a(_c0,function(_c5){return E(_c4);})));},_c6=new T(function(){return B(unCStr("FS"));}),_c7=28,_c8=function(_c9){var _ca=new T(function(){return B(A1(_c9,_c7));});return new T1(1,B(_9a(_c6,function(_cb){return E(_ca);})));},_cc=new T(function(){return B(unCStr("GS"));}),_cd=29,_ce=function(_cf){var _cg=new T(function(){return B(A1(_cf,_cd));});return new T1(1,B(_9a(_cc,function(_ch){return E(_cg);})));},_ci=new T(function(){return B(unCStr("RS"));}),_cj=30,_ck=function(_cl){var _cm=new T(function(){return B(A1(_cl,_cj));});return new T1(1,B(_9a(_ci,function(_cn){return E(_cm);})));},_co=new T(function(){return B(unCStr("US"));}),_cp=31,_cq=function(_cr){var _cs=new T(function(){return B(A1(_cr,_cp));});return new T1(1,B(_9a(_co,function(_ct){return E(_cs);})));},_cu=new T(function(){return B(unCStr("SP"));}),_cv=32,_cw=function(_cx){var _cy=new T(function(){return B(A1(_cx,_cv));});return new T1(1,B(_9a(_cu,function(_cz){return E(_cy);})));},_cA=new T(function(){return B(unCStr("DEL"));}),_cB=127,_cC=function(_cD){var _cE=new T(function(){return B(A1(_cD,_cB));});return new T1(1,B(_9a(_cA,function(_cF){return E(_cE);})));},_cG=new T2(1,_cC,_23),_cH=new T2(1,_cw,_cG),_cI=new T2(1,_cq,_cH),_cJ=new T2(1,_ck,_cI),_cK=new T2(1,_ce,_cJ),_cL=new T2(1,_c8,_cK),_cM=new T2(1,_c2,_cL),_cN=new T2(1,_bW,_cM),_cO=new T2(1,_bQ,_cN),_cP=new T2(1,_bK,_cO),_cQ=new T2(1,_bE,_cP),_cR=new T2(1,_by,_cQ),_cS=new T2(1,_bs,_cR),_cT=new T2(1,_bm,_cS),_cU=new T2(1,_bg,_cT),_cV=new T2(1,_ba,_cU),_cW=new T2(1,_b4,_cV),_cX=new T2(1,_aY,_cW),_cY=new T2(1,_aS,_cX),_cZ=new T2(1,_aM,_cY),_d0=new T2(1,_aG,_cZ),_d1=new T2(1,_aA,_d0),_d2=new T2(1,_au,_d1),_d3=new T2(1,_ao,_d2),_d4=new T2(1,_ai,_d3),_d5=new T2(1,_ac,_d4),_d6=new T2(1,_a6,_d5),_d7=new T2(1,_a0,_d6),_d8=new T2(1,_9U,_d7),_d9=new T2(1,_9O,_d8),_da=new T2(1,_9I,_d9),_db=new T2(1,_9C,_da),_dc=new T2(1,_9y,_db),_dd=new T(function(){return B(_92(_dc));}),_de=34,_df=new T1(0,1114111),_dg=92,_dh=39,_di=function(_dj){var _dk=new T(function(){return B(A1(_dj,_ab));}),_dl=new T(function(){return B(A1(_dj,_ah));}),_dm=new T(function(){return B(A1(_dj,_an));}),_dn=new T(function(){return B(A1(_dj,_at));}),_do=new T(function(){return B(A1(_dj,_az));}),_dp=new T(function(){return B(A1(_dj,_aF));}),_dq=new T(function(){return B(A1(_dj,_aL));}),_dr=new T(function(){return B(A1(_dj,_dg));}),_ds=new T(function(){return B(A1(_dj,_dh));}),_dt=new T(function(){return B(A1(_dj,_de));}),_du=new T(function(){var _dv=function(_dw){var _dx=new T(function(){return B(_7i(E(_dw)));}),_dy=function(_dz){var _dA=B(_7T(_dx,_dz));if(!B(_8S(_dA,_df))){return new T0(2);}else{return new F(function(){return A1(_dj,new T(function(){var _dB=B(_8P(_dA));if(_dB>>>0>1114111){return B(_8N(_dB));}else{return _dB;}}));});}};return new T1(1,B(_5P(_dw,_dy)));},_dC=new T(function(){var _dD=new T(function(){return B(A1(_dj,_cp));}),_dE=new T(function(){return B(A1(_dj,_cj));}),_dF=new T(function(){return B(A1(_dj,_cd));}),_dG=new T(function(){return B(A1(_dj,_c7));}),_dH=new T(function(){return B(A1(_dj,_c1));}),_dI=new T(function(){return B(A1(_dj,_bV));}),_dJ=new T(function(){return B(A1(_dj,_bP));}),_dK=new T(function(){return B(A1(_dj,_bJ));}),_dL=new T(function(){return B(A1(_dj,_bD));}),_dM=new T(function(){return B(A1(_dj,_bx));}),_dN=new T(function(){return B(A1(_dj,_br));}),_dO=new T(function(){return B(A1(_dj,_bl));}),_dP=new T(function(){return B(A1(_dj,_bf));}),_dQ=new T(function(){return B(A1(_dj,_b9));}),_dR=new T(function(){return B(A1(_dj,_b3));}),_dS=new T(function(){return B(A1(_dj,_aX));}),_dT=new T(function(){return B(A1(_dj,_aR));}),_dU=new T(function(){return B(A1(_dj,_9n));}),_dV=new T(function(){return B(A1(_dj,_a5));}),_dW=new T(function(){return B(A1(_dj,_9Z));}),_dX=new T(function(){return B(A1(_dj,_9T));}),_dY=new T(function(){return B(A1(_dj,_9N));}),_dZ=new T(function(){return B(A1(_dj,_9H));}),_e0=new T(function(){return B(A1(_dj,_9t));}),_e1=new T(function(){return B(A1(_dj,_9B));}),_e2=function(_e3){switch(E(_e3)){case 64:return E(_e1);case 65:return E(_e0);case 66:return E(_dZ);case 67:return E(_dY);case 68:return E(_dX);case 69:return E(_dW);case 70:return E(_dV);case 71:return E(_dk);case 72:return E(_dl);case 73:return E(_dm);case 74:return E(_dn);case 75:return E(_do);case 76:return E(_dp);case 77:return E(_dq);case 78:return E(_dU);case 79:return E(_dT);case 80:return E(_dS);case 81:return E(_dR);case 82:return E(_dQ);case 83:return E(_dP);case 84:return E(_dO);case 85:return E(_dN);case 86:return E(_dM);case 87:return E(_dL);case 88:return E(_dK);case 89:return E(_dJ);case 90:return E(_dI);case 91:return E(_dH);case 92:return E(_dG);case 93:return E(_dF);case 94:return E(_dE);case 95:return E(_dD);default:return new T0(2);}};return B(_3M(new T1(0,function(_e4){return (E(_e4)==94)?E(new T1(0,_e2)):new T0(2);}),new T(function(){return B(A1(_dd,_dj));})));});return B(_3M(new T1(1,B(_56(_8J,_8L,_dv))),_dC));});return new F(function(){return _3M(new T1(0,function(_e5){switch(E(_e5)){case 34:return E(_dt);case 39:return E(_ds);case 92:return E(_dr);case 97:return E(_dk);case 98:return E(_dl);case 102:return E(_dp);case 110:return E(_dn);case 114:return E(_dq);case 116:return E(_dm);case 118:return E(_do);default:return new T0(2);}}),_du);});},_e6=function(_e7){return new F(function(){return A1(_e7,_0);});},_e8=function(_e9){var _ea=E(_e9);if(!_ea._){return E(_e6);}else{var _eb=E(_ea.a),_ec=_eb>>>0,_ed=new T(function(){return B(_e8(_ea.b));});if(_ec>887){var _ee=u_iswspace(_eb);if(!E(_ee)){return E(_e6);}else{var _ef=function(_eg){var _eh=new T(function(){return B(A1(_ed,_eg));});return new T1(0,function(_ei){return E(_eh);});};return E(_ef);}}else{var _ej=E(_ec);if(_ej==32){var _ek=function(_el){var _em=new T(function(){return B(A1(_ed,_el));});return new T1(0,function(_en){return E(_em);});};return E(_ek);}else{if(_ej-9>>>0>4){if(E(_ej)==160){var _eo=function(_ep){var _eq=new T(function(){return B(A1(_ed,_ep));});return new T1(0,function(_er){return E(_eq);});};return E(_eo);}else{return E(_e6);}}else{var _es=function(_et){var _eu=new T(function(){return B(A1(_ed,_et));});return new T1(0,function(_ev){return E(_eu);});};return E(_es);}}}}},_ew=function(_ex){var _ey=new T(function(){return B(_ew(_ex));}),_ez=function(_eA){return (E(_eA)==92)?E(_ey):new T0(2);},_eB=function(_eC){return E(new T1(0,_ez));},_eD=new T1(1,function(_eE){return new F(function(){return A2(_e8,_eE,_eB);});}),_eF=new T(function(){return B(_di(function(_eG){return new F(function(){return A1(_ex,new T2(0,_eG,_8D));});}));}),_eH=function(_eI){var _eJ=E(_eI);if(_eJ==38){return E(_ey);}else{var _eK=_eJ>>>0;if(_eK>887){var _eL=u_iswspace(_eJ);return (E(_eL)==0)?new T0(2):E(_eD);}else{var _eM=E(_eK);return (_eM==32)?E(_eD):(_eM-9>>>0>4)?(E(_eM)==160)?E(_eD):new T0(2):E(_eD);}}};return new F(function(){return _3M(new T1(0,function(_eN){return (E(_eN)==92)?E(new T1(0,_eH)):new T0(2);}),new T1(0,function(_eO){var _eP=E(_eO);if(E(_eP)==92){return E(_eF);}else{return new F(function(){return A1(_ex,new T2(0,_eP,_8C));});}}));});},_eQ=function(_eR,_eS){var _eT=new T(function(){return B(A1(_eS,new T1(1,new T(function(){return B(A1(_eR,_23));}))));}),_eU=function(_eV){var _eW=E(_eV),_eX=E(_eW.a);if(E(_eX)==34){if(!E(_eW.b)){return E(_eT);}else{return new F(function(){return _eQ(function(_eY){return new F(function(){return A1(_eR,new T2(1,_eX,_eY));});},_eS);});}}else{return new F(function(){return _eQ(function(_eZ){return new F(function(){return A1(_eR,new T2(1,_eX,_eZ));});},_eS);});}};return new F(function(){return _ew(_eU);});},_f0=new T(function(){return B(unCStr("_\'"));}),_f1=function(_f2){var _f3=u_iswalnum(_f2);if(!E(_f3)){return new F(function(){return _8u(_4C,_f2,_f0);});}else{return true;}},_f4=function(_f5){return new F(function(){return _f1(E(_f5));});},_f6=new T(function(){return B(unCStr(",;()[]{}`"));}),_f7=new T(function(){return B(unCStr("=>"));}),_f8=new T2(1,_f7,_23),_f9=new T(function(){return B(unCStr("~"));}),_fa=new T2(1,_f9,_f8),_fb=new T(function(){return B(unCStr("@"));}),_fc=new T2(1,_fb,_fa),_fd=new T(function(){return B(unCStr("->"));}),_fe=new T2(1,_fd,_fc),_ff=new T(function(){return B(unCStr("<-"));}),_fg=new T2(1,_ff,_fe),_fh=new T(function(){return B(unCStr("|"));}),_fi=new T2(1,_fh,_fg),_fj=new T(function(){return B(unCStr("\\"));}),_fk=new T2(1,_fj,_fi),_fl=new T(function(){return B(unCStr("="));}),_fm=new T2(1,_fl,_fk),_fn=new T(function(){return B(unCStr("::"));}),_fo=new T2(1,_fn,_fm),_fp=new T(function(){return B(unCStr(".."));}),_fq=new T2(1,_fp,_fo),_fr=function(_fs){var _ft=new T(function(){return B(A1(_fs,_5K));}),_fu=new T(function(){var _fv=new T(function(){var _fw=function(_fx){var _fy=new T(function(){return B(A1(_fs,new T1(0,_fx)));});return new T1(0,function(_fz){return (E(_fz)==39)?E(_fy):new T0(2);});};return B(_di(_fw));}),_fA=function(_fB){var _fC=E(_fB);switch(E(_fC)){case 39:return new T0(2);case 92:return E(_fv);default:var _fD=new T(function(){return B(A1(_fs,new T1(0,_fC)));});return new T1(0,function(_fE){return (E(_fE)==39)?E(_fD):new T0(2);});}},_fF=new T(function(){var _fG=new T(function(){return B(_eQ(_5L,_fs));}),_fH=new T(function(){var _fI=new T(function(){var _fJ=new T(function(){var _fK=function(_fL){var _fM=E(_fL),_fN=u_iswalpha(_fM);return (E(_fN)==0)?(E(_fM)==95)?new T1(1,B(_5w(_f4,function(_fO){return new F(function(){return A1(_fs,new T1(3,new T2(1,_fM,_fO)));});}))):new T0(2):new T1(1,B(_5w(_f4,function(_fP){return new F(function(){return A1(_fs,new T1(3,new T2(1,_fM,_fP)));});})));};return B(_3M(new T1(0,_fK),new T(function(){return new T1(1,B(_56(_6K,_8q,_fs)));})));}),_fQ=function(_fR){return (!B(_8u(_4C,_fR,_8z)))?new T0(2):new T1(1,B(_5w(_8A,function(_fS){var _fT=new T2(1,_fR,_fS);if(!B(_8u(_4L,_fT,_fq))){return new F(function(){return A1(_fs,new T1(4,_fT));});}else{return new F(function(){return A1(_fs,new T1(2,_fT));});}})));};return B(_3M(new T1(0,_fQ),_fJ));});return B(_3M(new T1(0,function(_fU){if(!B(_8u(_4C,_fU,_f6))){return new T0(2);}else{return new F(function(){return A1(_fs,new T1(2,new T2(1,_fU,_23)));});}}),_fI));});return B(_3M(new T1(0,function(_fV){return (E(_fV)==34)?E(_fG):new T0(2);}),_fH));});return B(_3M(new T1(0,function(_fW){return (E(_fW)==39)?E(new T1(0,_fA)):new T0(2);}),_fF));});return new F(function(){return _3M(new T1(1,function(_fX){return (E(_fX)._==0)?E(_ft):new T0(2);}),_fu);});},_fY=0,_fZ=function(_g0,_g1){var _g2=new T(function(){var _g3=new T(function(){var _g4=function(_g5){var _g6=new T(function(){var _g7=new T(function(){return B(A1(_g1,_g5));});return B(_fr(function(_g8){var _g9=E(_g8);return (_g9._==2)?(!B(_4r(_g9.a,_4q)))?new T0(2):E(_g7):new T0(2);}));}),_ga=function(_gb){return E(_g6);};return new T1(1,function(_gc){return new F(function(){return A2(_e8,_gc,_ga);});});};return B(A2(_g0,_fY,_g4));});return B(_fr(function(_gd){var _ge=E(_gd);return (_ge._==2)?(!B(_4r(_ge.a,_4p)))?new T0(2):E(_g3):new T0(2);}));}),_gf=function(_gg){return E(_g2);};return function(_gh){return new F(function(){return A2(_e8,_gh,_gf);});};},_gi=function(_gj,_gk){var _gl=function(_gm){var _gn=new T(function(){return B(A1(_gj,_gm));}),_go=function(_gp){return new F(function(){return _3M(B(A1(_gn,_gp)),new T(function(){return new T1(1,B(_fZ(_gl,_gp)));}));});};return E(_go);},_gq=new T(function(){return B(A1(_gj,_gk));}),_gr=function(_gs){return new F(function(){return _3M(B(A1(_gq,_gs)),new T(function(){return new T1(1,B(_fZ(_gl,_gs)));}));});};return E(_gr);},_gt=function(_gu,_gv){var _gw=function(_gx,_gy){var _gz=function(_gA){return new F(function(){return A1(_gy,new T(function(){return  -E(_gA);}));});},_gB=new T(function(){return B(_fr(function(_gC){return new F(function(){return A3(_gu,_gC,_gx,_gz);});}));}),_gD=function(_gE){return E(_gB);},_gF=function(_gG){return new F(function(){return A2(_e8,_gG,_gD);});},_gH=new T(function(){return B(_fr(function(_gI){var _gJ=E(_gI);if(_gJ._==4){var _gK=E(_gJ.a);if(!_gK._){return new F(function(){return A3(_gu,_gJ,_gx,_gy);});}else{if(E(_gK.a)==45){if(!E(_gK.b)._){return E(new T1(1,_gF));}else{return new F(function(){return A3(_gu,_gJ,_gx,_gy);});}}else{return new F(function(){return A3(_gu,_gJ,_gx,_gy);});}}}else{return new F(function(){return A3(_gu,_gJ,_gx,_gy);});}}));}),_gL=function(_gM){return E(_gH);};return new T1(1,function(_gN){return new F(function(){return A2(_e8,_gN,_gL);});});};return new F(function(){return _gi(_gw,_gv);});},_gO=function(_gP){var _gQ=E(_gP);if(!_gQ._){var _gR=_gQ.b,_gS=new T(function(){return B(_7C(new T(function(){return B(_7i(E(_gQ.a)));}),new T(function(){return B(_79(_gR,0));},1),B(_7e(_7k,_gR))));});return new T1(1,_gS);}else{return (E(_gQ.b)._==0)?(E(_gQ.c)._==0)?new T1(1,new T(function(){return B(_7T(_78,_gQ.a));})):__Z:__Z;}},_gT=function(_gU,_gV){return new T0(2);},_gW=function(_gX){var _gY=E(_gX);if(_gY._==5){var _gZ=B(_gO(_gY.a));if(!_gZ._){return E(_gT);}else{var _h0=new T(function(){return B(_8P(_gZ.a));});return function(_h1,_h2){return new F(function(){return A1(_h2,_h0);});};}}else{return E(_gT);}},_h3=function(_h4,_h5){if(_h4>10){return new T0(2);}else{var _h6=new T(function(){var _h7=new T(function(){return B(A3(_gt,_gW,_1,function(_h8){return new F(function(){return A1(_h5,_h8);});}));});return B(_fr(function(_h9){var _ha=E(_h9);return (_ha._==3)?(!B(_4r(_ha.a,_4o)))?new T0(2):E(_h7):new T0(2);}));}),_hb=function(_hc){return E(_h6);};return new T1(1,function(_hd){return new F(function(){return A2(_e8,_hd,_hb);});});}},_he=function(_hf,_hg){return new F(function(){return _h3(E(_hf),_hg);});},_hh=new T(function(){return B(unCStr("IdentPay"));}),_hi=function(_hj,_hk){if(_hj>10){return new T0(2);}else{var _hl=new T(function(){var _hm=new T(function(){return B(A3(_gt,_gW,_1,function(_hn){return new F(function(){return A1(_hk,_hn);});}));});return B(_fr(function(_ho){var _hp=E(_ho);return (_hp._==3)?(!B(_4r(_hp.a,_hh)))?new T0(2):E(_hm):new T0(2);}));}),_hq=function(_hr){return E(_hl);};return new T1(1,function(_hs){return new F(function(){return A2(_e8,_hs,_hq);});});}},_ht=function(_hu,_hv){return new F(function(){return _hi(E(_hu),_hv);});},_hw=new T(function(){return B(unCStr("IdentChoice"));}),_hx=function(_hy,_hz){if(_hy>10){return new T0(2);}else{var _hA=new T(function(){var _hB=new T(function(){return B(A3(_gt,_gW,_1,function(_hC){return new F(function(){return A1(_hz,_hC);});}));});return B(_fr(function(_hD){var _hE=E(_hD);return (_hE._==3)?(!B(_4r(_hE.a,_hw)))?new T0(2):E(_hB):new T0(2);}));}),_hF=function(_hG){return E(_hA);};return new T1(1,function(_hH){return new F(function(){return A2(_e8,_hH,_hF);});});}},_hI=function(_hJ,_hK){return new F(function(){return _hx(E(_hJ),_hK);});},_hL=new T(function(){return B(unCStr("ConstMoney"));}),_hM=new T(function(){return B(unCStr("AvailableMoney"));}),_hN=new T(function(){return B(unCStr("AddMoney"));}),_hO=function(_hP,_hQ){var _hR=new T(function(){var _hS=new T(function(){if(_hP>10){return new T0(2);}else{var _hT=new T(function(){var _hU=new T(function(){return B(A3(_gt,_gW,_1,function(_hV){return new F(function(){return A1(_hQ,new T1(2,_hV));});}));});return B(_fr(function(_hW){var _hX=E(_hW);return (_hX._==3)?(!B(_4r(_hX.a,_hL)))?new T0(2):E(_hU):new T0(2);}));}),_hY=function(_hZ){return E(_hT);};return new T1(1,function(_i0){return new F(function(){return A2(_e8,_i0,_hY);});});}});if(_hP>10){return B(_3M(_4X,_hS));}else{var _i1=new T(function(){var _i2=new T(function(){var _i3=function(_i4){return new F(function(){return A3(_gi,_i5,_1,function(_i6){return new F(function(){return A1(_hQ,new T2(1,_i4,_i6));});});});};return B(A3(_gi,_i5,_1,_i3));});return B(_fr(function(_i7){var _i8=E(_i7);return (_i8._==3)?(!B(_4r(_i8.a,_hN)))?new T0(2):E(_i2):new T0(2);}));}),_i9=function(_ia){return E(_i1);};return B(_3M(new T1(1,function(_ib){return new F(function(){return A2(_e8,_ib,_i9);});}),_hS));}});if(_hP>10){return new F(function(){return _3M(_4X,_hR);});}else{var _ic=new T(function(){var _id=new T(function(){return B(A3(_gi,_he,_1,function(_ie){return new F(function(){return A1(_hQ,new T1(0,_ie));});}));});return B(_fr(function(_if){var _ig=E(_if);return (_ig._==3)?(!B(_4r(_ig.a,_hM)))?new T0(2):E(_id):new T0(2);}));}),_ih=function(_ii){return E(_ic);};return new F(function(){return _3M(new T1(1,function(_ij){return new F(function(){return A2(_e8,_ij,_ih);});}),_hR);});}},_i5=function(_ik,_il){return new F(function(){return _hO(E(_ik),_il);});},_im=new T0(7),_in=function(_io,_ip){return new F(function(){return A1(_ip,_im);});},_iq=new T2(0,_K,_in),_ir=new T0(8),_is=function(_it,_iu){return new F(function(){return A1(_iu,_ir);});},_iv=new T2(0,_J,_is),_iw=new T2(1,_iv,_23),_ix=new T2(1,_iq,_iw),_iy=function(_iz,_iA,_iB){var _iC=E(_iz);if(!_iC._){return new T0(2);}else{var _iD=E(_iC.a),_iE=_iD.a,_iF=new T(function(){return B(A2(_iD.b,_iA,_iB));}),_iG=new T(function(){return B(_fr(function(_iH){var _iI=E(_iH);switch(_iI._){case 3:return (!B(_4r(_iE,_iI.a)))?new T0(2):E(_iF);case 4:return (!B(_4r(_iE,_iI.a)))?new T0(2):E(_iF);default:return new T0(2);}}));}),_iJ=function(_iK){return E(_iG);};return new F(function(){return _3M(new T1(1,function(_iL){return new F(function(){return A2(_e8,_iL,_iJ);});}),new T(function(){return B(_iy(_iC.b,_iA,_iB));}));});}},_iM=new T(function(){return B(unCStr("ValueGE"));}),_iN=new T(function(){return B(unCStr("PersonChoseSomething"));}),_iO=new T(function(){return B(unCStr("PersonChoseThis"));}),_iP=new T(function(){return B(unCStr("BelowTimeout"));}),_iQ=new T(function(){return B(unCStr("AndObs"));}),_iR=new T(function(){return B(unCStr("OrObs"));}),_iS=new T(function(){return B(unCStr("NotObs"));}),_iT=function(_iU,_iV){var _iW=new T(function(){var _iX=E(_iU),_iY=new T(function(){var _iZ=new T(function(){var _j0=new T(function(){var _j1=new T(function(){var _j2=new T(function(){var _j3=new T(function(){if(_iX>10){return new T0(2);}else{var _j4=new T(function(){var _j5=new T(function(){var _j6=function(_j7){return new F(function(){return A3(_gi,_i5,_1,function(_j8){return new F(function(){return A1(_iV,new T2(6,_j7,_j8));});});});};return B(A3(_gi,_i5,_1,_j6));});return B(_fr(function(_j9){var _ja=E(_j9);return (_ja._==3)?(!B(_4r(_ja.a,_iM)))?new T0(2):E(_j5):new T0(2);}));}),_jb=function(_jc){return E(_j4);};return new T1(1,function(_jd){return new F(function(){return A2(_e8,_jd,_jb);});});}});if(_iX>10){return B(_3M(_4X,_j3));}else{var _je=new T(function(){var _jf=new T(function(){var _jg=function(_jh){return new F(function(){return A3(_gt,_gW,_1,function(_ji){return new F(function(){return A1(_iV,new T2(5,_jh,_ji));});});});};return B(A3(_gi,_hI,_1,_jg));});return B(_fr(function(_jj){var _jk=E(_jj);return (_jk._==3)?(!B(_4r(_jk.a,_iN)))?new T0(2):E(_jf):new T0(2);}));}),_jl=function(_jm){return E(_je);};return B(_3M(new T1(1,function(_jn){return new F(function(){return A2(_e8,_jn,_jl);});}),_j3));}});if(_iX>10){return B(_3M(_4X,_j2));}else{var _jo=new T(function(){var _jp=new T(function(){var _jq=function(_jr){var _js=function(_jt){return new F(function(){return A3(_gt,_gW,_1,function(_ju){return new F(function(){return A1(_iV,new T3(4,_jr,_jt,_ju));});});});};return new F(function(){return A3(_gt,_gW,_1,_js);});};return B(A3(_gi,_hI,_1,_jq));});return B(_fr(function(_jv){var _jw=E(_jv);return (_jw._==3)?(!B(_4r(_jw.a,_iO)))?new T0(2):E(_jp):new T0(2);}));}),_jx=function(_jy){return E(_jo);};return B(_3M(new T1(1,function(_jz){return new F(function(){return A2(_e8,_jz,_jx);});}),_j2));}});if(_iX>10){return B(_3M(_4X,_j1));}else{var _jA=new T(function(){var _jB=new T(function(){return B(A3(_gi,_iT,_1,function(_jC){return new F(function(){return A1(_iV,new T1(3,_jC));});}));});return B(_fr(function(_jD){var _jE=E(_jD);return (_jE._==3)?(!B(_4r(_jE.a,_iS)))?new T0(2):E(_jB):new T0(2);}));}),_jF=function(_jG){return E(_jA);};return B(_3M(new T1(1,function(_jH){return new F(function(){return A2(_e8,_jH,_jF);});}),_j1));}});if(_iX>10){return B(_3M(_4X,_j0));}else{var _jI=new T(function(){var _jJ=new T(function(){var _jK=function(_jL){return new F(function(){return A3(_gi,_iT,_1,function(_jM){return new F(function(){return A1(_iV,new T2(2,_jL,_jM));});});});};return B(A3(_gi,_iT,_1,_jK));});return B(_fr(function(_jN){var _jO=E(_jN);return (_jO._==3)?(!B(_4r(_jO.a,_iR)))?new T0(2):E(_jJ):new T0(2);}));}),_jP=function(_jQ){return E(_jI);};return B(_3M(new T1(1,function(_jR){return new F(function(){return A2(_e8,_jR,_jP);});}),_j0));}});if(_iX>10){return B(_3M(_4X,_iZ));}else{var _jS=new T(function(){var _jT=new T(function(){var _jU=function(_jV){return new F(function(){return A3(_gi,_iT,_1,function(_jW){return new F(function(){return A1(_iV,new T2(1,_jV,_jW));});});});};return B(A3(_gi,_iT,_1,_jU));});return B(_fr(function(_jX){var _jY=E(_jX);return (_jY._==3)?(!B(_4r(_jY.a,_iQ)))?new T0(2):E(_jT):new T0(2);}));}),_jZ=function(_k0){return E(_jS);};return B(_3M(new T1(1,function(_k1){return new F(function(){return A2(_e8,_k1,_jZ);});}),_iZ));}});if(_iX>10){return B(_3M(_4X,_iY));}else{var _k2=new T(function(){var _k3=new T(function(){return B(A3(_gt,_gW,_1,function(_k4){return new F(function(){return A1(_iV,new T1(0,_k4));});}));});return B(_fr(function(_k5){var _k6=E(_k5);return (_k6._==3)?(!B(_4r(_k6.a,_iP)))?new T0(2):E(_k3):new T0(2);}));}),_k7=function(_k8){return E(_k2);};return B(_3M(new T1(1,function(_k9){return new F(function(){return A2(_e8,_k9,_k7);});}),_iY));}});return new F(function(){return _3M(B(_iy(_ix,_iU,_iV)),_iW);});},_ka=__Z,_kb=new T(function(){return B(unCStr("CommitCash"));}),_kc=new T(function(){return B(unCStr("RedeemCC"));}),_kd=new T(function(){return B(unCStr("Pay"));}),_ke=new T(function(){return B(unCStr("Both"));}),_kf=new T(function(){return B(unCStr("Choice"));}),_kg=new T(function(){return B(unCStr("When"));}),_kh=function(_ki,_kj){var _kk=new T(function(){var _kl=new T(function(){return B(A1(_kj,_ka));});return B(_fr(function(_km){var _kn=E(_km);return (_kn._==3)?(!B(_4r(_kn.a,_1n)))?new T0(2):E(_kl):new T0(2);}));}),_ko=function(_kp){return E(_kk);},_kq=new T(function(){var _kr=E(_ki),_ks=new T(function(){var _kt=new T(function(){var _ku=new T(function(){var _kv=new T(function(){var _kw=new T(function(){if(_kr>10){return new T0(2);}else{var _kx=new T(function(){var _ky=new T(function(){var _kz=function(_kA){var _kB=function(_kC){var _kD=function(_kE){return new F(function(){return A3(_gi,_kh,_1,function(_kF){return new F(function(){return A1(_kj,new T4(6,_kA,_kC,_kE,_kF));});});});};return new F(function(){return A3(_gi,_kh,_1,_kD);});};return new F(function(){return A3(_gt,_gW,_1,_kB);});};return B(A3(_gi,_iT,_1,_kz));});return B(_fr(function(_kG){var _kH=E(_kG);return (_kH._==3)?(!B(_4r(_kH.a,_kg)))?new T0(2):E(_ky):new T0(2);}));}),_kI=function(_kJ){return E(_kx);};return new T1(1,function(_kK){return new F(function(){return A2(_e8,_kK,_kI);});});}});if(_kr>10){return B(_3M(_4X,_kw));}else{var _kL=new T(function(){var _kM=new T(function(){var _kN=function(_kO){var _kP=function(_kQ){return new F(function(){return A3(_gi,_kh,_1,function(_kR){return new F(function(){return A1(_kj,new T3(5,_kO,_kQ,_kR));});});});};return new F(function(){return A3(_gi,_kh,_1,_kP);});};return B(A3(_gi,_iT,_1,_kN));});return B(_fr(function(_kS){var _kT=E(_kS);return (_kT._==3)?(!B(_4r(_kT.a,_kf)))?new T0(2):E(_kM):new T0(2);}));}),_kU=function(_kV){return E(_kL);};return B(_3M(new T1(1,function(_kW){return new F(function(){return A2(_e8,_kW,_kU);});}),_kw));}});if(_kr>10){return B(_3M(_4X,_kv));}else{var _kX=new T(function(){var _kY=new T(function(){var _kZ=function(_l0){return new F(function(){return A3(_gi,_kh,_1,function(_l1){return new F(function(){return A1(_kj,new T2(4,_l0,_l1));});});});};return B(A3(_gi,_kh,_1,_kZ));});return B(_fr(function(_l2){var _l3=E(_l2);return (_l3._==3)?(!B(_4r(_l3.a,_ke)))?new T0(2):E(_kY):new T0(2);}));}),_l4=function(_l5){return E(_kX);};return B(_3M(new T1(1,function(_l6){return new F(function(){return A2(_e8,_l6,_l4);});}),_kv));}});if(_kr>10){return B(_3M(_4X,_ku));}else{var _l7=new T(function(){var _l8=new T(function(){var _l9=function(_la){var _lb=function(_lc){var _ld=function(_le){var _lf=function(_lg){var _lh=function(_li){return new F(function(){return A3(_gi,_kh,_1,function(_lj){return new F(function(){return A1(_kj,new T6(3,_la,_lc,_le,_lg,_li,_lj));});});});};return new F(function(){return A3(_gt,_gW,_1,_lh);});};return new F(function(){return A3(_gt,_gW,_1,_lf);});};return new F(function(){return A3(_gt,_gW,_1,_ld);});};return new F(function(){return A3(_gt,_gW,_1,_lb);});};return B(A3(_gi,_ht,_1,_l9));});return B(_fr(function(_lk){var _ll=E(_lk);return (_ll._==3)?(!B(_4r(_ll.a,_kd)))?new T0(2):E(_l8):new T0(2);}));}),_lm=function(_ln){return E(_l7);};return B(_3M(new T1(1,function(_lo){return new F(function(){return A2(_e8,_lo,_lm);});}),_ku));}});if(_kr>10){return B(_3M(_4X,_kt));}else{var _lp=new T(function(){var _lq=new T(function(){var _lr=function(_ls){return new F(function(){return A3(_gi,_kh,_1,function(_lt){return new F(function(){return A1(_kj,new T2(2,_ls,_lt));});});});};return B(A3(_gi,_he,_1,_lr));});return B(_fr(function(_lu){var _lv=E(_lu);return (_lv._==3)?(!B(_4r(_lv.a,_kc)))?new T0(2):E(_lq):new T0(2);}));}),_lw=function(_lx){return E(_lp);};return B(_3M(new T1(1,function(_ly){return new F(function(){return A2(_e8,_ly,_lw);});}),_kt));}});if(_kr>10){return B(_3M(_4X,_ks));}else{var _lz=new T(function(){var _lA=new T(function(){var _lB=function(_lC){var _lD=function(_lE){var _lF=function(_lG){var _lH=function(_lI){var _lJ=function(_lK){var _lL=function(_lM){return new F(function(){return A3(_gi,_kh,_1,function(_lN){return new F(function(){return A1(_kj,{_:1,a:_lC,b:_lE,c:_lG,d:_lI,e:_lK,f:_lM,g:_lN});});});});};return new F(function(){return A3(_gi,_kh,_1,_lL);});};return new F(function(){return A3(_gt,_gW,_1,_lJ);});};return new F(function(){return A3(_gt,_gW,_1,_lH);});};return new F(function(){return A3(_gt,_gW,_1,_lF);});};return new F(function(){return A3(_gt,_gW,_1,_lD);});};return B(A3(_gi,_he,_1,_lB));});return B(_fr(function(_lO){var _lP=E(_lO);return (_lP._==3)?(!B(_4r(_lP.a,_kb)))?new T0(2):E(_lA):new T0(2);}));}),_lQ=function(_lR){return E(_lz);};return B(_3M(new T1(1,function(_lS){return new F(function(){return A2(_e8,_lS,_lQ);});}),_ks));}});return new F(function(){return _3M(new T1(1,function(_lT){return new F(function(){return A2(_e8,_lT,_ko);});}),_kq);});},_lU=function(_lV){var _lW=function(_lX){return E(new T2(3,_lV,_4X));};return new T1(1,function(_lY){return new F(function(){return A2(_e8,_lY,_lW);});});},_lZ=new T(function(){return B(A3(_gi,_kh,_fY,_lU));}),_m0=new T(function(){return eval("(function () {return Blockly.Marlowe.workspaceToCode(demoWorkspace);})");}),_m1=function(_m2){while(1){var _m3=B((function(_m4){var _m5=E(_m4);if(!_m5._){return __Z;}else{var _m6=_m5.b,_m7=E(_m5.a);if(!E(_m7.b)._){return new T2(1,_m7.a,new T(function(){return B(_m1(_m6));}));}else{_m2=_m6;return __continue;}}})(_m2));if(_m3!=__continue){return _m3;}}},_m8=0,_m9=function(_){var _ma=__app0(E(_m0)),_mb=B(_m1(B(_3C(_lZ,new T(function(){var _mc=String(_ma);return fromJSStr(_mc);})))));if(!_mb._){return E(_2f);}else{if(!E(_mb.b)._){return new F(function(){return _29(_26,B(_1u(_m8,_mb.a,_23)),_);});}else{return E(_25);}}},_md="(function (b) { return (b.inputList.length); })",_me="(function (b, x) { return (b.inputList[x]); })",_mf=function(_mg,_mh,_){var _mi=eval(E(_me)),_mj=__app2(E(_mi),_mg,_mh);return new T1(0,_mj);},_mk=function(_ml,_mm,_mn,_){var _mo=E(_mn);if(!_mo._){return _23;}else{var _mp=B(_mf(_ml,E(_mo.a),_)),_mq=B(_mk(_ml,_,_mo.b,_));return new T2(1,_mp,_mq);}},_mr=function(_ms,_mt){if(_ms<=_mt){var _mu=function(_mv){return new T2(1,_mv,new T(function(){if(_mv!=_mt){return B(_mu(_mv+1|0));}else{return __Z;}}));};return new F(function(){return _mu(_ms);});}else{return __Z;}},_mw=function(_mx,_){var _my=eval(E(_md)),_mz=__app1(E(_my),_mx),_mA=Number(_mz),_mB=jsTrunc(_mA);return new F(function(){return _mk(_mx,_,new T(function(){return B(_mr(0,_mB-1|0));}),_);});},_mC="(function (y, ip) {y.previousConnection.connect(ip.connection);})",_mD="(function (x) { return x.name; })",_mE=new T(function(){return B(unCStr("\""));}),_mF=function(_mG){return new F(function(){return err(B(unAppCStr("No input matches \"",new T(function(){return B(_3(_mG,_mE));}))));});},_mH=function(_mI,_mJ,_){var _mK=E(_mJ);if(!_mK._){return new F(function(){return _mF(_mI);});}else{var _mL=E(_mK.a),_mM=E(_mD),_mN=eval(_mM),_mO=__app1(E(_mN),E(_mL.a)),_mP=String(_mO);if(!B(_4r(fromJSStr(_mP),_mI))){var _mQ=function(_mR,_mS,_){while(1){var _mT=E(_mS);if(!_mT._){return new F(function(){return _mF(_mR);});}else{var _mU=E(_mT.a),_mV=eval(_mM),_mW=__app1(E(_mV),E(_mU.a)),_mX=String(_mW);if(!B(_4r(fromJSStr(_mX),_mR))){_mS=_mT.b;continue;}else{return _mU;}}}};return new F(function(){return _mQ(_mI,_mK.b,_);});}else{return _mL;}}},_mY=function(_mZ,_n0,_n1,_){var _n2=B(_mw(_n0,_)),_n3=B(_mH(_mZ,_n2,_)),_n4=eval(E(_mC)),_n5=__app2(E(_n4),E(E(_n1).a),E(E(_n3).a));return new F(function(){return _27(_);});},_n6=function(_n7){return new F(function(){return err(B(unAppCStr("No fieldrow matches \"",new T(function(){return B(_3(_n7,_mE));}))));});},_n8=function(_n9,_na,_){var _nb=E(_na);if(!_nb._){return new F(function(){return _n6(_n9);});}else{var _nc=E(_nb.a),_nd=E(_mD),_ne=eval(_nd),_nf=__app1(E(_ne),E(_nc.a)),_ng=String(_nf);if(!B(_4r(fromJSStr(_ng),_n9))){var _nh=function(_ni,_nj,_){while(1){var _nk=E(_nj);if(!_nk._){return new F(function(){return _n6(_ni);});}else{var _nl=E(_nk.a),_nm=eval(_nd),_nn=__app1(E(_nm),E(_nl.a)),_no=String(_nn);if(!B(_4r(fromJSStr(_no),_ni))){_nj=_nk.b;continue;}else{return _nl;}}}};return new F(function(){return _nh(_n9,_nb.b,_);});}else{return _nc;}}},_np="(function (b) { return (b.fieldRow.length); })",_nq="(function (b, x) { return (b.fieldRow[x]); })",_nr=function(_ns,_nt,_){var _nu=eval(E(_nq)),_nv=__app2(E(_nu),_ns,_nt);return new T1(0,_nv);},_nw=function(_nx,_ny,_nz,_){var _nA=E(_nz);if(!_nA._){return _23;}else{var _nB=B(_nr(_nx,E(_nA.a),_)),_nC=B(_nw(_nx,_,_nA.b,_));return new T2(1,_nB,_nC);}},_nD=function(_nE,_){var _nF=eval(E(_np)),_nG=__app1(E(_nF),_nE),_nH=Number(_nG),_nI=jsTrunc(_nH);return new F(function(){return _nw(_nE,_,new T(function(){return B(_mr(0,_nI-1|0));}),_);});},_nJ=function(_nK,_){var _nL=E(_nK);if(!_nL._){return _23;}else{var _nM=B(_nD(E(E(_nL.a).a),_)),_nN=B(_nJ(_nL.b,_));return new T2(1,_nM,_nN);}},_nO=function(_nP){var _nQ=E(_nP);if(!_nQ._){return __Z;}else{return new F(function(){return _3(_nQ.a,new T(function(){return B(_nO(_nQ.b));},1));});}},_nR=function(_nS,_nT,_){var _nU=B(_mw(_nT,_)),_nV=B(_nJ(_nU,_));return new F(function(){return _n8(_nS,B(_nO(_nV)),_);});},_nW="(function (y, ip) {y.outputConnection.connect(ip.connection);})",_nX=function(_nY,_nZ,_o0,_){var _o1=B(_mw(_nZ,_)),_o2=B(_mH(_nY,_o1,_)),_o3=eval(E(_nW)),_o4=__app2(E(_o3),E(E(_o0).a),E(E(_o2).a));return new F(function(){return _27(_);});},_o5=new T(function(){return B(unCStr("contract_commitcash"));}),_o6=new T(function(){return B(unCStr("contract_redeemcc"));}),_o7=new T(function(){return B(unCStr("contract_pay"));}),_o8=new T(function(){return B(unCStr("contract_both"));}),_o9=new T(function(){return B(unCStr("contract_choice"));}),_oa=new T(function(){return B(unCStr("contract_when"));}),_ob="(function (x) {var c = demoWorkspace.newBlock(x); c.initSvg(); return c;})",_oc=function(_od,_){var _oe=eval(E(_ob)),_of=__app1(E(_oe),toJSStr(E(_od)));return new T1(0,_of);},_og=new T(function(){return B(unCStr("contract2"));}),_oh=new T(function(){return B(unCStr("contract1"));}),_oi=new T(function(){return B(unCStr("ccommit_id"));}),_oj=new T(function(){return B(unCStr("end_expiration"));}),_ok=new T(function(){return B(unCStr("start_expiration"));}),_ol=new T(function(){return B(unCStr("person_id"));}),_om=new T(function(){return B(unCStr("contract_null"));}),_on=new T(function(){return B(unCStr("observation"));}),_oo=new T(function(){return B(unCStr("timeout"));}),_op=new T(function(){return B(unCStr("contract"));}),_oq=new T(function(){return B(unCStr("expiration"));}),_or=new T(function(){return B(unCStr("ammount"));}),_os=new T(function(){return B(unCStr("payee_id"));}),_ot=new T(function(){return B(unCStr("payer_id"));}),_ou=new T(function(){return B(unCStr("pay_id"));}),_ov=function(_ow,_ox,_oy,_){var _oz=B(_mw(_ox,_)),_oA=B(_mH(_ow,_oz,_)),_oB=eval(E(_nW)),_oC=__app2(E(_oB),E(E(_oy).a),E(E(_oA).a));return new F(function(){return _27(_);});},_oD=new T(function(){return B(unCStr("observation_personchosethis"));}),_oE=new T(function(){return B(unCStr("observation_personchosesomething"));}),_oF=new T(function(){return B(unCStr("observation_value_ge"));}),_oG=new T(function(){return B(unCStr("observation_trueobs"));}),_oH=new T(function(){return B(unCStr("observation_falseobs"));}),_oI=new T(function(){return B(unCStr("observation_belowtimeout"));}),_oJ=new T(function(){return B(unCStr("observation_andobs"));}),_oK=new T(function(){return B(unCStr("observation_orobs"));}),_oL=new T(function(){return B(unCStr("observation_notobs"));}),_oM=new T(function(){return B(unCStr("value2"));}),_oN=new T(function(){return B(unCStr("value1"));}),_oO=new T(function(){return B(unCStr("person"));}),_oP=new T(function(){return B(unCStr("choice_id"));}),_oQ=new T(function(){return B(unCStr("choice_value"));}),_oR=new T(function(){return B(unCStr("observation2"));}),_oS=new T(function(){return B(unCStr("observation1"));}),_oT=new T(function(){return B(unCStr("block_number"));}),_oU=new T(function(){return B(unCStr("value_available_money"));}),_oV=new T(function(){return B(unCStr("value_add_money"));}),_oW=new T(function(){return B(unCStr("value_const_money"));}),_oX=new T(function(){return B(unCStr("money"));}),_oY=new T(function(){return B(unCStr("commit_id"));}),_oZ="(function (b, s) { return (b.setText(s)); })",_p0=function(_p1,_){var _p2=E(_p1);switch(_p2._){case 0:var _p3=B(_oc(_oU,_)),_p4=E(_p3),_p5=B(_nR(_oY,E(_p4.a),_)),_p6=eval(E(_oZ)),_p7=__app2(E(_p6),E(E(_p5).a),toJSStr(B(_d(0,E(_p2.a),_23))));return _p4;case 1:var _p8=B(_p0(_p2.a,_)),_p9=B(_p0(_p2.b,_)),_pa=B(_oc(_oV,_)),_pb=E(_pa),_pc=E(_pb.a),_pd=B(_ov(_oN,_pc,_p8,_)),_pe=B(_ov(_oM,_pc,_p9,_));return _pb;default:var _pf=B(_oc(_oW,_)),_pg=E(_pf),_ph=B(_nR(_oX,E(_pg.a),_)),_pi=eval(E(_oZ)),_pj=__app2(E(_pi),E(E(_ph).a),toJSStr(B(_d(0,E(_p2.a),_23))));return _pg;}},_pk=function(_pl,_){var _pm=E(_pl);switch(_pm._){case 0:var _pn=B(_oc(_oI,_)),_po=E(_pn),_pp=B(_nR(_oT,E(_po.a),_)),_pq=eval(E(_oZ)),_pr=__app2(E(_pq),E(E(_pp).a),toJSStr(B(_d(0,E(_pm.a),_23))));return _po;case 1:var _ps=B(_pk(_pm.a,_)),_pt=B(_pk(_pm.b,_)),_pu=B(_oc(_oJ,_)),_pv=E(_pu),_pw=E(_pv.a),_px=B(_nX(_oS,_pw,_ps,_)),_py=B(_nX(_oR,_pw,_pt,_));return _pv;case 2:var _pz=B(_pk(_pm.a,_)),_pA=B(_pk(_pm.b,_)),_pB=B(_oc(_oK,_)),_pC=E(_pB),_pD=E(_pC.a),_pE=B(_nX(_oS,_pD,_pz,_)),_pF=B(_nX(_oR,_pD,_pA,_));return _pC;case 3:var _pG=B(_pk(_pm.a,_)),_pH=B(_oc(_oL,_)),_pI=E(_pH),_pJ=B(_nX(_on,E(_pI.a),_pG,_));return _pI;case 4:var _pK=B(_oc(_oD,_)),_pL=E(_pK),_pM=E(_pL.a),_pN=B(_nR(_oP,_pM,_)),_pO=eval(E(_oZ)),_pP=__app2(E(_pO),E(E(_pN).a),toJSStr(B(_d(0,E(_pm.a),_23)))),_pQ=B(_nR(_oO,_pM,_)),_pR=__app2(E(_pO),E(E(_pQ).a),toJSStr(B(_d(0,E(_pm.b),_23)))),_pS=B(_nR(_oQ,_pM,_)),_pT=__app2(E(_pO),E(E(_pS).a),toJSStr(B(_d(0,E(_pm.c),_23))));return _pL;case 5:var _pU=B(_oc(_oE,_)),_pV=E(_pU),_pW=E(_pV.a),_pX=B(_nR(_oP,_pW,_)),_pY=eval(E(_oZ)),_pZ=__app2(E(_pY),E(E(_pX).a),toJSStr(B(_d(0,E(_pm.a),_23)))),_q0=B(_nR(_oO,_pW,_)),_q1=__app2(E(_pY),E(E(_q0).a),toJSStr(B(_d(0,E(_pm.b),_23))));return _pV;case 6:var _q2=B(_p0(_pm.a,_)),_q3=B(_p0(_pm.b,_)),_q4=B(_oc(_oF,_)),_q5=E(_q4),_q6=E(_q5.a),_q7=B(_ov(_oN,_q6,_q2,_)),_q8=B(_ov(_oM,_q6,_q3,_));return _q5;case 7:return new F(function(){return _oc(_oG,_);});break;default:return new F(function(){return _oc(_oH,_);});}},_q9=function(_qa,_){var _qb=E(_qa);switch(_qb._){case 0:return new F(function(){return _oc(_om,_);});break;case 1:var _qc=B(_q9(_qb.f,_)),_qd=B(_q9(_qb.g,_)),_qe=B(_oc(_o5,_)),_qf=E(_qe),_qg=E(_qf.a),_qh=B(_nR(_oi,_qg,_)),_qi=eval(E(_oZ)),_qj=__app2(E(_qi),E(E(_qh).a),toJSStr(B(_d(0,E(_qb.a),_23)))),_qk=B(_nR(_ol,_qg,_)),_ql=__app2(E(_qi),E(E(_qk).a),toJSStr(B(_d(0,E(_qb.b),_23)))),_qm=B(_nR(_or,_qg,_)),_qn=__app2(E(_qi),E(E(_qm).a),toJSStr(B(_d(0,E(_qb.c),_23)))),_qo=B(_nR(_ok,_qg,_)),_qp=__app2(E(_qi),E(E(_qo).a),toJSStr(B(_d(0,E(_qb.d),_23)))),_qq=B(_nR(_oj,_qg,_)),_qr=__app2(E(_qi),E(E(_qq).a),toJSStr(B(_d(0,E(_qb.e),_23)))),_qs=B(_mY(_oh,_qg,_qc,_)),_qt=B(_mY(_og,_qg,_qd,_));return _qf;case 2:var _qu=B(_q9(_qb.b,_)),_qv=B(_oc(_o6,_)),_qw=E(_qv),_qx=E(_qw.a),_qy=B(_nR(_oi,_qx,_)),_qz=eval(E(_oZ)),_qA=__app2(E(_qz),E(E(_qy).a),toJSStr(B(_d(0,E(_qb.a),_23)))),_qB=B(_mY(_op,_qx,_qu,_));return _qw;case 3:var _qC=B(_q9(_qb.f,_)),_qD=B(_oc(_o7,_)),_qE=E(_qD),_qF=E(_qE.a),_qG=B(_nR(_ou,_qF,_)),_qH=eval(E(_oZ)),_qI=__app2(E(_qH),E(E(_qG).a),toJSStr(B(_d(0,E(_qb.a),_23)))),_qJ=B(_nR(_ot,_qF,_)),_qK=__app2(E(_qH),E(E(_qJ).a),toJSStr(B(_d(0,E(_qb.b),_23)))),_qL=B(_nR(_os,_qF,_)),_qM=__app2(E(_qH),E(E(_qL).a),toJSStr(B(_d(0,E(_qb.c),_23)))),_qN=B(_nR(_or,_qF,_)),_qO=__app2(E(_qH),E(E(_qN).a),toJSStr(B(_d(0,E(_qb.d),_23)))),_qP=B(_nR(_oq,_qF,_)),_qQ=__app2(E(_qH),E(E(_qP).a),toJSStr(B(_d(0,E(_qb.e),_23)))),_qR=B(_mY(_op,_qF,_qC,_));return _qE;case 4:var _qS=B(_q9(_qb.a,_)),_qT=B(_q9(_qb.b,_)),_qU=B(_oc(_o8,_)),_qV=E(_qU),_qW=E(_qV.a),_qX=B(_mY(_oh,_qW,_qS,_)),_qY=B(_mY(_og,_qW,_qT,_));return _qV;case 5:var _qZ=B(_pk(_qb.a,_)),_r0=B(_q9(_qb.b,_)),_r1=B(_q9(_qb.c,_)),_r2=B(_oc(_o9,_)),_r3=E(_r2),_r4=E(_r3.a),_r5=B(_nX(_on,_r4,_qZ,_)),_r6=B(_mY(_oh,_r4,_r0,_)),_r7=B(_mY(_og,_r4,_r1,_));return _r3;default:var _r8=B(_pk(_qb.a,_)),_r9=B(_q9(_qb.c,_)),_ra=B(_q9(_qb.d,_)),_rb=B(_oc(_oa,_)),_rc=E(_rb),_rd=E(_rc.a),_re=B(_nR(_oo,_rd,_)),_rf=eval(E(_oZ)),_rg=__app2(E(_rf),E(E(_re).a),toJSStr(B(_d(0,E(_qb.b),_23)))),_rh=B(_nX(_on,_rd,_r8,_)),_ri=B(_mY(_oh,_rd,_r9,_)),_rj=B(_mY(_og,_rd,_ra,_));return _rc;}},_rk=new T(function(){return B(unCStr("base_contract"));}),_rl=new T(function(){return eval("(function() { demoWorkspace.render(); onresize(); })");}),_rm=new T(function(){return eval("(function() {return (demoWorkspace.getAllBlocks()[0]);})");}),_rn=new T(function(){return eval("(function () {var i; var b = demoWorkspace.getAllBlocks(); for (i = b.length - 1; i > 0; --i) { if (b[i] !== undefined) { b[i].dispose() } };})");}),_ro=function(_rp,_){var _rq=__app0(E(_rn)),_rr=__app0(E(_rm)),_rs=B(_m1(B(_3C(_lZ,_rp))));if(!_rs._){return E(_2f);}else{if(!E(_rs.b)._){var _rt=B(_q9(_rs.a,_)),_ru=B(_mY(_rk,_rr,_rt,_)),_rv=__app0(E(_rl));return _0;}else{return E(_25);}}},_rw="(function (t) {return document.getElementById(t).value})",_rx=function(_){var _ry=eval(E(_rw)),_rz=__app1(E(_ry),toJSStr(E(_26)));return new F(function(){return _ro(new T(function(){var _rA=String(_rz);return fromJSStr(_rA);}),_);});},_rB=new T0(1),_rC=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_rD=function(_rE){return new F(function(){return err(_rC);});},_rF=new T(function(){return B(_rD(_));}),_rG=function(_rH,_rI,_rJ){var _rK=E(_rJ);if(!_rK._){var _rL=_rK.a,_rM=E(_rI);if(!_rM._){var _rN=_rM.a,_rO=_rM.b;if(_rN<=(imul(3,_rL)|0)){return new T4(0,(1+_rN|0)+_rL|0,E(_rH),E(_rM),E(_rK));}else{var _rP=E(_rM.c);if(!_rP._){var _rQ=_rP.a,_rR=E(_rM.d);if(!_rR._){var _rS=_rR.a,_rT=_rR.b,_rU=_rR.c;if(_rS>=(imul(2,_rQ)|0)){var _rV=function(_rW){var _rX=E(_rR.d);return (_rX._==0)?new T4(0,(1+_rN|0)+_rL|0,E(_rT),E(new T4(0,(1+_rQ|0)+_rW|0,E(_rO),E(_rP),E(_rU))),E(new T4(0,(1+_rL|0)+_rX.a|0,E(_rH),E(_rX),E(_rK)))):new T4(0,(1+_rN|0)+_rL|0,E(_rT),E(new T4(0,(1+_rQ|0)+_rW|0,E(_rO),E(_rP),E(_rU))),E(new T4(0,1+_rL|0,E(_rH),E(_rB),E(_rK))));},_rY=E(_rU);if(!_rY._){return new F(function(){return _rV(_rY.a);});}else{return new F(function(){return _rV(0);});}}else{return new T4(0,(1+_rN|0)+_rL|0,E(_rO),E(_rP),E(new T4(0,(1+_rL|0)+_rS|0,E(_rH),E(_rR),E(_rK))));}}else{return E(_rF);}}else{return E(_rF);}}}else{return new T4(0,1+_rL|0,E(_rH),E(_rB),E(_rK));}}else{var _rZ=E(_rI);if(!_rZ._){var _s0=_rZ.a,_s1=_rZ.b,_s2=_rZ.d,_s3=E(_rZ.c);if(!_s3._){var _s4=_s3.a,_s5=E(_s2);if(!_s5._){var _s6=_s5.a,_s7=_s5.b,_s8=_s5.c;if(_s6>=(imul(2,_s4)|0)){var _s9=function(_sa){var _sb=E(_s5.d);return (_sb._==0)?new T4(0,1+_s0|0,E(_s7),E(new T4(0,(1+_s4|0)+_sa|0,E(_s1),E(_s3),E(_s8))),E(new T4(0,1+_sb.a|0,E(_rH),E(_sb),E(_rB)))):new T4(0,1+_s0|0,E(_s7),E(new T4(0,(1+_s4|0)+_sa|0,E(_s1),E(_s3),E(_s8))),E(new T4(0,1,E(_rH),E(_rB),E(_rB))));},_sc=E(_s8);if(!_sc._){return new F(function(){return _s9(_sc.a);});}else{return new F(function(){return _s9(0);});}}else{return new T4(0,1+_s0|0,E(_s1),E(_s3),E(new T4(0,1+_s6|0,E(_rH),E(_s5),E(_rB))));}}else{return new T4(0,3,E(_s1),E(_s3),E(new T4(0,1,E(_rH),E(_rB),E(_rB))));}}else{var _sd=E(_s2);return (_sd._==0)?new T4(0,3,E(_sd.b),E(new T4(0,1,E(_s1),E(_rB),E(_rB))),E(new T4(0,1,E(_rH),E(_rB),E(_rB)))):new T4(0,2,E(_rH),E(_rZ),E(_rB));}}else{return new T4(0,1,E(_rH),E(_rB),E(_rB));}}},_se=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_sf=function(_sg){return new F(function(){return err(_se);});},_sh=new T(function(){return B(_sf(_));}),_si=function(_sj,_sk,_sl){var _sm=E(_sk);if(!_sm._){var _sn=_sm.a,_so=E(_sl);if(!_so._){var _sp=_so.a,_sq=_so.b;if(_sp<=(imul(3,_sn)|0)){return new T4(0,(1+_sn|0)+_sp|0,E(_sj),E(_sm),E(_so));}else{var _sr=E(_so.c);if(!_sr._){var _ss=_sr.a,_st=_sr.b,_su=_sr.c,_sv=E(_so.d);if(!_sv._){var _sw=_sv.a;if(_ss>=(imul(2,_sw)|0)){var _sx=function(_sy){var _sz=E(_sj),_sA=E(_sr.d);return (_sA._==0)?new T4(0,(1+_sn|0)+_sp|0,E(_st),E(new T4(0,(1+_sn|0)+_sy|0,E(_sz),E(_sm),E(_su))),E(new T4(0,(1+_sw|0)+_sA.a|0,E(_sq),E(_sA),E(_sv)))):new T4(0,(1+_sn|0)+_sp|0,E(_st),E(new T4(0,(1+_sn|0)+_sy|0,E(_sz),E(_sm),E(_su))),E(new T4(0,1+_sw|0,E(_sq),E(_rB),E(_sv))));},_sB=E(_su);if(!_sB._){return new F(function(){return _sx(_sB.a);});}else{return new F(function(){return _sx(0);});}}else{return new T4(0,(1+_sn|0)+_sp|0,E(_sq),E(new T4(0,(1+_sn|0)+_ss|0,E(_sj),E(_sm),E(_sr))),E(_sv));}}else{return E(_sh);}}else{return E(_sh);}}}else{return new T4(0,1+_sn|0,E(_sj),E(_sm),E(_rB));}}else{var _sC=E(_sl);if(!_sC._){var _sD=_sC.a,_sE=_sC.b,_sF=_sC.d,_sG=E(_sC.c);if(!_sG._){var _sH=_sG.a,_sI=_sG.b,_sJ=_sG.c,_sK=E(_sF);if(!_sK._){var _sL=_sK.a;if(_sH>=(imul(2,_sL)|0)){var _sM=function(_sN){var _sO=E(_sj),_sP=E(_sG.d);return (_sP._==0)?new T4(0,1+_sD|0,E(_sI),E(new T4(0,1+_sN|0,E(_sO),E(_rB),E(_sJ))),E(new T4(0,(1+_sL|0)+_sP.a|0,E(_sE),E(_sP),E(_sK)))):new T4(0,1+_sD|0,E(_sI),E(new T4(0,1+_sN|0,E(_sO),E(_rB),E(_sJ))),E(new T4(0,1+_sL|0,E(_sE),E(_rB),E(_sK))));},_sQ=E(_sJ);if(!_sQ._){return new F(function(){return _sM(_sQ.a);});}else{return new F(function(){return _sM(0);});}}else{return new T4(0,1+_sD|0,E(_sE),E(new T4(0,1+_sH|0,E(_sj),E(_rB),E(_sG))),E(_sK));}}else{return new T4(0,3,E(_sI),E(new T4(0,1,E(_sj),E(_rB),E(_rB))),E(new T4(0,1,E(_sE),E(_rB),E(_rB))));}}else{var _sR=E(_sF);return (_sR._==0)?new T4(0,3,E(_sE),E(new T4(0,1,E(_sj),E(_rB),E(_rB))),E(_sR)):new T4(0,2,E(_sj),E(_rB),E(_sC));}}else{return new T4(0,1,E(_sj),E(_rB),E(_rB));}}},_sS=function(_sT,_sU,_sV,_sW,_sX){var _sY=E(_sX);if(!_sY._){var _sZ=_sY.c,_t0=_sY.d,_t1=E(_sY.b),_t2=E(_sT),_t3=E(_t1.a);if(_t2>=_t3){if(_t2!=_t3){return new F(function(){return _si(_t1,_sZ,B(_sS(_t2,_sU,_sV,_sW,_t0)));});}else{var _t4=E(_sU),_t5=E(_t1.b);if(_t4>=_t5){if(_t4!=_t5){return new F(function(){return _si(_t1,_sZ,B(_sS(_t2,_t4,_sV,_sW,_t0)));});}else{var _t6=E(_sV),_t7=E(_t1.c);if(_t6>=_t7){if(_t6!=_t7){return new F(function(){return _si(_t1,_sZ,B(_sS(_t2,_t4,_t6,_sW,_t0)));});}else{var _t8=E(_sW),_t9=E(_t1.d);if(_t8>=_t9){if(_t8!=_t9){return new F(function(){return _si(_t1,_sZ,B(_sS(_t2,_t4,_t6,_t8,_t0)));});}else{return new T4(0,_sY.a,E(new T4(0,_t2,_t4,_t6,_t8)),E(_sZ),E(_t0));}}else{return new F(function(){return _rG(_t1,B(_sS(_t2,_t4,_t6,_t8,_sZ)),_t0);});}}}else{return new F(function(){return _rG(_t1,B(_sS(_t2,_t4,_t6,_sW,_sZ)),_t0);});}}}else{return new F(function(){return _rG(_t1,B(_sS(_t2,_t4,_sV,_sW,_sZ)),_t0);});}}}else{return new F(function(){return _rG(_t1,B(_sS(_t2,_sU,_sV,_sW,_sZ)),_t0);});}}else{return new T4(0,1,E(new T4(0,_sT,_sU,_sV,_sW)),E(_rB),E(_rB));}},_ta=function(_tb,_tc){while(1){var _td=E(_tc);if(!_td._){return E(_tb);}else{var _te=E(_td.a),_tf=B(_sS(_te.a,_te.b,_te.c,_te.d,_tb));_tb=_tf;_tc=_td.b;continue;}}},_tg=function(_th,_ti,_tj,_tk,_tl,_tm){return new F(function(){return _ta(B(_sS(_ti,_tj,_tk,_tl,_th)),_tm);});},_tn=function(_to){return new T4(0,1,E(_to),E(_rB),E(_rB));},_tp=function(_tq,_tr){var _ts=E(_tr);if(!_ts._){return new F(function(){return _si(_ts.b,_ts.c,B(_tp(_tq,_ts.d)));});}else{return new F(function(){return _tn(_tq);});}},_tt=function(_tu,_tv){var _tw=E(_tv);if(!_tw._){return new F(function(){return _rG(_tw.b,B(_tt(_tu,_tw.c)),_tw.d);});}else{return new F(function(){return _tn(_tu);});}},_tx=function(_ty,_tz,_tA,_tB,_tC){return new F(function(){return _si(_tA,_tB,B(_tp(_ty,_tC)));});},_tD=function(_tE,_tF,_tG,_tH,_tI){return new F(function(){return _rG(_tG,B(_tt(_tE,_tH)),_tI);});},_tJ=function(_tK,_tL,_tM,_tN,_tO,_tP){var _tQ=E(_tL);if(!_tQ._){var _tR=_tQ.a,_tS=_tQ.b,_tT=_tQ.c,_tU=_tQ.d;if((imul(3,_tR)|0)>=_tM){if((imul(3,_tM)|0)>=_tR){return new T4(0,(_tR+_tM|0)+1|0,E(_tK),E(_tQ),E(new T4(0,_tM,E(_tN),E(_tO),E(_tP))));}else{return new F(function(){return _si(_tS,_tT,B(_tJ(_tK,_tU,_tM,_tN,_tO,_tP)));});}}else{return new F(function(){return _rG(_tN,B(_tV(_tK,_tR,_tS,_tT,_tU,_tO)),_tP);});}}else{return new F(function(){return _tD(_tK,_tM,_tN,_tO,_tP);});}},_tV=function(_tW,_tX,_tY,_tZ,_u0,_u1){var _u2=E(_u1);if(!_u2._){var _u3=_u2.a,_u4=_u2.b,_u5=_u2.c,_u6=_u2.d;if((imul(3,_tX)|0)>=_u3){if((imul(3,_u3)|0)>=_tX){return new T4(0,(_tX+_u3|0)+1|0,E(_tW),E(new T4(0,_tX,E(_tY),E(_tZ),E(_u0))),E(_u2));}else{return new F(function(){return _si(_tY,_tZ,B(_tJ(_tW,_u0,_u3,_u4,_u5,_u6)));});}}else{return new F(function(){return _rG(_u4,B(_tV(_tW,_tX,_tY,_tZ,_u0,_u5)),_u6);});}}else{return new F(function(){return _tx(_tW,_tX,_tY,_tZ,_u0);});}},_u7=function(_u8,_u9,_ua){var _ub=E(_u9);if(!_ub._){var _uc=_ub.a,_ud=_ub.b,_ue=_ub.c,_uf=_ub.d,_ug=E(_ua);if(!_ug._){var _uh=_ug.a,_ui=_ug.b,_uj=_ug.c,_uk=_ug.d;if((imul(3,_uc)|0)>=_uh){if((imul(3,_uh)|0)>=_uc){return new T4(0,(_uc+_uh|0)+1|0,E(_u8),E(_ub),E(_ug));}else{return new F(function(){return _si(_ud,_ue,B(_tJ(_u8,_uf,_uh,_ui,_uj,_uk)));});}}else{return new F(function(){return _rG(_ui,B(_tV(_u8,_uc,_ud,_ue,_uf,_uj)),_uk);});}}else{return new F(function(){return _tx(_u8,_uc,_ud,_ue,_uf);});}}else{return new F(function(){return _tt(_u8,_ua);});}},_ul=function(_um,_un){var _uo=E(_un);if(!_uo._){return new T3(0,_rB,_23,_23);}else{var _up=_uo.a,_uq=E(_um);if(_uq==1){var _ur=E(_uo.b);if(!_ur._){return new T3(0,new T(function(){return new T4(0,1,E(_up),E(_rB),E(_rB));}),_23,_23);}else{var _us=E(_up),_ut=E(_us.a),_uu=E(_ur.a),_uv=E(_uu.a);if(_ut>=_uv){if(_ut!=_uv){return new T3(0,new T4(0,1,E(_us),E(_rB),E(_rB)),_23,_ur);}else{var _uw=E(_us.b),_ux=E(_uu.b);if(_uw>=_ux){if(_uw!=_ux){return new T3(0,new T4(0,1,E(_us),E(_rB),E(_rB)),_23,_ur);}else{var _uy=E(_us.c),_uz=E(_uu.c);return (_uy>=_uz)?(_uy!=_uz)?new T3(0,new T4(0,1,E(_us),E(_rB),E(_rB)),_23,_ur):(E(_us.d)<E(_uu.d))?new T3(0,new T4(0,1,E(_us),E(_rB),E(_rB)),_ur,_23):new T3(0,new T4(0,1,E(_us),E(_rB),E(_rB)),_23,_ur):new T3(0,new T4(0,1,E(_us),E(_rB),E(_rB)),_ur,_23);}}else{return new T3(0,new T4(0,1,E(_us),E(_rB),E(_rB)),_ur,_23);}}}else{return new T3(0,new T4(0,1,E(_us),E(_rB),E(_rB)),_ur,_23);}}}else{var _uA=B(_ul(_uq>>1,_uo)),_uB=_uA.a,_uC=_uA.c,_uD=E(_uA.b);if(!_uD._){return new T3(0,_uB,_23,_uC);}else{var _uE=_uD.a,_uF=E(_uD.b);if(!_uF._){return new T3(0,new T(function(){return B(_tp(_uE,_uB));}),_23,_uC);}else{var _uG=E(_uE),_uH=E(_uG.a),_uI=E(_uF.a),_uJ=E(_uI.a);if(_uH>=_uJ){if(_uH!=_uJ){return new T3(0,_uB,_23,_uD);}else{var _uK=E(_uG.b),_uL=E(_uI.b);if(_uK>=_uL){if(_uK!=_uL){return new T3(0,_uB,_23,_uD);}else{var _uM=E(_uG.c),_uN=E(_uI.c);if(_uM>=_uN){if(_uM!=_uN){return new T3(0,_uB,_23,_uD);}else{if(E(_uG.d)<E(_uI.d)){var _uO=B(_ul(_uq>>1,_uF));return new T3(0,new T(function(){return B(_u7(_uG,_uB,_uO.a));}),_uO.b,_uO.c);}else{return new T3(0,_uB,_23,_uD);}}}else{var _uP=B(_ul(_uq>>1,_uF));return new T3(0,new T(function(){return B(_u7(_uG,_uB,_uP.a));}),_uP.b,_uP.c);}}}else{var _uQ=B(_ul(_uq>>1,_uF));return new T3(0,new T(function(){return B(_u7(_uG,_uB,_uQ.a));}),_uQ.b,_uQ.c);}}}else{var _uR=B(_ul(_uq>>1,_uF));return new T3(0,new T(function(){return B(_u7(_uG,_uB,_uR.a));}),_uR.b,_uR.c);}}}}}},_uS=function(_uT,_uU,_uV){var _uW=E(_uV);if(!_uW._){return E(_uU);}else{var _uX=_uW.a,_uY=E(_uW.b);if(!_uY._){return new F(function(){return _tp(_uX,_uU);});}else{var _uZ=E(_uX),_v0=_uZ.b,_v1=_uZ.c,_v2=_uZ.d,_v3=E(_uZ.a),_v4=E(_uY.a),_v5=E(_v4.a),_v6=function(_v7){var _v8=B(_ul(_uT,_uY)),_v9=_v8.a,_va=E(_v8.c);if(!_va._){return new F(function(){return _uS(_uT<<1,B(_u7(_uZ,_uU,_v9)),_v8.b);});}else{return new F(function(){return _ta(B(_u7(_uZ,_uU,_v9)),_va);});}};if(_v3>=_v5){if(_v3!=_v5){return new F(function(){return _tg(_uU,_v3,_v0,_v1,_v2,_uY);});}else{var _vb=E(_v0),_vc=E(_v4.b);if(_vb>=_vc){if(_vb!=_vc){return new F(function(){return _tg(_uU,_v3,_vb,_v1,_v2,_uY);});}else{var _vd=E(_v1),_ve=E(_v4.c);if(_vd>=_ve){if(_vd!=_ve){return new F(function(){return _tg(_uU,_v3,_vb,_vd,_v2,_uY);});}else{var _vf=E(_v2);if(_vf<E(_v4.d)){return new F(function(){return _v6(_);});}else{return new F(function(){return _tg(_uU,_v3,_vb,_vd,_vf,_uY);});}}}else{return new F(function(){return _v6(_);});}}}else{return new F(function(){return _v6(_);});}}}else{return new F(function(){return _v6(_);});}}}},_vg=function(_vh){var _vi=E(_vh);if(!_vi._){return new T0(1);}else{var _vj=_vi.a,_vk=E(_vi.b);if(!_vk._){return new T4(0,1,E(_vj),E(_rB),E(_rB));}else{var _vl=_vk.b,_vm=E(_vj),_vn=E(_vm.a),_vo=E(_vk.a),_vp=_vo.b,_vq=_vo.c,_vr=_vo.d,_vs=E(_vo.a);if(_vn>=_vs){if(_vn!=_vs){return new F(function(){return _tg(new T4(0,1,E(_vm),E(_rB),E(_rB)),_vs,_vp,_vq,_vr,_vl);});}else{var _vt=E(_vm.b),_vu=E(_vp);if(_vt>=_vu){if(_vt!=_vu){return new F(function(){return _tg(new T4(0,1,E(_vm),E(_rB),E(_rB)),_vs,_vu,_vq,_vr,_vl);});}else{var _vv=E(_vm.c),_vw=E(_vq);if(_vv>=_vw){if(_vv!=_vw){return new F(function(){return _tg(new T4(0,1,E(_vm),E(_rB),E(_rB)),_vs,_vu,_vw,_vr,_vl);});}else{var _vx=E(_vr);if(E(_vm.d)<_vx){return new F(function(){return _uS(1,new T4(0,1,E(_vm),E(_rB),E(_rB)),_vk);});}else{return new F(function(){return _tg(new T4(0,1,E(_vm),E(_rB),E(_rB)),_vs,_vu,_vw,_vx,_vl);});}}}else{return new F(function(){return _uS(1,new T4(0,1,E(_vm),E(_rB),E(_rB)),_vk);});}}}else{return new F(function(){return _uS(1,new T4(0,1,E(_vm),E(_rB),E(_rB)),_vk);});}}}else{return new F(function(){return _uS(1,new T4(0,1,E(_vm),E(_rB),E(_rB)),_vk);});}}}},_vy=function(_vz,_vA,_vB,_vC,_vD){var _vE=E(_vz);if(_vE==1){var _vF=E(_vD);if(!_vF._){return new T3(0,new T4(0,1,E(new T3(0,_vA,_vB,_vC)),E(_rB),E(_rB)),_23,_23);}else{var _vG=E(_vA),_vH=E(_vF.a),_vI=E(_vH.a);if(_vG>=_vI){if(_vG!=_vI){return new T3(0,new T4(0,1,E(new T3(0,_vG,_vB,_vC)),E(_rB),E(_rB)),_23,_vF);}else{var _vJ=E(_vH.b);return (_vB>=_vJ)?(_vB!=_vJ)?new T3(0,new T4(0,1,E(new T3(0,_vG,_vB,_vC)),E(_rB),E(_rB)),_23,_vF):(_vC<E(_vH.c))?new T3(0,new T4(0,1,E(new T3(0,_vG,_vB,_vC)),E(_rB),E(_rB)),_vF,_23):new T3(0,new T4(0,1,E(new T3(0,_vG,_vB,_vC)),E(_rB),E(_rB)),_23,_vF):new T3(0,new T4(0,1,E(new T3(0,_vG,_vB,_vC)),E(_rB),E(_rB)),_vF,_23);}}else{return new T3(0,new T4(0,1,E(new T3(0,_vG,_vB,_vC)),E(_rB),E(_rB)),_vF,_23);}}}else{var _vK=B(_vy(_vE>>1,_vA,_vB,_vC,_vD)),_vL=_vK.a,_vM=_vK.c,_vN=E(_vK.b);if(!_vN._){return new T3(0,_vL,_23,_vM);}else{var _vO=_vN.a,_vP=E(_vN.b);if(!_vP._){return new T3(0,new T(function(){return B(_tp(_vO,_vL));}),_23,_vM);}else{var _vQ=_vP.b,_vR=E(_vO),_vS=E(_vR.a),_vT=E(_vP.a),_vU=_vT.b,_vV=_vT.c,_vW=E(_vT.a);if(_vS>=_vW){if(_vS!=_vW){return new T3(0,_vL,_23,_vN);}else{var _vX=E(_vR.b),_vY=E(_vU);if(_vX>=_vY){if(_vX!=_vY){return new T3(0,_vL,_23,_vN);}else{var _vZ=E(_vV);if(E(_vR.c)<_vZ){var _w0=B(_vy(_vE>>1,_vW,_vY,_vZ,_vQ));return new T3(0,new T(function(){return B(_u7(_vR,_vL,_w0.a));}),_w0.b,_w0.c);}else{return new T3(0,_vL,_23,_vN);}}}else{var _w1=B(_w2(_vE>>1,_vW,_vY,_vV,_vQ));return new T3(0,new T(function(){return B(_u7(_vR,_vL,_w1.a));}),_w1.b,_w1.c);}}}else{var _w3=B(_w4(_vE>>1,_vW,_vU,_vV,_vQ));return new T3(0,new T(function(){return B(_u7(_vR,_vL,_w3.a));}),_w3.b,_w3.c);}}}}},_w2=function(_w5,_w6,_w7,_w8,_w9){var _wa=E(_w5);if(_wa==1){var _wb=E(_w9);if(!_wb._){return new T3(0,new T4(0,1,E(new T3(0,_w6,_w7,_w8)),E(_rB),E(_rB)),_23,_23);}else{var _wc=E(_w6),_wd=E(_wb.a),_we=E(_wd.a);if(_wc>=_we){if(_wc!=_we){return new T3(0,new T4(0,1,E(new T3(0,_wc,_w7,_w8)),E(_rB),E(_rB)),_23,_wb);}else{var _wf=E(_wd.b);if(_w7>=_wf){if(_w7!=_wf){return new T3(0,new T4(0,1,E(new T3(0,_wc,_w7,_w8)),E(_rB),E(_rB)),_23,_wb);}else{var _wg=E(_w8);return (_wg<E(_wd.c))?new T3(0,new T4(0,1,E(new T3(0,_wc,_w7,_wg)),E(_rB),E(_rB)),_wb,_23):new T3(0,new T4(0,1,E(new T3(0,_wc,_w7,_wg)),E(_rB),E(_rB)),_23,_wb);}}else{return new T3(0,new T4(0,1,E(new T3(0,_wc,_w7,_w8)),E(_rB),E(_rB)),_wb,_23);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_wc,_w7,_w8)),E(_rB),E(_rB)),_wb,_23);}}}else{var _wh=B(_w2(_wa>>1,_w6,_w7,_w8,_w9)),_wi=_wh.a,_wj=_wh.c,_wk=E(_wh.b);if(!_wk._){return new T3(0,_wi,_23,_wj);}else{var _wl=_wk.a,_wm=E(_wk.b);if(!_wm._){return new T3(0,new T(function(){return B(_tp(_wl,_wi));}),_23,_wj);}else{var _wn=_wm.b,_wo=E(_wl),_wp=E(_wo.a),_wq=E(_wm.a),_wr=_wq.b,_ws=_wq.c,_wt=E(_wq.a);if(_wp>=_wt){if(_wp!=_wt){return new T3(0,_wi,_23,_wk);}else{var _wu=E(_wo.b),_wv=E(_wr);if(_wu>=_wv){if(_wu!=_wv){return new T3(0,_wi,_23,_wk);}else{var _ww=E(_ws);if(E(_wo.c)<_ww){var _wx=B(_vy(_wa>>1,_wt,_wv,_ww,_wn));return new T3(0,new T(function(){return B(_u7(_wo,_wi,_wx.a));}),_wx.b,_wx.c);}else{return new T3(0,_wi,_23,_wk);}}}else{var _wy=B(_w2(_wa>>1,_wt,_wv,_ws,_wn));return new T3(0,new T(function(){return B(_u7(_wo,_wi,_wy.a));}),_wy.b,_wy.c);}}}else{var _wz=B(_w4(_wa>>1,_wt,_wr,_ws,_wn));return new T3(0,new T(function(){return B(_u7(_wo,_wi,_wz.a));}),_wz.b,_wz.c);}}}}},_w4=function(_wA,_wB,_wC,_wD,_wE){var _wF=E(_wA);if(_wF==1){var _wG=E(_wE);if(!_wG._){return new T3(0,new T4(0,1,E(new T3(0,_wB,_wC,_wD)),E(_rB),E(_rB)),_23,_23);}else{var _wH=E(_wB),_wI=E(_wG.a),_wJ=E(_wI.a);if(_wH>=_wJ){if(_wH!=_wJ){return new T3(0,new T4(0,1,E(new T3(0,_wH,_wC,_wD)),E(_rB),E(_rB)),_23,_wG);}else{var _wK=E(_wC),_wL=E(_wI.b);if(_wK>=_wL){if(_wK!=_wL){return new T3(0,new T4(0,1,E(new T3(0,_wH,_wK,_wD)),E(_rB),E(_rB)),_23,_wG);}else{var _wM=E(_wD);return (_wM<E(_wI.c))?new T3(0,new T4(0,1,E(new T3(0,_wH,_wK,_wM)),E(_rB),E(_rB)),_wG,_23):new T3(0,new T4(0,1,E(new T3(0,_wH,_wK,_wM)),E(_rB),E(_rB)),_23,_wG);}}else{return new T3(0,new T4(0,1,E(new T3(0,_wH,_wK,_wD)),E(_rB),E(_rB)),_wG,_23);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_wH,_wC,_wD)),E(_rB),E(_rB)),_wG,_23);}}}else{var _wN=B(_w4(_wF>>1,_wB,_wC,_wD,_wE)),_wO=_wN.a,_wP=_wN.c,_wQ=E(_wN.b);if(!_wQ._){return new T3(0,_wO,_23,_wP);}else{var _wR=_wQ.a,_wS=E(_wQ.b);if(!_wS._){return new T3(0,new T(function(){return B(_tp(_wR,_wO));}),_23,_wP);}else{var _wT=_wS.b,_wU=E(_wR),_wV=E(_wU.a),_wW=E(_wS.a),_wX=_wW.b,_wY=_wW.c,_wZ=E(_wW.a);if(_wV>=_wZ){if(_wV!=_wZ){return new T3(0,_wO,_23,_wQ);}else{var _x0=E(_wU.b),_x1=E(_wX);if(_x0>=_x1){if(_x0!=_x1){return new T3(0,_wO,_23,_wQ);}else{var _x2=E(_wY);if(E(_wU.c)<_x2){var _x3=B(_vy(_wF>>1,_wZ,_x1,_x2,_wT));return new T3(0,new T(function(){return B(_u7(_wU,_wO,_x3.a));}),_x3.b,_x3.c);}else{return new T3(0,_wO,_23,_wQ);}}}else{var _x4=B(_w2(_wF>>1,_wZ,_x1,_wY,_wT));return new T3(0,new T(function(){return B(_u7(_wU,_wO,_x4.a));}),_x4.b,_x4.c);}}}else{var _x5=B(_w4(_wF>>1,_wZ,_wX,_wY,_wT));return new T3(0,new T(function(){return B(_u7(_wU,_wO,_x5.a));}),_x5.b,_x5.c);}}}}},_x6=function(_x7,_x8,_x9,_xa,_xb){var _xc=E(_xb);if(!_xc._){var _xd=_xc.c,_xe=_xc.d,_xf=E(_xc.b),_xg=E(_xf.a);if(_x7>=_xg){if(_x7!=_xg){return new F(function(){return _si(_xf,_xd,B(_x6(_x7,_,_x9,_xa,_xe)));});}else{var _xh=E(_xf.b);if(_x9>=_xh){if(_x9!=_xh){return new F(function(){return _si(_xf,_xd,B(_x6(_x7,_,_x9,_xa,_xe)));});}else{var _xi=E(_xf.c);if(_xa>=_xi){if(_xa!=_xi){return new F(function(){return _si(_xf,_xd,B(_x6(_x7,_,_x9,_xa,_xe)));});}else{return new T4(0,_xc.a,E(new T3(0,_x7,_x9,_xa)),E(_xd),E(_xe));}}else{return new F(function(){return _rG(_xf,B(_x6(_x7,_,_x9,_xa,_xd)),_xe);});}}}else{return new F(function(){return _rG(_xf,B(_x6(_x7,_,_x9,_xa,_xd)),_xe);});}}}else{return new F(function(){return _rG(_xf,B(_x6(_x7,_,_x9,_xa,_xd)),_xe);});}}else{return new T4(0,1,E(new T3(0,_x7,_x9,_xa)),E(_rB),E(_rB));}},_xj=function(_xk,_xl,_xm,_xn,_xo){var _xp=E(_xo);if(!_xp._){var _xq=_xp.c,_xr=_xp.d,_xs=E(_xp.b),_xt=E(_xs.a);if(_xk>=_xt){if(_xk!=_xt){return new F(function(){return _si(_xs,_xq,B(_xj(_xk,_,_xm,_xn,_xr)));});}else{var _xu=E(_xs.b);if(_xm>=_xu){if(_xm!=_xu){return new F(function(){return _si(_xs,_xq,B(_xj(_xk,_,_xm,_xn,_xr)));});}else{var _xv=E(_xn),_xw=E(_xs.c);if(_xv>=_xw){if(_xv!=_xw){return new F(function(){return _si(_xs,_xq,B(_x6(_xk,_,_xm,_xv,_xr)));});}else{return new T4(0,_xp.a,E(new T3(0,_xk,_xm,_xv)),E(_xq),E(_xr));}}else{return new F(function(){return _rG(_xs,B(_x6(_xk,_,_xm,_xv,_xq)),_xr);});}}}else{return new F(function(){return _rG(_xs,B(_xj(_xk,_,_xm,_xn,_xq)),_xr);});}}}else{return new F(function(){return _rG(_xs,B(_xj(_xk,_,_xm,_xn,_xq)),_xr);});}}else{return new T4(0,1,E(new T3(0,_xk,_xm,_xn)),E(_rB),E(_rB));}},_xx=function(_xy,_xz,_xA,_xB,_xC){var _xD=E(_xC);if(!_xD._){var _xE=_xD.c,_xF=_xD.d,_xG=E(_xD.b),_xH=E(_xG.a);if(_xy>=_xH){if(_xy!=_xH){return new F(function(){return _si(_xG,_xE,B(_xx(_xy,_,_xA,_xB,_xF)));});}else{var _xI=E(_xA),_xJ=E(_xG.b);if(_xI>=_xJ){if(_xI!=_xJ){return new F(function(){return _si(_xG,_xE,B(_xj(_xy,_,_xI,_xB,_xF)));});}else{var _xK=E(_xB),_xL=E(_xG.c);if(_xK>=_xL){if(_xK!=_xL){return new F(function(){return _si(_xG,_xE,B(_x6(_xy,_,_xI,_xK,_xF)));});}else{return new T4(0,_xD.a,E(new T3(0,_xy,_xI,_xK)),E(_xE),E(_xF));}}else{return new F(function(){return _rG(_xG,B(_x6(_xy,_,_xI,_xK,_xE)),_xF);});}}}else{return new F(function(){return _rG(_xG,B(_xj(_xy,_,_xI,_xB,_xE)),_xF);});}}}else{return new F(function(){return _rG(_xG,B(_xx(_xy,_,_xA,_xB,_xE)),_xF);});}}else{return new T4(0,1,E(new T3(0,_xy,_xA,_xB)),E(_rB),E(_rB));}},_xM=function(_xN,_xO,_xP,_xQ){var _xR=E(_xQ);if(!_xR._){var _xS=_xR.c,_xT=_xR.d,_xU=E(_xR.b),_xV=E(_xN),_xW=E(_xU.a);if(_xV>=_xW){if(_xV!=_xW){return new F(function(){return _si(_xU,_xS,B(_xx(_xV,_,_xO,_xP,_xT)));});}else{var _xX=E(_xO),_xY=E(_xU.b);if(_xX>=_xY){if(_xX!=_xY){return new F(function(){return _si(_xU,_xS,B(_xj(_xV,_,_xX,_xP,_xT)));});}else{var _xZ=E(_xP),_y0=E(_xU.c);if(_xZ>=_y0){if(_xZ!=_y0){return new F(function(){return _si(_xU,_xS,B(_x6(_xV,_,_xX,_xZ,_xT)));});}else{return new T4(0,_xR.a,E(new T3(0,_xV,_xX,_xZ)),E(_xS),E(_xT));}}else{return new F(function(){return _rG(_xU,B(_x6(_xV,_,_xX,_xZ,_xS)),_xT);});}}}else{return new F(function(){return _rG(_xU,B(_xj(_xV,_,_xX,_xP,_xS)),_xT);});}}}else{return new F(function(){return _rG(_xU,B(_xx(_xV,_,_xO,_xP,_xS)),_xT);});}}else{return new T4(0,1,E(new T3(0,_xN,_xO,_xP)),E(_rB),E(_rB));}},_y1=function(_y2,_y3){while(1){var _y4=E(_y3);if(!_y4._){return E(_y2);}else{var _y5=E(_y4.a),_y6=B(_xM(_y5.a,_y5.b,_y5.c,_y2));_y2=_y6;_y3=_y4.b;continue;}}},_y7=function(_y8,_y9,_ya,_yb,_yc){return new F(function(){return _y1(B(_xM(_y9,_ya,_yb,_y8)),_yc);});},_yd=function(_ye,_yf,_yg){var _yh=E(_yf);return new F(function(){return _y1(B(_xM(_yh.a,_yh.b,_yh.c,_ye)),_yg);});},_yi=function(_yj,_yk,_yl){var _ym=E(_yl);if(!_ym._){return E(_yk);}else{var _yn=_ym.a,_yo=E(_ym.b);if(!_yo._){return new F(function(){return _tp(_yn,_yk);});}else{var _yp=E(_yn),_yq=_yp.b,_yr=_yp.c,_ys=E(_yp.a),_yt=E(_yo.a),_yu=_yt.b,_yv=_yt.c,_yw=E(_yt.a),_yx=function(_yy){var _yz=B(_w4(_yj,_yw,_yu,_yv,_yo.b)),_yA=_yz.a,_yB=E(_yz.c);if(!_yB._){return new F(function(){return _yi(_yj<<1,B(_u7(_yp,_yk,_yA)),_yz.b);});}else{return new F(function(){return _yd(B(_u7(_yp,_yk,_yA)),_yB.a,_yB.b);});}};if(_ys>=_yw){if(_ys!=_yw){return new F(function(){return _y7(_yk,_ys,_yq,_yr,_yo);});}else{var _yC=E(_yq),_yD=E(_yu);if(_yC>=_yD){if(_yC!=_yD){return new F(function(){return _y7(_yk,_ys,_yC,_yr,_yo);});}else{var _yE=E(_yr);if(_yE<E(_yv)){return new F(function(){return _yx(_);});}else{return new F(function(){return _y7(_yk,_ys,_yC,_yE,_yo);});}}}else{return new F(function(){return _yx(_);});}}}else{return new F(function(){return _yx(_);});}}}},_yF=function(_yG,_yH,_yI,_yJ,_yK,_yL){var _yM=E(_yL);if(!_yM._){return new F(function(){return _tp(new T3(0,_yI,_yJ,_yK),_yH);});}else{var _yN=E(_yI),_yO=E(_yM.a),_yP=_yO.b,_yQ=_yO.c,_yR=E(_yO.a),_yS=function(_yT){var _yU=B(_w4(_yG,_yR,_yP,_yQ,_yM.b)),_yV=_yU.a,_yW=E(_yU.c);if(!_yW._){return new F(function(){return _yi(_yG<<1,B(_u7(new T3(0,_yN,_yJ,_yK),_yH,_yV)),_yU.b);});}else{return new F(function(){return _yd(B(_u7(new T3(0,_yN,_yJ,_yK),_yH,_yV)),_yW.a,_yW.b);});}};if(_yN>=_yR){if(_yN!=_yR){return new F(function(){return _y7(_yH,_yN,_yJ,_yK,_yM);});}else{var _yX=E(_yP);if(_yJ>=_yX){if(_yJ!=_yX){return new F(function(){return _y7(_yH,_yN,_yJ,_yK,_yM);});}else{var _yY=E(_yK);if(_yY<E(_yQ)){return new F(function(){return _yS(_);});}else{return new F(function(){return _y7(_yH,_yN,_yJ,_yY,_yM);});}}}else{return new F(function(){return _yS(_);});}}}else{return new F(function(){return _yS(_);});}}},_yZ=function(_z0,_z1,_z2,_z3,_z4,_z5){var _z6=E(_z5);if(!_z6._){return new F(function(){return _tp(new T3(0,_z2,_z3,_z4),_z1);});}else{var _z7=E(_z2),_z8=E(_z6.a),_z9=_z8.b,_za=_z8.c,_zb=E(_z8.a),_zc=function(_zd){var _ze=B(_w4(_z0,_zb,_z9,_za,_z6.b)),_zf=_ze.a,_zg=E(_ze.c);if(!_zg._){return new F(function(){return _yi(_z0<<1,B(_u7(new T3(0,_z7,_z3,_z4),_z1,_zf)),_ze.b);});}else{return new F(function(){return _yd(B(_u7(new T3(0,_z7,_z3,_z4),_z1,_zf)),_zg.a,_zg.b);});}};if(_z7>=_zb){if(_z7!=_zb){return new F(function(){return _y7(_z1,_z7,_z3,_z4,_z6);});}else{var _zh=E(_z9);if(_z3>=_zh){if(_z3!=_zh){return new F(function(){return _y7(_z1,_z7,_z3,_z4,_z6);});}else{if(_z4<E(_za)){return new F(function(){return _zc(_);});}else{return new F(function(){return _y7(_z1,_z7,_z3,_z4,_z6);});}}}else{return new F(function(){return _zc(_);});}}}else{return new F(function(){return _zc(_);});}}},_zi=function(_zj,_zk,_zl,_zm,_zn,_zo){var _zp=E(_zo);if(!_zp._){return new F(function(){return _tp(new T3(0,_zl,_zm,_zn),_zk);});}else{var _zq=E(_zl),_zr=E(_zp.a),_zs=_zr.b,_zt=_zr.c,_zu=E(_zr.a),_zv=function(_zw){var _zx=B(_w4(_zj,_zu,_zs,_zt,_zp.b)),_zy=_zx.a,_zz=E(_zx.c);if(!_zz._){return new F(function(){return _yi(_zj<<1,B(_u7(new T3(0,_zq,_zm,_zn),_zk,_zy)),_zx.b);});}else{return new F(function(){return _yd(B(_u7(new T3(0,_zq,_zm,_zn),_zk,_zy)),_zz.a,_zz.b);});}};if(_zq>=_zu){if(_zq!=_zu){return new F(function(){return _y7(_zk,_zq,_zm,_zn,_zp);});}else{var _zA=E(_zm),_zB=E(_zs);if(_zA>=_zB){if(_zA!=_zB){return new F(function(){return _y7(_zk,_zq,_zA,_zn,_zp);});}else{var _zC=E(_zn);if(_zC<E(_zt)){return new F(function(){return _zv(_);});}else{return new F(function(){return _y7(_zk,_zq,_zA,_zC,_zp);});}}}else{return new F(function(){return _zv(_);});}}}else{return new F(function(){return _zv(_);});}}},_zD=function(_zE){var _zF=E(_zE);if(!_zF._){return new T0(1);}else{var _zG=_zF.a,_zH=E(_zF.b);if(!_zH._){return new T4(0,1,E(_zG),E(_rB),E(_rB));}else{var _zI=_zH.b,_zJ=E(_zG),_zK=E(_zJ.a),_zL=E(_zH.a),_zM=_zL.b,_zN=_zL.c,_zO=E(_zL.a);if(_zK>=_zO){if(_zK!=_zO){return new F(function(){return _y7(new T4(0,1,E(_zJ),E(_rB),E(_rB)),_zO,_zM,_zN,_zI);});}else{var _zP=E(_zJ.b),_zQ=E(_zM);if(_zP>=_zQ){if(_zP!=_zQ){return new F(function(){return _y7(new T4(0,1,E(_zJ),E(_rB),E(_rB)),_zO,_zQ,_zN,_zI);});}else{var _zR=E(_zN);if(E(_zJ.c)<_zR){return new F(function(){return _yZ(1,new T4(0,1,E(_zJ),E(_rB),E(_rB)),_zO,_zQ,_zR,_zI);});}else{return new F(function(){return _y7(new T4(0,1,E(_zJ),E(_rB),E(_rB)),_zO,_zQ,_zR,_zI);});}}}else{return new F(function(){return _yF(1,new T4(0,1,E(_zJ),E(_rB),E(_rB)),_zO,_zQ,_zN,_zI);});}}}else{return new F(function(){return _zi(1,new T4(0,1,E(_zJ),E(_rB),E(_rB)),_zO,_zM,_zN,_zI);});}}}},_zS=new T0(1),_zT=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_zU=function(_zV){return new F(function(){return err(_zT);});},_zW=new T(function(){return B(_zU(_));}),_zX=function(_zY,_zZ,_A0,_A1){var _A2=E(_A0);if(!_A2._){var _A3=_A2.a,_A4=E(_A1);if(!_A4._){var _A5=_A4.a,_A6=_A4.b,_A7=_A4.c;if(_A5<=(imul(3,_A3)|0)){return new T5(0,(1+_A3|0)+_A5|0,E(_zY),_zZ,E(_A2),E(_A4));}else{var _A8=E(_A4.d);if(!_A8._){var _A9=_A8.a,_Aa=_A8.b,_Ab=_A8.c,_Ac=_A8.d,_Ad=E(_A4.e);if(!_Ad._){var _Ae=_Ad.a;if(_A9>=(imul(2,_Ae)|0)){var _Af=function(_Ag){var _Ah=E(_zY),_Ai=E(_A8.e);return (_Ai._==0)?new T5(0,(1+_A3|0)+_A5|0,E(_Aa),_Ab,E(new T5(0,(1+_A3|0)+_Ag|0,E(_Ah),_zZ,E(_A2),E(_Ac))),E(new T5(0,(1+_Ae|0)+_Ai.a|0,E(_A6),_A7,E(_Ai),E(_Ad)))):new T5(0,(1+_A3|0)+_A5|0,E(_Aa),_Ab,E(new T5(0,(1+_A3|0)+_Ag|0,E(_Ah),_zZ,E(_A2),E(_Ac))),E(new T5(0,1+_Ae|0,E(_A6),_A7,E(_zS),E(_Ad))));},_Aj=E(_Ac);if(!_Aj._){return new F(function(){return _Af(_Aj.a);});}else{return new F(function(){return _Af(0);});}}else{return new T5(0,(1+_A3|0)+_A5|0,E(_A6),_A7,E(new T5(0,(1+_A3|0)+_A9|0,E(_zY),_zZ,E(_A2),E(_A8))),E(_Ad));}}else{return E(_zW);}}else{return E(_zW);}}}else{return new T5(0,1+_A3|0,E(_zY),_zZ,E(_A2),E(_zS));}}else{var _Ak=E(_A1);if(!_Ak._){var _Al=_Ak.a,_Am=_Ak.b,_An=_Ak.c,_Ao=_Ak.e,_Ap=E(_Ak.d);if(!_Ap._){var _Aq=_Ap.a,_Ar=_Ap.b,_As=_Ap.c,_At=_Ap.d,_Au=E(_Ao);if(!_Au._){var _Av=_Au.a;if(_Aq>=(imul(2,_Av)|0)){var _Aw=function(_Ax){var _Ay=E(_zY),_Az=E(_Ap.e);return (_Az._==0)?new T5(0,1+_Al|0,E(_Ar),_As,E(new T5(0,1+_Ax|0,E(_Ay),_zZ,E(_zS),E(_At))),E(new T5(0,(1+_Av|0)+_Az.a|0,E(_Am),_An,E(_Az),E(_Au)))):new T5(0,1+_Al|0,E(_Ar),_As,E(new T5(0,1+_Ax|0,E(_Ay),_zZ,E(_zS),E(_At))),E(new T5(0,1+_Av|0,E(_Am),_An,E(_zS),E(_Au))));},_AA=E(_At);if(!_AA._){return new F(function(){return _Aw(_AA.a);});}else{return new F(function(){return _Aw(0);});}}else{return new T5(0,1+_Al|0,E(_Am),_An,E(new T5(0,1+_Aq|0,E(_zY),_zZ,E(_zS),E(_Ap))),E(_Au));}}else{return new T5(0,3,E(_Ar),_As,E(new T5(0,1,E(_zY),_zZ,E(_zS),E(_zS))),E(new T5(0,1,E(_Am),_An,E(_zS),E(_zS))));}}else{var _AB=E(_Ao);return (_AB._==0)?new T5(0,3,E(_Am),_An,E(new T5(0,1,E(_zY),_zZ,E(_zS),E(_zS))),E(_AB)):new T5(0,2,E(_zY),_zZ,E(_zS),E(_Ak));}}else{return new T5(0,1,E(_zY),_zZ,E(_zS),E(_zS));}}},_AC=function(_AD,_AE){return new T5(0,1,E(_AD),_AE,E(_zS),E(_zS));},_AF=function(_AG,_AH,_AI){var _AJ=E(_AI);if(!_AJ._){return new F(function(){return _zX(_AJ.b,_AJ.c,_AJ.d,B(_AF(_AG,_AH,_AJ.e)));});}else{return new F(function(){return _AC(_AG,_AH);});}},_AK=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_AL=function(_AM){return new F(function(){return err(_AK);});},_AN=new T(function(){return B(_AL(_));}),_AO=function(_AP,_AQ,_AR,_AS){var _AT=E(_AS);if(!_AT._){var _AU=_AT.a,_AV=E(_AR);if(!_AV._){var _AW=_AV.a,_AX=_AV.b,_AY=_AV.c;if(_AW<=(imul(3,_AU)|0)){return new T5(0,(1+_AW|0)+_AU|0,E(_AP),_AQ,E(_AV),E(_AT));}else{var _AZ=E(_AV.d);if(!_AZ._){var _B0=_AZ.a,_B1=E(_AV.e);if(!_B1._){var _B2=_B1.a,_B3=_B1.b,_B4=_B1.c,_B5=_B1.d;if(_B2>=(imul(2,_B0)|0)){var _B6=function(_B7){var _B8=E(_B1.e);return (_B8._==0)?new T5(0,(1+_AW|0)+_AU|0,E(_B3),_B4,E(new T5(0,(1+_B0|0)+_B7|0,E(_AX),_AY,E(_AZ),E(_B5))),E(new T5(0,(1+_AU|0)+_B8.a|0,E(_AP),_AQ,E(_B8),E(_AT)))):new T5(0,(1+_AW|0)+_AU|0,E(_B3),_B4,E(new T5(0,(1+_B0|0)+_B7|0,E(_AX),_AY,E(_AZ),E(_B5))),E(new T5(0,1+_AU|0,E(_AP),_AQ,E(_zS),E(_AT))));},_B9=E(_B5);if(!_B9._){return new F(function(){return _B6(_B9.a);});}else{return new F(function(){return _B6(0);});}}else{return new T5(0,(1+_AW|0)+_AU|0,E(_AX),_AY,E(_AZ),E(new T5(0,(1+_AU|0)+_B2|0,E(_AP),_AQ,E(_B1),E(_AT))));}}else{return E(_AN);}}else{return E(_AN);}}}else{return new T5(0,1+_AU|0,E(_AP),_AQ,E(_zS),E(_AT));}}else{var _Ba=E(_AR);if(!_Ba._){var _Bb=_Ba.a,_Bc=_Ba.b,_Bd=_Ba.c,_Be=_Ba.e,_Bf=E(_Ba.d);if(!_Bf._){var _Bg=_Bf.a,_Bh=E(_Be);if(!_Bh._){var _Bi=_Bh.a,_Bj=_Bh.b,_Bk=_Bh.c,_Bl=_Bh.d;if(_Bi>=(imul(2,_Bg)|0)){var _Bm=function(_Bn){var _Bo=E(_Bh.e);return (_Bo._==0)?new T5(0,1+_Bb|0,E(_Bj),_Bk,E(new T5(0,(1+_Bg|0)+_Bn|0,E(_Bc),_Bd,E(_Bf),E(_Bl))),E(new T5(0,1+_Bo.a|0,E(_AP),_AQ,E(_Bo),E(_zS)))):new T5(0,1+_Bb|0,E(_Bj),_Bk,E(new T5(0,(1+_Bg|0)+_Bn|0,E(_Bc),_Bd,E(_Bf),E(_Bl))),E(new T5(0,1,E(_AP),_AQ,E(_zS),E(_zS))));},_Bp=E(_Bl);if(!_Bp._){return new F(function(){return _Bm(_Bp.a);});}else{return new F(function(){return _Bm(0);});}}else{return new T5(0,1+_Bb|0,E(_Bc),_Bd,E(_Bf),E(new T5(0,1+_Bi|0,E(_AP),_AQ,E(_Bh),E(_zS))));}}else{return new T5(0,3,E(_Bc),_Bd,E(_Bf),E(new T5(0,1,E(_AP),_AQ,E(_zS),E(_zS))));}}else{var _Bq=E(_Be);return (_Bq._==0)?new T5(0,3,E(_Bq.b),_Bq.c,E(new T5(0,1,E(_Bc),_Bd,E(_zS),E(_zS))),E(new T5(0,1,E(_AP),_AQ,E(_zS),E(_zS)))):new T5(0,2,E(_AP),_AQ,E(_Ba),E(_zS));}}else{return new T5(0,1,E(_AP),_AQ,E(_zS),E(_zS));}}},_Br=function(_Bs,_Bt,_Bu){var _Bv=E(_Bu);if(!_Bv._){return new F(function(){return _AO(_Bv.b,_Bv.c,B(_Br(_Bs,_Bt,_Bv.d)),_Bv.e);});}else{return new F(function(){return _AC(_Bs,_Bt);});}},_Bw=function(_Bx,_By,_Bz,_BA,_BB,_BC,_BD){return new F(function(){return _AO(_BA,_BB,B(_Br(_Bx,_By,_BC)),_BD);});},_BE=function(_BF,_BG,_BH,_BI,_BJ,_BK,_BL,_BM){var _BN=E(_BH);if(!_BN._){var _BO=_BN.a,_BP=_BN.b,_BQ=_BN.c,_BR=_BN.d,_BS=_BN.e;if((imul(3,_BO)|0)>=_BI){if((imul(3,_BI)|0)>=_BO){return new T5(0,(_BO+_BI|0)+1|0,E(_BF),_BG,E(_BN),E(new T5(0,_BI,E(_BJ),_BK,E(_BL),E(_BM))));}else{return new F(function(){return _zX(_BP,_BQ,_BR,B(_BE(_BF,_BG,_BS,_BI,_BJ,_BK,_BL,_BM)));});}}else{return new F(function(){return _AO(_BJ,_BK,B(_BT(_BF,_BG,_BO,_BP,_BQ,_BR,_BS,_BL)),_BM);});}}else{return new F(function(){return _Bw(_BF,_BG,_BI,_BJ,_BK,_BL,_BM);});}},_BT=function(_BU,_BV,_BW,_BX,_BY,_BZ,_C0,_C1){var _C2=E(_C1);if(!_C2._){var _C3=_C2.a,_C4=_C2.b,_C5=_C2.c,_C6=_C2.d,_C7=_C2.e;if((imul(3,_BW)|0)>=_C3){if((imul(3,_C3)|0)>=_BW){return new T5(0,(_BW+_C3|0)+1|0,E(_BU),_BV,E(new T5(0,_BW,E(_BX),_BY,E(_BZ),E(_C0))),E(_C2));}else{return new F(function(){return _zX(_BX,_BY,_BZ,B(_BE(_BU,_BV,_C0,_C3,_C4,_C5,_C6,_C7)));});}}else{return new F(function(){return _AO(_C4,_C5,B(_BT(_BU,_BV,_BW,_BX,_BY,_BZ,_C0,_C6)),_C7);});}}else{return new F(function(){return _AF(_BU,_BV,new T5(0,_BW,E(_BX),_BY,E(_BZ),E(_C0)));});}},_C8=function(_C9,_Ca,_Cb,_Cc){var _Cd=E(_Cb);if(!_Cd._){var _Ce=_Cd.a,_Cf=_Cd.b,_Cg=_Cd.c,_Ch=_Cd.d,_Ci=_Cd.e,_Cj=E(_Cc);if(!_Cj._){var _Ck=_Cj.a,_Cl=_Cj.b,_Cm=_Cj.c,_Cn=_Cj.d,_Co=_Cj.e;if((imul(3,_Ce)|0)>=_Ck){if((imul(3,_Ck)|0)>=_Ce){return new T5(0,(_Ce+_Ck|0)+1|0,E(_C9),_Ca,E(_Cd),E(_Cj));}else{return new F(function(){return _zX(_Cf,_Cg,_Ch,B(_BE(_C9,_Ca,_Ci,_Ck,_Cl,_Cm,_Cn,_Co)));});}}else{return new F(function(){return _AO(_Cl,_Cm,B(_BT(_C9,_Ca,_Ce,_Cf,_Cg,_Ch,_Ci,_Cn)),_Co);});}}else{return new F(function(){return _AF(_C9,_Ca,_Cd);});}}else{return new F(function(){return _Br(_C9,_Ca,_Cc);});}},_Cp=function(_Cq,_Cr,_Cs,_Ct,_Cu){var _Cv=E(_Cq);if(_Cv==1){var _Cw=E(_Cu);if(!_Cw._){return new T3(0,new T5(0,1,E(new T2(0,_Cr,_Cs)),_Ct,E(_zS),E(_zS)),_23,_23);}else{var _Cx=E(E(_Cw.a).a),_Cy=E(_Cr),_Cz=E(_Cx.a);return (_Cy>=_Cz)?(_Cy!=_Cz)?new T3(0,new T5(0,1,E(new T2(0,_Cy,_Cs)),_Ct,E(_zS),E(_zS)),_23,_Cw):(_Cs<E(_Cx.b))?new T3(0,new T5(0,1,E(new T2(0,_Cy,_Cs)),_Ct,E(_zS),E(_zS)),_Cw,_23):new T3(0,new T5(0,1,E(new T2(0,_Cy,_Cs)),_Ct,E(_zS),E(_zS)),_23,_Cw):new T3(0,new T5(0,1,E(new T2(0,_Cy,_Cs)),_Ct,E(_zS),E(_zS)),_Cw,_23);}}else{var _CA=B(_Cp(_Cv>>1,_Cr,_Cs,_Ct,_Cu)),_CB=_CA.a,_CC=_CA.c,_CD=E(_CA.b);if(!_CD._){return new T3(0,_CB,_23,_CC);}else{var _CE=E(_CD.a),_CF=_CE.a,_CG=_CE.b,_CH=E(_CD.b);if(!_CH._){return new T3(0,new T(function(){return B(_AF(_CF,_CG,_CB));}),_23,_CC);}else{var _CI=_CH.b,_CJ=E(_CH.a),_CK=_CJ.b,_CL=E(_CF),_CM=E(_CJ.a),_CN=_CM.b,_CO=E(_CL.a),_CP=E(_CM.a);if(_CO>=_CP){if(_CO!=_CP){return new T3(0,_CB,_23,_CD);}else{var _CQ=E(_CN);if(E(_CL.b)<_CQ){var _CR=B(_Cp(_Cv>>1,_CP,_CQ,_CK,_CI));return new T3(0,new T(function(){return B(_C8(_CL,_CG,_CB,_CR.a));}),_CR.b,_CR.c);}else{return new T3(0,_CB,_23,_CD);}}}else{var _CS=B(_CT(_Cv>>1,_CP,_CN,_CK,_CI));return new T3(0,new T(function(){return B(_C8(_CL,_CG,_CB,_CS.a));}),_CS.b,_CS.c);}}}}},_CT=function(_CU,_CV,_CW,_CX,_CY){var _CZ=E(_CU);if(_CZ==1){var _D0=E(_CY);if(!_D0._){return new T3(0,new T5(0,1,E(new T2(0,_CV,_CW)),_CX,E(_zS),E(_zS)),_23,_23);}else{var _D1=E(E(_D0.a).a),_D2=E(_CV),_D3=E(_D1.a);if(_D2>=_D3){if(_D2!=_D3){return new T3(0,new T5(0,1,E(new T2(0,_D2,_CW)),_CX,E(_zS),E(_zS)),_23,_D0);}else{var _D4=E(_CW);return (_D4<E(_D1.b))?new T3(0,new T5(0,1,E(new T2(0,_D2,_D4)),_CX,E(_zS),E(_zS)),_D0,_23):new T3(0,new T5(0,1,E(new T2(0,_D2,_D4)),_CX,E(_zS),E(_zS)),_23,_D0);}}else{return new T3(0,new T5(0,1,E(new T2(0,_D2,_CW)),_CX,E(_zS),E(_zS)),_D0,_23);}}}else{var _D5=B(_CT(_CZ>>1,_CV,_CW,_CX,_CY)),_D6=_D5.a,_D7=_D5.c,_D8=E(_D5.b);if(!_D8._){return new T3(0,_D6,_23,_D7);}else{var _D9=E(_D8.a),_Da=_D9.a,_Db=_D9.b,_Dc=E(_D8.b);if(!_Dc._){return new T3(0,new T(function(){return B(_AF(_Da,_Db,_D6));}),_23,_D7);}else{var _Dd=_Dc.b,_De=E(_Dc.a),_Df=_De.b,_Dg=E(_Da),_Dh=E(_De.a),_Di=_Dh.b,_Dj=E(_Dg.a),_Dk=E(_Dh.a);if(_Dj>=_Dk){if(_Dj!=_Dk){return new T3(0,_D6,_23,_D8);}else{var _Dl=E(_Di);if(E(_Dg.b)<_Dl){var _Dm=B(_Cp(_CZ>>1,_Dk,_Dl,_Df,_Dd));return new T3(0,new T(function(){return B(_C8(_Dg,_Db,_D6,_Dm.a));}),_Dm.b,_Dm.c);}else{return new T3(0,_D6,_23,_D8);}}}else{var _Dn=B(_CT(_CZ>>1,_Dk,_Di,_Df,_Dd));return new T3(0,new T(function(){return B(_C8(_Dg,_Db,_D6,_Dn.a));}),_Dn.b,_Dn.c);}}}}},_Do=function(_Dp,_Dq,_Dr,_Ds,_Dt){var _Du=E(_Dt);if(!_Du._){var _Dv=_Du.c,_Dw=_Du.d,_Dx=_Du.e,_Dy=E(_Du.b),_Dz=E(_Dy.a);if(_Dp>=_Dz){if(_Dp!=_Dz){return new F(function(){return _zX(_Dy,_Dv,_Dw,B(_Do(_Dp,_,_Dr,_Ds,_Dx)));});}else{var _DA=E(_Dy.b);if(_Dr>=_DA){if(_Dr!=_DA){return new F(function(){return _zX(_Dy,_Dv,_Dw,B(_Do(_Dp,_,_Dr,_Ds,_Dx)));});}else{return new T5(0,_Du.a,E(new T2(0,_Dp,_Dr)),_Ds,E(_Dw),E(_Dx));}}else{return new F(function(){return _AO(_Dy,_Dv,B(_Do(_Dp,_,_Dr,_Ds,_Dw)),_Dx);});}}}else{return new F(function(){return _AO(_Dy,_Dv,B(_Do(_Dp,_,_Dr,_Ds,_Dw)),_Dx);});}}else{return new T5(0,1,E(new T2(0,_Dp,_Dr)),_Ds,E(_zS),E(_zS));}},_DB=function(_DC,_DD,_DE,_DF,_DG){var _DH=E(_DG);if(!_DH._){var _DI=_DH.c,_DJ=_DH.d,_DK=_DH.e,_DL=E(_DH.b),_DM=E(_DL.a);if(_DC>=_DM){if(_DC!=_DM){return new F(function(){return _zX(_DL,_DI,_DJ,B(_DB(_DC,_,_DE,_DF,_DK)));});}else{var _DN=E(_DE),_DO=E(_DL.b);if(_DN>=_DO){if(_DN!=_DO){return new F(function(){return _zX(_DL,_DI,_DJ,B(_Do(_DC,_,_DN,_DF,_DK)));});}else{return new T5(0,_DH.a,E(new T2(0,_DC,_DN)),_DF,E(_DJ),E(_DK));}}else{return new F(function(){return _AO(_DL,_DI,B(_Do(_DC,_,_DN,_DF,_DJ)),_DK);});}}}else{return new F(function(){return _AO(_DL,_DI,B(_DB(_DC,_,_DE,_DF,_DJ)),_DK);});}}else{return new T5(0,1,E(new T2(0,_DC,_DE)),_DF,E(_zS),E(_zS));}},_DP=function(_DQ,_DR,_DS,_DT){var _DU=E(_DT);if(!_DU._){var _DV=_DU.c,_DW=_DU.d,_DX=_DU.e,_DY=E(_DU.b),_DZ=E(_DQ),_E0=E(_DY.a);if(_DZ>=_E0){if(_DZ!=_E0){return new F(function(){return _zX(_DY,_DV,_DW,B(_DB(_DZ,_,_DR,_DS,_DX)));});}else{var _E1=E(_DR),_E2=E(_DY.b);if(_E1>=_E2){if(_E1!=_E2){return new F(function(){return _zX(_DY,_DV,_DW,B(_Do(_DZ,_,_E1,_DS,_DX)));});}else{return new T5(0,_DU.a,E(new T2(0,_DZ,_E1)),_DS,E(_DW),E(_DX));}}else{return new F(function(){return _AO(_DY,_DV,B(_Do(_DZ,_,_E1,_DS,_DW)),_DX);});}}}else{return new F(function(){return _AO(_DY,_DV,B(_DB(_DZ,_,_DR,_DS,_DW)),_DX);});}}else{return new T5(0,1,E(new T2(0,_DQ,_DR)),_DS,E(_zS),E(_zS));}},_E3=function(_E4,_E5){while(1){var _E6=E(_E5);if(!_E6._){return E(_E4);}else{var _E7=E(_E6.a),_E8=E(_E7.a),_E9=B(_DP(_E8.a,_E8.b,_E7.b,_E4));_E4=_E9;_E5=_E6.b;continue;}}},_Ea=function(_Eb,_Ec,_Ed,_Ee,_Ef){return new F(function(){return _E3(B(_DP(_Ec,_Ed,_Ee,_Eb)),_Ef);});},_Eg=function(_Eh,_Ei,_Ej){var _Ek=E(_Ei),_El=E(_Ek.a);return new F(function(){return _E3(B(_DP(_El.a,_El.b,_Ek.b,_Eh)),_Ej);});},_Em=function(_En,_Eo,_Ep){var _Eq=E(_Ep);if(!_Eq._){return E(_Eo);}else{var _Er=E(_Eq.a),_Es=_Er.a,_Et=_Er.b,_Eu=E(_Eq.b);if(!_Eu._){return new F(function(){return _AF(_Es,_Et,_Eo);});}else{var _Ev=E(_Eu.a),_Ew=E(_Es),_Ex=_Ew.b,_Ey=E(_Ev.a),_Ez=_Ey.b,_EA=E(_Ew.a),_EB=E(_Ey.a),_EC=function(_ED){var _EE=B(_CT(_En,_EB,_Ez,_Ev.b,_Eu.b)),_EF=_EE.a,_EG=E(_EE.c);if(!_EG._){return new F(function(){return _Em(_En<<1,B(_C8(_Ew,_Et,_Eo,_EF)),_EE.b);});}else{return new F(function(){return _Eg(B(_C8(_Ew,_Et,_Eo,_EF)),_EG.a,_EG.b);});}};if(_EA>=_EB){if(_EA!=_EB){return new F(function(){return _Ea(_Eo,_EA,_Ex,_Et,_Eu);});}else{var _EH=E(_Ex);if(_EH<E(_Ez)){return new F(function(){return _EC(_);});}else{return new F(function(){return _Ea(_Eo,_EA,_EH,_Et,_Eu);});}}}else{return new F(function(){return _EC(_);});}}}},_EI=function(_EJ,_EK,_EL,_EM,_EN,_EO){var _EP=E(_EO);if(!_EP._){return new F(function(){return _AF(new T2(0,_EL,_EM),_EN,_EK);});}else{var _EQ=E(_EP.a),_ER=E(_EQ.a),_ES=_ER.b,_ET=E(_EL),_EU=E(_ER.a),_EV=function(_EW){var _EX=B(_CT(_EJ,_EU,_ES,_EQ.b,_EP.b)),_EY=_EX.a,_EZ=E(_EX.c);if(!_EZ._){return new F(function(){return _Em(_EJ<<1,B(_C8(new T2(0,_ET,_EM),_EN,_EK,_EY)),_EX.b);});}else{return new F(function(){return _Eg(B(_C8(new T2(0,_ET,_EM),_EN,_EK,_EY)),_EZ.a,_EZ.b);});}};if(_ET>=_EU){if(_ET!=_EU){return new F(function(){return _Ea(_EK,_ET,_EM,_EN,_EP);});}else{if(_EM<E(_ES)){return new F(function(){return _EV(_);});}else{return new F(function(){return _Ea(_EK,_ET,_EM,_EN,_EP);});}}}else{return new F(function(){return _EV(_);});}}},_F0=function(_F1,_F2,_F3,_F4,_F5,_F6){var _F7=E(_F6);if(!_F7._){return new F(function(){return _AF(new T2(0,_F3,_F4),_F5,_F2);});}else{var _F8=E(_F7.a),_F9=E(_F8.a),_Fa=_F9.b,_Fb=E(_F3),_Fc=E(_F9.a),_Fd=function(_Fe){var _Ff=B(_CT(_F1,_Fc,_Fa,_F8.b,_F7.b)),_Fg=_Ff.a,_Fh=E(_Ff.c);if(!_Fh._){return new F(function(){return _Em(_F1<<1,B(_C8(new T2(0,_Fb,_F4),_F5,_F2,_Fg)),_Ff.b);});}else{return new F(function(){return _Eg(B(_C8(new T2(0,_Fb,_F4),_F5,_F2,_Fg)),_Fh.a,_Fh.b);});}};if(_Fb>=_Fc){if(_Fb!=_Fc){return new F(function(){return _Ea(_F2,_Fb,_F4,_F5,_F7);});}else{var _Fi=E(_F4);if(_Fi<E(_Fa)){return new F(function(){return _Fd(_);});}else{return new F(function(){return _Ea(_F2,_Fb,_Fi,_F5,_F7);});}}}else{return new F(function(){return _Fd(_);});}}},_Fj=function(_Fk){var _Fl=E(_Fk);if(!_Fl._){return new T0(1);}else{var _Fm=E(_Fl.a),_Fn=_Fm.a,_Fo=_Fm.b,_Fp=E(_Fl.b);if(!_Fp._){return new T5(0,1,E(_Fn),_Fo,E(_zS),E(_zS));}else{var _Fq=_Fp.b,_Fr=E(_Fp.a),_Fs=_Fr.b,_Ft=E(_Fn),_Fu=E(_Fr.a),_Fv=_Fu.b,_Fw=E(_Ft.a),_Fx=E(_Fu.a);if(_Fw>=_Fx){if(_Fw!=_Fx){return new F(function(){return _Ea(new T5(0,1,E(_Ft),_Fo,E(_zS),E(_zS)),_Fx,_Fv,_Fs,_Fq);});}else{var _Fy=E(_Fv);if(E(_Ft.b)<_Fy){return new F(function(){return _EI(1,new T5(0,1,E(_Ft),_Fo,E(_zS),E(_zS)),_Fx,_Fy,_Fs,_Fq);});}else{return new F(function(){return _Ea(new T5(0,1,E(_Ft),_Fo,E(_zS),E(_zS)),_Fx,_Fy,_Fs,_Fq);});}}}else{return new F(function(){return _F0(1,new T5(0,1,E(_Ft),_Fo,E(_zS),E(_zS)),_Fx,_Fv,_Fs,_Fq);});}}}},_Fz=function(_FA,_FB,_FC,_FD,_FE){var _FF=E(_FA);if(_FF==1){var _FG=E(_FE);if(!_FG._){return new T3(0,new T5(0,1,E(new T2(0,_FB,_FC)),_FD,E(_zS),E(_zS)),_23,_23);}else{var _FH=E(E(_FG.a).a),_FI=E(_FB),_FJ=E(_FH.a);return (_FI>=_FJ)?(_FI!=_FJ)?new T3(0,new T5(0,1,E(new T2(0,_FI,_FC)),_FD,E(_zS),E(_zS)),_23,_FG):(_FC<E(_FH.b))?new T3(0,new T5(0,1,E(new T2(0,_FI,_FC)),_FD,E(_zS),E(_zS)),_FG,_23):new T3(0,new T5(0,1,E(new T2(0,_FI,_FC)),_FD,E(_zS),E(_zS)),_23,_FG):new T3(0,new T5(0,1,E(new T2(0,_FI,_FC)),_FD,E(_zS),E(_zS)),_FG,_23);}}else{var _FK=B(_Fz(_FF>>1,_FB,_FC,_FD,_FE)),_FL=_FK.a,_FM=_FK.c,_FN=E(_FK.b);if(!_FN._){return new T3(0,_FL,_23,_FM);}else{var _FO=E(_FN.a),_FP=_FO.a,_FQ=_FO.b,_FR=E(_FN.b);if(!_FR._){return new T3(0,new T(function(){return B(_AF(_FP,_FQ,_FL));}),_23,_FM);}else{var _FS=_FR.b,_FT=E(_FR.a),_FU=_FT.b,_FV=E(_FP),_FW=E(_FT.a),_FX=_FW.b,_FY=E(_FV.a),_FZ=E(_FW.a);if(_FY>=_FZ){if(_FY!=_FZ){return new T3(0,_FL,_23,_FN);}else{var _G0=E(_FX);if(E(_FV.b)<_G0){var _G1=B(_Fz(_FF>>1,_FZ,_G0,_FU,_FS));return new T3(0,new T(function(){return B(_C8(_FV,_FQ,_FL,_G1.a));}),_G1.b,_G1.c);}else{return new T3(0,_FL,_23,_FN);}}}else{var _G2=B(_G3(_FF>>1,_FZ,_FX,_FU,_FS));return new T3(0,new T(function(){return B(_C8(_FV,_FQ,_FL,_G2.a));}),_G2.b,_G2.c);}}}}},_G3=function(_G4,_G5,_G6,_G7,_G8){var _G9=E(_G4);if(_G9==1){var _Ga=E(_G8);if(!_Ga._){return new T3(0,new T5(0,1,E(new T2(0,_G5,_G6)),_G7,E(_zS),E(_zS)),_23,_23);}else{var _Gb=E(E(_Ga.a).a),_Gc=E(_G5),_Gd=E(_Gb.a);if(_Gc>=_Gd){if(_Gc!=_Gd){return new T3(0,new T5(0,1,E(new T2(0,_Gc,_G6)),_G7,E(_zS),E(_zS)),_23,_Ga);}else{var _Ge=E(_G6);return (_Ge<E(_Gb.b))?new T3(0,new T5(0,1,E(new T2(0,_Gc,_Ge)),_G7,E(_zS),E(_zS)),_Ga,_23):new T3(0,new T5(0,1,E(new T2(0,_Gc,_Ge)),_G7,E(_zS),E(_zS)),_23,_Ga);}}else{return new T3(0,new T5(0,1,E(new T2(0,_Gc,_G6)),_G7,E(_zS),E(_zS)),_Ga,_23);}}}else{var _Gf=B(_G3(_G9>>1,_G5,_G6,_G7,_G8)),_Gg=_Gf.a,_Gh=_Gf.c,_Gi=E(_Gf.b);if(!_Gi._){return new T3(0,_Gg,_23,_Gh);}else{var _Gj=E(_Gi.a),_Gk=_Gj.a,_Gl=_Gj.b,_Gm=E(_Gi.b);if(!_Gm._){return new T3(0,new T(function(){return B(_AF(_Gk,_Gl,_Gg));}),_23,_Gh);}else{var _Gn=_Gm.b,_Go=E(_Gm.a),_Gp=_Go.b,_Gq=E(_Gk),_Gr=E(_Go.a),_Gs=_Gr.b,_Gt=E(_Gq.a),_Gu=E(_Gr.a);if(_Gt>=_Gu){if(_Gt!=_Gu){return new T3(0,_Gg,_23,_Gi);}else{var _Gv=E(_Gs);if(E(_Gq.b)<_Gv){var _Gw=B(_Fz(_G9>>1,_Gu,_Gv,_Gp,_Gn));return new T3(0,new T(function(){return B(_C8(_Gq,_Gl,_Gg,_Gw.a));}),_Gw.b,_Gw.c);}else{return new T3(0,_Gg,_23,_Gi);}}}else{var _Gx=B(_G3(_G9>>1,_Gu,_Gs,_Gp,_Gn));return new T3(0,new T(function(){return B(_C8(_Gq,_Gl,_Gg,_Gx.a));}),_Gx.b,_Gx.c);}}}}},_Gy=function(_Gz,_GA,_GB,_GC,_GD){var _GE=E(_GD);if(!_GE._){var _GF=_GE.c,_GG=_GE.d,_GH=_GE.e,_GI=E(_GE.b),_GJ=E(_GI.a);if(_Gz>=_GJ){if(_Gz!=_GJ){return new F(function(){return _zX(_GI,_GF,_GG,B(_Gy(_Gz,_,_GB,_GC,_GH)));});}else{var _GK=E(_GI.b);if(_GB>=_GK){if(_GB!=_GK){return new F(function(){return _zX(_GI,_GF,_GG,B(_Gy(_Gz,_,_GB,_GC,_GH)));});}else{return new T5(0,_GE.a,E(new T2(0,_Gz,_GB)),_GC,E(_GG),E(_GH));}}else{return new F(function(){return _AO(_GI,_GF,B(_Gy(_Gz,_,_GB,_GC,_GG)),_GH);});}}}else{return new F(function(){return _AO(_GI,_GF,B(_Gy(_Gz,_,_GB,_GC,_GG)),_GH);});}}else{return new T5(0,1,E(new T2(0,_Gz,_GB)),_GC,E(_zS),E(_zS));}},_GL=function(_GM,_GN,_GO,_GP,_GQ){var _GR=E(_GQ);if(!_GR._){var _GS=_GR.c,_GT=_GR.d,_GU=_GR.e,_GV=E(_GR.b),_GW=E(_GV.a);if(_GM>=_GW){if(_GM!=_GW){return new F(function(){return _zX(_GV,_GS,_GT,B(_GL(_GM,_,_GO,_GP,_GU)));});}else{var _GX=E(_GO),_GY=E(_GV.b);if(_GX>=_GY){if(_GX!=_GY){return new F(function(){return _zX(_GV,_GS,_GT,B(_Gy(_GM,_,_GX,_GP,_GU)));});}else{return new T5(0,_GR.a,E(new T2(0,_GM,_GX)),_GP,E(_GT),E(_GU));}}else{return new F(function(){return _AO(_GV,_GS,B(_Gy(_GM,_,_GX,_GP,_GT)),_GU);});}}}else{return new F(function(){return _AO(_GV,_GS,B(_GL(_GM,_,_GO,_GP,_GT)),_GU);});}}else{return new T5(0,1,E(new T2(0,_GM,_GO)),_GP,E(_zS),E(_zS));}},_GZ=function(_H0,_H1,_H2,_H3){var _H4=E(_H3);if(!_H4._){var _H5=_H4.c,_H6=_H4.d,_H7=_H4.e,_H8=E(_H4.b),_H9=E(_H0),_Ha=E(_H8.a);if(_H9>=_Ha){if(_H9!=_Ha){return new F(function(){return _zX(_H8,_H5,_H6,B(_GL(_H9,_,_H1,_H2,_H7)));});}else{var _Hb=E(_H1),_Hc=E(_H8.b);if(_Hb>=_Hc){if(_Hb!=_Hc){return new F(function(){return _zX(_H8,_H5,_H6,B(_Gy(_H9,_,_Hb,_H2,_H7)));});}else{return new T5(0,_H4.a,E(new T2(0,_H9,_Hb)),_H2,E(_H6),E(_H7));}}else{return new F(function(){return _AO(_H8,_H5,B(_Gy(_H9,_,_Hb,_H2,_H6)),_H7);});}}}else{return new F(function(){return _AO(_H8,_H5,B(_GL(_H9,_,_H1,_H2,_H6)),_H7);});}}else{return new T5(0,1,E(new T2(0,_H0,_H1)),_H2,E(_zS),E(_zS));}},_Hd=function(_He,_Hf){while(1){var _Hg=E(_Hf);if(!_Hg._){return E(_He);}else{var _Hh=E(_Hg.a),_Hi=E(_Hh.a),_Hj=B(_GZ(_Hi.a,_Hi.b,_Hh.b,_He));_He=_Hj;_Hf=_Hg.b;continue;}}},_Hk=function(_Hl,_Hm,_Hn,_Ho,_Hp){return new F(function(){return _Hd(B(_GZ(_Hm,_Hn,_Ho,_Hl)),_Hp);});},_Hq=function(_Hr,_Hs,_Ht){var _Hu=E(_Hs),_Hv=E(_Hu.a);return new F(function(){return _Hd(B(_GZ(_Hv.a,_Hv.b,_Hu.b,_Hr)),_Ht);});},_Hw=function(_Hx,_Hy,_Hz){var _HA=E(_Hz);if(!_HA._){return E(_Hy);}else{var _HB=E(_HA.a),_HC=_HB.a,_HD=_HB.b,_HE=E(_HA.b);if(!_HE._){return new F(function(){return _AF(_HC,_HD,_Hy);});}else{var _HF=E(_HE.a),_HG=E(_HC),_HH=_HG.b,_HI=E(_HF.a),_HJ=_HI.b,_HK=E(_HG.a),_HL=E(_HI.a),_HM=function(_HN){var _HO=B(_G3(_Hx,_HL,_HJ,_HF.b,_HE.b)),_HP=_HO.a,_HQ=E(_HO.c);if(!_HQ._){return new F(function(){return _Hw(_Hx<<1,B(_C8(_HG,_HD,_Hy,_HP)),_HO.b);});}else{return new F(function(){return _Hq(B(_C8(_HG,_HD,_Hy,_HP)),_HQ.a,_HQ.b);});}};if(_HK>=_HL){if(_HK!=_HL){return new F(function(){return _Hk(_Hy,_HK,_HH,_HD,_HE);});}else{var _HR=E(_HH);if(_HR<E(_HJ)){return new F(function(){return _HM(_);});}else{return new F(function(){return _Hk(_Hy,_HK,_HR,_HD,_HE);});}}}else{return new F(function(){return _HM(_);});}}}},_HS=function(_HT,_HU,_HV,_HW,_HX,_HY){var _HZ=E(_HY);if(!_HZ._){return new F(function(){return _AF(new T2(0,_HV,_HW),_HX,_HU);});}else{var _I0=E(_HZ.a),_I1=E(_I0.a),_I2=_I1.b,_I3=E(_HV),_I4=E(_I1.a),_I5=function(_I6){var _I7=B(_G3(_HT,_I4,_I2,_I0.b,_HZ.b)),_I8=_I7.a,_I9=E(_I7.c);if(!_I9._){return new F(function(){return _Hw(_HT<<1,B(_C8(new T2(0,_I3,_HW),_HX,_HU,_I8)),_I7.b);});}else{return new F(function(){return _Hq(B(_C8(new T2(0,_I3,_HW),_HX,_HU,_I8)),_I9.a,_I9.b);});}};if(_I3>=_I4){if(_I3!=_I4){return new F(function(){return _Hk(_HU,_I3,_HW,_HX,_HZ);});}else{var _Ia=E(_HW);if(_Ia<E(_I2)){return new F(function(){return _I5(_);});}else{return new F(function(){return _Hk(_HU,_I3,_Ia,_HX,_HZ);});}}}else{return new F(function(){return _I5(_);});}}},_Ib=function(_Ic,_Id,_Ie,_If,_Ig,_Ih){var _Ii=E(_Ih);if(!_Ii._){return new F(function(){return _AF(new T2(0,_Ie,_If),_Ig,_Id);});}else{var _Ij=E(_Ii.a),_Ik=E(_Ij.a),_Il=_Ik.b,_Im=E(_Ie),_In=E(_Ik.a),_Io=function(_Ip){var _Iq=B(_G3(_Ic,_In,_Il,_Ij.b,_Ii.b)),_Ir=_Iq.a,_Is=E(_Iq.c);if(!_Is._){return new F(function(){return _Hw(_Ic<<1,B(_C8(new T2(0,_Im,_If),_Ig,_Id,_Ir)),_Iq.b);});}else{return new F(function(){return _Hq(B(_C8(new T2(0,_Im,_If),_Ig,_Id,_Ir)),_Is.a,_Is.b);});}};if(_Im>=_In){if(_Im!=_In){return new F(function(){return _Hk(_Id,_Im,_If,_Ig,_Ii);});}else{if(_If<E(_Il)){return new F(function(){return _Io(_);});}else{return new F(function(){return _Hk(_Id,_Im,_If,_Ig,_Ii);});}}}else{return new F(function(){return _Io(_);});}}},_It=function(_Iu){var _Iv=E(_Iu);if(!_Iv._){return new T0(1);}else{var _Iw=E(_Iv.a),_Ix=_Iw.a,_Iy=_Iw.b,_Iz=E(_Iv.b);if(!_Iz._){return new T5(0,1,E(_Ix),_Iy,E(_zS),E(_zS));}else{var _IA=_Iz.b,_IB=E(_Iz.a),_IC=_IB.b,_ID=E(_Ix),_IE=E(_IB.a),_IF=_IE.b,_IG=E(_ID.a),_IH=E(_IE.a);if(_IG>=_IH){if(_IG!=_IH){return new F(function(){return _Hk(new T5(0,1,E(_ID),_Iy,E(_zS),E(_zS)),_IH,_IF,_IC,_IA);});}else{var _II=E(_IF);if(E(_ID.b)<_II){return new F(function(){return _Ib(1,new T5(0,1,E(_ID),_Iy,E(_zS),E(_zS)),_IH,_II,_IC,_IA);});}else{return new F(function(){return _Hk(new T5(0,1,E(_ID),_Iy,E(_zS),E(_zS)),_IH,_II,_IC,_IA);});}}}else{return new F(function(){return _HS(1,new T5(0,1,E(_ID),_Iy,E(_zS),E(_zS)),_IH,_IF,_IC,_IA);});}}}},_IJ=function(_IK,_IL){while(1){var _IM=B((function(_IN,_IO){var _IP=E(_IO);if(!_IP._){_IK=new T2(1,new T2(0,_IP.b,_IP.c),new T(function(){return B(_IJ(_IN,_IP.e));}));_IL=_IP.d;return __continue;}else{return E(_IN);}})(_IK,_IL));if(_IM!=__continue){return _IM;}}},_IQ=function(_IR,_IS,_IT){return new F(function(){return A1(_IR,new T2(1,_2I,new T(function(){return B(A1(_IS,_IT));})));});},_IU=new T(function(){return B(unCStr("CC "));}),_IV=function(_IW,_IX,_IY,_IZ,_J0,_J1){var _J2=function(_J3){var _J4=new T(function(){var _J5=new T(function(){return B(_d(11,E(_IZ),new T2(1,_w,new T(function(){return B(_d(11,E(_J0),_J3));}))));});return B(_d(11,E(_IY),new T2(1,_w,_J5)));});return new F(function(){return _o(11,_IX,new T2(1,_w,_J4));});};if(_IW<11){return new F(function(){return _3(_IU,new T(function(){return B(_J2(_J1));},1));});}else{var _J6=new T(function(){return B(_3(_IU,new T(function(){return B(_J2(new T2(1,_b,_J1)));},1)));});return new T2(1,_c,_J6);}},_J7=function(_J8,_J9){var _Ja=E(_J8);return new F(function(){return _IV(0,_Ja.a,_Ja.b,_Ja.c,_Ja.d,_J9);});},_Jb=new T(function(){return B(unCStr("RC "));}),_Jc=function(_Jd,_Je,_Jf,_Jg,_Jh){var _Ji=function(_Jj){var _Jk=new T(function(){var _Jl=new T(function(){return B(_d(11,E(_Jf),new T2(1,_w,new T(function(){return B(_d(11,E(_Jg),_Jj));}))));});return B(_o(11,_Je,new T2(1,_w,_Jl)));},1);return new F(function(){return _3(_Jb,_Jk);});};if(_Jd<11){return new F(function(){return _Ji(_Jh);});}else{return new T2(1,_c,new T(function(){return B(_Ji(new T2(1,_b,_Jh)));}));}},_Jm=function(_Jn,_Jo){var _Jp=E(_Jn);return new F(function(){return _Jc(0,_Jp.a,_Jp.b,_Jp.c,_Jo);});},_Jq=new T(function(){return B(unCStr(": empty list"));}),_Jr=new T(function(){return B(unCStr("Prelude."));}),_Js=function(_Jt){return new F(function(){return err(B(_3(_Jr,new T(function(){return B(_3(_Jt,_Jq));},1))));});},_Ju=new T(function(){return B(unCStr("foldr1"));}),_Jv=new T(function(){return B(_Js(_Ju));}),_Jw=function(_Jx,_Jy){var _Jz=E(_Jy);if(!_Jz._){return E(_Jv);}else{var _JA=_Jz.a,_JB=E(_Jz.b);if(!_JB._){return E(_JA);}else{return new F(function(){return A2(_Jx,_JA,new T(function(){return B(_Jw(_Jx,_JB));}));});}}},_JC=function(_JD,_JE,_JF){var _JG=new T(function(){var _JH=function(_JI){var _JJ=E(_JD),_JK=new T(function(){return B(A3(_Jw,_IQ,new T2(1,function(_JL){return new F(function(){return _1i(0,_JJ.a,_JL);});},new T2(1,function(_JM){return new F(function(){return _d(0,E(_JJ.b),_JM);});},_23)),new T2(1,_b,_JI)));});return new T2(1,_c,_JK);};return B(A3(_Jw,_IQ,new T2(1,_JH,new T2(1,function(_JN){return new F(function(){return _d(0,E(_JE),_JN);});},_23)),new T2(1,_b,_JF)));});return new T2(0,_c,_JG);},_JO=function(_JP,_JQ){var _JR=E(_JP),_JS=B(_JC(_JR.a,_JR.b,_JQ));return new T2(1,_JS.a,_JS.b);},_JT=function(_JU,_JV){return new F(function(){return _2L(_JO,_JU,_JV);});},_JW=function(_JX,_JY,_JZ){var _K0=new T(function(){var _K1=function(_K2){var _K3=E(_JX),_K4=new T(function(){return B(A3(_Jw,_IQ,new T2(1,function(_K5){return new F(function(){return _i(0,_K3.a,_K5);});},new T2(1,function(_K6){return new F(function(){return _d(0,E(_K3.b),_K6);});},_23)),new T2(1,_b,_K2)));});return new T2(1,_c,_K4);};return B(A3(_Jw,_IQ,new T2(1,_K1,new T2(1,function(_K7){return new F(function(){return _d(0,E(_JY),_K7);});},_23)),new T2(1,_b,_JZ)));});return new T2(0,_c,_K0);},_K8=function(_K9,_Ka){var _Kb=E(_K9),_Kc=B(_JW(_Kb.a,_Kb.b,_Ka));return new T2(1,_Kc.a,_Kc.b);},_Kd=function(_Ke,_Kf){return new F(function(){return _2L(_K8,_Ke,_Kf);});},_Kg=new T2(1,_b,_23),_Kh=function(_Ki,_Kj){while(1){var _Kk=B((function(_Kl,_Km){var _Kn=E(_Km);if(!_Kn._){_Ki=new T2(1,_Kn.b,new T(function(){return B(_Kh(_Kl,_Kn.d));}));_Kj=_Kn.c;return __continue;}else{return E(_Kl);}})(_Ki,_Kj));if(_Kk!=__continue){return _Kk;}}},_Ko=function(_Kp,_Kq,_Kr,_Ks){var _Kt=new T(function(){var _Ku=new T(function(){return B(_IJ(_23,_Ks));}),_Kv=new T(function(){return B(_IJ(_23,_Kr));}),_Kw=new T(function(){return B(_Kh(_23,_Kq));}),_Kx=new T(function(){return B(_Kh(_23,_Kp));});return B(A3(_Jw,_IQ,new T2(1,function(_Ky){return new F(function(){return _2L(_J7,_Kx,_Ky);});},new T2(1,function(_Kz){return new F(function(){return _2L(_Jm,_Kw,_Kz);});},new T2(1,function(_KA){return new F(function(){return _JT(_Kv,_KA);});},new T2(1,function(_KB){return new F(function(){return _Kd(_Ku,_KB);});},_23)))),_Kg));});return new T2(0,_c,_Kt);},_KC=new T(function(){return B(err(_24));}),_KD=new T(function(){return B(err(_2e));}),_KE=function(_KF){return new F(function(){return _gt(_gW,_KF);});},_KG=new T(function(){return B(unCStr("["));}),_KH=function(_KI,_KJ){var _KK=function(_KL,_KM){var _KN=new T(function(){return B(A1(_KM,_23));}),_KO=new T(function(){var _KP=function(_KQ){return new F(function(){return _KK(_8D,function(_KR){return new F(function(){return A1(_KM,new T2(1,_KQ,_KR));});});});};return B(A2(_KI,_fY,_KP));}),_KS=new T(function(){return B(_fr(function(_KT){var _KU=E(_KT);if(_KU._==2){var _KV=E(_KU.a);if(!_KV._){return new T0(2);}else{var _KW=_KV.b;switch(E(_KV.a)){case 44:return (E(_KW)._==0)?(!E(_KL))?new T0(2):E(_KO):new T0(2);case 93:return (E(_KW)._==0)?E(_KN):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_KX=function(_KY){return E(_KS);};return new T1(1,function(_KZ){return new F(function(){return A2(_e8,_KZ,_KX);});});},_L0=function(_L1,_L2){return new F(function(){return _L3(_L2);});},_L3=function(_L4){var _L5=new T(function(){var _L6=new T(function(){var _L7=new T(function(){var _L8=function(_L9){return new F(function(){return _KK(_8D,function(_La){return new F(function(){return A1(_L4,new T2(1,_L9,_La));});});});};return B(A2(_KI,_fY,_L8));});return B(_3M(B(_KK(_8C,_L4)),_L7));});return B(_fr(function(_Lb){var _Lc=E(_Lb);return (_Lc._==2)?(!B(_4r(_Lc.a,_KG)))?new T0(2):E(_L6):new T0(2);}));}),_Ld=function(_Le){return E(_L5);};return new F(function(){return _3M(new T1(1,function(_Lf){return new F(function(){return A2(_e8,_Lf,_Ld);});}),new T(function(){return new T1(1,B(_fZ(_L0,_L4)));}));});};return new F(function(){return _L3(_KJ);});},_Lg=function(_Lh,_Li){return new F(function(){return _KH(_KE,_Li);});},_Lj=new T(function(){return B(_KH(_KE,_4Y));}),_Lk=function(_KF){return new F(function(){return _3C(_Lj,_KF);});},_Ll=function(_Lm){var _Ln=new T(function(){return B(A3(_gt,_gW,_Lm,_4Y));});return function(_Lo){return new F(function(){return _3C(_Ln,_Lo);});};},_Lp=new T4(0,_Ll,_Lk,_KE,_Lg),_Lq=function(_Lr){return new F(function(){return _gi(_hI,_Lr);});},_Ls=function(_Lt,_Lu){return new F(function(){return _KH(_Lq,_Lu);});},_Lv=new T(function(){return B(_KH(_Lq,_4Y));}),_Lw=function(_Lr){return new F(function(){return _3C(_Lv,_Lr);});},_Lx=function(_Ly){var _Lz=new T(function(){return B(A3(_gi,_hI,_Ly,_4Y));});return function(_Lo){return new F(function(){return _3C(_Lz,_Lo);});};},_LA=new T4(0,_Lx,_Lw,_Lq,_Ls),_LB=new T(function(){return B(unCStr(","));}),_LC=function(_LD){return E(E(_LD).c);},_LE=function(_LF,_LG,_LH){var _LI=new T(function(){return B(_LC(_LG));}),_LJ=new T(function(){return B(A2(_LC,_LF,_LH));}),_LK=function(_LL){var _LM=function(_LN){var _LO=new T(function(){var _LP=new T(function(){return B(A2(_LI,_LH,function(_LQ){return new F(function(){return A1(_LL,new T2(0,_LN,_LQ));});}));});return B(_fr(function(_LR){var _LS=E(_LR);return (_LS._==2)?(!B(_4r(_LS.a,_LB)))?new T0(2):E(_LP):new T0(2);}));}),_LT=function(_LU){return E(_LO);};return new T1(1,function(_LV){return new F(function(){return A2(_e8,_LV,_LT);});});};return new F(function(){return A1(_LJ,_LM);});};return E(_LK);},_LW=function(_LX,_LY,_LZ){var _M0=function(_KF){return new F(function(){return _LE(_LX,_LY,_KF);});},_M1=function(_M2,_M3){return new F(function(){return _M4(_M3);});},_M4=function(_M5){return new F(function(){return _3M(new T1(1,B(_fZ(_M0,_M5))),new T(function(){return new T1(1,B(_fZ(_M1,_M5)));}));});};return new F(function(){return _M4(_LZ);});},_M6=function(_M7,_M8){return new F(function(){return _LW(_LA,_Lp,_M8);});},_M9=new T(function(){return B(_KH(_M6,_4Y));}),_Ma=function(_Lr){return new F(function(){return _3C(_M9,_Lr);});},_Mb=new T(function(){return B(_LW(_LA,_Lp,_4Y));}),_Mc=function(_Lr){return new F(function(){return _3C(_Mb,_Lr);});},_Md=function(_Me,_Lr){return new F(function(){return _Mc(_Lr);});},_Mf=function(_Mg,_Mh){return new F(function(){return _KH(_M6,_Mh);});},_Mi=new T4(0,_Md,_Ma,_M6,_Mf),_Mj=function(_Mk,_Ml){return new F(function(){return _LW(_Mi,_Lp,_Ml);});},_Mm=function(_Mn,_Mo){return new F(function(){return _KH(_Mj,_Mo);});},_Mp=new T(function(){return B(_KH(_Mm,_4Y));}),_Mq=function(_Mr){return new F(function(){return _3C(_Mp,_Mr);});},_Ms=function(_Mt){return new F(function(){return _KH(_Mm,_Mt);});},_Mu=function(_Mv,_Mw){return new F(function(){return _Ms(_Mw);});},_Mx=new T(function(){return B(_KH(_Mj,_4Y));}),_My=function(_Mr){return new F(function(){return _3C(_Mx,_Mr);});},_Mz=function(_MA,_Mr){return new F(function(){return _My(_Mr);});},_MB=new T4(0,_Mz,_Mq,_Mm,_Mu),_MC=function(_Lr){return new F(function(){return _gi(_ht,_Lr);});},_MD=function(_ME,_MF){return new F(function(){return _KH(_MC,_MF);});},_MG=new T(function(){return B(_KH(_MC,_4Y));}),_MH=function(_Lr){return new F(function(){return _3C(_MG,_Lr);});},_MI=function(_MJ){var _MK=new T(function(){return B(A3(_gi,_ht,_MJ,_4Y));});return function(_Lo){return new F(function(){return _3C(_MK,_Lo);});};},_ML=new T4(0,_MI,_MH,_MC,_MD),_MM=function(_MN,_MO){return new F(function(){return _LW(_ML,_Lp,_MO);});},_MP=new T(function(){return B(_KH(_MM,_4Y));}),_MQ=function(_Lr){return new F(function(){return _3C(_MP,_Lr);});},_MR=new T(function(){return B(_LW(_ML,_Lp,_4Y));}),_MS=function(_Lr){return new F(function(){return _3C(_MR,_Lr);});},_MT=function(_MU,_Lr){return new F(function(){return _MS(_Lr);});},_MV=function(_MW,_MX){return new F(function(){return _KH(_MM,_MX);});},_MY=new T4(0,_MT,_MQ,_MM,_MV),_MZ=function(_N0,_N1){return new F(function(){return _LW(_MY,_Lp,_N1);});},_N2=function(_N3,_N4){return new F(function(){return _KH(_MZ,_N4);});},_N5=new T(function(){return B(_KH(_N2,_4Y));}),_N6=function(_Mr){return new F(function(){return _3C(_N5,_Mr);});},_N7=function(_N8){return new F(function(){return _KH(_N2,_N8);});},_N9=function(_Na,_Nb){return new F(function(){return _N7(_Nb);});},_Nc=new T(function(){return B(_KH(_MZ,_4Y));}),_Nd=function(_Mr){return new F(function(){return _3C(_Nc,_Mr);});},_Ne=function(_Nf,_Mr){return new F(function(){return _Nd(_Mr);});},_Ng=new T4(0,_Ne,_N6,_N2,_N9),_Nh=new T(function(){return B(unCStr("RC"));}),_Ni=function(_Nj,_Nk){if(_Nj>10){return new T0(2);}else{var _Nl=new T(function(){var _Nm=new T(function(){var _Nn=function(_No){var _Np=function(_Nq){return new F(function(){return A3(_gt,_gW,_1,function(_Nr){return new F(function(){return A1(_Nk,new T3(0,_No,_Nq,_Nr));});});});};return new F(function(){return A3(_gt,_gW,_1,_Np);});};return B(A3(_gi,_he,_1,_Nn));});return B(_fr(function(_Ns){var _Nt=E(_Ns);return (_Nt._==3)?(!B(_4r(_Nt.a,_Nh)))?new T0(2):E(_Nm):new T0(2);}));}),_Nu=function(_Nv){return E(_Nl);};return new T1(1,function(_Nw){return new F(function(){return A2(_e8,_Nw,_Nu);});});}},_Nx=function(_Ny,_Nz){return new F(function(){return _Ni(E(_Ny),_Nz);});},_NA=function(_Lr){return new F(function(){return _gi(_Nx,_Lr);});},_NB=function(_NC,_ND){return new F(function(){return _KH(_NA,_ND);});},_NE=new T(function(){return B(_KH(_NB,_4Y));}),_NF=function(_Mr){return new F(function(){return _3C(_NE,_Mr);});},_NG=new T(function(){return B(_KH(_NA,_4Y));}),_NH=function(_Mr){return new F(function(){return _3C(_NG,_Mr);});},_NI=function(_NJ,_Mr){return new F(function(){return _NH(_Mr);});},_NK=function(_NL,_NM){return new F(function(){return _KH(_NB,_NM);});},_NN=new T4(0,_NI,_NF,_NB,_NK),_NO=new T(function(){return B(unCStr("CC"));}),_NP=function(_NQ,_NR){if(_NQ>10){return new T0(2);}else{var _NS=new T(function(){var _NT=new T(function(){var _NU=function(_NV){var _NW=function(_NX){var _NY=function(_NZ){return new F(function(){return A3(_gt,_gW,_1,function(_O0){return new F(function(){return A1(_NR,new T4(0,_NV,_NX,_NZ,_O0));});});});};return new F(function(){return A3(_gt,_gW,_1,_NY);});};return new F(function(){return A3(_gt,_gW,_1,_NW);});};return B(A3(_gi,_he,_1,_NU));});return B(_fr(function(_O1){var _O2=E(_O1);return (_O2._==3)?(!B(_4r(_O2.a,_NO)))?new T0(2):E(_NT):new T0(2);}));}),_O3=function(_O4){return E(_NS);};return new T1(1,function(_O5){return new F(function(){return A2(_e8,_O5,_O3);});});}},_O6=function(_O7,_O8){return new F(function(){return _NP(E(_O7),_O8);});},_O9=function(_Lr){return new F(function(){return _gi(_O6,_Lr);});},_Oa=function(_Ob,_Oc){return new F(function(){return _KH(_O9,_Oc);});},_Od=new T(function(){return B(_KH(_Oa,_4Y));}),_Oe=function(_Mr){return new F(function(){return _3C(_Od,_Mr);});},_Of=new T(function(){return B(_KH(_O9,_4Y));}),_Og=function(_Mr){return new F(function(){return _3C(_Of,_Mr);});},_Oh=function(_Oi,_Mr){return new F(function(){return _Og(_Mr);});},_Oj=function(_Ok,_Ol){return new F(function(){return _KH(_Oa,_Ol);});},_Om=new T4(0,_Oh,_Oe,_Oa,_Oj),_On=function(_Oo,_Op,_Oq,_Or,_Os){var _Ot=new T(function(){return B(_LE(_Oo,_Op,_Os));}),_Ou=new T(function(){return B(_LC(_Or));}),_Ov=function(_Ow){var _Ox=function(_Oy){var _Oz=E(_Oy),_OA=new T(function(){var _OB=new T(function(){var _OC=function(_OD){var _OE=new T(function(){var _OF=new T(function(){return B(A2(_Ou,_Os,function(_OG){return new F(function(){return A1(_Ow,new T4(0,_Oz.a,_Oz.b,_OD,_OG));});}));});return B(_fr(function(_OH){var _OI=E(_OH);return (_OI._==2)?(!B(_4r(_OI.a,_LB)))?new T0(2):E(_OF):new T0(2);}));}),_OJ=function(_OK){return E(_OE);};return new T1(1,function(_OL){return new F(function(){return A2(_e8,_OL,_OJ);});});};return B(A3(_LC,_Oq,_Os,_OC));});return B(_fr(function(_OM){var _ON=E(_OM);return (_ON._==2)?(!B(_4r(_ON.a,_LB)))?new T0(2):E(_OB):new T0(2);}));}),_OO=function(_OP){return E(_OA);};return new T1(1,function(_OQ){return new F(function(){return A2(_e8,_OQ,_OO);});});};return new F(function(){return A1(_Ot,_Ox);});};return E(_Ov);},_OR=function(_OS,_OT,_OU,_OV,_OW){var _OX=function(_KF){return new F(function(){return _On(_OS,_OT,_OU,_OV,_KF);});},_OY=function(_OZ,_P0){return new F(function(){return _P1(_P0);});},_P1=function(_P2){return new F(function(){return _3M(new T1(1,B(_fZ(_OX,_P2))),new T(function(){return new T1(1,B(_fZ(_OY,_P2)));}));});};return new F(function(){return _P1(_OW);});},_P3=new T(function(){return B(_OR(_Om,_NN,_Ng,_MB,_lU));}),_P4=new T(function(){return B(unCStr("contractInput"));}),_P5=function(_P6,_P7,_P8,_){var _P9=E(_P4),_Pa=eval(E(_rw)),_Pb=__app1(E(_Pa),toJSStr(_P9)),_Pc=B(_m1(B(_3C(_P3,new T(function(){var _Pd=String(_Pb);return fromJSStr(_Pd);})))));if(!_Pc._){return E(_KD);}else{if(!E(_Pc.b)._){var _Pe=E(_Pc.a),_Pf=B(_Ko(new T(function(){return B(_vg(_Pe.a));},1),new T(function(){return B(_zD(_Pe.b));},1),new T(function(){return B(_It(_Pe.c));},1),new T(function(){return B(_DP(_P8,_P6,_P7,B(_Fj(_Pe.d))));},1)));return new F(function(){return _29(_P9,new T2(1,_Pf.a,_Pf.b),_);});}else{return E(_KC);}}},_Pg=function(_Ph,_Pi,_Pj,_){var _Pk=E(_P4),_Pl=eval(E(_rw)),_Pm=__app1(E(_Pl),toJSStr(_Pk)),_Pn=B(_m1(B(_3C(_P3,new T(function(){var _Po=String(_Pm);return fromJSStr(_Po);})))));if(!_Pn._){return E(_KD);}else{if(!E(_Pn.b)._){var _Pp=E(_Pn.a),_Pq=B(_Ko(new T(function(){return B(_vg(_Pp.a));},1),new T(function(){return B(_zD(_Pp.b));},1),new T(function(){return B(_GZ(_Pj,_Ph,_Pi,B(_It(_Pp.c))));},1),new T(function(){return B(_Fj(_Pp.d));},1)));return new F(function(){return _29(_Pk,new T2(1,_Pq.a,_Pq.b),_);});}else{return E(_KC);}}},_Pr=new T(function(){return B(unCStr("contractOutput"));}),_Ps=new T(function(){return B(unCStr("([], [], [], [])"));}),_Pt=new T(function(){return B(unCStr("([], [])"));}),_Pu=new T(function(){return B(unCStr("contractState"));}),_Pv=new T(function(){return B(_d(0,0,_23));}),_Pw=new T(function(){return B(unCStr("currBlock"));}),_Px=function(_){var _Py=__app0(E(_rn)),_Pz=B(_29(_26,_23,_)),_PA=B(_29(_Pw,_Pv,_)),_PB=B(_29(_Pu,_Pt,_)),_PC=B(_29(_P4,_Ps,_));return new F(function(){return _29(_Pr,_23,_);});},_PD=function(_PE,_PF,_PG,_PH,_){var _PI=E(_P4),_PJ=eval(E(_rw)),_PK=__app1(E(_PJ),toJSStr(_PI)),_PL=B(_m1(B(_3C(_P3,new T(function(){var _PM=String(_PK);return fromJSStr(_PM);})))));if(!_PL._){return E(_KD);}else{if(!E(_PL.b)._){var _PN=E(_PL.a),_PO=B(_Ko(new T(function(){return B(_sS(_PG,_PE,_PF,_PH,B(_vg(_PN.a))));},1),new T(function(){return B(_zD(_PN.b));},1),new T(function(){return B(_It(_PN.c));},1),new T(function(){return B(_Fj(_PN.d));},1)));return new F(function(){return _29(_PI,new T2(1,_PO.a,_PO.b),_);});}else{return E(_KC);}}},_PP=new T(function(){return B(unCStr("ManuallyRedeemed"));}),_PQ=new T(function(){return B(unCStr("NotRedeemed "));}),_PR=function(_PS,_PT,_PU){var _PV=E(_PT);if(!_PV._){var _PW=function(_PX){return new F(function(){return _d(11,E(_PV.a),new T2(1,_w,new T(function(){return B(_d(11,E(_PV.b),_PX));})));});};if(E(_PS)<11){return new F(function(){return _3(_PQ,new T(function(){return B(_PW(_PU));},1));});}else{var _PY=new T(function(){return B(_3(_PQ,new T(function(){return B(_PW(new T2(1,_b,_PU)));},1)));});return new T2(1,_c,_PY);}}else{return new F(function(){return _3(_PP,_PU);});}},_PZ=function(_Q0,_Q1,_Q2){var _Q3=new T(function(){var _Q4=function(_Q5){var _Q6=E(_Q1),_Q7=new T(function(){return B(A3(_Jw,_IQ,new T2(1,function(_Q8){return new F(function(){return _d(0,E(_Q6.a),_Q8);});},new T2(1,function(_Mr){return new F(function(){return _PR(_m8,_Q6.b,_Mr);});},_23)),new T2(1,_b,_Q5)));});return new T2(1,_c,_Q7);};return B(A3(_Jw,_IQ,new T2(1,function(_Q9){return new F(function(){return _o(0,_Q0,_Q9);});},new T2(1,_Q4,_23)),new T2(1,_b,_Q2)));});return new T2(0,_c,_Q3);},_Qa=function(_Qb,_Qc){var _Qd=E(_Qb),_Qe=B(_PZ(_Qd.a,_Qd.b,_Qc));return new T2(1,_Qe.a,_Qe.b);},_Qf=function(_Qg,_Qh){return new F(function(){return _2L(_Qa,_Qg,_Qh);});},_Qi=function(_Qj,_Qk,_Ql,_Qm){var _Qn=E(_Qj);if(_Qn==1){var _Qo=E(_Qm);if(!_Qo._){return new T3(0,new T(function(){var _Qp=E(_Qk);return new T5(0,1,E(_Qp),_Ql,E(_zS),E(_zS));}),_23,_23);}else{var _Qq=E(_Qk);return (_Qq<E(E(_Qo.a).a))?new T3(0,new T5(0,1,E(_Qq),_Ql,E(_zS),E(_zS)),_Qo,_23):new T3(0,new T5(0,1,E(_Qq),_Ql,E(_zS),E(_zS)),_23,_Qo);}}else{var _Qr=B(_Qi(_Qn>>1,_Qk,_Ql,_Qm)),_Qs=_Qr.a,_Qt=_Qr.c,_Qu=E(_Qr.b);if(!_Qu._){return new T3(0,_Qs,_23,_Qt);}else{var _Qv=E(_Qu.a),_Qw=_Qv.a,_Qx=_Qv.b,_Qy=E(_Qu.b);if(!_Qy._){return new T3(0,new T(function(){return B(_AF(_Qw,_Qx,_Qs));}),_23,_Qt);}else{var _Qz=E(_Qy.a),_QA=E(_Qw),_QB=E(_Qz.a);if(_QA<_QB){var _QC=B(_Qi(_Qn>>1,_QB,_Qz.b,_Qy.b));return new T3(0,new T(function(){return B(_C8(_QA,_Qx,_Qs,_QC.a));}),_QC.b,_QC.c);}else{return new T3(0,_Qs,_23,_Qu);}}}}},_QD=function(_QE,_QF,_QG){var _QH=E(_QG);if(!_QH._){var _QI=_QH.c,_QJ=_QH.d,_QK=_QH.e,_QL=E(_QH.b);if(_QE>=_QL){if(_QE!=_QL){return new F(function(){return _zX(_QL,_QI,_QJ,B(_QD(_QE,_QF,_QK)));});}else{return new T5(0,_QH.a,E(_QE),_QF,E(_QJ),E(_QK));}}else{return new F(function(){return _AO(_QL,_QI,B(_QD(_QE,_QF,_QJ)),_QK);});}}else{return new T5(0,1,E(_QE),_QF,E(_zS),E(_zS));}},_QM=function(_QN,_QO){while(1){var _QP=E(_QO);if(!_QP._){return E(_QN);}else{var _QQ=E(_QP.a),_QR=B(_QD(E(_QQ.a),_QQ.b,_QN));_QN=_QR;_QO=_QP.b;continue;}}},_QS=function(_QT,_QU,_QV,_QW){return new F(function(){return _QM(B(_QD(E(_QU),_QV,_QT)),_QW);});},_QX=function(_QY,_QZ,_R0){var _R1=E(_QZ);return new F(function(){return _QM(B(_QD(E(_R1.a),_R1.b,_QY)),_R0);});},_R2=function(_R3,_R4,_R5){while(1){var _R6=E(_R5);if(!_R6._){return E(_R4);}else{var _R7=E(_R6.a),_R8=_R7.a,_R9=_R7.b,_Ra=E(_R6.b);if(!_Ra._){return new F(function(){return _AF(_R8,_R9,_R4);});}else{var _Rb=E(_Ra.a),_Rc=E(_R8),_Rd=E(_Rb.a);if(_Rc<_Rd){var _Re=B(_Qi(_R3,_Rd,_Rb.b,_Ra.b)),_Rf=_Re.a,_Rg=E(_Re.c);if(!_Rg._){var _Rh=_R3<<1,_Ri=B(_C8(_Rc,_R9,_R4,_Rf));_R3=_Rh;_R4=_Ri;_R5=_Re.b;continue;}else{return new F(function(){return _QX(B(_C8(_Rc,_R9,_R4,_Rf)),_Rg.a,_Rg.b);});}}else{return new F(function(){return _QS(_R4,_Rc,_R9,_Ra);});}}}}},_Rj=function(_Rk,_Rl,_Rm,_Rn,_Ro){var _Rp=E(_Ro);if(!_Rp._){return new F(function(){return _AF(_Rm,_Rn,_Rl);});}else{var _Rq=E(_Rp.a),_Rr=E(_Rm),_Rs=E(_Rq.a);if(_Rr<_Rs){var _Rt=B(_Qi(_Rk,_Rs,_Rq.b,_Rp.b)),_Ru=_Rt.a,_Rv=E(_Rt.c);if(!_Rv._){return new F(function(){return _R2(_Rk<<1,B(_C8(_Rr,_Rn,_Rl,_Ru)),_Rt.b);});}else{return new F(function(){return _QX(B(_C8(_Rr,_Rn,_Rl,_Ru)),_Rv.a,_Rv.b);});}}else{return new F(function(){return _QS(_Rl,_Rr,_Rn,_Rp);});}}},_Rw=function(_Rx){var _Ry=E(_Rx);if(!_Ry._){return new T0(1);}else{var _Rz=E(_Ry.a),_RA=_Rz.a,_RB=_Rz.b,_RC=E(_Ry.b);if(!_RC._){var _RD=E(_RA);return new T5(0,1,E(_RD),_RB,E(_zS),E(_zS));}else{var _RE=_RC.b,_RF=E(_RC.a),_RG=_RF.b,_RH=E(_RA),_RI=E(_RF.a);if(_RH<_RI){return new F(function(){return _Rj(1,new T5(0,1,E(_RH),_RB,E(_zS),E(_zS)),_RI,_RG,_RE);});}else{return new F(function(){return _QS(new T5(0,1,E(_RH),_RB,E(_zS),E(_zS)),_RI,_RG,_RE);});}}}},_RJ=new T(function(){return B(unCStr("ChoiceMade "));}),_RK=new T(function(){return B(unCStr("DuplicateRedeem "));}),_RL=new T(function(){return B(unCStr("ExpiredCommitRedeemed "));}),_RM=new T(function(){return B(unCStr("CommitRedeemed "));}),_RN=new T(function(){return B(unCStr("SuccessfulCommit "));}),_RO=new T(function(){return B(unCStr("FailedPay "));}),_RP=new T(function(){return B(unCStr("ExpiredPay "));}),_RQ=new T(function(){return B(unCStr("SuccessfulPay "));}),_RR=function(_RS,_RT,_RU){var _RV=E(_RT);switch(_RV._){case 0:var _RW=function(_RX){var _RY=new T(function(){var _RZ=new T(function(){return B(_d(11,E(_RV.c),new T2(1,_w,new T(function(){return B(_d(11,E(_RV.d),_RX));}))));});return B(_d(11,E(_RV.b),new T2(1,_w,_RZ)));});return new F(function(){return _1i(11,_RV.a,new T2(1,_w,_RY));});};if(_RS<11){return new F(function(){return _3(_RQ,new T(function(){return B(_RW(_RU));},1));});}else{var _S0=new T(function(){return B(_3(_RQ,new T(function(){return B(_RW(new T2(1,_b,_RU)));},1)));});return new T2(1,_c,_S0);}break;case 1:var _S1=function(_S2){var _S3=new T(function(){var _S4=new T(function(){return B(_d(11,E(_RV.c),new T2(1,_w,new T(function(){return B(_d(11,E(_RV.d),_S2));}))));});return B(_d(11,E(_RV.b),new T2(1,_w,_S4)));});return new F(function(){return _1i(11,_RV.a,new T2(1,_w,_S3));});};if(_RS<11){return new F(function(){return _3(_RP,new T(function(){return B(_S1(_RU));},1));});}else{var _S5=new T(function(){return B(_3(_RP,new T(function(){return B(_S1(new T2(1,_b,_RU)));},1)));});return new T2(1,_c,_S5);}break;case 2:var _S6=function(_S7){var _S8=new T(function(){var _S9=new T(function(){return B(_d(11,E(_RV.c),new T2(1,_w,new T(function(){return B(_d(11,E(_RV.d),_S7));}))));});return B(_d(11,E(_RV.b),new T2(1,_w,_S9)));});return new F(function(){return _1i(11,_RV.a,new T2(1,_w,_S8));});};if(_RS<11){return new F(function(){return _3(_RO,new T(function(){return B(_S6(_RU));},1));});}else{var _Sa=new T(function(){return B(_3(_RO,new T(function(){return B(_S6(new T2(1,_b,_RU)));},1)));});return new T2(1,_c,_Sa);}break;case 3:var _Sb=function(_Sc){var _Sd=new T(function(){var _Se=new T(function(){return B(_d(11,E(_RV.b),new T2(1,_w,new T(function(){return B(_d(11,E(_RV.c),_Sc));}))));});return B(_o(11,_RV.a,new T2(1,_w,_Se)));},1);return new F(function(){return _3(_RN,_Sd);});};if(_RS<11){return new F(function(){return _Sb(_RU);});}else{return new T2(1,_c,new T(function(){return B(_Sb(new T2(1,_b,_RU)));}));}break;case 4:var _Sf=function(_Sg){var _Sh=new T(function(){var _Si=new T(function(){return B(_d(11,E(_RV.b),new T2(1,_w,new T(function(){return B(_d(11,E(_RV.c),_Sg));}))));});return B(_o(11,_RV.a,new T2(1,_w,_Si)));},1);return new F(function(){return _3(_RM,_Sh);});};if(_RS<11){return new F(function(){return _Sf(_RU);});}else{return new T2(1,_c,new T(function(){return B(_Sf(new T2(1,_b,_RU)));}));}break;case 5:var _Sj=function(_Sk){var _Sl=new T(function(){var _Sm=new T(function(){return B(_d(11,E(_RV.b),new T2(1,_w,new T(function(){return B(_d(11,E(_RV.c),_Sk));}))));});return B(_o(11,_RV.a,new T2(1,_w,_Sm)));},1);return new F(function(){return _3(_RL,_Sl);});};if(_RS<11){return new F(function(){return _Sj(_RU);});}else{return new T2(1,_c,new T(function(){return B(_Sj(new T2(1,_b,_RU)));}));}break;case 6:var _Sn=function(_So){return new F(function(){return _o(11,_RV.a,new T2(1,_w,new T(function(){return B(_d(11,E(_RV.b),_So));})));});};if(_RS<11){return new F(function(){return _3(_RK,new T(function(){return B(_Sn(_RU));},1));});}else{var _Sp=new T(function(){return B(_3(_RK,new T(function(){return B(_Sn(new T2(1,_b,_RU)));},1)));});return new T2(1,_c,_Sp);}break;default:var _Sq=function(_Sr){var _Ss=new T(function(){var _St=new T(function(){return B(_d(11,E(_RV.b),new T2(1,_w,new T(function(){return B(_d(11,E(_RV.c),_Sr));}))));});return B(_i(11,_RV.a,new T2(1,_w,_St)));},1);return new F(function(){return _3(_RJ,_Ss);});};if(_RS<11){return new F(function(){return _Sq(_RU);});}else{return new T2(1,_c,new T(function(){return B(_Sq(new T2(1,_b,_RU)));}));}}},_Su=function(_Sv,_Sw){return E(_Sv)==E(_Sw);},_Sx=function(_Sy,_Sz){var _SA=E(_Sy);switch(_SA._){case 0:var _SB=E(_Sz);if(!_SB._){if(E(_SA.a)!=E(_SB.a)){return false;}else{if(E(_SA.b)!=E(_SB.b)){return false;}else{if(E(_SA.c)!=E(_SB.c)){return false;}else{return new F(function(){return _Su(_SA.d,_SB.d);});}}}}else{return false;}break;case 1:var _SC=E(_Sz);if(_SC._==1){if(E(_SA.a)!=E(_SC.a)){return false;}else{if(E(_SA.b)!=E(_SC.b)){return false;}else{if(E(_SA.c)!=E(_SC.c)){return false;}else{return new F(function(){return _Su(_SA.d,_SC.d);});}}}}else{return false;}break;case 2:var _SD=E(_Sz);if(_SD._==2){if(E(_SA.a)!=E(_SD.a)){return false;}else{if(E(_SA.b)!=E(_SD.b)){return false;}else{if(E(_SA.c)!=E(_SD.c)){return false;}else{return new F(function(){return _Su(_SA.d,_SD.d);});}}}}else{return false;}break;case 3:var _SE=E(_Sz);if(_SE._==3){if(E(_SA.a)!=E(_SE.a)){return false;}else{if(E(_SA.b)!=E(_SE.b)){return false;}else{return new F(function(){return _Su(_SA.c,_SE.c);});}}}else{return false;}break;case 4:var _SF=E(_Sz);if(_SF._==4){if(E(_SA.a)!=E(_SF.a)){return false;}else{if(E(_SA.b)!=E(_SF.b)){return false;}else{return new F(function(){return _Su(_SA.c,_SF.c);});}}}else{return false;}break;case 5:var _SG=E(_Sz);if(_SG._==5){if(E(_SA.a)!=E(_SG.a)){return false;}else{if(E(_SA.b)!=E(_SG.b)){return false;}else{return new F(function(){return _Su(_SA.c,_SG.c);});}}}else{return false;}break;case 6:var _SH=E(_Sz);if(_SH._==6){if(E(_SA.a)!=E(_SH.a)){return false;}else{return new F(function(){return _Su(_SA.b,_SH.b);});}}else{return false;}break;default:var _SI=E(_Sz);if(_SI._==7){if(E(_SA.a)!=E(_SI.a)){return false;}else{if(E(_SA.b)!=E(_SI.b)){return false;}else{return new F(function(){return _Su(_SA.c,_SI.c);});}}}else{return false;}}},_SJ=function(_SK,_SL){return (!B(_Sx(_SK,_SL)))?true:false;},_SM=new T2(0,_Sx,_SJ),_SN=function(_SO,_SP){while(1){var _SQ=E(_SO);switch(_SQ._){case 0:var _SR=E(_SP);if(!_SR._){return new F(function(){return _Su(_SQ.a,_SR.a);});}else{return false;}break;case 1:var _SS=E(_SP);if(_SS._==1){if(!B(_SN(_SQ.a,_SS.a))){return false;}else{_SO=_SQ.b;_SP=_SS.b;continue;}}else{return false;}break;default:var _ST=E(_SP);if(_ST._==2){return new F(function(){return _Su(_SQ.a,_ST.a);});}else{return false;}}}},_SU=function(_SV,_SW){while(1){var _SX=E(_SV);switch(_SX._){case 0:var _SY=E(_SW);if(!_SY._){return new F(function(){return _Su(_SX.a,_SY.a);});}else{return false;}break;case 1:var _SZ=E(_SW);if(_SZ._==1){if(!B(_SU(_SX.a,_SZ.a))){return false;}else{_SV=_SX.b;_SW=_SZ.b;continue;}}else{return false;}break;case 2:var _T0=E(_SW);if(_T0._==2){if(!B(_SU(_SX.a,_T0.a))){return false;}else{_SV=_SX.b;_SW=_T0.b;continue;}}else{return false;}break;case 3:var _T1=E(_SW);if(_T1._==3){_SV=_SX.a;_SW=_T1.a;continue;}else{return false;}break;case 4:var _T2=E(_SW);if(_T2._==4){if(E(_SX.a)!=E(_T2.a)){return false;}else{if(E(_SX.b)!=E(_T2.b)){return false;}else{return new F(function(){return _Su(_SX.c,_T2.c);});}}}else{return false;}break;case 5:var _T3=E(_SW);if(_T3._==5){if(E(_SX.a)!=E(_T3.a)){return false;}else{return new F(function(){return _Su(_SX.b,_T3.b);});}}else{return false;}break;case 6:var _T4=E(_SW);if(_T4._==6){if(!B(_SN(_SX.a,_T4.a))){return false;}else{return new F(function(){return _SN(_SX.b,_T4.b);});}}else{return false;}break;case 7:return (E(_SW)._==7)?true:false;default:return (E(_SW)._==8)?true:false;}}},_T5=function(_T6,_T7){while(1){var _T8=E(_T6);switch(_T8._){case 0:return (E(_T7)._==0)?true:false;case 1:var _T9=E(_T7);if(_T9._==1){if(E(_T8.a)!=E(_T9.a)){return false;}else{if(E(_T8.b)!=E(_T9.b)){return false;}else{if(E(_T8.c)!=E(_T9.c)){return false;}else{if(E(_T8.d)!=E(_T9.d)){return false;}else{if(E(_T8.e)!=E(_T9.e)){return false;}else{if(!B(_T5(_T8.f,_T9.f))){return false;}else{_T6=_T8.g;_T7=_T9.g;continue;}}}}}}}else{return false;}break;case 2:var _Ta=E(_T7);if(_Ta._==2){if(E(_T8.a)!=E(_Ta.a)){return false;}else{_T6=_T8.b;_T7=_Ta.b;continue;}}else{return false;}break;case 3:var _Tb=E(_T7);if(_Tb._==3){if(E(_T8.a)!=E(_Tb.a)){return false;}else{if(E(_T8.b)!=E(_Tb.b)){return false;}else{if(E(_T8.c)!=E(_Tb.c)){return false;}else{if(E(_T8.d)!=E(_Tb.d)){return false;}else{if(E(_T8.e)!=E(_Tb.e)){return false;}else{_T6=_T8.f;_T7=_Tb.f;continue;}}}}}}else{return false;}break;case 4:var _Tc=E(_T7);if(_Tc._==4){if(!B(_T5(_T8.a,_Tc.a))){return false;}else{_T6=_T8.b;_T7=_Tc.b;continue;}}else{return false;}break;case 5:var _Td=E(_T7);if(_Td._==5){if(!B(_SU(_T8.a,_Td.a))){return false;}else{if(!B(_T5(_T8.b,_Td.b))){return false;}else{_T6=_T8.c;_T7=_Td.c;continue;}}}else{return false;}break;default:var _Te=E(_T7);if(_Te._==6){if(!B(_SU(_T8.a,_Te.a))){return false;}else{if(E(_T8.b)!=E(_Te.b)){return false;}else{if(!B(_T5(_T8.c,_Te.c))){return false;}else{_T6=_T8.d;_T7=_Te.d;continue;}}}}else{return false;}}}},_Tf=function(_Tg,_Th,_Ti,_Tj){if(_Tg!=_Ti){return false;}else{return new F(function(){return _Su(_Th,_Tj);});}},_Tk=function(_Tl,_Tm){var _Tn=E(_Tl),_To=E(_Tm);return new F(function(){return _Tf(E(_Tn.a),_Tn.b,E(_To.a),_To.b);});},_Tp=function(_Tq,_Tr,_Ts,_Tt){return (_Tq!=_Ts)?true:(E(_Tr)!=E(_Tt))?true:false;},_Tu=function(_Tv,_Tw){var _Tx=E(_Tv),_Ty=E(_Tw);return new F(function(){return _Tp(E(_Tx.a),_Tx.b,E(_Ty.a),_Ty.b);});},_Tz=new T2(0,_Tk,_Tu),_TA=function(_TB,_TC){return E(_TB)!=E(_TC);},_TD=new T2(0,_Su,_TA),_TE=function(_TF,_TG,_TH,_TI,_TJ,_TK){return (!B(A3(_8s,_TF,_TH,_TJ)))?true:(!B(A3(_8s,_TG,_TI,_TK)))?true:false;},_TL=function(_TM,_TN,_TO,_TP){var _TQ=E(_TO),_TR=E(_TP);return new F(function(){return _TE(_TM,_TN,_TQ.a,_TQ.b,_TR.a,_TR.b);});},_TS=function(_TT,_TU,_TV,_TW,_TX,_TY){if(!B(A3(_8s,_TT,_TV,_TX))){return false;}else{return new F(function(){return A3(_8s,_TU,_TW,_TY);});}},_TZ=function(_U0,_U1,_U2,_U3){var _U4=E(_U2),_U5=E(_U3);return new F(function(){return _TS(_U0,_U1,_U4.a,_U4.b,_U5.a,_U5.b);});},_U6=function(_U7,_U8){return new T2(0,function(_U9,_Ua){return new F(function(){return _TZ(_U7,_U8,_U9,_Ua);});},function(_U9,_Ua){return new F(function(){return _TL(_U7,_U8,_U9,_Ua);});});},_Ub=function(_Uc,_Ud,_Ue){while(1){var _Uf=E(_Ud);if(!_Uf._){return (E(_Ue)._==0)?true:false;}else{var _Ug=E(_Ue);if(!_Ug._){return false;}else{if(!B(A3(_8s,_Uc,_Uf.a,_Ug.a))){return false;}else{_Ud=_Uf.b;_Ue=_Ug.b;continue;}}}}},_Uh=function(_Ui,_Uj){var _Uk=new T(function(){return B(_U6(_Ui,_Uj));}),_Ul=function(_Um,_Un){var _Uo=function(_Up){var _Uq=function(_Ur){if(_Up!=_Ur){return false;}else{return new F(function(){return _Ub(_Uk,B(_IJ(_23,_Um)),B(_IJ(_23,_Un)));});}},_Us=E(_Un);if(!_Us._){return new F(function(){return _Uq(_Us.a);});}else{return new F(function(){return _Uq(0);});}},_Ut=E(_Um);if(!_Ut._){return new F(function(){return _Uo(_Ut.a);});}else{return new F(function(){return _Uo(0);});}};return E(_Ul);},_Uu=new T(function(){return B(_Uh(_Tz,_TD));}),_Uv=new T2(0,_Su,_TA),_Uw=function(_Ux,_Uy){var _Uz=E(_Ux);if(!_Uz._){var _UA=E(_Uy);if(!_UA._){if(E(_Uz.a)!=E(_UA.a)){return false;}else{return new F(function(){return _Su(_Uz.b,_UA.b);});}}else{return false;}}else{return (E(_Uy)._==0)?false:true;}},_UB=function(_UC,_UD,_UE,_UF){if(_UC!=_UE){return false;}else{return new F(function(){return _Uw(_UD,_UF);});}},_UG=function(_UH,_UI){var _UJ=E(_UH),_UK=E(_UI);return new F(function(){return _UB(E(_UJ.a),_UJ.b,E(_UK.a),_UK.b);});},_UL=function(_UM,_UN,_UO,_UP){if(_UM!=_UO){return true;}else{var _UQ=E(_UN);if(!_UQ._){var _UR=E(_UP);return (_UR._==0)?(E(_UQ.a)!=E(_UR.a))?true:(E(_UQ.b)!=E(_UR.b))?true:false:true;}else{return (E(_UP)._==0)?true:false;}}},_US=function(_UT,_UU){var _UV=E(_UT),_UW=E(_UU);return new F(function(){return _UL(E(_UV.a),_UV.b,E(_UW.a),_UW.b);});},_UX=new T2(0,_UG,_US),_UY=new T(function(){return B(_Uh(_Uv,_UX));}),_UZ=function(_V0,_V1){var _V2=E(_V0),_V3=E(_V1);return (_V2>_V3)?E(_V2):E(_V3);},_V4=function(_V5,_V6){var _V7=E(_V5),_V8=E(_V6);return (_V7>_V8)?E(_V8):E(_V7);},_V9=function(_Va,_Vb){return (_Va>=_Vb)?(_Va!=_Vb)?2:1:0;},_Vc=function(_Vd,_Ve){return new F(function(){return _V9(E(_Vd),E(_Ve));});},_Vf=function(_Vg,_Vh){return E(_Vg)>=E(_Vh);},_Vi=function(_Vj,_Vk){return E(_Vj)>E(_Vk);},_Vl=function(_Vm,_Vn){return E(_Vm)<=E(_Vn);},_Vo=function(_Vp,_Vq){return E(_Vp)<E(_Vq);},_Vr={_:0,a:_Uv,b:_Vc,c:_Vo,d:_Vl,e:_Vi,f:_Vf,g:_UZ,h:_V4},_Vs=function(_Vt,_Vu,_Vv,_Vw,_Vx){while(1){var _Vy=E(_Vx);if(!_Vy._){var _Vz=_Vy.c,_VA=_Vy.d,_VB=E(_Vy.b),_VC=E(_VB.a);if(_Vt>=_VC){if(_Vt!=_VC){_Vu=_;_Vx=_VA;continue;}else{var _VD=E(_VB.b);if(_Vv>=_VD){if(_Vv!=_VD){_Vu=_;_Vx=_VA;continue;}else{var _VE=E(_VB.c);if(_Vw>=_VE){if(_Vw!=_VE){_Vu=_;_Vx=_VA;continue;}else{return true;}}else{_Vu=_;_Vx=_Vz;continue;}}}else{_Vu=_;_Vx=_Vz;continue;}}}else{_Vu=_;_Vx=_Vz;continue;}}else{return false;}}},_VF=function(_VG,_VH,_VI,_VJ,_VK){while(1){var _VL=E(_VK);if(!_VL._){var _VM=_VL.c,_VN=_VL.d,_VO=E(_VL.b),_VP=E(_VO.a);if(_VG>=_VP){if(_VG!=_VP){_VH=_;_VK=_VN;continue;}else{var _VQ=E(_VO.b);if(_VI>=_VQ){if(_VI!=_VQ){_VH=_;_VK=_VN;continue;}else{var _VR=E(_VJ),_VS=E(_VO.c);if(_VR>=_VS){if(_VR!=_VS){return new F(function(){return _Vs(_VG,_,_VI,_VR,_VN);});}else{return true;}}else{return new F(function(){return _Vs(_VG,_,_VI,_VR,_VM);});}}}else{_VH=_;_VK=_VM;continue;}}}else{_VH=_;_VK=_VM;continue;}}else{return false;}}},_VT=function(_VU,_VV,_VW,_VX,_VY){while(1){var _VZ=E(_VY);if(!_VZ._){var _W0=_VZ.c,_W1=_VZ.d,_W2=E(_VZ.b),_W3=E(_W2.a);if(_VU>=_W3){if(_VU!=_W3){_VV=_;_VY=_W1;continue;}else{var _W4=E(_VW),_W5=E(_W2.b);if(_W4>=_W5){if(_W4!=_W5){return new F(function(){return _VF(_VU,_,_W4,_VX,_W1);});}else{var _W6=E(_VX),_W7=E(_W2.c);if(_W6>=_W7){if(_W6!=_W7){return new F(function(){return _Vs(_VU,_,_W4,_W6,_W1);});}else{return true;}}else{return new F(function(){return _Vs(_VU,_,_W4,_W6,_W0);});}}}else{return new F(function(){return _VF(_VU,_,_W4,_VX,_W0);});}}}else{_VV=_;_VY=_W0;continue;}}else{return false;}}},_W8=function(_W9,_Wa,_Wb,_Wc){var _Wd=E(_Wc);if(!_Wd._){var _We=_Wd.c,_Wf=_Wd.d,_Wg=E(_Wd.b),_Wh=E(_W9),_Wi=E(_Wg.a);if(_Wh>=_Wi){if(_Wh!=_Wi){return new F(function(){return _VT(_Wh,_,_Wa,_Wb,_Wf);});}else{var _Wj=E(_Wa),_Wk=E(_Wg.b);if(_Wj>=_Wk){if(_Wj!=_Wk){return new F(function(){return _VF(_Wh,_,_Wj,_Wb,_Wf);});}else{var _Wl=E(_Wb),_Wm=E(_Wg.c);if(_Wl>=_Wm){if(_Wl!=_Wm){return new F(function(){return _Vs(_Wh,_,_Wj,_Wl,_Wf);});}else{return true;}}else{return new F(function(){return _Vs(_Wh,_,_Wj,_Wl,_We);});}}}else{return new F(function(){return _VF(_Wh,_,_Wj,_Wb,_We);});}}}else{return new F(function(){return _VT(_Wh,_,_Wa,_Wb,_We);});}}else{return false;}},_Wn=function(_Wo,_Wp,_Wq,_Wr,_Ws){var _Wt=E(_Ws);if(!_Wt._){if(E(_Wt.b)>E(_Wp)){return false;}else{return new F(function(){return _W8(_Wq,_Wr,_Wt.a,E(_Wo).b);});}}else{return false;}},_Wu=function(_Wv,_Ww,_Wx,_Wy,_Wz){var _WA=E(_Wz);if(!_WA._){var _WB=new T(function(){var _WC=B(_Wu(_WA.a,_WA.b,_WA.c,_WA.d,_WA.e));return new T2(0,_WC.a,_WC.b);});return new T2(0,new T(function(){return E(E(_WB).a);}),new T(function(){return B(_AO(_Ww,_Wx,_Wy,E(_WB).b));}));}else{return new T2(0,new T2(0,_Ww,_Wx),_Wy);}},_WD=function(_WE,_WF,_WG,_WH,_WI){var _WJ=E(_WH);if(!_WJ._){var _WK=new T(function(){var _WL=B(_WD(_WJ.a,_WJ.b,_WJ.c,_WJ.d,_WJ.e));return new T2(0,_WL.a,_WL.b);});return new T2(0,new T(function(){return E(E(_WK).a);}),new T(function(){return B(_zX(_WF,_WG,E(_WK).b,_WI));}));}else{return new T2(0,new T2(0,_WF,_WG),_WI);}},_WM=function(_WN,_WO){var _WP=E(_WN);if(!_WP._){var _WQ=_WP.a,_WR=E(_WO);if(!_WR._){var _WS=_WR.a;if(_WQ<=_WS){var _WT=B(_WD(_WS,_WR.b,_WR.c,_WR.d,_WR.e)),_WU=E(_WT.a);return new F(function(){return _AO(_WU.a,_WU.b,_WP,_WT.b);});}else{var _WV=B(_Wu(_WQ,_WP.b,_WP.c,_WP.d,_WP.e)),_WW=E(_WV.a);return new F(function(){return _zX(_WW.a,_WW.b,_WV.b,_WR);});}}else{return E(_WP);}}else{return E(_WO);}},_WX=function(_WY,_WZ,_X0,_X1,_X2,_X3){var _X4=E(_WY);if(!_X4._){var _X5=_X4.a,_X6=_X4.b,_X7=_X4.c,_X8=_X4.d,_X9=_X4.e;if((imul(3,_X5)|0)>=_WZ){if((imul(3,_WZ)|0)>=_X5){return new F(function(){return _WM(_X4,new T5(0,_WZ,E(_X0),_X1,E(_X2),E(_X3)));});}else{return new F(function(){return _zX(_X6,_X7,_X8,B(_WX(_X9,_WZ,_X0,_X1,_X2,_X3)));});}}else{return new F(function(){return _AO(_X0,_X1,B(_Xa(_X5,_X6,_X7,_X8,_X9,_X2)),_X3);});}}else{return new T5(0,_WZ,E(_X0),_X1,E(_X2),E(_X3));}},_Xa=function(_Xb,_Xc,_Xd,_Xe,_Xf,_Xg){var _Xh=E(_Xg);if(!_Xh._){var _Xi=_Xh.a,_Xj=_Xh.b,_Xk=_Xh.c,_Xl=_Xh.d,_Xm=_Xh.e;if((imul(3,_Xb)|0)>=_Xi){if((imul(3,_Xi)|0)>=_Xb){return new F(function(){return _WM(new T5(0,_Xb,E(_Xc),_Xd,E(_Xe),E(_Xf)),_Xh);});}else{return new F(function(){return _zX(_Xc,_Xd,_Xe,B(_WX(_Xf,_Xi,_Xj,_Xk,_Xl,_Xm)));});}}else{return new F(function(){return _AO(_Xj,_Xk,B(_Xa(_Xb,_Xc,_Xd,_Xe,_Xf,_Xl)),_Xm);});}}else{return new T5(0,_Xb,E(_Xc),_Xd,E(_Xe),E(_Xf));}},_Xn=function(_Xo,_Xp){var _Xq=E(_Xo);if(!_Xq._){var _Xr=_Xq.a,_Xs=_Xq.b,_Xt=_Xq.c,_Xu=_Xq.d,_Xv=_Xq.e,_Xw=E(_Xp);if(!_Xw._){var _Xx=_Xw.a,_Xy=_Xw.b,_Xz=_Xw.c,_XA=_Xw.d,_XB=_Xw.e;if((imul(3,_Xr)|0)>=_Xx){if((imul(3,_Xx)|0)>=_Xr){return new F(function(){return _WM(_Xq,_Xw);});}else{return new F(function(){return _zX(_Xs,_Xt,_Xu,B(_WX(_Xv,_Xx,_Xy,_Xz,_XA,_XB)));});}}else{return new F(function(){return _AO(_Xy,_Xz,B(_Xa(_Xr,_Xs,_Xt,_Xu,_Xv,_XA)),_XB);});}}else{return E(_Xq);}}else{return E(_Xp);}},_XC=function(_XD,_XE){var _XF=E(_XE);if(!_XF._){var _XG=_XF.b,_XH=_XF.c,_XI=B(_XC(_XD,_XF.d)),_XJ=_XI.a,_XK=_XI.b,_XL=B(_XC(_XD,_XF.e)),_XM=_XL.a,_XN=_XL.b;return (!B(A2(_XD,_XG,_XH)))?new T2(0,B(_Xn(_XJ,_XM)),B(_C8(_XG,_XH,_XK,_XN))):new T2(0,B(_C8(_XG,_XH,_XJ,_XM)),B(_Xn(_XK,_XN)));}else{return new T2(0,_zS,_zS);}},_XO=__Z,_XP=function(_XQ,_XR){while(1){var _XS=B((function(_XT,_XU){var _XV=E(_XU);if(!_XV._){var _XW=_XV.e,_XX=new T(function(){var _XY=E(_XV.c),_XZ=E(_XY.b);if(!_XZ._){return new T2(1,new T3(5,_XV.b,_XY.a,_XZ.a),new T(function(){return B(_XP(_XT,_XW));}));}else{return B(_XP(_XT,_XW));}},1);_XQ=_XX;_XR=_XV.d;return __continue;}else{return E(_XT);}})(_XQ,_XR));if(_XS!=__continue){return _XS;}}},_Y0=function(_Y1,_Y2){var _Y3=E(_Y2);return (_Y3._==0)?new T5(0,_Y3.a,E(_Y3.b),new T(function(){return B(A1(_Y1,_Y3.c));}),E(B(_Y0(_Y1,_Y3.d))),E(B(_Y0(_Y1,_Y3.e)))):new T0(1);},_Y4=new T0(1),_Y5=function(_Y6){var _Y7=E(_Y6),_Y8=E(_Y7.b);return new T2(0,_Y7.a,_Y4);},_Y9=function(_Ya){return E(E(_Ya).b);},_Yb=function(_Yc,_Yd,_Ye){var _Yf=E(_Yd);if(!_Yf._){return E(_Ye);}else{var _Yg=function(_Yh,_Yi){while(1){var _Yj=E(_Yi);if(!_Yj._){var _Yk=_Yj.b,_Yl=_Yj.e;switch(B(A3(_Y9,_Yc,_Yh,_Yk))){case 0:return new F(function(){return _C8(_Yk,_Yj.c,B(_Yg(_Yh,_Yj.d)),_Yl);});break;case 1:return E(_Yl);default:_Yi=_Yl;continue;}}else{return new T0(1);}}};return new F(function(){return _Yg(_Yf.a,_Ye);});}},_Ym=function(_Yn,_Yo,_Yp){var _Yq=E(_Yo);if(!_Yq._){return E(_Yp);}else{var _Yr=function(_Ys,_Yt){while(1){var _Yu=E(_Yt);if(!_Yu._){var _Yv=_Yu.b,_Yw=_Yu.d;switch(B(A3(_Y9,_Yn,_Yv,_Ys))){case 0:return new F(function(){return _C8(_Yv,_Yu.c,_Yw,B(_Yr(_Ys,_Yu.e)));});break;case 1:return E(_Yw);default:_Yt=_Yw;continue;}}else{return new T0(1);}}};return new F(function(){return _Yr(_Yq.a,_Yp);});}},_Yx=function(_Yy,_Yz,_YA,_YB){var _YC=E(_Yz),_YD=E(_YB);if(!_YD._){var _YE=_YD.b,_YF=_YD.c,_YG=_YD.d,_YH=_YD.e;switch(B(A3(_Y9,_Yy,_YC,_YE))){case 0:return new F(function(){return _AO(_YE,_YF,B(_Yx(_Yy,_YC,_YA,_YG)),_YH);});break;case 1:return E(_YD);default:return new F(function(){return _zX(_YE,_YF,_YG,B(_Yx(_Yy,_YC,_YA,_YH)));});}}else{return new T5(0,1,E(_YC),_YA,E(_zS),E(_zS));}},_YI=function(_YJ,_YK,_YL,_YM){return new F(function(){return _Yx(_YJ,_YK,_YL,_YM);});},_YN=function(_YO){return E(E(_YO).d);},_YP=function(_YQ){return E(E(_YQ).f);},_YR=function(_YS,_YT,_YU,_YV){var _YW=E(_YT);if(!_YW._){var _YX=E(_YU);if(!_YX._){return E(_YV);}else{var _YY=function(_YZ,_Z0){while(1){var _Z1=E(_Z0);if(!_Z1._){if(!B(A3(_YP,_YS,_Z1.b,_YZ))){return E(_Z1);}else{_Z0=_Z1.d;continue;}}else{return new T0(1);}}};return new F(function(){return _YY(_YX.a,_YV);});}}else{var _Z2=_YW.a,_Z3=E(_YU);if(!_Z3._){var _Z4=function(_Z5,_Z6){while(1){var _Z7=E(_Z6);if(!_Z7._){if(!B(A3(_YN,_YS,_Z7.b,_Z5))){return E(_Z7);}else{_Z6=_Z7.e;continue;}}else{return new T0(1);}}};return new F(function(){return _Z4(_Z2,_YV);});}else{var _Z8=function(_Z9,_Za,_Zb){while(1){var _Zc=E(_Zb);if(!_Zc._){var _Zd=_Zc.b;if(!B(A3(_YN,_YS,_Zd,_Z9))){if(!B(A3(_YP,_YS,_Zd,_Za))){return E(_Zc);}else{_Zb=_Zc.d;continue;}}else{_Zb=_Zc.e;continue;}}else{return new T0(1);}}};return new F(function(){return _Z8(_Z2,_Z3.a,_YV);});}}},_Ze=function(_Zf,_Zg,_Zh,_Zi,_Zj){var _Zk=E(_Zj);if(!_Zk._){var _Zl=_Zk.b,_Zm=_Zk.c,_Zn=_Zk.d,_Zo=_Zk.e,_Zp=E(_Zi);if(!_Zp._){var _Zq=_Zp.b,_Zr=function(_Zs){var _Zt=new T1(1,E(_Zq));return new F(function(){return _C8(_Zq,_Zp.c,B(_Ze(_Zf,_Zg,_Zt,_Zp.d,B(_YR(_Zf,_Zg,_Zt,_Zk)))),B(_Ze(_Zf,_Zt,_Zh,_Zp.e,B(_YR(_Zf,_Zt,_Zh,_Zk)))));});};if(!E(_Zn)._){return new F(function(){return _Zr(_);});}else{if(!E(_Zo)._){return new F(function(){return _Zr(_);});}else{return new F(function(){return _YI(_Zf,_Zl,_Zm,_Zp);});}}}else{return new F(function(){return _C8(_Zl,_Zm,B(_Yb(_Zf,_Zg,_Zn)),B(_Ym(_Zf,_Zh,_Zo)));});}}else{return E(_Zi);}},_Zu=function(_Zv,_Zw,_Zx,_Zy,_Zz,_ZA,_ZB,_ZC,_ZD,_ZE,_ZF,_ZG,_ZH){var _ZI=function(_ZJ){var _ZK=new T1(1,E(_Zz));return new F(function(){return _C8(_Zz,_ZA,B(_Ze(_Zv,_Zw,_ZK,_ZB,B(_YR(_Zv,_Zw,_ZK,new T5(0,_ZD,E(_ZE),_ZF,E(_ZG),E(_ZH)))))),B(_Ze(_Zv,_ZK,_Zx,_ZC,B(_YR(_Zv,_ZK,_Zx,new T5(0,_ZD,E(_ZE),_ZF,E(_ZG),E(_ZH)))))));});};if(!E(_ZG)._){return new F(function(){return _ZI(_);});}else{if(!E(_ZH)._){return new F(function(){return _ZI(_);});}else{return new F(function(){return _YI(_Zv,_ZE,_ZF,new T5(0,_Zy,E(_Zz),_ZA,E(_ZB),E(_ZC)));});}}},_ZL=function(_ZM,_ZN,_ZO){var _ZP=new T(function(){var _ZQ=new T(function(){return E(E(_ZO).b);}),_ZR=B(_XC(function(_ZS,_ZT){var _ZU=E(_ZT);return new F(function(){return _Wn(_ZM,_ZQ,_ZS,_ZU.a,_ZU.b);});},_ZN));return new T2(0,_ZR.a,_ZR.b);}),_ZV=new T(function(){return E(E(_ZP).a);});return new T2(0,new T(function(){var _ZW=B(_Y0(_Y5,_ZV));if(!_ZW._){var _ZX=E(E(_ZP).b);if(!_ZX._){return B(_Zu(_Vr,_XO,_XO,_ZW.a,_ZW.b,_ZW.c,_ZW.d,_ZW.e,_ZX.a,_ZX.b,_ZX.c,_ZX.d,_ZX.e));}else{return E(_ZW);}}else{return E(E(_ZP).b);}}),new T(function(){return B(_XP(_23,_ZV));}));},_ZY=function(_ZZ,_100,_101,_102){while(1){var _103=E(_102);if(!_103._){var _104=_103.d,_105=_103.e,_106=E(_103.b),_107=E(_106.a);if(_ZZ>=_107){if(_ZZ!=_107){_100=_;_102=_105;continue;}else{var _108=E(_106.b);if(_101>=_108){if(_101!=_108){_100=_;_102=_105;continue;}else{return true;}}else{_100=_;_102=_104;continue;}}}else{_100=_;_102=_104;continue;}}else{return false;}}},_109=function(_10a,_10b,_10c,_10d){while(1){var _10e=E(_10d);if(!_10e._){var _10f=_10e.d,_10g=_10e.e,_10h=E(_10e.b),_10i=E(_10h.a);if(_10a>=_10i){if(_10a!=_10i){_10b=_;_10d=_10g;continue;}else{var _10j=E(_10c),_10k=E(_10h.b);if(_10j>=_10k){if(_10j!=_10k){return new F(function(){return _ZY(_10a,_,_10j,_10g);});}else{return true;}}else{return new F(function(){return _ZY(_10a,_,_10j,_10f);});}}}else{_10b=_;_10d=_10f;continue;}}else{return false;}}},_10l=function(_10m,_10n,_10o,_10p,_10q){var _10r=E(_10q);if(!_10r._){var _10s=_10r.c,_10t=_10r.d,_10u=_10r.e,_10v=E(_10r.b),_10w=E(_10v.a);if(_10m>=_10w){if(_10m!=_10w){return new F(function(){return _zX(_10v,_10s,_10t,B(_10l(_10m,_,_10o,_10p,_10u)));});}else{var _10x=E(_10v.b);if(_10o>=_10x){if(_10o!=_10x){return new F(function(){return _zX(_10v,_10s,_10t,B(_10l(_10m,_,_10o,_10p,_10u)));});}else{return new T5(0,_10r.a,E(new T2(0,_10m,_10o)),_10p,E(_10t),E(_10u));}}else{return new F(function(){return _AO(_10v,_10s,B(_10l(_10m,_,_10o,_10p,_10t)),_10u);});}}}else{return new F(function(){return _AO(_10v,_10s,B(_10l(_10m,_,_10o,_10p,_10t)),_10u);});}}else{return new T5(0,1,E(new T2(0,_10m,_10o)),_10p,E(_zS),E(_zS));}},_10y=function(_10z,_10A,_10B,_10C,_10D){var _10E=E(_10D);if(!_10E._){var _10F=_10E.c,_10G=_10E.d,_10H=_10E.e,_10I=E(_10E.b),_10J=E(_10I.a);if(_10z>=_10J){if(_10z!=_10J){return new F(function(){return _zX(_10I,_10F,_10G,B(_10y(_10z,_,_10B,_10C,_10H)));});}else{var _10K=E(_10B),_10L=E(_10I.b);if(_10K>=_10L){if(_10K!=_10L){return new F(function(){return _zX(_10I,_10F,_10G,B(_10l(_10z,_,_10K,_10C,_10H)));});}else{return new T5(0,_10E.a,E(new T2(0,_10z,_10K)),_10C,E(_10G),E(_10H));}}else{return new F(function(){return _AO(_10I,_10F,B(_10l(_10z,_,_10K,_10C,_10G)),_10H);});}}}else{return new F(function(){return _AO(_10I,_10F,B(_10y(_10z,_,_10B,_10C,_10G)),_10H);});}}else{return new T5(0,1,E(new T2(0,_10z,_10B)),_10C,E(_zS),E(_zS));}},_10M=function(_10N,_10O,_10P,_10Q){var _10R=E(_10Q);if(!_10R._){var _10S=_10R.c,_10T=_10R.d,_10U=_10R.e,_10V=E(_10R.b),_10W=E(_10N),_10X=E(_10V.a);if(_10W>=_10X){if(_10W!=_10X){return new F(function(){return _zX(_10V,_10S,_10T,B(_10y(_10W,_,_10O,_10P,_10U)));});}else{var _10Y=E(_10O),_10Z=E(_10V.b);if(_10Y>=_10Z){if(_10Y!=_10Z){return new F(function(){return _zX(_10V,_10S,_10T,B(_10l(_10W,_,_10Y,_10P,_10U)));});}else{return new T5(0,_10R.a,E(new T2(0,_10W,_10Y)),_10P,E(_10T),E(_10U));}}else{return new F(function(){return _AO(_10V,_10S,B(_10l(_10W,_,_10Y,_10P,_10T)),_10U);});}}}else{return new F(function(){return _AO(_10V,_10S,B(_10y(_10W,_,_10O,_10P,_10T)),_10U);});}}else{return new T5(0,1,E(new T2(0,_10N,_10O)),_10P,E(_zS),E(_zS));}},_110=function(_111,_112,_113){while(1){var _114=B((function(_115,_116,_117){var _118=E(_117);if(!_118._){var _119=_118.c,_11a=_118.e,_11b=E(_118.b),_11c=_11b.a,_11d=_11b.b,_11e=B(_110(_115,_116,_118.d)),_11f=_11e.a,_11g=_11e.b,_11h=function(_11i){return new F(function(){return _110(new T(function(){return B(_10M(_11c,_11d,_119,_11f));}),new T2(1,new T3(7,_11c,_11d,_119),_11g),_11a);});},_11j=E(_11f);if(!_11j._){var _11k=_11j.d,_11l=_11j.e,_11m=E(_11j.b),_11n=E(_11c),_11o=E(_11m.a);if(_11n>=_11o){if(_11n!=_11o){if(!B(_109(_11n,_,_11d,_11l))){return new F(function(){return _11h(_);});}else{_111=_11j;_112=_11g;_113=_11a;return __continue;}}else{var _11p=E(_11d),_11q=E(_11m.b);if(_11p>=_11q){if(_11p!=_11q){if(!B(_ZY(_11n,_,_11p,_11l))){return new F(function(){return _11h(_);});}else{_111=_11j;_112=_11g;_113=_11a;return __continue;}}else{_111=_11j;_112=_11g;_113=_11a;return __continue;}}else{if(!B(_ZY(_11n,_,_11p,_11k))){return new F(function(){return _11h(_);});}else{_111=_11j;_112=_11g;_113=_11a;return __continue;}}}}else{if(!B(_109(_11n,_,_11d,_11k))){return new F(function(){return _11h(_);});}else{_111=_11j;_112=_11g;_113=_11a;return __continue;}}}else{return new F(function(){return _11h(_);});}}else{return new T2(0,_115,_116);}})(_111,_112,_113));if(_114!=__continue){return _114;}}},_11r=function(_11s,_11t,_11u,_11v){while(1){var _11w=E(_11v);if(!_11w._){var _11x=_11w.d,_11y=_11w.e,_11z=E(_11w.b),_11A=E(_11z.a);if(_11s>=_11A){if(_11s!=_11A){_11t=_;_11v=_11y;continue;}else{var _11B=E(_11z.b);if(_11u>=_11B){if(_11u!=_11B){_11t=_;_11v=_11y;continue;}else{return new T1(1,_11w.c);}}else{_11t=_;_11v=_11x;continue;}}}else{_11t=_;_11v=_11x;continue;}}else{return __Z;}}},_11C=function(_11D,_11E,_11F,_11G){while(1){var _11H=E(_11G);if(!_11H._){var _11I=_11H.d,_11J=_11H.e,_11K=E(_11H.b),_11L=E(_11K.a);if(_11D>=_11L){if(_11D!=_11L){_11E=_;_11G=_11J;continue;}else{var _11M=E(_11F),_11N=E(_11K.b);if(_11M>=_11N){if(_11M!=_11N){return new F(function(){return _11r(_11D,_,_11M,_11J);});}else{return new T1(1,_11H.c);}}else{return new F(function(){return _11r(_11D,_,_11M,_11I);});}}}else{_11E=_;_11G=_11I;continue;}}else{return __Z;}}},_11O=function(_11P,_11Q,_11R,_11S,_11T){while(1){var _11U=E(_11T);if(!_11U._){var _11V=_11U.c,_11W=_11U.d,_11X=E(_11U.b),_11Y=E(_11P),_11Z=E(_11X.a);if(_11Y>=_11Z){if(_11Y!=_11Z){_11P=_11Y;_11T=_11W;continue;}else{var _120=E(_11Q),_121=E(_11X.b);if(_120>=_121){if(_120!=_121){_11P=_11Y;_11Q=_120;_11T=_11W;continue;}else{var _122=E(_11R),_123=E(_11X.c);if(_122>=_123){if(_122!=_123){_11P=_11Y;_11Q=_120;_11R=_122;_11T=_11W;continue;}else{var _124=E(_11X.d);if(_11S>=_124){if(_11S!=_124){_11P=_11Y;_11Q=_120;_11R=_122;_11T=_11W;continue;}else{return true;}}else{_11P=_11Y;_11Q=_120;_11R=_122;_11T=_11V;continue;}}}else{_11P=_11Y;_11Q=_120;_11R=_122;_11T=_11V;continue;}}}else{_11P=_11Y;_11Q=_120;_11T=_11V;continue;}}}else{_11P=_11Y;_11T=_11V;continue;}}else{return false;}}},_125=function(_126,_127){return E(_126)+E(_127)|0;},_128=0,_129=function(_12a,_12b,_12c){var _12d=function(_12e,_12f){while(1){var _12g=B((function(_12h,_12i){var _12j=E(_12i);if(!_12j._){var _12k=new T(function(){return B(_12d(_12h,_12j.e));}),_12l=function(_12m){var _12n=E(_12j.c),_12o=E(_12n.b);if(!_12o._){if(E(_12n.a)!=E(_12b)){return new F(function(){return A1(_12k,_12m);});}else{if(E(_12o.b)>E(_12c)){return new F(function(){return A1(_12k,new T(function(){return B(_125(_12m,_12o.a));}));});}else{return new F(function(){return A1(_12k,_12m);});}}}else{return new F(function(){return A1(_12k,_12m);});}};_12e=_12l;_12f=_12j.d;return __continue;}else{return E(_12h);}})(_12e,_12f));if(_12g!=__continue){return _12g;}}};return new F(function(){return A3(_12d,_5L,_12a,_128);});},_12p=function(_12q,_12r){while(1){var _12s=E(_12r);if(!_12s._){var _12t=E(_12s.b);if(_12q>=_12t){if(_12q!=_12t){_12r=_12s.e;continue;}else{return new T1(1,_12s.c);}}else{_12r=_12s.d;continue;}}else{return __Z;}}},_12u=new T(function(){return B(unCStr("attempt to discount when insufficient cash available"));}),_12v=new T(function(){return B(err(_12u));}),_12w=function(_12x,_12y){var _12z=E(_12y);if(!_12z._){return E(_12v);}else{var _12A=_12z.b,_12B=E(_12z.a),_12C=_12B.a,_12D=E(_12B.b),_12E=_12D.a,_12F=E(_12D.b);if(!_12F._){var _12G=_12F.b,_12H=E(_12F.a);return (_12x>_12H)?(_12H>=_12x)?E(_12A):new T2(1,new T2(0,_12C,new T2(0,_12E,new T2(0,_128,_12G))),new T(function(){return B(_12w(_12x-_12H|0,_12A));})):new T2(1,new T2(0,_12C,new T2(0,_12E,new T2(0,_12H-_12x|0,_12G))),_23);}else{return E(_12A);}}},_12I=function(_12J,_12K){var _12L=E(_12K);if(!_12L._){return E(_12v);}else{var _12M=_12L.b,_12N=E(_12L.a),_12O=_12N.a,_12P=E(_12N.b),_12Q=_12P.a,_12R=E(_12P.b);if(!_12R._){var _12S=_12R.b,_12T=E(_12J),_12U=E(_12R.a);return (_12T>_12U)?(_12U>=_12T)?E(_12M):new T2(1,new T2(0,_12O,new T2(0,_12Q,new T2(0,_128,_12S))),new T(function(){return B(_12w(_12T-_12U|0,_12M));})):new T2(1,new T2(0,_12O,new T2(0,_12Q,new T2(0,_12U-_12T|0,_12S))),_23);}else{return E(_12M);}}},_12V=function(_12W,_12X){var _12Y=E(_12X);if(!_12Y._){var _12Z=_12Y.b,_130=_12Y.c,_131=_12Y.d,_132=_12Y.e;if(!B(A2(_12W,_12Z,_130))){return new F(function(){return _Xn(B(_12V(_12W,_131)),B(_12V(_12W,_132)));});}else{return new F(function(){return _C8(_12Z,_130,B(_12V(_12W,_131)),B(_12V(_12W,_132)));});}}else{return new T0(1);}},_133=function(_134,_135){var _136=E(_134);if(!_136._){var _137=E(_135);if(!_137._){return new F(function(){return _Vc(_136.b,_137.b);});}else{return 0;}}else{return (E(_135)._==0)?2:1;}},_138=function(_139,_13a){return new F(function(){return _133(E(E(_139).b).b,E(E(_13a).b).b);});},_13b=new T2(1,_23,_23),_13c=function(_13d,_13e){var _13f=function(_13g,_13h){var _13i=E(_13g);if(!_13i._){return E(_13h);}else{var _13j=_13i.a,_13k=E(_13h);if(!_13k._){return E(_13i);}else{var _13l=_13k.a;return (B(A2(_13d,_13j,_13l))==2)?new T2(1,_13l,new T(function(){return B(_13f(_13i,_13k.b));})):new T2(1,_13j,new T(function(){return B(_13f(_13i.b,_13k));}));}}},_13m=function(_13n){var _13o=E(_13n);if(!_13o._){return __Z;}else{var _13p=E(_13o.b);return (_13p._==0)?E(_13o):new T2(1,new T(function(){return B(_13f(_13o.a,_13p.a));}),new T(function(){return B(_13m(_13p.b));}));}},_13q=new T(function(){return B(_13r(B(_13m(_23))));}),_13r=function(_13s){while(1){var _13t=E(_13s);if(!_13t._){return E(_13q);}else{if(!E(_13t.b)._){return E(_13t.a);}else{_13s=B(_13m(_13t));continue;}}}},_13u=new T(function(){return B(_13v(_23));}),_13w=function(_13x,_13y,_13z){while(1){var _13A=B((function(_13B,_13C,_13D){var _13E=E(_13D);if(!_13E._){return new T2(1,new T2(1,_13B,_13C),_13u);}else{var _13F=_13E.a;if(B(A2(_13d,_13B,_13F))==2){var _13G=new T2(1,_13B,_13C);_13x=_13F;_13y=_13G;_13z=_13E.b;return __continue;}else{return new T2(1,new T2(1,_13B,_13C),new T(function(){return B(_13v(_13E));}));}}})(_13x,_13y,_13z));if(_13A!=__continue){return _13A;}}},_13H=function(_13I,_13J,_13K){while(1){var _13L=B((function(_13M,_13N,_13O){var _13P=E(_13O);if(!_13P._){return new T2(1,new T(function(){return B(A1(_13N,new T2(1,_13M,_23)));}),_13u);}else{var _13Q=_13P.a,_13R=_13P.b;switch(B(A2(_13d,_13M,_13Q))){case 0:_13I=_13Q;_13J=function(_13S){return new F(function(){return A1(_13N,new T2(1,_13M,_13S));});};_13K=_13R;return __continue;case 1:_13I=_13Q;_13J=function(_13T){return new F(function(){return A1(_13N,new T2(1,_13M,_13T));});};_13K=_13R;return __continue;default:return new T2(1,new T(function(){return B(A1(_13N,new T2(1,_13M,_23)));}),new T(function(){return B(_13v(_13P));}));}}})(_13I,_13J,_13K));if(_13L!=__continue){return _13L;}}},_13v=function(_13U){var _13V=E(_13U);if(!_13V._){return E(_13b);}else{var _13W=_13V.a,_13X=E(_13V.b);if(!_13X._){return new T2(1,_13V,_23);}else{var _13Y=_13X.a,_13Z=_13X.b;if(B(A2(_13d,_13W,_13Y))==2){return new F(function(){return _13w(_13Y,new T2(1,_13W,_23),_13Z);});}else{return new F(function(){return _13H(_13Y,function(_140){return new T2(1,_13W,_140);},_13Z);});}}}};return new F(function(){return _13r(B(_13v(_13e)));});},_141=function(_142,_143,_144){var _145=B(_Rw(B(_12I(_143,B(_13c(_138,B(_IJ(_23,B(_12V(function(_146,_147){return new F(function(){return A1(_142,_147);});},_144))))))))));if(!_145._){var _148=E(_144);if(!_148._){return new F(function(){return _Zu(_Vr,_XO,_XO,_145.a,_145.b,_145.c,_145.d,_145.e,_148.a,_148.b,_148.c,_148.d,_148.e);});}else{return E(_145);}}else{return E(_144);}},_149=function(_14a,_14b,_14c,_14d){while(1){var _14e=E(_14d);if(!_14e._){var _14f=_14e.d,_14g=_14e.e,_14h=E(_14e.b),_14i=E(_14h.a);if(_14a>=_14i){if(_14a!=_14i){_14b=_;_14d=_14g;continue;}else{var _14j=E(_14h.b);if(_14c>=_14j){if(_14c!=_14j){_14b=_;_14d=_14g;continue;}else{return new T1(1,_14e.c);}}else{_14b=_;_14d=_14f;continue;}}}else{_14b=_;_14d=_14f;continue;}}else{return __Z;}}},_14k=function(_14l,_14m,_14n,_14o){while(1){var _14p=E(_14o);if(!_14p._){var _14q=_14p.d,_14r=_14p.e,_14s=E(_14p.b),_14t=E(_14s.a);if(_14l>=_14t){if(_14l!=_14t){_14m=_;_14o=_14r;continue;}else{var _14u=E(_14n),_14v=E(_14s.b);if(_14u>=_14v){if(_14u!=_14v){return new F(function(){return _149(_14l,_,_14u,_14r);});}else{return new T1(1,_14p.c);}}else{return new F(function(){return _149(_14l,_,_14u,_14q);});}}}else{_14m=_;_14o=_14q;continue;}}else{return __Z;}}},_14w=function(_14x,_14y){var _14z=E(_14y);switch(_14z._){case 0:var _14A=B(_12p(E(_14z.a),_14x));if(!_14A._){return E(_128);}else{var _14B=E(E(_14A.a).b);return (_14B._==0)?E(_14B.a):E(_128);}break;case 1:return B(_14w(_14x,_14z.a))+B(_14w(_14x,_14z.b))|0;default:return E(_14z.a);}},_14C=function(_14D,_14E,_14F){var _14G=E(_14F);if(!_14G._){var _14H=_14G.d,_14I=_14G.e,_14J=E(_14G.b),_14K=E(_14D),_14L=E(_14J.a);if(_14K>=_14L){if(_14K!=_14L){return new F(function(){return _109(_14K,_,_14E,_14I);});}else{var _14M=E(_14E),_14N=E(_14J.b);if(_14M>=_14N){if(_14M!=_14N){return new F(function(){return _ZY(_14K,_,_14M,_14I);});}else{return true;}}else{return new F(function(){return _ZY(_14K,_,_14M,_14H);});}}}else{return new F(function(){return _109(_14K,_,_14E,_14H);});}}else{return false;}},_14O=function(_14P,_14Q,_14R){while(1){var _14S=E(_14Q);switch(_14S._){case 0:return (E(_14S.a)>E(E(_14R).b))?true:false;case 1:if(!B(_14O(_14P,_14S.a,_14R))){return false;}else{_14Q=_14S.b;continue;}break;case 2:if(!B(_14O(_14P,_14S.a,_14R))){_14Q=_14S.b;continue;}else{return true;}break;case 3:return (!B(_14O(_14P,_14S.a,_14R)))?true:false;case 4:var _14T=_14S.b,_14U=_14S.c,_14V=E(E(_14P).b);if(!_14V._){var _14W=_14V.d,_14X=_14V.e,_14Y=E(_14V.b),_14Z=E(_14S.a),_150=E(_14Y.a);if(_14Z>=_150){if(_14Z!=_150){var _151=B(_14k(_14Z,_,_14T,_14X));if(!_151._){return false;}else{return new F(function(){return _Su(_151.a,_14U);});}}else{var _152=E(_14T),_153=E(_14Y.b);if(_152>=_153){if(_152!=_153){var _154=B(_149(_14Z,_,_152,_14X));if(!_154._){return false;}else{return new F(function(){return _Su(_154.a,_14U);});}}else{return new F(function(){return _Su(_14V.c,_14U);});}}else{var _155=B(_149(_14Z,_,_152,_14W));if(!_155._){return false;}else{return new F(function(){return _Su(_155.a,_14U);});}}}}else{var _156=B(_14k(_14Z,_,_14T,_14W));if(!_156._){return false;}else{return new F(function(){return _Su(_156.a,_14U);});}}}else{return false;}break;case 5:return new F(function(){return _14C(_14S.a,_14S.b,E(_14P).b);});break;case 6:var _157=E(_14P).a;return B(_14w(_157,_14S.a))>=B(_14w(_157,_14S.b));case 7:return true;default:return false;}}},_158=function(_159,_15a,_15b,_15c){var _15d=E(_15b);switch(_15d._){case 0:return new T3(0,_15a,_ka,_23);case 1:var _15e=_15d.a,_15f=_15d.b,_15g=_15d.c,_15h=_15d.g,_15i=E(_15d.e),_15j=E(E(_15c).b),_15k=_15i<=_15j,_15l=new T(function(){return E(_15d.d)<=_15j;}),_15m=new T(function(){return B(_QD(E(_15e),new T2(0,_15f,new T(function(){if(!E(_15k)){if(!E(_15l)){return new T2(0,_15g,_15i);}else{return new T0(1);}}else{return new T0(1);}})),E(_15a).a));});return (!E(_15k))?(!E(_15l))?(!B(_11O(_15e,_15f,_15g,_15i,E(_159).a)))?new T3(0,_15a,_15d,_23):new T3(0,new T(function(){return new T2(0,_15m,E(_15a).b);}),_15d.f,new T2(1,new T3(3,_15e,_15f,_15g),_23)):new T3(0,new T(function(){return new T2(0,_15m,E(_15a).b);}),_15h,_23):new T3(0,new T(function(){return new T2(0,_15m,E(_15a).b);}),_15h,_23);case 2:var _15n=_15d.b,_15o=E(_15a),_15p=_15o.a,_15q=E(_15d.a),_15r=B(_12p(_15q,_15p));if(!_15r._){return new T3(0,_15o,_15d,_23);}else{var _15s=E(_15r.a),_15t=_15s.a,_15u=E(_15s.b);if(!_15u._){var _15v=_15u.a;return (!B(_VT(_15q,_,_15t,_15v,E(_159).b)))?new T3(0,_15o,_15d,_23):new T3(0,new T2(0,new T(function(){return B(_QD(_15q,new T2(0,_15t,_Y4),_15p));}),_15o.b),_15n,new T2(1,new T3(4,_15q,_15t,_15v),_23));}else{return new T3(0,_15o,_15n,new T2(1,new T2(6,_15q,_15t),_23));}}break;case 3:var _15w=_15d.a,_15x=_15d.b,_15y=_15d.c,_15z=_15d.d,_15A=_15d.f,_15B=E(E(_15c).b);if(E(_15d.e)>_15B){var _15C=function(_15D){var _15E=E(_15z);if(E(_15D)!=_15E){return new T3(0,_15a,_15d,_23);}else{var _15F=E(_15a),_15G=_15F.a;if(B(_129(_15G,_15x,_15B))<_15E){return new T3(0,_15F,_15A,new T2(1,new T4(2,_15w,_15x,_15y,_15E),_23));}else{var _15H=new T(function(){return B(_141(function(_15I){var _15J=E(_15I),_15K=E(_15J.b);return (_15K._==0)?(E(_15J.a)!=E(_15x))?false:(E(_15K.b)>_15B)?true:false:false;},_15E,_15G));});return new T3(0,new T2(0,_15H,_15F.b),_15A,new T2(1,new T4(0,_15w,_15x,_15y,_15E),_23));}}},_15L=E(E(_159).c);if(!_15L._){var _15M=_15L.d,_15N=_15L.e,_15O=E(_15L.b),_15P=E(_15w),_15Q=E(_15O.a);if(_15P>=_15Q){if(_15P!=_15Q){var _15R=B(_11C(_15P,_,_15y,_15N));if(!_15R._){return new T3(0,_15a,_15d,_23);}else{return new F(function(){return _15C(_15R.a);});}}else{var _15S=E(_15y),_15T=E(_15O.b);if(_15S>=_15T){if(_15S!=_15T){var _15U=B(_11r(_15P,_,_15S,_15N));if(!_15U._){return new T3(0,_15a,_15d,_23);}else{return new F(function(){return _15C(_15U.a);});}}else{return new F(function(){return _15C(_15L.c);});}}else{var _15V=B(_11r(_15P,_,_15S,_15M));if(!_15V._){return new T3(0,_15a,_15d,_23);}else{return new F(function(){return _15C(_15V.a);});}}}}else{var _15W=B(_11C(_15P,_,_15y,_15M));if(!_15W._){return new T3(0,_15a,_15d,_23);}else{return new F(function(){return _15C(_15W.a);});}}}else{return new T3(0,_15a,_15d,_23);}}else{return new T3(0,_15a,_15A,new T2(1,new T4(1,_15w,_15x,_15y,_15z),_23));}break;case 4:var _15X=new T(function(){var _15Y=B(_158(_159,_15a,_15d.a,_15c));return new T3(0,_15Y.a,_15Y.b,_15Y.c);}),_15Z=new T(function(){var _160=B(_158(_159,new T(function(){return E(E(_15X).a);}),_15d.b,_15c));return new T3(0,_160.a,_160.b,_160.c);}),_161=new T(function(){return B(_3(E(_15X).c,new T(function(){return E(E(_15Z).c);},1)));}),_162=new T(function(){var _163=E(_15X).b,_164=E(_15Z).b,_165=function(_166){var _167=E(_164);switch(_167._){case 0:return E(_163);case 1:return new T2(4,_163,_167);case 2:return new T2(4,_163,_167);case 3:return new T2(4,_163,_167);case 4:return new T2(4,_163,_167);case 5:return new T2(4,_163,_167);default:return new T2(4,_163,_167);}};switch(E(_163)._){case 0:return E(_164);break;case 1:return B(_165(_));break;case 2:return B(_165(_));break;case 3:return B(_165(_));break;case 4:return B(_165(_));break;case 5:return B(_165(_));break;default:return B(_165(_));}});return new T3(0,new T(function(){return E(E(_15Z).a);}),_162,_161);case 5:return (!B(_14O(_15a,_15d.a,_15c)))?new T3(0,_15a,_15d.c,_23):new T3(0,_15a,_15d.b,_23);default:var _168=E(_15c);return (E(_15d.b)>E(_168.b))?(!B(_14O(_15a,_15d.a,_168)))?new T3(0,_15a,_15d,_23):new T3(0,_15a,_15d.c,_23):new T3(0,_15a,_15d.d,_23);}},_169=function(_16a,_16b,_16c,_16d){var _16e=new T(function(){var _16f=B(_ZL(_16a,new T(function(){return E(E(_16b).a);},1),_16d));return new T2(0,_16f.a,_16f.b);}),_16g=new T(function(){var _16h=B(_110(new T(function(){return E(E(_16b).b);}),_23,E(_16a).d));return new T2(0,_16h.a,_16h.b);}),_16i=new T(function(){var _16j=new T(function(){var _16k=E(_16b);return new T2(0,new T(function(){return E(E(_16e).a);}),new T(function(){return E(E(_16g).a);}));}),_16l=B(_158(_16a,_16j,_16c,_16d));return new T3(0,_16l.a,_16l.b,_16l.c);}),_16m=new T(function(){var _16n=new T(function(){return B(_3(E(_16e).b,new T(function(){return E(E(_16i).c);},1)));},1);return B(_3(E(_16g).b,_16n));});return new T3(0,new T(function(){return E(E(_16i).a);}),new T(function(){return E(E(_16i).b);}),_16m);},_16o=function(_16p,_16q,_16r,_16s,_16t,_16u){var _16v=new T2(0,_16q,_16r),_16w=B(_169(_16p,_16v,_16s,_16t)),_16x=_16w.b,_16y=_16w.c,_16z=E(_16w.a),_16A=_16z.a,_16B=_16z.b,_16C=function(_16D){return new F(function(){return _16o(_16p,_16A,_16B,_16x,_16t,new T(function(){return B(_3(_16y,_16u));}));});};if(!B(A2(_UY,_16A,_16q))){return new F(function(){return _16C(_);});}else{if(!B(A2(_Uu,_16B,_16r))){return new F(function(){return _16C(_);});}else{if(!B(_T5(_16x,_16s))){return new F(function(){return _16C(_);});}else{if(!B(_Ub(_SM,_16y,_23))){return new F(function(){return _16C(_);});}else{return new T3(0,_16v,_16s,_16u);}}}}},_16E=new T(function(){return B(err(_24));}),_16F=new T(function(){return B(err(_2e));}),_16G=new T(function(){return B(A3(_gt,_gW,_fY,_lU));}),_16H=new T(function(){return B(err(_24));}),_16I=new T(function(){return B(err(_2e));}),_16J=function(_Lr){return new F(function(){return _gi(_he,_Lr);});},_16K=function(_16L,_16M){return new F(function(){return _KH(_16J,_16M);});},_16N=new T(function(){return B(_KH(_16J,_4Y));}),_16O=function(_Lr){return new F(function(){return _3C(_16N,_Lr);});},_16P=function(_16Q){var _16R=new T(function(){return B(A3(_gi,_he,_16Q,_4Y));});return function(_Lo){return new F(function(){return _3C(_16R,_Lo);});};},_16S=new T4(0,_16P,_16O,_16J,_16K),_16T=new T(function(){return B(unCStr("NotRedeemed"));}),_16U=function(_16V,_16W){var _16X=new T(function(){var _16Y=new T(function(){return B(A1(_16W,_Y4));});return B(_fr(function(_16Z){var _170=E(_16Z);return (_170._==3)?(!B(_4r(_170.a,_PP)))?new T0(2):E(_16Y):new T0(2);}));}),_171=function(_172){return E(_16X);},_173=new T(function(){if(E(_16V)>10){return new T0(2);}else{var _174=new T(function(){var _175=new T(function(){var _176=function(_177){return new F(function(){return A3(_gt,_gW,_1,function(_178){return new F(function(){return A1(_16W,new T2(0,_177,_178));});});});};return B(A3(_gt,_gW,_1,_176));});return B(_fr(function(_179){var _17a=E(_179);return (_17a._==3)?(!B(_4r(_17a.a,_16T)))?new T0(2):E(_175):new T0(2);}));}),_17b=function(_17c){return E(_174);};return new T1(1,function(_17d){return new F(function(){return A2(_e8,_17d,_17b);});});}});return new F(function(){return _3M(new T1(1,function(_17e){return new F(function(){return A2(_e8,_17e,_171);});}),_173);});},_17f=function(_Lr){return new F(function(){return _gi(_16U,_Lr);});},_17g=function(_17h,_17i){return new F(function(){return _KH(_17f,_17i);});},_17j=new T(function(){return B(_KH(_17f,_4Y));}),_17k=function(_Lr){return new F(function(){return _3C(_17j,_Lr);});},_17l=function(_17m){var _17n=new T(function(){return B(A3(_gi,_16U,_17m,_4Y));});return function(_Lo){return new F(function(){return _3C(_17n,_Lo);});};},_17o=new T4(0,_17l,_17k,_17f,_17g),_17p=function(_17q,_17r){return new F(function(){return _LW(_Lp,_17o,_17r);});},_17s=new T(function(){return B(_KH(_17p,_4Y));}),_17t=function(_Lr){return new F(function(){return _3C(_17s,_Lr);});},_17u=new T(function(){return B(_LW(_Lp,_17o,_4Y));}),_17v=function(_Lr){return new F(function(){return _3C(_17u,_Lr);});},_17w=function(_17x,_Lr){return new F(function(){return _17v(_Lr);});},_17y=function(_17z,_17A){return new F(function(){return _KH(_17p,_17A);});},_17B=new T4(0,_17w,_17t,_17p,_17y),_17C=function(_17D,_17E){return new F(function(){return _LW(_16S,_17B,_17E);});},_17F=function(_17G,_17H){return new F(function(){return _KH(_17C,_17H);});},_17I=new T(function(){return B(_KH(_17F,_4Y));}),_17J=function(_Mr){return new F(function(){return _3C(_17I,_Mr);});},_17K=function(_17L){return new F(function(){return _KH(_17F,_17L);});},_17M=function(_17N,_17O){return new F(function(){return _17K(_17O);});},_17P=new T(function(){return B(_KH(_17C,_4Y));}),_17Q=function(_Mr){return new F(function(){return _3C(_17P,_Mr);});},_17R=function(_17S,_Mr){return new F(function(){return _17Q(_Mr);});},_17T=new T4(0,_17R,_17J,_17F,_17M),_17U=new T(function(){return B(_LW(_17T,_MB,_lU));}),_17V=new T(function(){return B(unAppCStr("[]",_23));}),_17W=42,_17X=new T2(1,_2J,_23),_17Y=function(_17Z){var _180=E(_17Z);if(!_180._){return E(_17X);}else{var _181=new T(function(){return B(_RR(0,_180.a,new T(function(){return B(_17Y(_180.b));})));});return new T2(1,_2I,_181);}},_182=function(_){var _183=E(_P4),_184=eval(E(_rw)),_185=_184,_186=__app1(E(_185),toJSStr(_183)),_187=E(_Pu),_188=__app1(E(_185),toJSStr(_187)),_189=__app0(E(_m0)),_18a=E(_Pw),_18b=__app1(E(_185),toJSStr(_18a)),_18c=new T(function(){var _18d=B(_m1(B(_3C(_16G,new T(function(){var _18e=String(_18b);return fromJSStr(_18e);})))));if(!_18d._){return E(_16F);}else{if(!E(_18d.b)._){return E(_18d.a);}else{return E(_16E);}}}),_18f=B(_m1(B(_3C(_17U,new T(function(){var _18g=String(_188);return fromJSStr(_18g);})))));if(!_18f._){return E(_16I);}else{if(!E(_18f.b)._){var _18h=E(_18f.a),_18i=new T(function(){var _18j=B(_m1(B(_3C(_lZ,new T(function(){var _18k=String(_189);return fromJSStr(_18k);})))));if(!_18j._){return E(_2f);}else{if(!E(_18j.b)._){return E(_18j.a);}else{return E(_25);}}}),_18l=new T(function(){var _18m=B(_m1(B(_3C(_P3,new T(function(){var _18n=String(_186);return fromJSStr(_18n);})))));if(!_18m._){return E(_KD);}else{if(!E(_18m.b)._){var _18o=E(_18m.a);return new T4(0,new T(function(){return B(_vg(_18o.a));}),new T(function(){return B(_zD(_18o.b));}),new T(function(){return B(_It(_18o.c));}),new T(function(){return B(_Fj(_18o.d));}));}else{return E(_KC);}}}),_18p=B(_16o(_18l,new T(function(){return B(_Rw(_18h.a));}),new T(function(){return B(_Fj(_18h.b));}),_18i,new T2(0,_17W,_18c),_23)),_18q=function(_,_18r){var _18s=B(_29(_26,B(_1u(_m8,_18p.b,_23)),_)),_18t=E(_18p.a),_18u=new T(function(){var _18v=new T(function(){return B(_IJ(_23,_18t.b));}),_18w=new T(function(){return B(_IJ(_23,_18t.a));});return B(A3(_Jw,_IQ,new T2(1,function(_18x){return new F(function(){return _Qf(_18w,_18x);});},new T2(1,function(_18y){return new F(function(){return _Kd(_18v,_18y);});},_23)),_Kg));}),_18z=B(_29(_187,new T2(1,_c,_18u),_)),_18A=B(_29(_183,_Ps,_)),_18B=B(_29(_18a,B(_d(0,E(_18c)+1|0,_23)),_)),_18C=__app1(E(_185),toJSStr(E(_26)));return new F(function(){return _ro(new T(function(){var _18D=String(_18C);return fromJSStr(_18D);}),_);});},_18E=E(_18p.c);if(!_18E._){var _18F=B(_29(_Pr,_17V,_));return new F(function(){return _18q(_,_18F);});}else{var _18G=new T(function(){return B(_RR(0,_18E.a,new T(function(){return B(_17Y(_18E.b));})));}),_18H=B(_29(_Pr,new T2(1,_2K,_18G),_));return new F(function(){return _18q(_,_18H);});}}else{return E(_16H);}}},_18I=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_18J=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_18K=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_18L=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_18M=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_18N=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_18O=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_18P=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_18Q=function(_){return new F(function(){return __jsNull();});},_18R=function(_18S){var _18T=B(A1(_18S,_));return E(_18T);},_18U=new T(function(){return B(_18R(_18Q));}),_18V=new T(function(){return E(_18U);}),_18W=function(_18X,_18Y,_18Z,_){var _190=E(_P4),_191=eval(E(_rw)),_192=__app1(E(_191),toJSStr(_190)),_193=B(_m1(B(_3C(_P3,new T(function(){var _194=String(_192);return fromJSStr(_194);})))));if(!_193._){return E(_KD);}else{if(!E(_193.b)._){var _195=E(_193.a),_196=B(_Ko(new T(function(){return B(_vg(_195.a));},1),new T(function(){return B(_xM(_18Z,_18X,_18Y,B(_zD(_195.b))));},1),new T(function(){return B(_It(_195.c));},1),new T(function(){return B(_Fj(_195.d));},1)));return new F(function(){return _29(_190,new T2(1,_196.a,_196.b),_);});}else{return E(_KC);}}},_197=function(_){var _198=eval(E(_rw)),_199=__app1(E(_198),toJSStr(E(_26))),_19a=B(_ro(new T(function(){var _19b=String(_199);return fromJSStr(_19b);}),_)),_19c=__createJSFunc(0,function(_){var _19d=B(_Px(_));return _18V;}),_19e=__app2(E(_18K),"clear_workspace",_19c),_19f=__createJSFunc(0,function(_){var _19g=B(_m9(_));return _18V;}),_19h=__app2(E(_18J),"b2c",_19f),_19i=__createJSFunc(0,function(_){var _19j=B(_rx(_));return _18V;}),_19k=__app2(E(_18I),"c2b",_19i),_19l=function(_19m){var _19n=new T(function(){var _19o=Number(E(_19m));return jsTrunc(_19o);}),_19p=function(_19q){var _19r=new T(function(){var _19s=Number(E(_19q));return jsTrunc(_19s);}),_19t=function(_19u){var _19v=new T(function(){var _19w=Number(E(_19u));return jsTrunc(_19w);}),_19x=function(_19y,_){var _19z=B(_PD(_19n,_19r,_19v,new T(function(){var _19A=Number(E(_19y));return jsTrunc(_19A);}),_));return _18V;};return E(_19x);};return E(_19t);};return E(_19p);},_19B=__createJSFunc(5,E(_19l)),_19C=__app2(E(_18P),"commit",_19B),_19D=function(_19E){var _19F=new T(function(){var _19G=Number(E(_19E));return jsTrunc(_19G);}),_19H=function(_19I){var _19J=new T(function(){var _19K=Number(E(_19I));return jsTrunc(_19K);}),_19L=function(_19M,_){var _19N=B(_18W(_19F,_19J,new T(function(){var _19O=Number(E(_19M));return jsTrunc(_19O);}),_));return _18V;};return E(_19L);};return E(_19H);},_19P=__createJSFunc(4,E(_19D)),_19Q=__app2(E(_18O),"redeem",_19P),_19R=function(_19S){var _19T=new T(function(){var _19U=Number(E(_19S));return jsTrunc(_19U);}),_19V=function(_19W){var _19X=new T(function(){var _19Y=Number(E(_19W));return jsTrunc(_19Y);}),_19Z=function(_1a0,_){var _1a1=B(_Pg(_19T,_19X,new T(function(){var _1a2=Number(E(_1a0));return jsTrunc(_1a2);}),_));return _18V;};return E(_19Z);};return E(_19V);},_1a3=__createJSFunc(4,E(_19R)),_1a4=__app2(E(_18N),"claim",_1a3),_1a5=function(_1a6){var _1a7=new T(function(){var _1a8=Number(E(_1a6));return jsTrunc(_1a8);}),_1a9=function(_1aa){var _1ab=new T(function(){var _1ac=Number(E(_1aa));return jsTrunc(_1ac);}),_1ad=function(_1ae,_){var _1af=B(_P5(_1a7,_1ab,new T(function(){var _1ag=Number(E(_1ae));return jsTrunc(_1ag);}),_));return _18V;};return E(_1ad);};return E(_1a9);},_1ah=__createJSFunc(4,E(_1a5)),_1ai=__app2(E(_18M),"choose",_1ah),_1aj=__createJSFunc(0,function(_){var _1ak=B(_182(_));return _18V;}),_1al=__app2(E(_18L),"execute",_1aj);return _0;},_1am=function(_){return new F(function(){return _197(_);});};
var hasteMain = function() {B(A(_1am, [0]));};window.onload = hasteMain;
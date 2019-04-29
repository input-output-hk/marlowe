"use strict";
var __haste_prog_id = 'f3e690e4e73190c3f6884b5d075434e54bd6c1412bdd561b84a34914426777cc';
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

var _0=new T0(1),_1=__Z,_2=function(_3,_4){var _5=E(_3);if(!_5._){var _6=_5.a,_7=E(_4);if(!_7._){var _8=_7.a;return (_6!=_8)?(_6>_8)?2:0:1;}else{var _9=I_compareInt(_7.a,_6);return (_9<=0)?(_9>=0)?1:2:0;}}else{var _a=_5.a,_b=E(_4);if(!_b._){var _c=I_compareInt(_a,_b.a);return (_c>=0)?(_c<=0)?1:2:0;}else{var _d=I_compare(_a,_b.a);return (_d>=0)?(_d<=0)?1:2:0;}}},_e=function(_f,_g){var _h=E(_f);if(!_h._){var _i=_h.a,_j=E(_g);return (_j._==0)?_i>=_j.a:I_compareInt(_j.a,_i)<=0;}else{var _k=_h.a,_l=E(_g);return (_l._==0)?I_compareInt(_k,_l.a)>=0:I_compare(_k,_l.a)>=0;}},_m=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_n=function(_o){return new F(function(){return err(_m);});},_p=new T(function(){return B(_n(_));}),_q=function(_r,_s,_t,_u){var _v=E(_t);if(!_v._){var _w=_v.a,_x=E(_u);if(!_x._){var _y=_x.a,_z=_x.b,_A=_x.c;if(_y<=(imul(3,_w)|0)){return new T5(0,(1+_w|0)+_y|0,E(_r),_s,E(_v),E(_x));}else{var _B=E(_x.d);if(!_B._){var _C=_B.a,_D=_B.b,_E=_B.c,_F=_B.d,_G=E(_x.e);if(!_G._){var _H=_G.a;if(_C>=(imul(2,_H)|0)){var _I=function(_J){var _K=E(_r),_L=E(_B.e);return (_L._==0)?new T5(0,(1+_w|0)+_y|0,E(_D),_E,E(new T5(0,(1+_w|0)+_J|0,E(_K),_s,E(_v),E(_F))),E(new T5(0,(1+_H|0)+_L.a|0,E(_z),_A,E(_L),E(_G)))):new T5(0,(1+_w|0)+_y|0,E(_D),_E,E(new T5(0,(1+_w|0)+_J|0,E(_K),_s,E(_v),E(_F))),E(new T5(0,1+_H|0,E(_z),_A,E(_0),E(_G))));},_M=E(_F);if(!_M._){return new F(function(){return _I(_M.a);});}else{return new F(function(){return _I(0);});}}else{return new T5(0,(1+_w|0)+_y|0,E(_z),_A,E(new T5(0,(1+_w|0)+_C|0,E(_r),_s,E(_v),E(_B))),E(_G));}}else{return E(_p);}}else{return E(_p);}}}else{return new T5(0,1+_w|0,E(_r),_s,E(_v),E(_0));}}else{var _N=E(_u);if(!_N._){var _O=_N.a,_P=_N.b,_Q=_N.c,_R=_N.e,_S=E(_N.d);if(!_S._){var _T=_S.a,_U=_S.b,_V=_S.c,_W=_S.d,_X=E(_R);if(!_X._){var _Y=_X.a;if(_T>=(imul(2,_Y)|0)){var _Z=function(_10){var _11=E(_r),_12=E(_S.e);return (_12._==0)?new T5(0,1+_O|0,E(_U),_V,E(new T5(0,1+_10|0,E(_11),_s,E(_0),E(_W))),E(new T5(0,(1+_Y|0)+_12.a|0,E(_P),_Q,E(_12),E(_X)))):new T5(0,1+_O|0,E(_U),_V,E(new T5(0,1+_10|0,E(_11),_s,E(_0),E(_W))),E(new T5(0,1+_Y|0,E(_P),_Q,E(_0),E(_X))));},_13=E(_W);if(!_13._){return new F(function(){return _Z(_13.a);});}else{return new F(function(){return _Z(0);});}}else{return new T5(0,1+_O|0,E(_P),_Q,E(new T5(0,1+_T|0,E(_r),_s,E(_0),E(_S))),E(_X));}}else{return new T5(0,3,E(_U),_V,E(new T5(0,1,E(_r),_s,E(_0),E(_0))),E(new T5(0,1,E(_P),_Q,E(_0),E(_0))));}}else{var _14=E(_R);return (_14._==0)?new T5(0,3,E(_P),_Q,E(new T5(0,1,E(_r),_s,E(_0),E(_0))),E(_14)):new T5(0,2,E(_r),_s,E(_0),E(_N));}}else{return new T5(0,1,E(_r),_s,E(_0),E(_0));}}},_15=function(_16,_17){return new T5(0,1,E(_16),_17,E(_0),E(_0));},_18=function(_19,_1a,_1b){var _1c=E(_1b);if(!_1c._){return new F(function(){return _q(_1c.b,_1c.c,_1c.d,B(_18(_19,_1a,_1c.e)));});}else{return new F(function(){return _15(_19,_1a);});}},_1d=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_1e=function(_1f){return new F(function(){return err(_1d);});},_1g=new T(function(){return B(_1e(_));}),_1h=function(_1i,_1j,_1k,_1l){var _1m=E(_1l);if(!_1m._){var _1n=_1m.a,_1o=E(_1k);if(!_1o._){var _1p=_1o.a,_1q=_1o.b,_1r=_1o.c;if(_1p<=(imul(3,_1n)|0)){return new T5(0,(1+_1p|0)+_1n|0,E(_1i),_1j,E(_1o),E(_1m));}else{var _1s=E(_1o.d);if(!_1s._){var _1t=_1s.a,_1u=E(_1o.e);if(!_1u._){var _1v=_1u.a,_1w=_1u.b,_1x=_1u.c,_1y=_1u.d;if(_1v>=(imul(2,_1t)|0)){var _1z=function(_1A){var _1B=E(_1u.e);return (_1B._==0)?new T5(0,(1+_1p|0)+_1n|0,E(_1w),_1x,E(new T5(0,(1+_1t|0)+_1A|0,E(_1q),_1r,E(_1s),E(_1y))),E(new T5(0,(1+_1n|0)+_1B.a|0,E(_1i),_1j,E(_1B),E(_1m)))):new T5(0,(1+_1p|0)+_1n|0,E(_1w),_1x,E(new T5(0,(1+_1t|0)+_1A|0,E(_1q),_1r,E(_1s),E(_1y))),E(new T5(0,1+_1n|0,E(_1i),_1j,E(_0),E(_1m))));},_1C=E(_1y);if(!_1C._){return new F(function(){return _1z(_1C.a);});}else{return new F(function(){return _1z(0);});}}else{return new T5(0,(1+_1p|0)+_1n|0,E(_1q),_1r,E(_1s),E(new T5(0,(1+_1n|0)+_1v|0,E(_1i),_1j,E(_1u),E(_1m))));}}else{return E(_1g);}}else{return E(_1g);}}}else{return new T5(0,1+_1n|0,E(_1i),_1j,E(_0),E(_1m));}}else{var _1D=E(_1k);if(!_1D._){var _1E=_1D.a,_1F=_1D.b,_1G=_1D.c,_1H=_1D.e,_1I=E(_1D.d);if(!_1I._){var _1J=_1I.a,_1K=E(_1H);if(!_1K._){var _1L=_1K.a,_1M=_1K.b,_1N=_1K.c,_1O=_1K.d;if(_1L>=(imul(2,_1J)|0)){var _1P=function(_1Q){var _1R=E(_1K.e);return (_1R._==0)?new T5(0,1+_1E|0,E(_1M),_1N,E(new T5(0,(1+_1J|0)+_1Q|0,E(_1F),_1G,E(_1I),E(_1O))),E(new T5(0,1+_1R.a|0,E(_1i),_1j,E(_1R),E(_0)))):new T5(0,1+_1E|0,E(_1M),_1N,E(new T5(0,(1+_1J|0)+_1Q|0,E(_1F),_1G,E(_1I),E(_1O))),E(new T5(0,1,E(_1i),_1j,E(_0),E(_0))));},_1S=E(_1O);if(!_1S._){return new F(function(){return _1P(_1S.a);});}else{return new F(function(){return _1P(0);});}}else{return new T5(0,1+_1E|0,E(_1F),_1G,E(_1I),E(new T5(0,1+_1L|0,E(_1i),_1j,E(_1K),E(_0))));}}else{return new T5(0,3,E(_1F),_1G,E(_1I),E(new T5(0,1,E(_1i),_1j,E(_0),E(_0))));}}else{var _1T=E(_1H);return (_1T._==0)?new T5(0,3,E(_1T.b),_1T.c,E(new T5(0,1,E(_1F),_1G,E(_0),E(_0))),E(new T5(0,1,E(_1i),_1j,E(_0),E(_0)))):new T5(0,2,E(_1i),_1j,E(_1D),E(_0));}}else{return new T5(0,1,E(_1i),_1j,E(_0),E(_0));}}},_1U=function(_1V,_1W,_1X){var _1Y=E(_1X);if(!_1Y._){return new F(function(){return _1h(_1Y.b,_1Y.c,B(_1U(_1V,_1W,_1Y.d)),_1Y.e);});}else{return new F(function(){return _15(_1V,_1W);});}},_1Z=function(_20,_21,_22,_23,_24,_25,_26){return new F(function(){return _1h(_23,_24,B(_1U(_20,_21,_25)),_26);});},_27=function(_28,_29,_2a,_2b,_2c,_2d,_2e,_2f){var _2g=E(_2a);if(!_2g._){var _2h=_2g.a,_2i=_2g.b,_2j=_2g.c,_2k=_2g.d,_2l=_2g.e;if((imul(3,_2h)|0)>=_2b){if((imul(3,_2b)|0)>=_2h){return new T5(0,(_2h+_2b|0)+1|0,E(_28),_29,E(_2g),E(new T5(0,_2b,E(_2c),_2d,E(_2e),E(_2f))));}else{return new F(function(){return _q(_2i,_2j,_2k,B(_27(_28,_29,_2l,_2b,_2c,_2d,_2e,_2f)));});}}else{return new F(function(){return _1h(_2c,_2d,B(_2m(_28,_29,_2h,_2i,_2j,_2k,_2l,_2e)),_2f);});}}else{return new F(function(){return _1Z(_28,_29,_2b,_2c,_2d,_2e,_2f);});}},_2m=function(_2n,_2o,_2p,_2q,_2r,_2s,_2t,_2u){var _2v=E(_2u);if(!_2v._){var _2w=_2v.a,_2x=_2v.b,_2y=_2v.c,_2z=_2v.d,_2A=_2v.e;if((imul(3,_2p)|0)>=_2w){if((imul(3,_2w)|0)>=_2p){return new T5(0,(_2p+_2w|0)+1|0,E(_2n),_2o,E(new T5(0,_2p,E(_2q),_2r,E(_2s),E(_2t))),E(_2v));}else{return new F(function(){return _q(_2q,_2r,_2s,B(_27(_2n,_2o,_2t,_2w,_2x,_2y,_2z,_2A)));});}}else{return new F(function(){return _1h(_2x,_2y,B(_2m(_2n,_2o,_2p,_2q,_2r,_2s,_2t,_2z)),_2A);});}}else{return new F(function(){return _18(_2n,_2o,new T5(0,_2p,E(_2q),_2r,E(_2s),E(_2t)));});}},_2B=function(_2C,_2D,_2E,_2F){var _2G=E(_2E);if(!_2G._){var _2H=_2G.a,_2I=_2G.b,_2J=_2G.c,_2K=_2G.d,_2L=_2G.e,_2M=E(_2F);if(!_2M._){var _2N=_2M.a,_2O=_2M.b,_2P=_2M.c,_2Q=_2M.d,_2R=_2M.e;if((imul(3,_2H)|0)>=_2N){if((imul(3,_2N)|0)>=_2H){return new T5(0,(_2H+_2N|0)+1|0,E(_2C),_2D,E(_2G),E(_2M));}else{return new F(function(){return _q(_2I,_2J,_2K,B(_27(_2C,_2D,_2L,_2N,_2O,_2P,_2Q,_2R)));});}}else{return new F(function(){return _1h(_2O,_2P,B(_2m(_2C,_2D,_2H,_2I,_2J,_2K,_2L,_2Q)),_2R);});}}else{return new F(function(){return _18(_2C,_2D,_2G);});}}else{return new F(function(){return _1U(_2C,_2D,_2F);});}},_2S=function(_2T,_2U,_2V,_2W,_2X){var _2Y=E(_2T);if(_2Y==1){var _2Z=E(_2X);if(!_2Z._){return new T3(0,new T5(0,1,E(new T2(0,_2U,_2V)),_2W,E(_0),E(_0)),_1,_1);}else{var _30=E(E(_2Z.a).a);switch(B(_2(_2U,_30.a))){case 0:return new T3(0,new T5(0,1,E(new T2(0,_2U,_2V)),_2W,E(_0),E(_0)),_2Z,_1);case 1:return (!B(_e(_2V,_30.b)))?new T3(0,new T5(0,1,E(new T2(0,_2U,_2V)),_2W,E(_0),E(_0)),_2Z,_1):new T3(0,new T5(0,1,E(new T2(0,_2U,_2V)),_2W,E(_0),E(_0)),_1,_2Z);default:return new T3(0,new T5(0,1,E(new T2(0,_2U,_2V)),_2W,E(_0),E(_0)),_1,_2Z);}}}else{var _31=B(_2S(_2Y>>1,_2U,_2V,_2W,_2X)),_32=_31.a,_33=_31.c,_34=E(_31.b);if(!_34._){return new T3(0,_32,_1,_33);}else{var _35=E(_34.a),_36=_35.a,_37=_35.b,_38=E(_34.b);if(!_38._){return new T3(0,new T(function(){return B(_18(_36,_37,_32));}),_1,_33);}else{var _39=_38.b,_3a=E(_38.a),_3b=_3a.b,_3c=E(_36),_3d=E(_3a.a),_3e=_3d.a,_3f=_3d.b;switch(B(_2(_3c.a,_3e))){case 0:var _3g=B(_2S(_2Y>>1,_3e,_3f,_3b,_39));return new T3(0,new T(function(){return B(_2B(_3c,_37,_32,_3g.a));}),_3g.b,_3g.c);case 1:if(!B(_e(_3c.b,_3f))){var _3h=B(_2S(_2Y>>1,_3e,_3f,_3b,_39));return new T3(0,new T(function(){return B(_2B(_3c,_37,_32,_3h.a));}),_3h.b,_3h.c);}else{return new T3(0,_32,_1,_34);}break;default:return new T3(0,_32,_1,_34);}}}}},_3i=function(_3j,_3k,_3l,_3m){var _3n=E(_3m);if(!_3n._){var _3o=_3n.c,_3p=_3n.d,_3q=_3n.e,_3r=E(_3n.b);switch(B(_2(_3j,_3r.a))){case 0:return new F(function(){return _1h(_3r,_3o,B(_3i(_3j,_3k,_3l,_3p)),_3q);});break;case 1:switch(B(_2(_3k,_3r.b))){case 0:return new F(function(){return _1h(_3r,_3o,B(_3i(_3j,_3k,_3l,_3p)),_3q);});break;case 1:return new T5(0,_3n.a,E(new T2(0,_3j,_3k)),_3l,E(_3p),E(_3q));default:return new F(function(){return _q(_3r,_3o,_3p,B(_3i(_3j,_3k,_3l,_3q)));});}break;default:return new F(function(){return _q(_3r,_3o,_3p,B(_3i(_3j,_3k,_3l,_3q)));});}}else{return new T5(0,1,E(new T2(0,_3j,_3k)),_3l,E(_0),E(_0));}},_3s=function(_3t,_3u){while(1){var _3v=E(_3u);if(!_3v._){return E(_3t);}else{var _3w=E(_3v.a),_3x=E(_3w.a),_3y=B(_3i(_3x.a,_3x.b,_3w.b,_3t));_3t=_3y;_3u=_3v.b;continue;}}},_3z=function(_3A,_3B,_3C,_3D,_3E){return new F(function(){return _3s(B(_3i(_3B,_3C,_3D,_3A)),_3E);});},_3F=function(_3G,_3H,_3I){var _3J=E(_3H),_3K=E(_3J.a);return new F(function(){return _3s(B(_3i(_3K.a,_3K.b,_3J.b,_3G)),_3I);});},_3L=function(_3M,_3N,_3O){var _3P=E(_3O);if(!_3P._){return E(_3N);}else{var _3Q=E(_3P.a),_3R=_3Q.a,_3S=_3Q.b,_3T=E(_3P.b);if(!_3T._){return new F(function(){return _18(_3R,_3S,_3N);});}else{var _3U=E(_3T.a),_3V=E(_3R),_3W=_3V.a,_3X=_3V.b,_3Y=E(_3U.a),_3Z=_3Y.a,_40=_3Y.b,_41=function(_42){var _43=B(_2S(_3M,_3Z,_40,_3U.b,_3T.b)),_44=_43.a,_45=E(_43.c);if(!_45._){return new F(function(){return _3L(_3M<<1,B(_2B(_3V,_3S,_3N,_44)),_43.b);});}else{return new F(function(){return _3F(B(_2B(_3V,_3S,_3N,_44)),_45.a,_45.b);});}};switch(B(_2(_3W,_3Z))){case 0:return new F(function(){return _41(_);});break;case 1:if(!B(_e(_3X,_40))){return new F(function(){return _41(_);});}else{return new F(function(){return _3z(_3N,_3W,_3X,_3S,_3T);});}break;default:return new F(function(){return _3z(_3N,_3W,_3X,_3S,_3T);});}}}},_46=function(_47,_48,_49,_4a,_4b,_4c){var _4d=E(_4c);if(!_4d._){return new F(function(){return _18(new T2(0,_49,_4a),_4b,_48);});}else{var _4e=E(_4d.a),_4f=E(_4e.a),_4g=_4f.a,_4h=_4f.b,_4i=function(_4j){var _4k=B(_2S(_47,_4g,_4h,_4e.b,_4d.b)),_4l=_4k.a,_4m=E(_4k.c);if(!_4m._){return new F(function(){return _3L(_47<<1,B(_2B(new T2(0,_49,_4a),_4b,_48,_4l)),_4k.b);});}else{return new F(function(){return _3F(B(_2B(new T2(0,_49,_4a),_4b,_48,_4l)),_4m.a,_4m.b);});}};switch(B(_2(_49,_4g))){case 0:return new F(function(){return _4i(_);});break;case 1:if(!B(_e(_4a,_4h))){return new F(function(){return _4i(_);});}else{return new F(function(){return _3z(_48,_49,_4a,_4b,_4d);});}break;default:return new F(function(){return _3z(_48,_49,_4a,_4b,_4d);});}}},_4n=function(_4o){var _4p=E(_4o);if(!_4p._){return new T0(1);}else{var _4q=E(_4p.a),_4r=_4q.a,_4s=_4q.b,_4t=E(_4p.b);if(!_4t._){return new T5(0,1,E(_4r),_4s,E(_0),E(_0));}else{var _4u=_4t.b,_4v=E(_4t.a),_4w=_4v.b,_4x=E(_4r),_4y=E(_4v.a),_4z=_4y.a,_4A=_4y.b;switch(B(_2(_4x.a,_4z))){case 0:return new F(function(){return _46(1,new T5(0,1,E(_4x),_4s,E(_0),E(_0)),_4z,_4A,_4w,_4u);});break;case 1:if(!B(_e(_4x.b,_4A))){return new F(function(){return _46(1,new T5(0,1,E(_4x),_4s,E(_0),E(_0)),_4z,_4A,_4w,_4u);});}else{return new F(function(){return _3z(new T5(0,1,E(_4x),_4s,E(_0),E(_0)),_4z,_4A,_4w,_4u);});}break;default:return new F(function(){return _3z(new T5(0,1,E(_4x),_4s,E(_0),E(_0)),_4z,_4A,_4w,_4u);});}}}},_4B=new T0(1),_4C=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_4D=function(_4E){return new F(function(){return err(_4C);});},_4F=new T(function(){return B(_4D(_));}),_4G=function(_4H,_4I,_4J){var _4K=E(_4I);if(!_4K._){var _4L=_4K.a,_4M=E(_4J);if(!_4M._){var _4N=_4M.a,_4O=_4M.b;if(_4N<=(imul(3,_4L)|0)){return new T4(0,(1+_4L|0)+_4N|0,E(_4H),E(_4K),E(_4M));}else{var _4P=E(_4M.c);if(!_4P._){var _4Q=_4P.a,_4R=_4P.b,_4S=_4P.c,_4T=E(_4M.d);if(!_4T._){var _4U=_4T.a;if(_4Q>=(imul(2,_4U)|0)){var _4V=function(_4W){var _4X=E(_4H),_4Y=E(_4P.d);return (_4Y._==0)?new T4(0,(1+_4L|0)+_4N|0,E(_4R),E(new T4(0,(1+_4L|0)+_4W|0,E(_4X),E(_4K),E(_4S))),E(new T4(0,(1+_4U|0)+_4Y.a|0,E(_4O),E(_4Y),E(_4T)))):new T4(0,(1+_4L|0)+_4N|0,E(_4R),E(new T4(0,(1+_4L|0)+_4W|0,E(_4X),E(_4K),E(_4S))),E(new T4(0,1+_4U|0,E(_4O),E(_4B),E(_4T))));},_4Z=E(_4S);if(!_4Z._){return new F(function(){return _4V(_4Z.a);});}else{return new F(function(){return _4V(0);});}}else{return new T4(0,(1+_4L|0)+_4N|0,E(_4O),E(new T4(0,(1+_4L|0)+_4Q|0,E(_4H),E(_4K),E(_4P))),E(_4T));}}else{return E(_4F);}}else{return E(_4F);}}}else{return new T4(0,1+_4L|0,E(_4H),E(_4K),E(_4B));}}else{var _50=E(_4J);if(!_50._){var _51=_50.a,_52=_50.b,_53=_50.d,_54=E(_50.c);if(!_54._){var _55=_54.a,_56=_54.b,_57=_54.c,_58=E(_53);if(!_58._){var _59=_58.a;if(_55>=(imul(2,_59)|0)){var _5a=function(_5b){var _5c=E(_4H),_5d=E(_54.d);return (_5d._==0)?new T4(0,1+_51|0,E(_56),E(new T4(0,1+_5b|0,E(_5c),E(_4B),E(_57))),E(new T4(0,(1+_59|0)+_5d.a|0,E(_52),E(_5d),E(_58)))):new T4(0,1+_51|0,E(_56),E(new T4(0,1+_5b|0,E(_5c),E(_4B),E(_57))),E(new T4(0,1+_59|0,E(_52),E(_4B),E(_58))));},_5e=E(_57);if(!_5e._){return new F(function(){return _5a(_5e.a);});}else{return new F(function(){return _5a(0);});}}else{return new T4(0,1+_51|0,E(_52),E(new T4(0,1+_55|0,E(_4H),E(_4B),E(_54))),E(_58));}}else{return new T4(0,3,E(_56),E(new T4(0,1,E(_4H),E(_4B),E(_4B))),E(new T4(0,1,E(_52),E(_4B),E(_4B))));}}else{var _5f=E(_53);return (_5f._==0)?new T4(0,3,E(_52),E(new T4(0,1,E(_4H),E(_4B),E(_4B))),E(_5f)):new T4(0,2,E(_4H),E(_4B),E(_50));}}else{return new T4(0,1,E(_4H),E(_4B),E(_4B));}}},_5g=function(_5h){return new T4(0,1,E(_5h),E(_4B),E(_4B));},_5i=function(_5j,_5k){var _5l=E(_5k);if(!_5l._){return new F(function(){return _4G(_5l.b,_5l.c,B(_5i(_5j,_5l.d)));});}else{return new F(function(){return _5g(_5j);});}},_5m=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_5n=function(_5o){return new F(function(){return err(_5m);});},_5p=new T(function(){return B(_5n(_));}),_5q=function(_5r,_5s,_5t){var _5u=E(_5t);if(!_5u._){var _5v=_5u.a,_5w=E(_5s);if(!_5w._){var _5x=_5w.a,_5y=_5w.b;if(_5x<=(imul(3,_5v)|0)){return new T4(0,(1+_5x|0)+_5v|0,E(_5r),E(_5w),E(_5u));}else{var _5z=E(_5w.c);if(!_5z._){var _5A=_5z.a,_5B=E(_5w.d);if(!_5B._){var _5C=_5B.a,_5D=_5B.b,_5E=_5B.c;if(_5C>=(imul(2,_5A)|0)){var _5F=function(_5G){var _5H=E(_5B.d);return (_5H._==0)?new T4(0,(1+_5x|0)+_5v|0,E(_5D),E(new T4(0,(1+_5A|0)+_5G|0,E(_5y),E(_5z),E(_5E))),E(new T4(0,(1+_5v|0)+_5H.a|0,E(_5r),E(_5H),E(_5u)))):new T4(0,(1+_5x|0)+_5v|0,E(_5D),E(new T4(0,(1+_5A|0)+_5G|0,E(_5y),E(_5z),E(_5E))),E(new T4(0,1+_5v|0,E(_5r),E(_4B),E(_5u))));},_5I=E(_5E);if(!_5I._){return new F(function(){return _5F(_5I.a);});}else{return new F(function(){return _5F(0);});}}else{return new T4(0,(1+_5x|0)+_5v|0,E(_5y),E(_5z),E(new T4(0,(1+_5v|0)+_5C|0,E(_5r),E(_5B),E(_5u))));}}else{return E(_5p);}}else{return E(_5p);}}}else{return new T4(0,1+_5v|0,E(_5r),E(_4B),E(_5u));}}else{var _5J=E(_5s);if(!_5J._){var _5K=_5J.a,_5L=_5J.b,_5M=_5J.d,_5N=E(_5J.c);if(!_5N._){var _5O=_5N.a,_5P=E(_5M);if(!_5P._){var _5Q=_5P.a,_5R=_5P.b,_5S=_5P.c;if(_5Q>=(imul(2,_5O)|0)){var _5T=function(_5U){var _5V=E(_5P.d);return (_5V._==0)?new T4(0,1+_5K|0,E(_5R),E(new T4(0,(1+_5O|0)+_5U|0,E(_5L),E(_5N),E(_5S))),E(new T4(0,1+_5V.a|0,E(_5r),E(_5V),E(_4B)))):new T4(0,1+_5K|0,E(_5R),E(new T4(0,(1+_5O|0)+_5U|0,E(_5L),E(_5N),E(_5S))),E(new T4(0,1,E(_5r),E(_4B),E(_4B))));},_5W=E(_5S);if(!_5W._){return new F(function(){return _5T(_5W.a);});}else{return new F(function(){return _5T(0);});}}else{return new T4(0,1+_5K|0,E(_5L),E(_5N),E(new T4(0,1+_5Q|0,E(_5r),E(_5P),E(_4B))));}}else{return new T4(0,3,E(_5L),E(_5N),E(new T4(0,1,E(_5r),E(_4B),E(_4B))));}}else{var _5X=E(_5M);return (_5X._==0)?new T4(0,3,E(_5X.b),E(new T4(0,1,E(_5L),E(_4B),E(_4B))),E(new T4(0,1,E(_5r),E(_4B),E(_4B)))):new T4(0,2,E(_5r),E(_5J),E(_4B));}}else{return new T4(0,1,E(_5r),E(_4B),E(_4B));}}},_5Y=function(_5Z,_60){var _61=E(_60);if(!_61._){return new F(function(){return _5q(_61.b,B(_5Y(_5Z,_61.c)),_61.d);});}else{return new F(function(){return _5g(_5Z);});}},_62=function(_63,_64,_65,_66,_67){return new F(function(){return _4G(_65,_66,B(_5i(_63,_67)));});},_68=function(_69,_6a,_6b,_6c,_6d){return new F(function(){return _5q(_6b,B(_5Y(_69,_6c)),_6d);});},_6e=function(_6f,_6g,_6h,_6i,_6j,_6k){var _6l=E(_6g);if(!_6l._){var _6m=_6l.a,_6n=_6l.b,_6o=_6l.c,_6p=_6l.d;if((imul(3,_6m)|0)>=_6h){if((imul(3,_6h)|0)>=_6m){return new T4(0,(_6m+_6h|0)+1|0,E(_6f),E(_6l),E(new T4(0,_6h,E(_6i),E(_6j),E(_6k))));}else{return new F(function(){return _4G(_6n,_6o,B(_6e(_6f,_6p,_6h,_6i,_6j,_6k)));});}}else{return new F(function(){return _5q(_6i,B(_6q(_6f,_6m,_6n,_6o,_6p,_6j)),_6k);});}}else{return new F(function(){return _68(_6f,_6h,_6i,_6j,_6k);});}},_6q=function(_6r,_6s,_6t,_6u,_6v,_6w){var _6x=E(_6w);if(!_6x._){var _6y=_6x.a,_6z=_6x.b,_6A=_6x.c,_6B=_6x.d;if((imul(3,_6s)|0)>=_6y){if((imul(3,_6y)|0)>=_6s){return new T4(0,(_6s+_6y|0)+1|0,E(_6r),E(new T4(0,_6s,E(_6t),E(_6u),E(_6v))),E(_6x));}else{return new F(function(){return _4G(_6t,_6u,B(_6e(_6r,_6v,_6y,_6z,_6A,_6B)));});}}else{return new F(function(){return _5q(_6z,B(_6q(_6r,_6s,_6t,_6u,_6v,_6A)),_6B);});}}else{return new F(function(){return _62(_6r,_6s,_6t,_6u,_6v);});}},_6C=function(_6D,_6E,_6F){var _6G=E(_6E);if(!_6G._){var _6H=_6G.a,_6I=_6G.b,_6J=_6G.c,_6K=_6G.d,_6L=E(_6F);if(!_6L._){var _6M=_6L.a,_6N=_6L.b,_6O=_6L.c,_6P=_6L.d;if((imul(3,_6H)|0)>=_6M){if((imul(3,_6M)|0)>=_6H){return new T4(0,(_6H+_6M|0)+1|0,E(_6D),E(_6G),E(_6L));}else{return new F(function(){return _4G(_6I,_6J,B(_6e(_6D,_6K,_6M,_6N,_6O,_6P)));});}}else{return new F(function(){return _5q(_6N,B(_6q(_6D,_6H,_6I,_6J,_6K,_6O)),_6P);});}}else{return new F(function(){return _62(_6D,_6H,_6I,_6J,_6K);});}}else{return new F(function(){return _5Y(_6D,_6F);});}},_6Q=function(_6R,_6S,_6T,_6U,_6V){var _6W=E(_6R);if(_6W==1){var _6X=E(_6V);if(!_6X._){return new T3(0,new T4(0,1,E(new T3(0,_6S,_6T,_6U)),E(_4B),E(_4B)),_1,_1);}else{var _6Y=E(_6X.a);switch(B(_2(_6S,_6Y.a))){case 0:return new T3(0,new T4(0,1,E(new T3(0,_6S,_6T,_6U)),E(_4B),E(_4B)),_6X,_1);case 1:switch(B(_2(_6T,_6Y.b))){case 0:return new T3(0,new T4(0,1,E(new T3(0,_6S,_6T,_6U)),E(_4B),E(_4B)),_6X,_1);case 1:return (!B(_e(_6U,_6Y.c)))?new T3(0,new T4(0,1,E(new T3(0,_6S,_6T,_6U)),E(_4B),E(_4B)),_6X,_1):new T3(0,new T4(0,1,E(new T3(0,_6S,_6T,_6U)),E(_4B),E(_4B)),_1,_6X);default:return new T3(0,new T4(0,1,E(new T3(0,_6S,_6T,_6U)),E(_4B),E(_4B)),_1,_6X);}break;default:return new T3(0,new T4(0,1,E(new T3(0,_6S,_6T,_6U)),E(_4B),E(_4B)),_1,_6X);}}}else{var _6Z=B(_6Q(_6W>>1,_6S,_6T,_6U,_6V)),_70=_6Z.a,_71=_6Z.c,_72=E(_6Z.b);if(!_72._){return new T3(0,_70,_1,_71);}else{var _73=_72.a,_74=E(_72.b);if(!_74._){return new T3(0,new T(function(){return B(_5i(_73,_70));}),_1,_71);}else{var _75=_74.b,_76=E(_73),_77=E(_74.a),_78=_77.a,_79=_77.b,_7a=_77.c;switch(B(_2(_76.a,_78))){case 0:var _7b=B(_6Q(_6W>>1,_78,_79,_7a,_75));return new T3(0,new T(function(){return B(_6C(_76,_70,_7b.a));}),_7b.b,_7b.c);case 1:switch(B(_2(_76.b,_79))){case 0:var _7c=B(_6Q(_6W>>1,_78,_79,_7a,_75));return new T3(0,new T(function(){return B(_6C(_76,_70,_7c.a));}),_7c.b,_7c.c);case 1:if(!B(_e(_76.c,_7a))){var _7d=B(_6Q(_6W>>1,_78,_79,_7a,_75));return new T3(0,new T(function(){return B(_6C(_76,_70,_7d.a));}),_7d.b,_7d.c);}else{return new T3(0,_70,_1,_72);}break;default:return new T3(0,_70,_1,_72);}break;default:return new T3(0,_70,_1,_72);}}}}},_7e=function(_7f,_7g,_7h,_7i){var _7j=E(_7i);if(!_7j._){var _7k=_7j.c,_7l=_7j.d,_7m=E(_7j.b);switch(B(_2(_7f,_7m.a))){case 0:return new F(function(){return _5q(_7m,B(_7e(_7f,_7g,_7h,_7k)),_7l);});break;case 1:switch(B(_2(_7g,_7m.b))){case 0:return new F(function(){return _5q(_7m,B(_7e(_7f,_7g,_7h,_7k)),_7l);});break;case 1:switch(B(_2(_7h,_7m.c))){case 0:return new F(function(){return _5q(_7m,B(_7e(_7f,_7g,_7h,_7k)),_7l);});break;case 1:return new T4(0,_7j.a,E(new T3(0,_7f,_7g,_7h)),E(_7k),E(_7l));default:return new F(function(){return _4G(_7m,_7k,B(_7e(_7f,_7g,_7h,_7l)));});}break;default:return new F(function(){return _4G(_7m,_7k,B(_7e(_7f,_7g,_7h,_7l)));});}break;default:return new F(function(){return _4G(_7m,_7k,B(_7e(_7f,_7g,_7h,_7l)));});}}else{return new T4(0,1,E(new T3(0,_7f,_7g,_7h)),E(_4B),E(_4B));}},_7n=function(_7o,_7p){while(1){var _7q=E(_7p);if(!_7q._){return E(_7o);}else{var _7r=E(_7q.a),_7s=B(_7e(_7r.a,_7r.b,_7r.c,_7o));_7o=_7s;_7p=_7q.b;continue;}}},_7t=function(_7u,_7v,_7w,_7x,_7y){return new F(function(){return _7n(B(_7e(_7v,_7w,_7x,_7u)),_7y);});},_7z=function(_7A,_7B,_7C){var _7D=E(_7B);return new F(function(){return _7n(B(_7e(_7D.a,_7D.b,_7D.c,_7A)),_7C);});},_7E=function(_7F,_7G,_7H){var _7I=E(_7H);if(!_7I._){return E(_7G);}else{var _7J=_7I.a,_7K=E(_7I.b);if(!_7K._){return new F(function(){return _5i(_7J,_7G);});}else{var _7L=E(_7J),_7M=_7L.a,_7N=_7L.b,_7O=_7L.c,_7P=E(_7K.a),_7Q=_7P.a,_7R=_7P.b,_7S=_7P.c,_7T=function(_7U){var _7V=B(_6Q(_7F,_7Q,_7R,_7S,_7K.b)),_7W=_7V.a,_7X=E(_7V.c);if(!_7X._){return new F(function(){return _7E(_7F<<1,B(_6C(_7L,_7G,_7W)),_7V.b);});}else{return new F(function(){return _7z(B(_6C(_7L,_7G,_7W)),_7X.a,_7X.b);});}};switch(B(_2(_7M,_7Q))){case 0:return new F(function(){return _7T(_);});break;case 1:switch(B(_2(_7N,_7R))){case 0:return new F(function(){return _7T(_);});break;case 1:if(!B(_e(_7O,_7S))){return new F(function(){return _7T(_);});}else{return new F(function(){return _7t(_7G,_7M,_7N,_7O,_7K);});}break;default:return new F(function(){return _7t(_7G,_7M,_7N,_7O,_7K);});}break;default:return new F(function(){return _7t(_7G,_7M,_7N,_7O,_7K);});}}}},_7Y=function(_7Z,_80,_81,_82,_83,_84){var _85=E(_84);if(!_85._){return new F(function(){return _5i(new T3(0,_81,_82,_83),_80);});}else{var _86=E(_85.a),_87=_86.a,_88=_86.b,_89=_86.c,_8a=function(_8b){var _8c=B(_6Q(_7Z,_87,_88,_89,_85.b)),_8d=_8c.a,_8e=E(_8c.c);if(!_8e._){return new F(function(){return _7E(_7Z<<1,B(_6C(new T3(0,_81,_82,_83),_80,_8d)),_8c.b);});}else{return new F(function(){return _7z(B(_6C(new T3(0,_81,_82,_83),_80,_8d)),_8e.a,_8e.b);});}};switch(B(_2(_81,_87))){case 0:return new F(function(){return _8a(_);});break;case 1:switch(B(_2(_82,_88))){case 0:return new F(function(){return _8a(_);});break;case 1:if(!B(_e(_83,_89))){return new F(function(){return _8a(_);});}else{return new F(function(){return _7t(_80,_81,_82,_83,_85);});}break;default:return new F(function(){return _7t(_80,_81,_82,_83,_85);});}break;default:return new F(function(){return _7t(_80,_81,_82,_83,_85);});}}},_8f=function(_8g){var _8h=E(_8g);if(!_8h._){return new T0(1);}else{var _8i=_8h.a,_8j=E(_8h.b);if(!_8j._){return new T4(0,1,E(_8i),E(_4B),E(_4B));}else{var _8k=_8j.b,_8l=E(_8i),_8m=E(_8j.a),_8n=_8m.a,_8o=_8m.b,_8p=_8m.c;switch(B(_2(_8l.a,_8n))){case 0:return new F(function(){return _7Y(1,new T4(0,1,E(_8l),E(_4B),E(_4B)),_8n,_8o,_8p,_8k);});break;case 1:switch(B(_2(_8l.b,_8o))){case 0:return new F(function(){return _7Y(1,new T4(0,1,E(_8l),E(_4B),E(_4B)),_8n,_8o,_8p,_8k);});break;case 1:if(!B(_e(_8l.c,_8p))){return new F(function(){return _7Y(1,new T4(0,1,E(_8l),E(_4B),E(_4B)),_8n,_8o,_8p,_8k);});}else{return new F(function(){return _7t(new T4(0,1,E(_8l),E(_4B),E(_4B)),_8n,_8o,_8p,_8k);});}break;default:return new F(function(){return _7t(new T4(0,1,E(_8l),E(_4B),E(_4B)),_8n,_8o,_8p,_8k);});}break;default:return new F(function(){return _7t(new T4(0,1,E(_8l),E(_4B),E(_4B)),_8n,_8o,_8p,_8k);});}}}},_8q=function(_8r,_8s,_8t,_8u,_8v){var _8w=E(_8r);if(_8w==1){var _8x=E(_8v);if(!_8x._){return new T3(0,new T5(0,1,E(new T2(0,_8s,_8t)),_8u,E(_0),E(_0)),_1,_1);}else{var _8y=E(E(_8x.a).a);switch(B(_2(_8s,_8y.a))){case 0:return new T3(0,new T5(0,1,E(new T2(0,_8s,_8t)),_8u,E(_0),E(_0)),_8x,_1);case 1:return (!B(_e(_8t,_8y.b)))?new T3(0,new T5(0,1,E(new T2(0,_8s,_8t)),_8u,E(_0),E(_0)),_8x,_1):new T3(0,new T5(0,1,E(new T2(0,_8s,_8t)),_8u,E(_0),E(_0)),_1,_8x);default:return new T3(0,new T5(0,1,E(new T2(0,_8s,_8t)),_8u,E(_0),E(_0)),_1,_8x);}}}else{var _8z=B(_8q(_8w>>1,_8s,_8t,_8u,_8v)),_8A=_8z.a,_8B=_8z.c,_8C=E(_8z.b);if(!_8C._){return new T3(0,_8A,_1,_8B);}else{var _8D=E(_8C.a),_8E=_8D.a,_8F=_8D.b,_8G=E(_8C.b);if(!_8G._){return new T3(0,new T(function(){return B(_18(_8E,_8F,_8A));}),_1,_8B);}else{var _8H=_8G.b,_8I=E(_8G.a),_8J=_8I.b,_8K=E(_8E),_8L=E(_8I.a),_8M=_8L.a,_8N=_8L.b;switch(B(_2(_8K.a,_8M))){case 0:var _8O=B(_8q(_8w>>1,_8M,_8N,_8J,_8H));return new T3(0,new T(function(){return B(_2B(_8K,_8F,_8A,_8O.a));}),_8O.b,_8O.c);case 1:if(!B(_e(_8K.b,_8N))){var _8P=B(_8q(_8w>>1,_8M,_8N,_8J,_8H));return new T3(0,new T(function(){return B(_2B(_8K,_8F,_8A,_8P.a));}),_8P.b,_8P.c);}else{return new T3(0,_8A,_1,_8C);}break;default:return new T3(0,_8A,_1,_8C);}}}}},_8Q=function(_8R,_8S,_8T,_8U){var _8V=E(_8U);if(!_8V._){var _8W=_8V.c,_8X=_8V.d,_8Y=_8V.e,_8Z=E(_8V.b);switch(B(_2(_8R,_8Z.a))){case 0:return new F(function(){return _1h(_8Z,_8W,B(_8Q(_8R,_8S,_8T,_8X)),_8Y);});break;case 1:switch(B(_2(_8S,_8Z.b))){case 0:return new F(function(){return _1h(_8Z,_8W,B(_8Q(_8R,_8S,_8T,_8X)),_8Y);});break;case 1:return new T5(0,_8V.a,E(new T2(0,_8R,_8S)),_8T,E(_8X),E(_8Y));default:return new F(function(){return _q(_8Z,_8W,_8X,B(_8Q(_8R,_8S,_8T,_8Y)));});}break;default:return new F(function(){return _q(_8Z,_8W,_8X,B(_8Q(_8R,_8S,_8T,_8Y)));});}}else{return new T5(0,1,E(new T2(0,_8R,_8S)),_8T,E(_0),E(_0));}},_90=function(_91,_92){while(1){var _93=E(_92);if(!_93._){return E(_91);}else{var _94=E(_93.a),_95=E(_94.a),_96=B(_8Q(_95.a,_95.b,_94.b,_91));_91=_96;_92=_93.b;continue;}}},_97=function(_98,_99,_9a,_9b,_9c){return new F(function(){return _90(B(_8Q(_99,_9a,_9b,_98)),_9c);});},_9d=function(_9e,_9f,_9g){var _9h=E(_9f),_9i=E(_9h.a);return new F(function(){return _90(B(_8Q(_9i.a,_9i.b,_9h.b,_9e)),_9g);});},_9j=function(_9k,_9l,_9m){var _9n=E(_9m);if(!_9n._){return E(_9l);}else{var _9o=E(_9n.a),_9p=_9o.a,_9q=_9o.b,_9r=E(_9n.b);if(!_9r._){return new F(function(){return _18(_9p,_9q,_9l);});}else{var _9s=E(_9r.a),_9t=E(_9p),_9u=_9t.a,_9v=_9t.b,_9w=E(_9s.a),_9x=_9w.a,_9y=_9w.b,_9z=function(_9A){var _9B=B(_8q(_9k,_9x,_9y,_9s.b,_9r.b)),_9C=_9B.a,_9D=E(_9B.c);if(!_9D._){return new F(function(){return _9j(_9k<<1,B(_2B(_9t,_9q,_9l,_9C)),_9B.b);});}else{return new F(function(){return _9d(B(_2B(_9t,_9q,_9l,_9C)),_9D.a,_9D.b);});}};switch(B(_2(_9u,_9x))){case 0:return new F(function(){return _9z(_);});break;case 1:if(!B(_e(_9v,_9y))){return new F(function(){return _9z(_);});}else{return new F(function(){return _97(_9l,_9u,_9v,_9q,_9r);});}break;default:return new F(function(){return _97(_9l,_9u,_9v,_9q,_9r);});}}}},_9E=function(_9F,_9G,_9H,_9I,_9J,_9K){var _9L=E(_9K);if(!_9L._){return new F(function(){return _18(new T2(0,_9H,_9I),_9J,_9G);});}else{var _9M=E(_9L.a),_9N=E(_9M.a),_9O=_9N.a,_9P=_9N.b,_9Q=function(_9R){var _9S=B(_8q(_9F,_9O,_9P,_9M.b,_9L.b)),_9T=_9S.a,_9U=E(_9S.c);if(!_9U._){return new F(function(){return _9j(_9F<<1,B(_2B(new T2(0,_9H,_9I),_9J,_9G,_9T)),_9S.b);});}else{return new F(function(){return _9d(B(_2B(new T2(0,_9H,_9I),_9J,_9G,_9T)),_9U.a,_9U.b);});}};switch(B(_2(_9H,_9O))){case 0:return new F(function(){return _9Q(_);});break;case 1:if(!B(_e(_9I,_9P))){return new F(function(){return _9Q(_);});}else{return new F(function(){return _97(_9G,_9H,_9I,_9J,_9L);});}break;default:return new F(function(){return _97(_9G,_9H,_9I,_9J,_9L);});}}},_9V=function(_9W){var _9X=E(_9W);if(!_9X._){return new T0(1);}else{var _9Y=E(_9X.a),_9Z=_9Y.a,_a0=_9Y.b,_a1=E(_9X.b);if(!_a1._){return new T5(0,1,E(_9Z),_a0,E(_0),E(_0));}else{var _a2=_a1.b,_a3=E(_a1.a),_a4=_a3.b,_a5=E(_9Z),_a6=E(_a3.a),_a7=_a6.a,_a8=_a6.b;switch(B(_2(_a5.a,_a7))){case 0:return new F(function(){return _9E(1,new T5(0,1,E(_a5),_a0,E(_0),E(_0)),_a7,_a8,_a4,_a2);});break;case 1:if(!B(_e(_a5.b,_a8))){return new F(function(){return _9E(1,new T5(0,1,E(_a5),_a0,E(_0),E(_0)),_a7,_a8,_a4,_a2);});}else{return new F(function(){return _97(new T5(0,1,E(_a5),_a0,E(_0),E(_0)),_a7,_a8,_a4,_a2);});}break;default:return new F(function(){return _97(new T5(0,1,E(_a5),_a0,E(_0),E(_0)),_a7,_a8,_a4,_a2);});}}}},_a9=function(_aa,_ab,_ac,_ad,_ae,_af){var _ag=E(_aa);if(_ag==1){var _ah=E(_af);if(!_ah._){return new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_1,_1);}else{var _ai=E(_ah.a);switch(B(_2(_ab,_ai.a))){case 0:return new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_ah,_1);case 1:switch(B(_2(_ac,_ai.b))){case 0:return new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_ah,_1);case 1:switch(B(_2(_ad,_ai.c))){case 0:return new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_ah,_1);case 1:return (!B(_e(_ae,_ai.d)))?new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_ah,_1):new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_1,_ah);default:return new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_1,_ah);}break;default:return new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_1,_ah);}break;default:return new T3(0,new T4(0,1,E(new T4(0,_ab,_ac,_ad,_ae)),E(_4B),E(_4B)),_1,_ah);}}}else{var _aj=B(_a9(_ag>>1,_ab,_ac,_ad,_ae,_af)),_ak=_aj.a,_al=_aj.c,_am=E(_aj.b);if(!_am._){return new T3(0,_ak,_1,_al);}else{var _an=_am.a,_ao=E(_am.b);if(!_ao._){return new T3(0,new T(function(){return B(_5i(_an,_ak));}),_1,_al);}else{var _ap=_ao.b,_aq=E(_an),_ar=E(_ao.a),_as=_ar.a,_at=_ar.b,_au=_ar.c,_av=_ar.d;switch(B(_2(_aq.a,_as))){case 0:var _aw=B(_a9(_ag>>1,_as,_at,_au,_av,_ap));return new T3(0,new T(function(){return B(_6C(_aq,_ak,_aw.a));}),_aw.b,_aw.c);case 1:switch(B(_2(_aq.b,_at))){case 0:var _ax=B(_a9(_ag>>1,_as,_at,_au,_av,_ap));return new T3(0,new T(function(){return B(_6C(_aq,_ak,_ax.a));}),_ax.b,_ax.c);case 1:switch(B(_2(_aq.c,_au))){case 0:var _ay=B(_a9(_ag>>1,_as,_at,_au,_av,_ap));return new T3(0,new T(function(){return B(_6C(_aq,_ak,_ay.a));}),_ay.b,_ay.c);case 1:if(!B(_e(_aq.d,_av))){var _az=B(_a9(_ag>>1,_as,_at,_au,_av,_ap));return new T3(0,new T(function(){return B(_6C(_aq,_ak,_az.a));}),_az.b,_az.c);}else{return new T3(0,_ak,_1,_am);}break;default:return new T3(0,_ak,_1,_am);}break;default:return new T3(0,_ak,_1,_am);}break;default:return new T3(0,_ak,_1,_am);}}}}},_aA=function(_aB,_aC,_aD,_aE,_aF){var _aG=E(_aF);if(!_aG._){var _aH=_aG.c,_aI=_aG.d,_aJ=E(_aG.b);switch(B(_2(_aB,_aJ.a))){case 0:return new F(function(){return _5q(_aJ,B(_aA(_aB,_aC,_aD,_aE,_aH)),_aI);});break;case 1:switch(B(_2(_aC,_aJ.b))){case 0:return new F(function(){return _5q(_aJ,B(_aA(_aB,_aC,_aD,_aE,_aH)),_aI);});break;case 1:switch(B(_2(_aD,_aJ.c))){case 0:return new F(function(){return _5q(_aJ,B(_aA(_aB,_aC,_aD,_aE,_aH)),_aI);});break;case 1:switch(B(_2(_aE,_aJ.d))){case 0:return new F(function(){return _5q(_aJ,B(_aA(_aB,_aC,_aD,_aE,_aH)),_aI);});break;case 1:return new T4(0,_aG.a,E(new T4(0,_aB,_aC,_aD,_aE)),E(_aH),E(_aI));default:return new F(function(){return _4G(_aJ,_aH,B(_aA(_aB,_aC,_aD,_aE,_aI)));});}break;default:return new F(function(){return _4G(_aJ,_aH,B(_aA(_aB,_aC,_aD,_aE,_aI)));});}break;default:return new F(function(){return _4G(_aJ,_aH,B(_aA(_aB,_aC,_aD,_aE,_aI)));});}break;default:return new F(function(){return _4G(_aJ,_aH,B(_aA(_aB,_aC,_aD,_aE,_aI)));});}}else{return new T4(0,1,E(new T4(0,_aB,_aC,_aD,_aE)),E(_4B),E(_4B));}},_aK=function(_aL,_aM){while(1){var _aN=E(_aM);if(!_aN._){return E(_aL);}else{var _aO=E(_aN.a),_aP=B(_aA(_aO.a,_aO.b,_aO.c,_aO.d,_aL));_aL=_aP;_aM=_aN.b;continue;}}},_aQ=function(_aR,_aS,_aT,_aU,_aV,_aW){return new F(function(){return _aK(B(_aA(_aS,_aT,_aU,_aV,_aR)),_aW);});},_aX=function(_aY,_aZ,_b0){var _b1=E(_aZ);return new F(function(){return _aK(B(_aA(_b1.a,_b1.b,_b1.c,_b1.d,_aY)),_b0);});},_b2=function(_b3,_b4,_b5){var _b6=E(_b5);if(!_b6._){return E(_b4);}else{var _b7=_b6.a,_b8=E(_b6.b);if(!_b8._){return new F(function(){return _5i(_b7,_b4);});}else{var _b9=E(_b7),_ba=_b9.a,_bb=_b9.b,_bc=_b9.c,_bd=_b9.d,_be=E(_b8.a),_bf=_be.a,_bg=_be.b,_bh=_be.c,_bi=_be.d,_bj=function(_bk){var _bl=B(_a9(_b3,_bf,_bg,_bh,_bi,_b8.b)),_bm=_bl.a,_bn=E(_bl.c);if(!_bn._){return new F(function(){return _b2(_b3<<1,B(_6C(_b9,_b4,_bm)),_bl.b);});}else{return new F(function(){return _aX(B(_6C(_b9,_b4,_bm)),_bn.a,_bn.b);});}};switch(B(_2(_ba,_bf))){case 0:return new F(function(){return _bj(_);});break;case 1:switch(B(_2(_bb,_bg))){case 0:return new F(function(){return _bj(_);});break;case 1:switch(B(_2(_bc,_bh))){case 0:return new F(function(){return _bj(_);});break;case 1:if(!B(_e(_bd,_bi))){return new F(function(){return _bj(_);});}else{return new F(function(){return _aQ(_b4,_ba,_bb,_bc,_bd,_b8);});}break;default:return new F(function(){return _aQ(_b4,_ba,_bb,_bc,_bd,_b8);});}break;default:return new F(function(){return _aQ(_b4,_ba,_bb,_bc,_bd,_b8);});}break;default:return new F(function(){return _aQ(_b4,_ba,_bb,_bc,_bd,_b8);});}}}},_bo=function(_bp,_bq,_br,_bs,_bt,_bu,_bv){var _bw=E(_bv);if(!_bw._){return new F(function(){return _5i(new T4(0,_br,_bs,_bt,_bu),_bq);});}else{var _bx=E(_bw.a),_by=_bx.a,_bz=_bx.b,_bA=_bx.c,_bB=_bx.d,_bC=function(_bD){var _bE=B(_a9(_bp,_by,_bz,_bA,_bB,_bw.b)),_bF=_bE.a,_bG=E(_bE.c);if(!_bG._){return new F(function(){return _b2(_bp<<1,B(_6C(new T4(0,_br,_bs,_bt,_bu),_bq,_bF)),_bE.b);});}else{return new F(function(){return _aX(B(_6C(new T4(0,_br,_bs,_bt,_bu),_bq,_bF)),_bG.a,_bG.b);});}};switch(B(_2(_br,_by))){case 0:return new F(function(){return _bC(_);});break;case 1:switch(B(_2(_bs,_bz))){case 0:return new F(function(){return _bC(_);});break;case 1:switch(B(_2(_bt,_bA))){case 0:return new F(function(){return _bC(_);});break;case 1:if(!B(_e(_bu,_bB))){return new F(function(){return _bC(_);});}else{return new F(function(){return _aQ(_bq,_br,_bs,_bt,_bu,_bw);});}break;default:return new F(function(){return _aQ(_bq,_br,_bs,_bt,_bu,_bw);});}break;default:return new F(function(){return _aQ(_bq,_br,_bs,_bt,_bu,_bw);});}break;default:return new F(function(){return _aQ(_bq,_br,_bs,_bt,_bu,_bw);});}}},_bH=function(_bI){var _bJ=E(_bI);if(!_bJ._){return new T0(1);}else{var _bK=_bJ.a,_bL=E(_bJ.b);if(!_bL._){return new T4(0,1,E(_bK),E(_4B),E(_4B));}else{var _bM=_bL.b,_bN=E(_bK),_bO=E(_bL.a),_bP=_bO.a,_bQ=_bO.b,_bR=_bO.c,_bS=_bO.d;switch(B(_2(_bN.a,_bP))){case 0:return new F(function(){return _bo(1,new T4(0,1,E(_bN),E(_4B),E(_4B)),_bP,_bQ,_bR,_bS,_bM);});break;case 1:switch(B(_2(_bN.b,_bQ))){case 0:return new F(function(){return _bo(1,new T4(0,1,E(_bN),E(_4B),E(_4B)),_bP,_bQ,_bR,_bS,_bM);});break;case 1:switch(B(_2(_bN.c,_bR))){case 0:return new F(function(){return _bo(1,new T4(0,1,E(_bN),E(_4B),E(_4B)),_bP,_bQ,_bR,_bS,_bM);});break;case 1:if(!B(_e(_bN.d,_bS))){return new F(function(){return _bo(1,new T4(0,1,E(_bN),E(_4B),E(_4B)),_bP,_bQ,_bR,_bS,_bM);});}else{return new F(function(){return _aQ(new T4(0,1,E(_bN),E(_4B),E(_4B)),_bP,_bQ,_bR,_bS,_bM);});}break;default:return new F(function(){return _aQ(new T4(0,1,E(_bN),E(_4B),E(_4B)),_bP,_bQ,_bR,_bS,_bM);});}break;default:return new F(function(){return _aQ(new T4(0,1,E(_bN),E(_4B),E(_4B)),_bP,_bQ,_bR,_bS,_bM);});}break;default:return new F(function(){return _aQ(new T4(0,1,E(_bN),E(_4B),E(_4B)),_bP,_bQ,_bR,_bS,_bM);});}}}},_bT=0,_bU=function(_bV){var _bW=E(_bV);if(!_bW._){return E(_bW.a);}else{return new F(function(){return I_toInt(_bW.a);});}},_bX=function(_bY){return new F(function(){return _bU(_bY);});},_bZ=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_c0=new T(function(){return B(err(_bZ));}),_c1=function(_c2,_c3){while(1){var _c4=B((function(_c5,_c6){var _c7=E(_c6);if(!_c7._){_c2=new T2(1,new T2(0,_c7.b,_c7.c),new T(function(){return B(_c1(_c5,_c7.e));}));_c3=_c7.d;return __continue;}else{return E(_c5);}})(_c2,_c3));if(_c4!=__continue){return _c4;}}},_c8=44,_c9=function(_ca,_cb,_cc){return new F(function(){return A1(_ca,new T2(1,_c8,new T(function(){return B(A1(_cb,_cc));})));});},_cd=new T(function(){return B(unCStr("CC "));}),_ce=function(_cf,_cg){var _ch=E(_cf);return (_ch._==0)?E(_cg):new T2(1,_ch.a,new T(function(){return B(_ce(_ch.b,_cg));}));},_ci=function(_cj){while(1){var _ck=E(_cj);if(!_ck._){_cj=new T1(1,I_fromInt(_ck.a));continue;}else{return new F(function(){return I_toString(_ck.a);});}}},_cl=function(_cm,_cn){return new F(function(){return _ce(fromJSStr(B(_ci(_cm))),_cn);});},_co=function(_cp,_cq){var _cr=E(_cp);if(!_cr._){var _cs=_cr.a,_ct=E(_cq);return (_ct._==0)?_cs<_ct.a:I_compareInt(_ct.a,_cs)>0;}else{var _cu=_cr.a,_cv=E(_cq);return (_cv._==0)?I_compareInt(_cu,_cv.a)<0:I_compare(_cu,_cv.a)<0;}},_cw=41,_cx=40,_cy=new T1(0,0),_cz=function(_cA,_cB,_cC){if(_cA<=6){return new F(function(){return _cl(_cB,_cC);});}else{if(!B(_co(_cB,_cy))){return new F(function(){return _cl(_cB,_cC);});}else{return new T2(1,_cx,new T(function(){return B(_ce(fromJSStr(B(_ci(_cB))),new T2(1,_cw,_cC)));}));}}},_cD=new T(function(){return B(unCStr("IdentCC "));}),_cE=function(_cF,_cG,_cH){if(_cF<11){return new F(function(){return _ce(_cD,new T(function(){return B(_cz(11,_cG,_cH));},1));});}else{var _cI=new T(function(){return B(_ce(_cD,new T(function(){return B(_cz(11,_cG,new T2(1,_cw,_cH)));},1)));});return new T2(1,_cx,_cI);}},_cJ=32,_cK=function(_cL,_cM,_cN,_cO,_cP,_cQ){var _cR=function(_cS){var _cT=new T(function(){var _cU=new T(function(){return B(_cz(11,_cO,new T2(1,_cJ,new T(function(){return B(_cz(11,_cP,_cS));}))));});return B(_cz(11,_cN,new T2(1,_cJ,_cU)));});return new F(function(){return _cE(11,_cM,new T2(1,_cJ,_cT));});};if(_cL<11){return new F(function(){return _ce(_cd,new T(function(){return B(_cR(_cQ));},1));});}else{var _cV=new T(function(){return B(_ce(_cd,new T(function(){return B(_cR(new T2(1,_cw,_cQ)));},1)));});return new T2(1,_cx,_cV);}},_cW=function(_cX,_cY){var _cZ=E(_cX);return new F(function(){return _cK(0,_cZ.a,_cZ.b,_cZ.c,_cZ.d,_cY);});},_d0=new T(function(){return B(unCStr("RC "));}),_d1=function(_d2,_d3,_d4,_d5,_d6){var _d7=function(_d8){var _d9=new T(function(){var _da=new T(function(){return B(_cz(11,_d4,new T2(1,_cJ,new T(function(){return B(_cz(11,_d5,_d8));}))));});return B(_cE(11,_d3,new T2(1,_cJ,_da)));},1);return new F(function(){return _ce(_d0,_d9);});};if(_d2<11){return new F(function(){return _d7(_d6);});}else{return new T2(1,_cx,new T(function(){return B(_d7(new T2(1,_cw,_d6)));}));}},_db=function(_dc,_dd){var _de=E(_dc);return new F(function(){return _d1(0,_de.a,_de.b,_de.c,_dd);});},_df=new T(function(){return B(unCStr("IdentPay "));}),_dg=function(_dh,_di,_dj){if(_dh<11){return new F(function(){return _ce(_df,new T(function(){return B(_cz(11,_di,_dj));},1));});}else{var _dk=new T(function(){return B(_ce(_df,new T(function(){return B(_cz(11,_di,new T2(1,_cw,_dj)));},1)));});return new T2(1,_cx,_dk);}},_dl=new T(function(){return B(unCStr(": empty list"));}),_dm=new T(function(){return B(unCStr("Prelude."));}),_dn=function(_do){return new F(function(){return err(B(_ce(_dm,new T(function(){return B(_ce(_do,_dl));},1))));});},_dp=new T(function(){return B(unCStr("foldr1"));}),_dq=new T(function(){return B(_dn(_dp));}),_dr=function(_ds,_dt){var _du=E(_dt);if(!_du._){return E(_dq);}else{var _dv=_du.a,_dw=E(_du.b);if(!_dw._){return E(_dv);}else{return new F(function(){return A2(_ds,_dv,new T(function(){return B(_dr(_ds,_dw));}));});}}},_dx=function(_dy,_dz,_dA){var _dB=new T(function(){var _dC=function(_dD){var _dE=E(_dy),_dF=new T(function(){return B(A3(_dr,_c9,new T2(1,function(_dG){return new F(function(){return _dg(0,_dE.a,_dG);});},new T2(1,function(_dH){return new F(function(){return _cz(0,_dE.b,_dH);});},_1)),new T2(1,_cw,_dD)));});return new T2(1,_cx,_dF);};return B(A3(_dr,_c9,new T2(1,_dC,new T2(1,function(_dI){return new F(function(){return _cz(0,_dz,_dI);});},_1)),new T2(1,_cw,_dA)));});return new T2(0,_cx,_dB);},_dJ=function(_dK,_dL){var _dM=E(_dK),_dN=B(_dx(_dM.a,_dM.b,_dL));return new T2(1,_dN.a,_dN.b);},_dO=93,_dP=91,_dQ=function(_dR,_dS,_dT){var _dU=E(_dS);if(!_dU._){return new F(function(){return unAppCStr("[]",_dT);});}else{var _dV=new T(function(){var _dW=new T(function(){var _dX=function(_dY){var _dZ=E(_dY);if(!_dZ._){return E(new T2(1,_dO,_dT));}else{var _e0=new T(function(){return B(A2(_dR,_dZ.a,new T(function(){return B(_dX(_dZ.b));})));});return new T2(1,_c8,_e0);}};return B(_dX(_dU.b));});return B(A2(_dR,_dU.a,_dW));});return new T2(1,_dP,_dV);}},_e1=function(_e2,_e3){return new F(function(){return _dQ(_dJ,_e2,_e3);});},_e4=new T(function(){return B(unCStr("IdentChoice "));}),_e5=function(_e6,_e7,_e8){if(_e6<11){return new F(function(){return _ce(_e4,new T(function(){return B(_cz(11,_e7,_e8));},1));});}else{var _e9=new T(function(){return B(_ce(_e4,new T(function(){return B(_cz(11,_e7,new T2(1,_cw,_e8)));},1)));});return new T2(1,_cx,_e9);}},_ea=function(_eb,_ec,_ed){var _ee=new T(function(){var _ef=function(_eg){var _eh=E(_eb),_ei=new T(function(){return B(A3(_dr,_c9,new T2(1,function(_ej){return new F(function(){return _e5(0,_eh.a,_ej);});},new T2(1,function(_ek){return new F(function(){return _cz(0,_eh.b,_ek);});},_1)),new T2(1,_cw,_eg)));});return new T2(1,_cx,_ei);};return B(A3(_dr,_c9,new T2(1,_ef,new T2(1,function(_el){return new F(function(){return _cz(0,_ec,_el);});},_1)),new T2(1,_cw,_ed)));});return new T2(0,_cx,_ee);},_em=function(_en,_eo){var _ep=E(_en),_eq=B(_ea(_ep.a,_ep.b,_eo));return new T2(1,_eq.a,_eq.b);},_er=function(_es,_et){return new F(function(){return _dQ(_em,_es,_et);});},_eu=new T2(1,_cw,_1),_ev=function(_ew,_ex){while(1){var _ey=B((function(_ez,_eA){var _eB=E(_eA);if(!_eB._){_ew=new T2(1,_eB.b,new T(function(){return B(_ev(_ez,_eB.d));}));_ex=_eB.c;return __continue;}else{return E(_ez);}})(_ew,_ex));if(_ey!=__continue){return _ey;}}},_eC=function(_eD,_eE,_eF,_eG){var _eH=new T(function(){var _eI=new T(function(){return B(_c1(_1,_eG));}),_eJ=new T(function(){return B(_c1(_1,_eF));}),_eK=new T(function(){return B(_ev(_1,_eE));}),_eL=new T(function(){return B(_ev(_1,_eD));});return B(A3(_dr,_c9,new T2(1,function(_eM){return new F(function(){return _dQ(_cW,_eL,_eM);});},new T2(1,function(_eN){return new F(function(){return _dQ(_db,_eK,_eN);});},new T2(1,function(_eO){return new F(function(){return _e1(_eJ,_eO);});},new T2(1,function(_eP){return new F(function(){return _er(_eI,_eP);});},_1)))),_eu));});return new T2(0,_cx,_eH);},_eQ=new T(function(){return B(err(_bZ));}),_eR=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_eS=new T(function(){return B(err(_eR));}),_eT=new T0(2),_eU=function(_eV){return new T2(3,_eV,_eT);},_eW=new T(function(){return B(unCStr("base"));}),_eX=new T(function(){return B(unCStr("Control.Exception.Base"));}),_eY=new T(function(){return B(unCStr("PatternMatchFail"));}),_eZ=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_eW,_eX,_eY),_f0=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_eZ,_1,_1),_f1=function(_f2){return E(_f0);},_f3=function(_f4){return E(E(_f4).a);},_f5=function(_f6,_f7,_f8){var _f9=B(A1(_f6,_)),_fa=B(A1(_f7,_)),_fb=hs_eqWord64(_f9.a,_fa.a);if(!_fb){return __Z;}else{var _fc=hs_eqWord64(_f9.b,_fa.b);return (!_fc)?__Z:new T1(1,_f8);}},_fd=function(_fe){var _ff=E(_fe);return new F(function(){return _f5(B(_f3(_ff.a)),_f1,_ff.b);});},_fg=function(_fh){return E(E(_fh).a);},_fi=function(_fj){return new T2(0,_fk,_fj);},_fl=function(_fm,_fn){return new F(function(){return _ce(E(_fm).a,_fn);});},_fo=function(_fp,_fq){return new F(function(){return _dQ(_fl,_fp,_fq);});},_fr=function(_fs,_ft,_fu){return new F(function(){return _ce(E(_ft).a,_fu);});},_fv=new T3(0,_fr,_fg,_fo),_fk=new T(function(){return new T5(0,_f1,_fv,_fi,_fd,_fg);}),_fw=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_fx=function(_fy){return E(E(_fy).c);},_fz=function(_fA,_fB){return new F(function(){return die(new T(function(){return B(A2(_fx,_fB,_fA));}));});},_fC=function(_fD,_fE){return new F(function(){return _fz(_fD,_fE);});},_fF=function(_fG,_fH){var _fI=E(_fH);if(!_fI._){return new T2(0,_1,_1);}else{var _fJ=_fI.a;if(!B(A1(_fG,_fJ))){return new T2(0,_1,_fI);}else{var _fK=new T(function(){var _fL=B(_fF(_fG,_fI.b));return new T2(0,_fL.a,_fL.b);});return new T2(0,new T2(1,_fJ,new T(function(){return E(E(_fK).a);})),new T(function(){return E(E(_fK).b);}));}}},_fM=32,_fN=new T(function(){return B(unCStr("\n"));}),_fO=function(_fP){return (E(_fP)==124)?false:true;},_fQ=function(_fR,_fS){var _fT=B(_fF(_fO,B(unCStr(_fR)))),_fU=_fT.a,_fV=function(_fW,_fX){var _fY=new T(function(){var _fZ=new T(function(){return B(_ce(_fS,new T(function(){return B(_ce(_fX,_fN));},1)));});return B(unAppCStr(": ",_fZ));},1);return new F(function(){return _ce(_fW,_fY);});},_g0=E(_fT.b);if(!_g0._){return new F(function(){return _fV(_fU,_1);});}else{if(E(_g0.a)==124){return new F(function(){return _fV(_fU,new T2(1,_fM,_g0.b));});}else{return new F(function(){return _fV(_fU,_1);});}}},_g1=function(_g2){return new F(function(){return _fC(new T1(0,new T(function(){return B(_fQ(_g2,_fw));})),_fk);});},_g3=new T(function(){return B(_g1("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_g4=function(_g5,_g6){while(1){var _g7=B((function(_g8,_g9){var _ga=E(_g8);switch(_ga._){case 0:var _gb=E(_g9);if(!_gb._){return __Z;}else{_g5=B(A1(_ga.a,_gb.a));_g6=_gb.b;return __continue;}break;case 1:var _gc=B(A1(_ga.a,_g9)),_gd=_g9;_g5=_gc;_g6=_gd;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_ga.a,_g9),new T(function(){return B(_g4(_ga.b,_g9));}));default:return E(_ga.a);}})(_g5,_g6));if(_g7!=__continue){return _g7;}}},_ge=function(_gf,_gg){var _gh=function(_gi){var _gj=E(_gg);if(_gj._==3){return new T2(3,_gj.a,new T(function(){return B(_ge(_gf,_gj.b));}));}else{var _gk=E(_gf);if(_gk._==2){return E(_gj);}else{var _gl=E(_gj);if(_gl._==2){return E(_gk);}else{var _gm=function(_gn){var _go=E(_gl);if(_go._==4){var _gp=function(_gq){return new T1(4,new T(function(){return B(_ce(B(_g4(_gk,_gq)),_go.a));}));};return new T1(1,_gp);}else{var _gr=E(_gk);if(_gr._==1){var _gs=_gr.a,_gt=E(_go);if(!_gt._){return new T1(1,function(_gu){return new F(function(){return _ge(B(A1(_gs,_gu)),_gt);});});}else{var _gv=function(_gw){return new F(function(){return _ge(B(A1(_gs,_gw)),new T(function(){return B(A1(_gt.a,_gw));}));});};return new T1(1,_gv);}}else{var _gx=E(_go);if(!_gx._){return E(_g3);}else{var _gy=function(_gz){return new F(function(){return _ge(_gr,new T(function(){return B(A1(_gx.a,_gz));}));});};return new T1(1,_gy);}}}},_gA=E(_gk);switch(_gA._){case 1:var _gB=E(_gl);if(_gB._==4){var _gC=function(_gD){return new T1(4,new T(function(){return B(_ce(B(_g4(B(A1(_gA.a,_gD)),_gD)),_gB.a));}));};return new T1(1,_gC);}else{return new F(function(){return _gm(_);});}break;case 4:var _gE=_gA.a,_gF=E(_gl);switch(_gF._){case 0:var _gG=function(_gH){var _gI=new T(function(){return B(_ce(_gE,new T(function(){return B(_g4(_gF,_gH));},1)));});return new T1(4,_gI);};return new T1(1,_gG);case 1:var _gJ=function(_gK){var _gL=new T(function(){return B(_ce(_gE,new T(function(){return B(_g4(B(A1(_gF.a,_gK)),_gK));},1)));});return new T1(4,_gL);};return new T1(1,_gJ);default:return new T1(4,new T(function(){return B(_ce(_gE,_gF.a));}));}break;default:return new F(function(){return _gm(_);});}}}}},_gM=E(_gf);switch(_gM._){case 0:var _gN=E(_gg);if(!_gN._){var _gO=function(_gP){return new F(function(){return _ge(B(A1(_gM.a,_gP)),new T(function(){return B(A1(_gN.a,_gP));}));});};return new T1(0,_gO);}else{return new F(function(){return _gh(_);});}break;case 3:return new T2(3,_gM.a,new T(function(){return B(_ge(_gM.b,_gg));}));default:return new F(function(){return _gh(_);});}},_gQ=new T(function(){return B(unCStr("("));}),_gR=new T(function(){return B(unCStr(")"));}),_gS=function(_gT,_gU){while(1){var _gV=E(_gT);if(!_gV._){return (E(_gU)._==0)?true:false;}else{var _gW=E(_gU);if(!_gW._){return false;}else{if(E(_gV.a)!=E(_gW.a)){return false;}else{_gT=_gV.b;_gU=_gW.b;continue;}}}}},_gX=function(_gY,_gZ){return E(_gY)!=E(_gZ);},_h0=function(_h1,_h2){return E(_h1)==E(_h2);},_h3=new T2(0,_h0,_gX),_h4=function(_h5,_h6){while(1){var _h7=E(_h5);if(!_h7._){return (E(_h6)._==0)?true:false;}else{var _h8=E(_h6);if(!_h8._){return false;}else{if(E(_h7.a)!=E(_h8.a)){return false;}else{_h5=_h7.b;_h6=_h8.b;continue;}}}}},_h9=function(_ha,_hb){return (!B(_h4(_ha,_hb)))?true:false;},_hc=new T2(0,_h4,_h9),_hd=function(_he,_hf){var _hg=E(_he);switch(_hg._){case 0:return new T1(0,function(_hh){return new F(function(){return _hd(B(A1(_hg.a,_hh)),_hf);});});case 1:return new T1(1,function(_hi){return new F(function(){return _hd(B(A1(_hg.a,_hi)),_hf);});});case 2:return new T0(2);case 3:return new F(function(){return _ge(B(A1(_hf,_hg.a)),new T(function(){return B(_hd(_hg.b,_hf));}));});break;default:var _hj=function(_hk){var _hl=E(_hk);if(!_hl._){return __Z;}else{var _hm=E(_hl.a);return new F(function(){return _ce(B(_g4(B(A1(_hf,_hm.a)),_hm.b)),new T(function(){return B(_hj(_hl.b));},1));});}},_hn=B(_hj(_hg.a));return (_hn._==0)?new T0(2):new T1(4,_hn);}},_ho=function(_hp,_hq){var _hr=E(_hp);if(!_hr){return new F(function(){return A1(_hq,_bT);});}else{var _hs=new T(function(){return B(_ho(_hr-1|0,_hq));});return new T1(0,function(_ht){return E(_hs);});}},_hu=function(_hv,_hw,_hx){var _hy=new T(function(){return B(A1(_hv,_eU));}),_hz=function(_hA,_hB,_hC,_hD){while(1){var _hE=B((function(_hF,_hG,_hH,_hI){var _hJ=E(_hF);switch(_hJ._){case 0:var _hK=E(_hG);if(!_hK._){return new F(function(){return A1(_hw,_hI);});}else{var _hL=_hH+1|0,_hM=_hI;_hA=B(A1(_hJ.a,_hK.a));_hB=_hK.b;_hC=_hL;_hD=_hM;return __continue;}break;case 1:var _hN=B(A1(_hJ.a,_hG)),_hO=_hG,_hL=_hH,_hM=_hI;_hA=_hN;_hB=_hO;_hC=_hL;_hD=_hM;return __continue;case 2:return new F(function(){return A1(_hw,_hI);});break;case 3:var _hP=new T(function(){return B(_hd(_hJ,_hI));});return new F(function(){return _ho(_hH,function(_hQ){return E(_hP);});});break;default:return new F(function(){return _hd(_hJ,_hI);});}})(_hA,_hB,_hC,_hD));if(_hE!=__continue){return _hE;}}};return function(_hR){return new F(function(){return _hz(_hy,_hR,0,_hx);});};},_hS=function(_hT){return new F(function(){return A1(_hT,_1);});},_hU=function(_hV,_hW){var _hX=function(_hY){var _hZ=E(_hY);if(!_hZ._){return E(_hS);}else{var _i0=_hZ.a;if(!B(A1(_hV,_i0))){return E(_hS);}else{var _i1=new T(function(){return B(_hX(_hZ.b));}),_i2=function(_i3){var _i4=new T(function(){return B(A1(_i1,function(_i5){return new F(function(){return A1(_i3,new T2(1,_i0,_i5));});}));});return new T1(0,function(_i6){return E(_i4);});};return E(_i2);}}};return function(_i7){return new F(function(){return A2(_hX,_i7,_hW);});};},_i8=new T0(6),_i9=function(_ia){return E(_ia);},_ib=new T(function(){return B(unCStr("valDig: Bad base"));}),_ic=new T(function(){return B(err(_ib));}),_id=function(_ie,_if){var _ig=function(_ih,_ii){var _ij=E(_ih);if(!_ij._){var _ik=new T(function(){return B(A1(_ii,_1));});return function(_il){return new F(function(){return A1(_il,_ik);});};}else{var _im=E(_ij.a),_in=function(_io){var _ip=new T(function(){return B(_ig(_ij.b,function(_iq){return new F(function(){return A1(_ii,new T2(1,_io,_iq));});}));}),_ir=function(_is){var _it=new T(function(){return B(A1(_ip,_is));});return new T1(0,function(_iu){return E(_it);});};return E(_ir);};switch(E(_ie)){case 8:if(48>_im){var _iv=new T(function(){return B(A1(_ii,_1));});return function(_iw){return new F(function(){return A1(_iw,_iv);});};}else{if(_im>55){var _ix=new T(function(){return B(A1(_ii,_1));});return function(_iy){return new F(function(){return A1(_iy,_ix);});};}else{return new F(function(){return _in(_im-48|0);});}}break;case 10:if(48>_im){var _iz=new T(function(){return B(A1(_ii,_1));});return function(_iA){return new F(function(){return A1(_iA,_iz);});};}else{if(_im>57){var _iB=new T(function(){return B(A1(_ii,_1));});return function(_iC){return new F(function(){return A1(_iC,_iB);});};}else{return new F(function(){return _in(_im-48|0);});}}break;case 16:if(48>_im){if(97>_im){if(65>_im){var _iD=new T(function(){return B(A1(_ii,_1));});return function(_iE){return new F(function(){return A1(_iE,_iD);});};}else{if(_im>70){var _iF=new T(function(){return B(A1(_ii,_1));});return function(_iG){return new F(function(){return A1(_iG,_iF);});};}else{return new F(function(){return _in((_im-65|0)+10|0);});}}}else{if(_im>102){if(65>_im){var _iH=new T(function(){return B(A1(_ii,_1));});return function(_iI){return new F(function(){return A1(_iI,_iH);});};}else{if(_im>70){var _iJ=new T(function(){return B(A1(_ii,_1));});return function(_iK){return new F(function(){return A1(_iK,_iJ);});};}else{return new F(function(){return _in((_im-65|0)+10|0);});}}}else{return new F(function(){return _in((_im-97|0)+10|0);});}}}else{if(_im>57){if(97>_im){if(65>_im){var _iL=new T(function(){return B(A1(_ii,_1));});return function(_iM){return new F(function(){return A1(_iM,_iL);});};}else{if(_im>70){var _iN=new T(function(){return B(A1(_ii,_1));});return function(_iO){return new F(function(){return A1(_iO,_iN);});};}else{return new F(function(){return _in((_im-65|0)+10|0);});}}}else{if(_im>102){if(65>_im){var _iP=new T(function(){return B(A1(_ii,_1));});return function(_iQ){return new F(function(){return A1(_iQ,_iP);});};}else{if(_im>70){var _iR=new T(function(){return B(A1(_ii,_1));});return function(_iS){return new F(function(){return A1(_iS,_iR);});};}else{return new F(function(){return _in((_im-65|0)+10|0);});}}}else{return new F(function(){return _in((_im-97|0)+10|0);});}}}else{return new F(function(){return _in(_im-48|0);});}}break;default:return E(_ic);}}},_iT=function(_iU){var _iV=E(_iU);if(!_iV._){return new T0(2);}else{return new F(function(){return A1(_if,_iV);});}};return function(_iW){return new F(function(){return A3(_ig,_iW,_i9,_iT);});};},_iX=16,_iY=8,_iZ=function(_j0){var _j1=function(_j2){return new F(function(){return A1(_j0,new T1(5,new T2(0,_iY,_j2)));});},_j3=function(_j4){return new F(function(){return A1(_j0,new T1(5,new T2(0,_iX,_j4)));});},_j5=function(_j6){switch(E(_j6)){case 79:return new T1(1,B(_id(_iY,_j1)));case 88:return new T1(1,B(_id(_iX,_j3)));case 111:return new T1(1,B(_id(_iY,_j1)));case 120:return new T1(1,B(_id(_iX,_j3)));default:return new T0(2);}};return function(_j7){return (E(_j7)==48)?E(new T1(0,_j5)):new T0(2);};},_j8=function(_j9){return new T1(0,B(_iZ(_j9)));},_ja=__Z,_jb=function(_jc){return new F(function(){return A1(_jc,_ja);});},_jd=function(_je){return new F(function(){return A1(_je,_ja);});},_jf=10,_jg=new T1(0,1),_jh=new T1(0,2147483647),_ji=function(_jj,_jk){while(1){var _jl=E(_jj);if(!_jl._){var _jm=_jl.a,_jn=E(_jk);if(!_jn._){var _jo=_jn.a,_jp=addC(_jm,_jo);if(!E(_jp.b)){return new T1(0,_jp.a);}else{_jj=new T1(1,I_fromInt(_jm));_jk=new T1(1,I_fromInt(_jo));continue;}}else{_jj=new T1(1,I_fromInt(_jm));_jk=_jn;continue;}}else{var _jq=E(_jk);if(!_jq._){_jj=_jl;_jk=new T1(1,I_fromInt(_jq.a));continue;}else{return new T1(1,I_add(_jl.a,_jq.a));}}}},_jr=new T(function(){return B(_ji(_jh,_jg));}),_js=function(_jt){var _ju=E(_jt);if(!_ju._){var _jv=E(_ju.a);return (_jv==( -2147483648))?E(_jr):new T1(0, -_jv);}else{return new T1(1,I_negate(_ju.a));}},_jw=new T1(0,10),_jx=function(_jy,_jz){while(1){var _jA=E(_jy);if(!_jA._){return E(_jz);}else{var _jB=_jz+1|0;_jy=_jA.b;_jz=_jB;continue;}}},_jC=function(_jD,_jE){var _jF=E(_jE);return (_jF._==0)?__Z:new T2(1,new T(function(){return B(A1(_jD,_jF.a));}),new T(function(){return B(_jC(_jD,_jF.b));}));},_jG=function(_jH){return new T1(0,_jH);},_jI=function(_jJ){return new F(function(){return _jG(E(_jJ));});},_jK=new T(function(){return B(unCStr("this should not happen"));}),_jL=new T(function(){return B(err(_jK));}),_jM=function(_jN,_jO){while(1){var _jP=E(_jN);if(!_jP._){var _jQ=_jP.a,_jR=E(_jO);if(!_jR._){var _jS=_jR.a;if(!(imul(_jQ,_jS)|0)){return new T1(0,imul(_jQ,_jS)|0);}else{_jN=new T1(1,I_fromInt(_jQ));_jO=new T1(1,I_fromInt(_jS));continue;}}else{_jN=new T1(1,I_fromInt(_jQ));_jO=_jR;continue;}}else{var _jT=E(_jO);if(!_jT._){_jN=_jP;_jO=new T1(1,I_fromInt(_jT.a));continue;}else{return new T1(1,I_mul(_jP.a,_jT.a));}}}},_jU=function(_jV,_jW){var _jX=E(_jW);if(!_jX._){return __Z;}else{var _jY=E(_jX.b);return (_jY._==0)?E(_jL):new T2(1,B(_ji(B(_jM(_jX.a,_jV)),_jY.a)),new T(function(){return B(_jU(_jV,_jY.b));}));}},_jZ=new T1(0,0),_k0=function(_k1,_k2,_k3){while(1){var _k4=B((function(_k5,_k6,_k7){var _k8=E(_k7);if(!_k8._){return E(_jZ);}else{if(!E(_k8.b)._){return E(_k8.a);}else{var _k9=E(_k6);if(_k9<=40){var _ka=function(_kb,_kc){while(1){var _kd=E(_kc);if(!_kd._){return E(_kb);}else{var _ke=B(_ji(B(_jM(_kb,_k5)),_kd.a));_kb=_ke;_kc=_kd.b;continue;}}};return new F(function(){return _ka(_jZ,_k8);});}else{var _kf=B(_jM(_k5,_k5));if(!(_k9%2)){var _kg=B(_jU(_k5,_k8));_k1=_kf;_k2=quot(_k9+1|0,2);_k3=_kg;return __continue;}else{var _kg=B(_jU(_k5,new T2(1,_jZ,_k8)));_k1=_kf;_k2=quot(_k9+1|0,2);_k3=_kg;return __continue;}}}}})(_k1,_k2,_k3));if(_k4!=__continue){return _k4;}}},_kh=function(_ki,_kj){return new F(function(){return _k0(_ki,new T(function(){return B(_jx(_kj,0));},1),B(_jC(_jI,_kj)));});},_kk=function(_kl){var _km=new T(function(){var _kn=new T(function(){var _ko=function(_kp){return new F(function(){return A1(_kl,new T1(1,new T(function(){return B(_kh(_jw,_kp));})));});};return new T1(1,B(_id(_jf,_ko)));}),_kq=function(_kr){if(E(_kr)==43){var _ks=function(_kt){return new F(function(){return A1(_kl,new T1(1,new T(function(){return B(_kh(_jw,_kt));})));});};return new T1(1,B(_id(_jf,_ks)));}else{return new T0(2);}},_ku=function(_kv){if(E(_kv)==45){var _kw=function(_kx){return new F(function(){return A1(_kl,new T1(1,new T(function(){return B(_js(B(_kh(_jw,_kx))));})));});};return new T1(1,B(_id(_jf,_kw)));}else{return new T0(2);}};return B(_ge(B(_ge(new T1(0,_ku),new T1(0,_kq))),_kn));});return new F(function(){return _ge(new T1(0,function(_ky){return (E(_ky)==101)?E(_km):new T0(2);}),new T1(0,function(_kz){return (E(_kz)==69)?E(_km):new T0(2);}));});},_kA=function(_kB){var _kC=function(_kD){return new F(function(){return A1(_kB,new T1(1,_kD));});};return function(_kE){return (E(_kE)==46)?new T1(1,B(_id(_jf,_kC))):new T0(2);};},_kF=function(_kG){return new T1(0,B(_kA(_kG)));},_kH=function(_kI){var _kJ=function(_kK){var _kL=function(_kM){return new T1(1,B(_hu(_kk,_jb,function(_kN){return new F(function(){return A1(_kI,new T1(5,new T3(1,_kK,_kM,_kN)));});})));};return new T1(1,B(_hu(_kF,_jd,_kL)));};return new F(function(){return _id(_jf,_kJ);});},_kO=function(_kP){return new T1(1,B(_kH(_kP)));},_kQ=function(_kR){return E(E(_kR).a);},_kS=function(_kT,_kU,_kV){while(1){var _kW=E(_kV);if(!_kW._){return false;}else{if(!B(A3(_kQ,_kT,_kU,_kW.a))){_kV=_kW.b;continue;}else{return true;}}}},_kX=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_kY=function(_kZ){return new F(function(){return _kS(_h3,_kZ,_kX);});},_l0=false,_l1=true,_l2=function(_l3){var _l4=new T(function(){return B(A1(_l3,_iY));}),_l5=new T(function(){return B(A1(_l3,_iX));});return function(_l6){switch(E(_l6)){case 79:return E(_l4);case 88:return E(_l5);case 111:return E(_l4);case 120:return E(_l5);default:return new T0(2);}};},_l7=function(_l8){return new T1(0,B(_l2(_l8)));},_l9=function(_la){return new F(function(){return A1(_la,_jf);});},_lb=function(_lc,_ld){var _le=jsShowI(_lc);return new F(function(){return _ce(fromJSStr(_le),_ld);});},_lf=function(_lg,_lh,_li){if(_lh>=0){return new F(function(){return _lb(_lh,_li);});}else{if(_lg<=6){return new F(function(){return _lb(_lh,_li);});}else{return new T2(1,_cx,new T(function(){var _lj=jsShowI(_lh);return B(_ce(fromJSStr(_lj),new T2(1,_cw,_li)));}));}}},_lk=function(_ll){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_lf(9,_ll,_1));}))));});},_lm=function(_ln,_lo){var _lp=E(_ln);if(!_lp._){var _lq=_lp.a,_lr=E(_lo);return (_lr._==0)?_lq<=_lr.a:I_compareInt(_lr.a,_lq)>=0;}else{var _ls=_lp.a,_lt=E(_lo);return (_lt._==0)?I_compareInt(_ls,_lt.a)<=0:I_compare(_ls,_lt.a)<=0;}},_lu=function(_lv){return new T0(2);},_lw=function(_lx){var _ly=E(_lx);if(!_ly._){return E(_lu);}else{var _lz=_ly.a,_lA=E(_ly.b);if(!_lA._){return E(_lz);}else{var _lB=new T(function(){return B(_lw(_lA));}),_lC=function(_lD){return new F(function(){return _ge(B(A1(_lz,_lD)),new T(function(){return B(A1(_lB,_lD));}));});};return E(_lC);}}},_lE=function(_lF,_lG){var _lH=function(_lI,_lJ,_lK){var _lL=E(_lI);if(!_lL._){return new F(function(){return A1(_lK,_lF);});}else{var _lM=E(_lJ);if(!_lM._){return new T0(2);}else{if(E(_lL.a)!=E(_lM.a)){return new T0(2);}else{var _lN=new T(function(){return B(_lH(_lL.b,_lM.b,_lK));});return new T1(0,function(_lO){return E(_lN);});}}}};return function(_lP){return new F(function(){return _lH(_lF,_lP,_lG);});};},_lQ=new T(function(){return B(unCStr("SO"));}),_lR=14,_lS=function(_lT){var _lU=new T(function(){return B(A1(_lT,_lR));});return new T1(1,B(_lE(_lQ,function(_lV){return E(_lU);})));},_lW=new T(function(){return B(unCStr("SOH"));}),_lX=1,_lY=function(_lZ){var _m0=new T(function(){return B(A1(_lZ,_lX));});return new T1(1,B(_lE(_lW,function(_m1){return E(_m0);})));},_m2=function(_m3){return new T1(1,B(_hu(_lY,_lS,_m3)));},_m4=new T(function(){return B(unCStr("NUL"));}),_m5=0,_m6=function(_m7){var _m8=new T(function(){return B(A1(_m7,_m5));});return new T1(1,B(_lE(_m4,function(_m9){return E(_m8);})));},_ma=new T(function(){return B(unCStr("STX"));}),_mb=2,_mc=function(_md){var _me=new T(function(){return B(A1(_md,_mb));});return new T1(1,B(_lE(_ma,function(_mf){return E(_me);})));},_mg=new T(function(){return B(unCStr("ETX"));}),_mh=3,_mi=function(_mj){var _mk=new T(function(){return B(A1(_mj,_mh));});return new T1(1,B(_lE(_mg,function(_ml){return E(_mk);})));},_mm=new T(function(){return B(unCStr("EOT"));}),_mn=4,_mo=function(_mp){var _mq=new T(function(){return B(A1(_mp,_mn));});return new T1(1,B(_lE(_mm,function(_mr){return E(_mq);})));},_ms=new T(function(){return B(unCStr("ENQ"));}),_mt=5,_mu=function(_mv){var _mw=new T(function(){return B(A1(_mv,_mt));});return new T1(1,B(_lE(_ms,function(_mx){return E(_mw);})));},_my=new T(function(){return B(unCStr("ACK"));}),_mz=6,_mA=function(_mB){var _mC=new T(function(){return B(A1(_mB,_mz));});return new T1(1,B(_lE(_my,function(_mD){return E(_mC);})));},_mE=new T(function(){return B(unCStr("BEL"));}),_mF=7,_mG=function(_mH){var _mI=new T(function(){return B(A1(_mH,_mF));});return new T1(1,B(_lE(_mE,function(_mJ){return E(_mI);})));},_mK=new T(function(){return B(unCStr("BS"));}),_mL=8,_mM=function(_mN){var _mO=new T(function(){return B(A1(_mN,_mL));});return new T1(1,B(_lE(_mK,function(_mP){return E(_mO);})));},_mQ=new T(function(){return B(unCStr("HT"));}),_mR=9,_mS=function(_mT){var _mU=new T(function(){return B(A1(_mT,_mR));});return new T1(1,B(_lE(_mQ,function(_mV){return E(_mU);})));},_mW=new T(function(){return B(unCStr("LF"));}),_mX=10,_mY=function(_mZ){var _n0=new T(function(){return B(A1(_mZ,_mX));});return new T1(1,B(_lE(_mW,function(_n1){return E(_n0);})));},_n2=new T(function(){return B(unCStr("VT"));}),_n3=11,_n4=function(_n5){var _n6=new T(function(){return B(A1(_n5,_n3));});return new T1(1,B(_lE(_n2,function(_n7){return E(_n6);})));},_n8=new T(function(){return B(unCStr("FF"));}),_n9=12,_na=function(_nb){var _nc=new T(function(){return B(A1(_nb,_n9));});return new T1(1,B(_lE(_n8,function(_nd){return E(_nc);})));},_ne=new T(function(){return B(unCStr("CR"));}),_nf=13,_ng=function(_nh){var _ni=new T(function(){return B(A1(_nh,_nf));});return new T1(1,B(_lE(_ne,function(_nj){return E(_ni);})));},_nk=new T(function(){return B(unCStr("SI"));}),_nl=15,_nm=function(_nn){var _no=new T(function(){return B(A1(_nn,_nl));});return new T1(1,B(_lE(_nk,function(_np){return E(_no);})));},_nq=new T(function(){return B(unCStr("DLE"));}),_nr=16,_ns=function(_nt){var _nu=new T(function(){return B(A1(_nt,_nr));});return new T1(1,B(_lE(_nq,function(_nv){return E(_nu);})));},_nw=new T(function(){return B(unCStr("DC1"));}),_nx=17,_ny=function(_nz){var _nA=new T(function(){return B(A1(_nz,_nx));});return new T1(1,B(_lE(_nw,function(_nB){return E(_nA);})));},_nC=new T(function(){return B(unCStr("DC2"));}),_nD=18,_nE=function(_nF){var _nG=new T(function(){return B(A1(_nF,_nD));});return new T1(1,B(_lE(_nC,function(_nH){return E(_nG);})));},_nI=new T(function(){return B(unCStr("DC3"));}),_nJ=19,_nK=function(_nL){var _nM=new T(function(){return B(A1(_nL,_nJ));});return new T1(1,B(_lE(_nI,function(_nN){return E(_nM);})));},_nO=new T(function(){return B(unCStr("DC4"));}),_nP=20,_nQ=function(_nR){var _nS=new T(function(){return B(A1(_nR,_nP));});return new T1(1,B(_lE(_nO,function(_nT){return E(_nS);})));},_nU=new T(function(){return B(unCStr("NAK"));}),_nV=21,_nW=function(_nX){var _nY=new T(function(){return B(A1(_nX,_nV));});return new T1(1,B(_lE(_nU,function(_nZ){return E(_nY);})));},_o0=new T(function(){return B(unCStr("SYN"));}),_o1=22,_o2=function(_o3){var _o4=new T(function(){return B(A1(_o3,_o1));});return new T1(1,B(_lE(_o0,function(_o5){return E(_o4);})));},_o6=new T(function(){return B(unCStr("ETB"));}),_o7=23,_o8=function(_o9){var _oa=new T(function(){return B(A1(_o9,_o7));});return new T1(1,B(_lE(_o6,function(_ob){return E(_oa);})));},_oc=new T(function(){return B(unCStr("CAN"));}),_od=24,_oe=function(_of){var _og=new T(function(){return B(A1(_of,_od));});return new T1(1,B(_lE(_oc,function(_oh){return E(_og);})));},_oi=new T(function(){return B(unCStr("EM"));}),_oj=25,_ok=function(_ol){var _om=new T(function(){return B(A1(_ol,_oj));});return new T1(1,B(_lE(_oi,function(_on){return E(_om);})));},_oo=new T(function(){return B(unCStr("SUB"));}),_op=26,_oq=function(_or){var _os=new T(function(){return B(A1(_or,_op));});return new T1(1,B(_lE(_oo,function(_ot){return E(_os);})));},_ou=new T(function(){return B(unCStr("ESC"));}),_ov=27,_ow=function(_ox){var _oy=new T(function(){return B(A1(_ox,_ov));});return new T1(1,B(_lE(_ou,function(_oz){return E(_oy);})));},_oA=new T(function(){return B(unCStr("FS"));}),_oB=28,_oC=function(_oD){var _oE=new T(function(){return B(A1(_oD,_oB));});return new T1(1,B(_lE(_oA,function(_oF){return E(_oE);})));},_oG=new T(function(){return B(unCStr("GS"));}),_oH=29,_oI=function(_oJ){var _oK=new T(function(){return B(A1(_oJ,_oH));});return new T1(1,B(_lE(_oG,function(_oL){return E(_oK);})));},_oM=new T(function(){return B(unCStr("RS"));}),_oN=30,_oO=function(_oP){var _oQ=new T(function(){return B(A1(_oP,_oN));});return new T1(1,B(_lE(_oM,function(_oR){return E(_oQ);})));},_oS=new T(function(){return B(unCStr("US"));}),_oT=31,_oU=function(_oV){var _oW=new T(function(){return B(A1(_oV,_oT));});return new T1(1,B(_lE(_oS,function(_oX){return E(_oW);})));},_oY=new T(function(){return B(unCStr("SP"));}),_oZ=32,_p0=function(_p1){var _p2=new T(function(){return B(A1(_p1,_oZ));});return new T1(1,B(_lE(_oY,function(_p3){return E(_p2);})));},_p4=new T(function(){return B(unCStr("DEL"));}),_p5=127,_p6=function(_p7){var _p8=new T(function(){return B(A1(_p7,_p5));});return new T1(1,B(_lE(_p4,function(_p9){return E(_p8);})));},_pa=new T2(1,_p6,_1),_pb=new T2(1,_p0,_pa),_pc=new T2(1,_oU,_pb),_pd=new T2(1,_oO,_pc),_pe=new T2(1,_oI,_pd),_pf=new T2(1,_oC,_pe),_pg=new T2(1,_ow,_pf),_ph=new T2(1,_oq,_pg),_pi=new T2(1,_ok,_ph),_pj=new T2(1,_oe,_pi),_pk=new T2(1,_o8,_pj),_pl=new T2(1,_o2,_pk),_pm=new T2(1,_nW,_pl),_pn=new T2(1,_nQ,_pm),_po=new T2(1,_nK,_pn),_pp=new T2(1,_nE,_po),_pq=new T2(1,_ny,_pp),_pr=new T2(1,_ns,_pq),_ps=new T2(1,_nm,_pr),_pt=new T2(1,_ng,_ps),_pu=new T2(1,_na,_pt),_pv=new T2(1,_n4,_pu),_pw=new T2(1,_mY,_pv),_px=new T2(1,_mS,_pw),_py=new T2(1,_mM,_px),_pz=new T2(1,_mG,_py),_pA=new T2(1,_mA,_pz),_pB=new T2(1,_mu,_pA),_pC=new T2(1,_mo,_pB),_pD=new T2(1,_mi,_pC),_pE=new T2(1,_mc,_pD),_pF=new T2(1,_m6,_pE),_pG=new T2(1,_m2,_pF),_pH=new T(function(){return B(_lw(_pG));}),_pI=34,_pJ=new T1(0,1114111),_pK=92,_pL=39,_pM=function(_pN){var _pO=new T(function(){return B(A1(_pN,_mF));}),_pP=new T(function(){return B(A1(_pN,_mL));}),_pQ=new T(function(){return B(A1(_pN,_mR));}),_pR=new T(function(){return B(A1(_pN,_mX));}),_pS=new T(function(){return B(A1(_pN,_n3));}),_pT=new T(function(){return B(A1(_pN,_n9));}),_pU=new T(function(){return B(A1(_pN,_nf));}),_pV=new T(function(){return B(A1(_pN,_pK));}),_pW=new T(function(){return B(A1(_pN,_pL));}),_pX=new T(function(){return B(A1(_pN,_pI));}),_pY=new T(function(){var _pZ=function(_q0){var _q1=new T(function(){return B(_jG(E(_q0)));}),_q2=function(_q3){var _q4=B(_kh(_q1,_q3));if(!B(_lm(_q4,_pJ))){return new T0(2);}else{return new F(function(){return A1(_pN,new T(function(){var _q5=B(_bU(_q4));if(_q5>>>0>1114111){return B(_lk(_q5));}else{return _q5;}}));});}};return new T1(1,B(_id(_q0,_q2)));},_q6=new T(function(){var _q7=new T(function(){return B(A1(_pN,_oT));}),_q8=new T(function(){return B(A1(_pN,_oN));}),_q9=new T(function(){return B(A1(_pN,_oH));}),_qa=new T(function(){return B(A1(_pN,_oB));}),_qb=new T(function(){return B(A1(_pN,_ov));}),_qc=new T(function(){return B(A1(_pN,_op));}),_qd=new T(function(){return B(A1(_pN,_oj));}),_qe=new T(function(){return B(A1(_pN,_od));}),_qf=new T(function(){return B(A1(_pN,_o7));}),_qg=new T(function(){return B(A1(_pN,_o1));}),_qh=new T(function(){return B(A1(_pN,_nV));}),_qi=new T(function(){return B(A1(_pN,_nP));}),_qj=new T(function(){return B(A1(_pN,_nJ));}),_qk=new T(function(){return B(A1(_pN,_nD));}),_ql=new T(function(){return B(A1(_pN,_nx));}),_qm=new T(function(){return B(A1(_pN,_nr));}),_qn=new T(function(){return B(A1(_pN,_nl));}),_qo=new T(function(){return B(A1(_pN,_lR));}),_qp=new T(function(){return B(A1(_pN,_mz));}),_qq=new T(function(){return B(A1(_pN,_mt));}),_qr=new T(function(){return B(A1(_pN,_mn));}),_qs=new T(function(){return B(A1(_pN,_mh));}),_qt=new T(function(){return B(A1(_pN,_mb));}),_qu=new T(function(){return B(A1(_pN,_lX));}),_qv=new T(function(){return B(A1(_pN,_m5));}),_qw=function(_qx){switch(E(_qx)){case 64:return E(_qv);case 65:return E(_qu);case 66:return E(_qt);case 67:return E(_qs);case 68:return E(_qr);case 69:return E(_qq);case 70:return E(_qp);case 71:return E(_pO);case 72:return E(_pP);case 73:return E(_pQ);case 74:return E(_pR);case 75:return E(_pS);case 76:return E(_pT);case 77:return E(_pU);case 78:return E(_qo);case 79:return E(_qn);case 80:return E(_qm);case 81:return E(_ql);case 82:return E(_qk);case 83:return E(_qj);case 84:return E(_qi);case 85:return E(_qh);case 86:return E(_qg);case 87:return E(_qf);case 88:return E(_qe);case 89:return E(_qd);case 90:return E(_qc);case 91:return E(_qb);case 92:return E(_qa);case 93:return E(_q9);case 94:return E(_q8);case 95:return E(_q7);default:return new T0(2);}};return B(_ge(new T1(0,function(_qy){return (E(_qy)==94)?E(new T1(0,_qw)):new T0(2);}),new T(function(){return B(A1(_pH,_pN));})));});return B(_ge(new T1(1,B(_hu(_l7,_l9,_pZ))),_q6));});return new F(function(){return _ge(new T1(0,function(_qz){switch(E(_qz)){case 34:return E(_pX);case 39:return E(_pW);case 92:return E(_pV);case 97:return E(_pO);case 98:return E(_pP);case 102:return E(_pT);case 110:return E(_pR);case 114:return E(_pU);case 116:return E(_pQ);case 118:return E(_pS);default:return new T0(2);}}),_pY);});},_qA=function(_qB){return new F(function(){return A1(_qB,_bT);});},_qC=function(_qD){var _qE=E(_qD);if(!_qE._){return E(_qA);}else{var _qF=E(_qE.a),_qG=_qF>>>0,_qH=new T(function(){return B(_qC(_qE.b));});if(_qG>887){var _qI=u_iswspace(_qF);if(!E(_qI)){return E(_qA);}else{var _qJ=function(_qK){var _qL=new T(function(){return B(A1(_qH,_qK));});return new T1(0,function(_qM){return E(_qL);});};return E(_qJ);}}else{var _qN=E(_qG);if(_qN==32){var _qO=function(_qP){var _qQ=new T(function(){return B(A1(_qH,_qP));});return new T1(0,function(_qR){return E(_qQ);});};return E(_qO);}else{if(_qN-9>>>0>4){if(E(_qN)==160){var _qS=function(_qT){var _qU=new T(function(){return B(A1(_qH,_qT));});return new T1(0,function(_qV){return E(_qU);});};return E(_qS);}else{return E(_qA);}}else{var _qW=function(_qX){var _qY=new T(function(){return B(A1(_qH,_qX));});return new T1(0,function(_qZ){return E(_qY);});};return E(_qW);}}}}},_r0=function(_r1){var _r2=new T(function(){return B(_r0(_r1));}),_r3=function(_r4){return (E(_r4)==92)?E(_r2):new T0(2);},_r5=function(_r6){return E(new T1(0,_r3));},_r7=new T1(1,function(_r8){return new F(function(){return A2(_qC,_r8,_r5);});}),_r9=new T(function(){return B(_pM(function(_ra){return new F(function(){return A1(_r1,new T2(0,_ra,_l1));});}));}),_rb=function(_rc){var _rd=E(_rc);if(_rd==38){return E(_r2);}else{var _re=_rd>>>0;if(_re>887){var _rf=u_iswspace(_rd);return (E(_rf)==0)?new T0(2):E(_r7);}else{var _rg=E(_re);return (_rg==32)?E(_r7):(_rg-9>>>0>4)?(E(_rg)==160)?E(_r7):new T0(2):E(_r7);}}};return new F(function(){return _ge(new T1(0,function(_rh){return (E(_rh)==92)?E(new T1(0,_rb)):new T0(2);}),new T1(0,function(_ri){var _rj=E(_ri);if(E(_rj)==92){return E(_r9);}else{return new F(function(){return A1(_r1,new T2(0,_rj,_l0));});}}));});},_rk=function(_rl,_rm){var _rn=new T(function(){return B(A1(_rm,new T1(1,new T(function(){return B(A1(_rl,_1));}))));}),_ro=function(_rp){var _rq=E(_rp),_rr=E(_rq.a);if(E(_rr)==34){if(!E(_rq.b)){return E(_rn);}else{return new F(function(){return _rk(function(_rs){return new F(function(){return A1(_rl,new T2(1,_rr,_rs));});},_rm);});}}else{return new F(function(){return _rk(function(_rt){return new F(function(){return A1(_rl,new T2(1,_rr,_rt));});},_rm);});}};return new F(function(){return _r0(_ro);});},_ru=new T(function(){return B(unCStr("_\'"));}),_rv=function(_rw){var _rx=u_iswalnum(_rw);if(!E(_rx)){return new F(function(){return _kS(_h3,_rw,_ru);});}else{return true;}},_ry=function(_rz){return new F(function(){return _rv(E(_rz));});},_rA=new T(function(){return B(unCStr(",;()[]{}`"));}),_rB=new T(function(){return B(unCStr("=>"));}),_rC=new T2(1,_rB,_1),_rD=new T(function(){return B(unCStr("~"));}),_rE=new T2(1,_rD,_rC),_rF=new T(function(){return B(unCStr("@"));}),_rG=new T2(1,_rF,_rE),_rH=new T(function(){return B(unCStr("->"));}),_rI=new T2(1,_rH,_rG),_rJ=new T(function(){return B(unCStr("<-"));}),_rK=new T2(1,_rJ,_rI),_rL=new T(function(){return B(unCStr("|"));}),_rM=new T2(1,_rL,_rK),_rN=new T(function(){return B(unCStr("\\"));}),_rO=new T2(1,_rN,_rM),_rP=new T(function(){return B(unCStr("="));}),_rQ=new T2(1,_rP,_rO),_rR=new T(function(){return B(unCStr("::"));}),_rS=new T2(1,_rR,_rQ),_rT=new T(function(){return B(unCStr(".."));}),_rU=new T2(1,_rT,_rS),_rV=function(_rW){var _rX=new T(function(){return B(A1(_rW,_i8));}),_rY=new T(function(){var _rZ=new T(function(){var _s0=function(_s1){var _s2=new T(function(){return B(A1(_rW,new T1(0,_s1)));});return new T1(0,function(_s3){return (E(_s3)==39)?E(_s2):new T0(2);});};return B(_pM(_s0));}),_s4=function(_s5){var _s6=E(_s5);switch(E(_s6)){case 39:return new T0(2);case 92:return E(_rZ);default:var _s7=new T(function(){return B(A1(_rW,new T1(0,_s6)));});return new T1(0,function(_s8){return (E(_s8)==39)?E(_s7):new T0(2);});}},_s9=new T(function(){var _sa=new T(function(){return B(_rk(_i9,_rW));}),_sb=new T(function(){var _sc=new T(function(){var _sd=new T(function(){var _se=function(_sf){var _sg=E(_sf),_sh=u_iswalpha(_sg);return (E(_sh)==0)?(E(_sg)==95)?new T1(1,B(_hU(_ry,function(_si){return new F(function(){return A1(_rW,new T1(3,new T2(1,_sg,_si)));});}))):new T0(2):new T1(1,B(_hU(_ry,function(_sj){return new F(function(){return A1(_rW,new T1(3,new T2(1,_sg,_sj)));});})));};return B(_ge(new T1(0,_se),new T(function(){return new T1(1,B(_hu(_j8,_kO,_rW)));})));}),_sk=function(_sl){return (!B(_kS(_h3,_sl,_kX)))?new T0(2):new T1(1,B(_hU(_kY,function(_sm){var _sn=new T2(1,_sl,_sm);if(!B(_kS(_hc,_sn,_rU))){return new F(function(){return A1(_rW,new T1(4,_sn));});}else{return new F(function(){return A1(_rW,new T1(2,_sn));});}})));};return B(_ge(new T1(0,_sk),_sd));});return B(_ge(new T1(0,function(_so){if(!B(_kS(_h3,_so,_rA))){return new T0(2);}else{return new F(function(){return A1(_rW,new T1(2,new T2(1,_so,_1)));});}}),_sc));});return B(_ge(new T1(0,function(_sp){return (E(_sp)==34)?E(_sa):new T0(2);}),_sb));});return B(_ge(new T1(0,function(_sq){return (E(_sq)==39)?E(new T1(0,_s4)):new T0(2);}),_s9));});return new F(function(){return _ge(new T1(1,function(_sr){return (E(_sr)._==0)?E(_rX):new T0(2);}),_rY);});},_ss=0,_st=function(_su,_sv){var _sw=new T(function(){var _sx=new T(function(){var _sy=function(_sz){var _sA=new T(function(){var _sB=new T(function(){return B(A1(_sv,_sz));});return B(_rV(function(_sC){var _sD=E(_sC);return (_sD._==2)?(!B(_gS(_sD.a,_gR)))?new T0(2):E(_sB):new T0(2);}));}),_sE=function(_sF){return E(_sA);};return new T1(1,function(_sG){return new F(function(){return A2(_qC,_sG,_sE);});});};return B(A2(_su,_ss,_sy));});return B(_rV(function(_sH){var _sI=E(_sH);return (_sI._==2)?(!B(_gS(_sI.a,_gQ)))?new T0(2):E(_sx):new T0(2);}));}),_sJ=function(_sK){return E(_sw);};return function(_sL){return new F(function(){return A2(_qC,_sL,_sJ);});};},_sM=function(_sN,_sO){var _sP=function(_sQ){var _sR=new T(function(){return B(A1(_sN,_sQ));}),_sS=function(_sT){return new F(function(){return _ge(B(A1(_sR,_sT)),new T(function(){return new T1(1,B(_st(_sP,_sT)));}));});};return E(_sS);},_sU=new T(function(){return B(A1(_sN,_sO));}),_sV=function(_sW){return new F(function(){return _ge(B(A1(_sU,_sW)),new T(function(){return new T1(1,B(_st(_sP,_sW)));}));});};return E(_sV);},_sX=function(_sY,_sZ){var _t0=function(_t1,_t2){var _t3=function(_t4){return new F(function(){return A1(_t2,new T(function(){return B(_js(_t4));}));});},_t5=new T(function(){return B(_rV(function(_t6){return new F(function(){return A3(_sY,_t6,_t1,_t3);});}));}),_t7=function(_t8){return E(_t5);},_t9=function(_ta){return new F(function(){return A2(_qC,_ta,_t7);});},_tb=new T(function(){return B(_rV(function(_tc){var _td=E(_tc);if(_td._==4){var _te=E(_td.a);if(!_te._){return new F(function(){return A3(_sY,_td,_t1,_t2);});}else{if(E(_te.a)==45){if(!E(_te.b)._){return E(new T1(1,_t9));}else{return new F(function(){return A3(_sY,_td,_t1,_t2);});}}else{return new F(function(){return A3(_sY,_td,_t1,_t2);});}}}else{return new F(function(){return A3(_sY,_td,_t1,_t2);});}}));}),_tf=function(_tg){return E(_tb);};return new T1(1,function(_th){return new F(function(){return A2(_qC,_th,_tf);});});};return new F(function(){return _sM(_t0,_sZ);});},_ti=function(_tj){var _tk=E(_tj);if(!_tk._){var _tl=_tk.b,_tm=new T(function(){return B(_k0(new T(function(){return B(_jG(E(_tk.a)));}),new T(function(){return B(_jx(_tl,0));},1),B(_jC(_jI,_tl))));});return new T1(1,_tm);}else{return (E(_tk.b)._==0)?(E(_tk.c)._==0)?new T1(1,new T(function(){return B(_kh(_jw,_tk.a));})):__Z:__Z;}},_tn=function(_to,_tp){return new T0(2);},_tq=function(_tr){var _ts=E(_tr);if(_ts._==5){var _tt=B(_ti(_ts.a));return (_tt._==0)?E(_tn):function(_tu,_tv){return new F(function(){return A1(_tv,_tt.a);});};}else{return E(_tn);}},_tw=function(_tx){return new F(function(){return _sX(_tq,_tx);});},_ty=new T(function(){return B(unCStr("["));}),_tz=function(_tA,_tB){var _tC=function(_tD,_tE){var _tF=new T(function(){return B(A1(_tE,_1));}),_tG=new T(function(){var _tH=function(_tI){return new F(function(){return _tC(_l1,function(_tJ){return new F(function(){return A1(_tE,new T2(1,_tI,_tJ));});});});};return B(A2(_tA,_ss,_tH));}),_tK=new T(function(){return B(_rV(function(_tL){var _tM=E(_tL);if(_tM._==2){var _tN=E(_tM.a);if(!_tN._){return new T0(2);}else{var _tO=_tN.b;switch(E(_tN.a)){case 44:return (E(_tO)._==0)?(!E(_tD))?new T0(2):E(_tG):new T0(2);case 93:return (E(_tO)._==0)?E(_tF):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_tP=function(_tQ){return E(_tK);};return new T1(1,function(_tR){return new F(function(){return A2(_qC,_tR,_tP);});});},_tS=function(_tT,_tU){return new F(function(){return _tV(_tU);});},_tV=function(_tW){var _tX=new T(function(){var _tY=new T(function(){var _tZ=new T(function(){var _u0=function(_u1){return new F(function(){return _tC(_l1,function(_u2){return new F(function(){return A1(_tW,new T2(1,_u1,_u2));});});});};return B(A2(_tA,_ss,_u0));});return B(_ge(B(_tC(_l0,_tW)),_tZ));});return B(_rV(function(_u3){var _u4=E(_u3);return (_u4._==2)?(!B(_gS(_u4.a,_ty)))?new T0(2):E(_tY):new T0(2);}));}),_u5=function(_u6){return E(_tX);};return new F(function(){return _ge(new T1(1,function(_u7){return new F(function(){return A2(_qC,_u7,_u5);});}),new T(function(){return new T1(1,B(_st(_tS,_tW)));}));});};return new F(function(){return _tV(_tB);});},_u8=function(_u9,_ua){return new F(function(){return _tz(_tw,_ua);});},_ub=function(_uc){var _ud=new T(function(){return B(A3(_sX,_tq,_uc,_eU));});return function(_ue){return new F(function(){return _g4(_ud,_ue);});};},_uf=new T(function(){return B(_tz(_tw,_eU));}),_ug=function(_tx){return new F(function(){return _g4(_uf,_tx);});},_uh=new T4(0,_ub,_ug,_tw,_u8),_ui=11,_uj=new T(function(){return B(unCStr("IdentChoice"));}),_uk=function(_ul,_um){if(_ul>10){return new T0(2);}else{var _un=new T(function(){var _uo=new T(function(){return B(A3(_sX,_tq,_ui,function(_up){return new F(function(){return A1(_um,_up);});}));});return B(_rV(function(_uq){var _ur=E(_uq);return (_ur._==3)?(!B(_gS(_ur.a,_uj)))?new T0(2):E(_uo):new T0(2);}));}),_us=function(_ut){return E(_un);};return new T1(1,function(_uu){return new F(function(){return A2(_qC,_uu,_us);});});}},_uv=function(_uw,_ux){return new F(function(){return _uk(E(_uw),_ux);});},_uy=function(_uz){return new F(function(){return _sM(_uv,_uz);});},_uA=function(_uB,_uC){return new F(function(){return _tz(_uy,_uC);});},_uD=new T(function(){return B(_tz(_uy,_eU));}),_uE=function(_uz){return new F(function(){return _g4(_uD,_uz);});},_uF=function(_uG){var _uH=new T(function(){return B(A3(_sM,_uv,_uG,_eU));});return function(_ue){return new F(function(){return _g4(_uH,_ue);});};},_uI=new T4(0,_uF,_uE,_uy,_uA),_uJ=new T(function(){return B(unCStr(","));}),_uK=function(_uL){return E(E(_uL).c);},_uM=function(_uN,_uO,_uP){var _uQ=new T(function(){return B(_uK(_uO));}),_uR=new T(function(){return B(A2(_uK,_uN,_uP));}),_uS=function(_uT){var _uU=function(_uV){var _uW=new T(function(){var _uX=new T(function(){return B(A2(_uQ,_uP,function(_uY){return new F(function(){return A1(_uT,new T2(0,_uV,_uY));});}));});return B(_rV(function(_uZ){var _v0=E(_uZ);return (_v0._==2)?(!B(_gS(_v0.a,_uJ)))?new T0(2):E(_uX):new T0(2);}));}),_v1=function(_v2){return E(_uW);};return new T1(1,function(_v3){return new F(function(){return A2(_qC,_v3,_v1);});});};return new F(function(){return A1(_uR,_uU);});};return E(_uS);},_v4=function(_v5,_v6,_v7){var _v8=function(_tx){return new F(function(){return _uM(_v5,_v6,_tx);});},_v9=function(_va,_vb){return new F(function(){return _vc(_vb);});},_vc=function(_vd){return new F(function(){return _ge(new T1(1,B(_st(_v8,_vd))),new T(function(){return new T1(1,B(_st(_v9,_vd)));}));});};return new F(function(){return _vc(_v7);});},_ve=function(_vf,_vg){return new F(function(){return _v4(_uI,_uh,_vg);});},_vh=new T(function(){return B(_tz(_ve,_eU));}),_vi=function(_uz){return new F(function(){return _g4(_vh,_uz);});},_vj=new T(function(){return B(_v4(_uI,_uh,_eU));}),_vk=function(_uz){return new F(function(){return _g4(_vj,_uz);});},_vl=function(_vm,_uz){return new F(function(){return _vk(_uz);});},_vn=function(_vo,_vp){return new F(function(){return _tz(_ve,_vp);});},_vq=new T4(0,_vl,_vi,_ve,_vn),_vr=function(_vs,_vt){return new F(function(){return _v4(_vq,_uh,_vt);});},_vu=function(_vv,_vw){return new F(function(){return _tz(_vr,_vw);});},_vx=new T(function(){return B(_tz(_vu,_eU));}),_vy=function(_vz){return new F(function(){return _g4(_vx,_vz);});},_vA=function(_vB){return new F(function(){return _tz(_vu,_vB);});},_vC=function(_vD,_vE){return new F(function(){return _vA(_vE);});},_vF=new T(function(){return B(_tz(_vr,_eU));}),_vG=function(_vz){return new F(function(){return _g4(_vF,_vz);});},_vH=function(_vI,_vz){return new F(function(){return _vG(_vz);});},_vJ=new T4(0,_vH,_vy,_vu,_vC),_vK=new T(function(){return B(unCStr("IdentPay"));}),_vL=function(_vM,_vN){if(_vM>10){return new T0(2);}else{var _vO=new T(function(){var _vP=new T(function(){return B(A3(_sX,_tq,_ui,function(_vQ){return new F(function(){return A1(_vN,_vQ);});}));});return B(_rV(function(_vR){var _vS=E(_vR);return (_vS._==3)?(!B(_gS(_vS.a,_vK)))?new T0(2):E(_vP):new T0(2);}));}),_vT=function(_vU){return E(_vO);};return new T1(1,function(_vV){return new F(function(){return A2(_qC,_vV,_vT);});});}},_vW=function(_vX,_vY){return new F(function(){return _vL(E(_vX),_vY);});},_vZ=function(_uz){return new F(function(){return _sM(_vW,_uz);});},_w0=function(_w1,_w2){return new F(function(){return _tz(_vZ,_w2);});},_w3=new T(function(){return B(_tz(_vZ,_eU));}),_w4=function(_uz){return new F(function(){return _g4(_w3,_uz);});},_w5=function(_w6){var _w7=new T(function(){return B(A3(_sM,_vW,_w6,_eU));});return function(_ue){return new F(function(){return _g4(_w7,_ue);});};},_w8=new T4(0,_w5,_w4,_vZ,_w0),_w9=function(_wa,_wb){return new F(function(){return _v4(_w8,_uh,_wb);});},_wc=new T(function(){return B(_tz(_w9,_eU));}),_wd=function(_uz){return new F(function(){return _g4(_wc,_uz);});},_we=new T(function(){return B(_v4(_w8,_uh,_eU));}),_wf=function(_uz){return new F(function(){return _g4(_we,_uz);});},_wg=function(_wh,_uz){return new F(function(){return _wf(_uz);});},_wi=function(_wj,_wk){return new F(function(){return _tz(_w9,_wk);});},_wl=new T4(0,_wg,_wd,_w9,_wi),_wm=function(_wn,_wo){return new F(function(){return _v4(_wl,_uh,_wo);});},_wp=function(_wq,_wr){return new F(function(){return _tz(_wm,_wr);});},_ws=new T(function(){return B(_tz(_wp,_eU));}),_wt=function(_vz){return new F(function(){return _g4(_ws,_vz);});},_wu=function(_wv){return new F(function(){return _tz(_wp,_wv);});},_ww=function(_wx,_wy){return new F(function(){return _wu(_wy);});},_wz=new T(function(){return B(_tz(_wm,_eU));}),_wA=function(_vz){return new F(function(){return _g4(_wz,_vz);});},_wB=function(_wC,_vz){return new F(function(){return _wA(_vz);});},_wD=new T4(0,_wB,_wt,_wp,_ww),_wE=new T(function(){return B(unCStr("IdentCC"));}),_wF=function(_wG,_wH){if(_wG>10){return new T0(2);}else{var _wI=new T(function(){var _wJ=new T(function(){return B(A3(_sX,_tq,_ui,function(_wK){return new F(function(){return A1(_wH,_wK);});}));});return B(_rV(function(_wL){var _wM=E(_wL);return (_wM._==3)?(!B(_gS(_wM.a,_wE)))?new T0(2):E(_wJ):new T0(2);}));}),_wN=function(_wO){return E(_wI);};return new T1(1,function(_wP){return new F(function(){return A2(_qC,_wP,_wN);});});}},_wQ=function(_wR,_wS){return new F(function(){return _wF(E(_wR),_wS);});},_wT=new T(function(){return B(unCStr("RC"));}),_wU=function(_wV,_wW){if(_wV>10){return new T0(2);}else{var _wX=new T(function(){var _wY=new T(function(){var _wZ=function(_x0){var _x1=function(_x2){return new F(function(){return A3(_sX,_tq,_ui,function(_x3){return new F(function(){return A1(_wW,new T3(0,_x0,_x2,_x3));});});});};return new F(function(){return A3(_sX,_tq,_ui,_x1);});};return B(A3(_sM,_wQ,_ui,_wZ));});return B(_rV(function(_x4){var _x5=E(_x4);return (_x5._==3)?(!B(_gS(_x5.a,_wT)))?new T0(2):E(_wY):new T0(2);}));}),_x6=function(_x7){return E(_wX);};return new T1(1,function(_x8){return new F(function(){return A2(_qC,_x8,_x6);});});}},_x9=function(_xa,_xb){return new F(function(){return _wU(E(_xa),_xb);});},_xc=function(_uz){return new F(function(){return _sM(_x9,_uz);});},_xd=function(_xe,_xf){return new F(function(){return _tz(_xc,_xf);});},_xg=new T(function(){return B(_tz(_xd,_eU));}),_xh=function(_vz){return new F(function(){return _g4(_xg,_vz);});},_xi=new T(function(){return B(_tz(_xc,_eU));}),_xj=function(_vz){return new F(function(){return _g4(_xi,_vz);});},_xk=function(_xl,_vz){return new F(function(){return _xj(_vz);});},_xm=function(_xn,_xo){return new F(function(){return _tz(_xd,_xo);});},_xp=new T4(0,_xk,_xh,_xd,_xm),_xq=new T(function(){return B(unCStr("CC"));}),_xr=function(_xs,_xt){if(_xs>10){return new T0(2);}else{var _xu=new T(function(){var _xv=new T(function(){var _xw=function(_xx){var _xy=function(_xz){var _xA=function(_xB){return new F(function(){return A3(_sX,_tq,_ui,function(_xC){return new F(function(){return A1(_xt,new T4(0,_xx,_xz,_xB,_xC));});});});};return new F(function(){return A3(_sX,_tq,_ui,_xA);});};return new F(function(){return A3(_sX,_tq,_ui,_xy);});};return B(A3(_sM,_wQ,_ui,_xw));});return B(_rV(function(_xD){var _xE=E(_xD);return (_xE._==3)?(!B(_gS(_xE.a,_xq)))?new T0(2):E(_xv):new T0(2);}));}),_xF=function(_xG){return E(_xu);};return new T1(1,function(_xH){return new F(function(){return A2(_qC,_xH,_xF);});});}},_xI=function(_xJ,_xK){return new F(function(){return _xr(E(_xJ),_xK);});},_xL=function(_uz){return new F(function(){return _sM(_xI,_uz);});},_xM=function(_xN,_xO){return new F(function(){return _tz(_xL,_xO);});},_xP=new T(function(){return B(_tz(_xM,_eU));}),_xQ=function(_vz){return new F(function(){return _g4(_xP,_vz);});},_xR=new T(function(){return B(_tz(_xL,_eU));}),_xS=function(_vz){return new F(function(){return _g4(_xR,_vz);});},_xT=function(_xU,_vz){return new F(function(){return _xS(_vz);});},_xV=function(_xW,_xX){return new F(function(){return _tz(_xM,_xX);});},_xY=new T4(0,_xT,_xQ,_xM,_xV),_xZ=function(_y0,_y1,_y2,_y3,_y4){var _y5=new T(function(){return B(_uM(_y0,_y1,_y4));}),_y6=new T(function(){return B(_uK(_y3));}),_y7=function(_y8){var _y9=function(_ya){var _yb=E(_ya),_yc=new T(function(){var _yd=new T(function(){var _ye=function(_yf){var _yg=new T(function(){var _yh=new T(function(){return B(A2(_y6,_y4,function(_yi){return new F(function(){return A1(_y8,new T4(0,_yb.a,_yb.b,_yf,_yi));});}));});return B(_rV(function(_yj){var _yk=E(_yj);return (_yk._==2)?(!B(_gS(_yk.a,_uJ)))?new T0(2):E(_yh):new T0(2);}));}),_yl=function(_ym){return E(_yg);};return new T1(1,function(_yn){return new F(function(){return A2(_qC,_yn,_yl);});});};return B(A3(_uK,_y2,_y4,_ye));});return B(_rV(function(_yo){var _yp=E(_yo);return (_yp._==2)?(!B(_gS(_yp.a,_uJ)))?new T0(2):E(_yd):new T0(2);}));}),_yq=function(_yr){return E(_yc);};return new T1(1,function(_ys){return new F(function(){return A2(_qC,_ys,_yq);});});};return new F(function(){return A1(_y5,_y9);});};return E(_y7);},_yt=function(_yu,_yv,_yw,_yx,_yy){var _yz=function(_tx){return new F(function(){return _xZ(_yu,_yv,_yw,_yx,_tx);});},_yA=function(_yB,_yC){return new F(function(){return _yD(_yC);});},_yD=function(_yE){return new F(function(){return _ge(new T1(1,B(_st(_yz,_yE))),new T(function(){return new T1(1,B(_st(_yA,_yE)));}));});};return new F(function(){return _yD(_yy);});},_yF=function(_yG){var _yH=function(_yI){return E(new T2(3,_yG,_eT));};return new T1(1,function(_yJ){return new F(function(){return A2(_qC,_yJ,_yH);});});},_yK=new T(function(){return B(_yt(_xY,_xp,_wD,_vJ,_yF));}),_yL=function(_yM,_yN,_yO,_yP){var _yQ=E(_yM);if(_yQ==1){var _yR=E(_yP);return (_yR._==0)?new T3(0,new T(function(){return new T5(0,1,E(_yN),_yO,E(_0),E(_0));}),_1,_1):(!B(_e(_yN,E(_yR.a).a)))?new T3(0,new T(function(){return new T5(0,1,E(_yN),_yO,E(_0),E(_0));}),_yR,_1):new T3(0,new T(function(){return new T5(0,1,E(_yN),_yO,E(_0),E(_0));}),_1,_yR);}else{var _yS=B(_yL(_yQ>>1,_yN,_yO,_yP)),_yT=_yS.a,_yU=_yS.c,_yV=E(_yS.b);if(!_yV._){return new T3(0,_yT,_1,_yU);}else{var _yW=E(_yV.a),_yX=_yW.a,_yY=_yW.b,_yZ=E(_yV.b);if(!_yZ._){return new T3(0,new T(function(){return B(_18(_yX,_yY,_yT));}),_1,_yU);}else{var _z0=E(_yZ.a),_z1=_z0.a;if(!B(_e(_yX,_z1))){var _z2=B(_yL(_yQ>>1,_z1,_z0.b,_yZ.b));return new T3(0,new T(function(){return B(_2B(_yX,_yY,_yT,_z2.a));}),_z2.b,_z2.c);}else{return new T3(0,_yT,_1,_yV);}}}}},_z3=function(_z4,_z5,_z6){var _z7=E(_z4),_z8=E(_z6);if(!_z8._){var _z9=_z8.b,_za=_z8.c,_zb=_z8.d,_zc=_z8.e;switch(B(_2(_z7,_z9))){case 0:return new F(function(){return _1h(_z9,_za,B(_z3(_z7,_z5,_zb)),_zc);});break;case 1:return new T5(0,_z8.a,E(_z7),_z5,E(_zb),E(_zc));default:return new F(function(){return _q(_z9,_za,_zb,B(_z3(_z7,_z5,_zc)));});}}else{return new T5(0,1,E(_z7),_z5,E(_0),E(_0));}},_zd=function(_ze,_zf){while(1){var _zg=E(_zf);if(!_zg._){return E(_ze);}else{var _zh=E(_zg.a),_zi=B(_z3(_zh.a,_zh.b,_ze));_ze=_zi;_zf=_zg.b;continue;}}},_zj=function(_zk,_zl,_zm,_zn){return new F(function(){return _zd(B(_z3(_zl,_zm,_zk)),_zn);});},_zo=function(_zp,_zq,_zr){var _zs=E(_zq);return new F(function(){return _zd(B(_z3(_zs.a,_zs.b,_zp)),_zr);});},_zt=function(_zu,_zv,_zw){while(1){var _zx=E(_zw);if(!_zx._){return E(_zv);}else{var _zy=E(_zx.a),_zz=_zy.a,_zA=_zy.b,_zB=E(_zx.b);if(!_zB._){return new F(function(){return _18(_zz,_zA,_zv);});}else{var _zC=E(_zB.a),_zD=_zC.a;if(!B(_e(_zz,_zD))){var _zE=B(_yL(_zu,_zD,_zC.b,_zB.b)),_zF=_zE.a,_zG=E(_zE.c);if(!_zG._){var _zH=_zu<<1,_zI=B(_2B(_zz,_zA,_zv,_zF));_zu=_zH;_zv=_zI;_zw=_zE.b;continue;}else{return new F(function(){return _zo(B(_2B(_zz,_zA,_zv,_zF)),_zG.a,_zG.b);});}}else{return new F(function(){return _zj(_zv,_zz,_zA,_zB);});}}}}},_zJ=function(_zK,_zL,_zM,_zN,_zO){var _zP=E(_zO);if(!_zP._){return new F(function(){return _18(_zM,_zN,_zL);});}else{var _zQ=E(_zP.a),_zR=_zQ.a;if(!B(_e(_zM,_zR))){var _zS=B(_yL(_zK,_zR,_zQ.b,_zP.b)),_zT=_zS.a,_zU=E(_zS.c);if(!_zU._){return new F(function(){return _zt(_zK<<1,B(_2B(_zM,_zN,_zL,_zT)),_zS.b);});}else{return new F(function(){return _zo(B(_2B(_zM,_zN,_zL,_zT)),_zU.a,_zU.b);});}}else{return new F(function(){return _zj(_zL,_zM,_zN,_zP);});}}},_zV=function(_zW){var _zX=E(_zW);if(!_zX._){return new T0(1);}else{var _zY=E(_zX.a),_zZ=_zY.a,_A0=_zY.b,_A1=E(_zX.b);if(!_A1._){return new T5(0,1,E(_zZ),_A0,E(_0),E(_0));}else{var _A2=_A1.b,_A3=E(_A1.a),_A4=_A3.a,_A5=_A3.b;if(!B(_e(_zZ,_A4))){return new F(function(){return _zJ(1,new T5(0,1,E(_zZ),_A0,E(_0),E(_0)),_A4,_A5,_A2);});}else{return new F(function(){return _zj(new T5(0,1,E(_zZ),_A0,E(_0),E(_0)),_A4,_A5,_A2);});}}}},_A6=function(_){return _bT;},_A7=new T(function(){return B(unCStr(": Choose"));}),_A8=new T(function(){return eval("(function (x, y, z) {var a = document.getElementById(\'actions\'); var r = a.insertRow(); var c1 = r.insertCell(); c1.appendChild(document.createTextNode(x + \' \')); var input = document.createElement(\'input\'); input.type = \'number\'; var ch = \'ibox\' + a.childNodes.length; input.id = ch; input.value = 0; input.style.setProperty(\'width\', \'5em\'); input.style.setProperty(\'display\', \'inline\'); c1.appendChild(input); c1.appendChild(document.createTextNode(\' \' + y)); var c2 = r.insertCell(); var btn = document.createElement(\'button\'); c2.appendChild(btn); btn.appendChild(document.createTextNode(\'Add action\')); btn.style.setProperty(\'width\', \'100%\'); btn.onclick = function () {Haste.addActionWithNum(z, document.getElementById(ch).value);};})");}),_A9=function(_Aa,_Ab,_){var _Ac=new T(function(){return B(A3(_dr,_c9,new T2(1,function(_Ad){return new F(function(){return _e5(0,_Aa,_Ad);});},new T2(1,function(_Ae){return new F(function(){return _cz(0,_Ab,_Ae);});},_1)),_eu));}),_Af=__app3(E(_A8),toJSStr(B(unAppCStr("P",new T(function(){return B(_ce(B(_cz(0,_Ab,_1)),_A7));})))),toJSStr(B(unAppCStr("for choice with id ",new T(function(){return B(_cz(0,_Aa,_1));})))),toJSStr(new T2(1,_cx,_Ac)));return new F(function(){return _A6(_);});},_Ag=function(_Ah,_Ai,_){while(1){var _Aj=B((function(_Ak,_Al,_){var _Am=E(_Al);if(!_Am._){var _An=E(_Am.b);_Ah=function(_){var _Ao=B(_A9(_An.a,_An.b,_));return new F(function(){return _Ag(_Ak,_Am.e,_);});};_Ai=_Am.d;return __continue;}else{return new F(function(){return A1(_Ak,_);});}})(_Ah,_Ai,_));if(_Aj!=__continue){return _Aj;}}},_Ap=new T(function(){return B(unCStr("SIP "));}),_Aq=new T(function(){return B(unCStr("SIRC "));}),_Ar=new T(function(){return B(unCStr("SICC "));}),_As=function(_At,_Au,_Av){var _Aw=E(_Au);switch(_Aw._){case 0:var _Ax=function(_Ay){var _Az=new T(function(){var _AA=new T(function(){return B(_cz(11,_Aw.c,new T2(1,_cJ,new T(function(){return B(_cz(11,_Aw.d,_Ay));}))));});return B(_cz(11,_Aw.b,new T2(1,_cJ,_AA)));});return new F(function(){return _cE(11,_Aw.a,new T2(1,_cJ,_Az));});};if(_At<11){return new F(function(){return _ce(_Ar,new T(function(){return B(_Ax(_Av));},1));});}else{var _AB=new T(function(){return B(_ce(_Ar,new T(function(){return B(_Ax(new T2(1,_cw,_Av)));},1)));});return new T2(1,_cx,_AB);}break;case 1:var _AC=function(_AD){var _AE=new T(function(){var _AF=new T(function(){return B(_cz(11,_Aw.b,new T2(1,_cJ,new T(function(){return B(_cz(11,_Aw.c,_AD));}))));});return B(_cE(11,_Aw.a,new T2(1,_cJ,_AF)));},1);return new F(function(){return _ce(_Aq,_AE);});};if(_At<11){return new F(function(){return _AC(_Av);});}else{return new T2(1,_cx,new T(function(){return B(_AC(new T2(1,_cw,_Av)));}));}break;default:var _AG=function(_AH){var _AI=new T(function(){var _AJ=new T(function(){return B(_cz(11,_Aw.b,new T2(1,_cJ,new T(function(){return B(_cz(11,_Aw.c,_AH));}))));});return B(_dg(11,_Aw.a,new T2(1,_cJ,_AJ)));},1);return new F(function(){return _ce(_Ap,_AI);});};if(_At<11){return new F(function(){return _AG(_Av);});}else{return new T2(1,_cx,new T(function(){return B(_AG(new T2(1,_cw,_Av)));}));}}},_AK=new T(function(){return B(unCStr(" ADA"));}),_AL=new T(function(){return eval("(function (x, y) {var r = document.getElementById(\'actions\').insertRow(); var c1 = r.insertCell(); c1.appendChild(document.createTextNode(x)); var c2 = r.insertCell(); var btn = document.createElement(\'button\'); c2.appendChild(btn); btn.appendChild(document.createTextNode(\'Add action\')); btn.style.setProperty(\'width\', \'100%\'); btn.onclick = function () {Haste.addAction(y);};})");}),_AM=function(_AN,_AO,_AP,_){var _AQ=new T(function(){var _AR=new T(function(){var _AS=new T(function(){var _AT=new T(function(){return B(unAppCStr(") of ",new T(function(){return B(_ce(B(_cz(0,_AP,_1)),_AK));})));},1);return B(_ce(B(_cz(0,_AN,_1)),_AT));});return B(unAppCStr(": Claim payment (with id: ",_AS));},1);return B(_ce(B(_cz(0,_AO,_1)),_AR));}),_AU=__app2(E(_AL),toJSStr(B(unAppCStr("P",_AQ))),toJSStr(B(_As(0,new T3(2,_AN,_AO,_AP),_1))));return new F(function(){return _A6(_);});},_AV=function(_AW,_AX,_){while(1){var _AY=B((function(_AZ,_B0,_){var _B1=E(_B0);if(!_B1._){var _B2=E(_B1.b);_AW=function(_){var _B3=B(_AM(_B2.a,_B2.b,_B1.c,_));return new F(function(){return _AV(_AZ,_B1.e,_);});};_AX=_B1.d;return __continue;}else{return new F(function(){return A1(_AZ,_);});}})(_AW,_AX,_));if(_AY!=__continue){return _AY;}}},_B4=new T(function(){return B(unCStr(")"));}),_B5=function(_B6,_B7,_B8,_){var _B9=new T(function(){var _Ba=new T(function(){var _Bb=new T(function(){var _Bc=new T(function(){return B(unAppCStr(" ADA from commit (with id: ",new T(function(){return B(_ce(B(_cz(0,_B6,_1)),_B4));})));},1);return B(_ce(B(_cz(0,_B8,_1)),_Bc));});return B(unAppCStr(": Redeem ",_Bb));},1);return B(_ce(B(_cz(0,_B7,_1)),_Ba));}),_Bd=__app2(E(_AL),toJSStr(B(unAppCStr("P",_B9))),toJSStr(B(_As(0,new T3(1,_B6,_B7,_B8),_1))));return new F(function(){return _A6(_);});},_Be=function(_Bf,_Bg,_){while(1){var _Bh=B((function(_Bi,_Bj,_){var _Bk=E(_Bj);if(!_Bk._){var _Bl=E(_Bk.b);_Bf=function(_){var _Bm=B(_B5(_Bl.a,_Bl.b,_Bl.c,_));return new F(function(){return _Be(_Bi,_Bk.d,_);});};_Bg=_Bk.c;return __continue;}else{return new F(function(){return A1(_Bi,_);});}})(_Bf,_Bg,_));if(_Bh!=__continue){return _Bh;}}},_Bn=function(_){return _bT;},_Bo=function(_Bp,_Bq,_Br,_Bs,_){var _Bt=new T(function(){var _Bu=new T(function(){var _Bv=new T(function(){var _Bw=new T(function(){var _Bx=new T(function(){var _By=new T(function(){return B(unAppCStr(" ADA expiring on: ",new T(function(){return B(_cz(0,_Bs,_1));})));},1);return B(_ce(B(_cz(0,_Br,_1)),_By));});return B(unAppCStr(") of ",_Bx));},1);return B(_ce(B(_cz(0,_Bp,_1)),_Bw));});return B(unAppCStr(": Make commit (with id: ",_Bv));},1);return B(_ce(B(_cz(0,_Bq,_1)),_Bu));}),_Bz=__app2(E(_AL),toJSStr(B(unAppCStr("P",_Bt))),toJSStr(B(_As(0,new T4(0,_Bp,_Bq,_Br,_Bs),_1))));return new F(function(){return _A6(_);});},_BA=function(_BB,_BC,_){while(1){var _BD=B((function(_BE,_BF,_){var _BG=E(_BF);if(!_BG._){var _BH=E(_BG.b);_BB=function(_){var _BI=B(_Bo(_BH.a,_BH.b,_BH.c,_BH.d,_));return new F(function(){return _BA(_BE,_BG.d,_);});};_BC=_BG.c;return __continue;}else{return new F(function(){return A1(_BE,_);});}})(_BB,_BC,_));if(_BD!=__continue){return _BD;}}},_BJ=function(_BK,_BL,_BM,_BN,_){var _BO=B(_BA(_Bn,_BK,_)),_BP=B(_Be(_Bn,_BL,_)),_BQ=B(_AV(_Bn,_BM,_));return new F(function(){return _Ag(_Bn,_BN,_);});},_BR=function(_BS,_BT){while(1){var _BU=E(_BS),_BV=E(_BT);if(!_BV._){switch(B(_2(_BU,_BV.b))){case 0:_BS=_BU;_BT=_BV.d;continue;case 1:return new T1(1,_BV.c);default:_BS=_BU;_BT=_BV.e;continue;}}else{return __Z;}}},_BW=function(_BX,_BY){while(1){var _BZ=E(_BX),_C0=E(_BY);if(!_C0._){switch(B(_2(_BZ,_C0.b))){case 0:_BX=_BZ;_BY=_C0.d;continue;case 1:return true;default:_BX=_BZ;_BY=_C0.e;continue;}}else{return false;}}},_C1=function(_C2,_C3){var _C4=E(_C2);if(!_C4._){var _C5=_C4.a,_C6=E(_C3);return (_C6._==0)?_C5==_C6.a:(I_compareInt(_C6.a,_C5)==0)?true:false;}else{var _C7=_C4.a,_C8=E(_C3);return (_C8._==0)?(I_compareInt(_C7,_C8.a)==0)?true:false:(I_compare(_C7,_C8.a)==0)?true:false;}},_C9=function(_Ca,_Cb){var _Cc=E(_Ca),_Cd=E(_Cb);return (!B(_C1(_Cc.a,_Cd.a)))?true:(!B(_C1(_Cc.b,_Cd.b)))?true:(!B(_C1(_Cc.c,_Cd.c)))?true:(!B(_C1(_Cc.d,_Cd.d)))?true:false;},_Ce=function(_Cf,_Cg,_Ch,_Ci,_Cj,_Ck,_Cl,_Cm){if(!B(_C1(_Cf,_Cj))){return false;}else{if(!B(_C1(_Cg,_Ck))){return false;}else{if(!B(_C1(_Ch,_Cl))){return false;}else{return new F(function(){return _C1(_Ci,_Cm);});}}}},_Cn=function(_Co,_Cp){var _Cq=E(_Co),_Cr=E(_Cp);return new F(function(){return _Ce(_Cq.a,_Cq.b,_Cq.c,_Cq.d,_Cr.a,_Cr.b,_Cr.c,_Cr.d);});},_Cs=new T2(0,_Cn,_C9),_Ct=function(_Cu,_Cv,_Cw,_Cx,_Cy,_Cz,_CA,_CB){switch(B(_2(_Cu,_Cy))){case 0:return true;case 1:switch(B(_2(_Cv,_Cz))){case 0:return true;case 1:switch(B(_2(_Cw,_CA))){case 0:return true;case 1:return new F(function(){return _co(_Cx,_CB);});break;default:return false;}break;default:return false;}break;default:return false;}},_CC=function(_CD,_CE){var _CF=E(_CD),_CG=E(_CE);return new F(function(){return _Ct(_CF.a,_CF.b,_CF.c,_CF.d,_CG.a,_CG.b,_CG.c,_CG.d);});},_CH=function(_CI,_CJ,_CK,_CL,_CM,_CN,_CO,_CP){switch(B(_2(_CI,_CM))){case 0:return true;case 1:switch(B(_2(_CJ,_CN))){case 0:return true;case 1:switch(B(_2(_CK,_CO))){case 0:return true;case 1:return new F(function(){return _lm(_CL,_CP);});break;default:return false;}break;default:return false;}break;default:return false;}},_CQ=function(_CR,_CS){var _CT=E(_CR),_CU=E(_CS);return new F(function(){return _CH(_CT.a,_CT.b,_CT.c,_CT.d,_CU.a,_CU.b,_CU.c,_CU.d);});},_CV=function(_CW,_CX){var _CY=E(_CW);if(!_CY._){var _CZ=_CY.a,_D0=E(_CX);return (_D0._==0)?_CZ>_D0.a:I_compareInt(_D0.a,_CZ)<0;}else{var _D1=_CY.a,_D2=E(_CX);return (_D2._==0)?I_compareInt(_D1,_D2.a)>0:I_compare(_D1,_D2.a)>0;}},_D3=function(_D4,_D5,_D6,_D7,_D8,_D9,_Da,_Db){switch(B(_2(_D4,_D8))){case 0:return false;case 1:switch(B(_2(_D5,_D9))){case 0:return false;case 1:switch(B(_2(_D6,_Da))){case 0:return false;case 1:return new F(function(){return _CV(_D7,_Db);});break;default:return true;}break;default:return true;}break;default:return true;}},_Dc=function(_Dd,_De){var _Df=E(_Dd),_Dg=E(_De);return new F(function(){return _D3(_Df.a,_Df.b,_Df.c,_Df.d,_Dg.a,_Dg.b,_Dg.c,_Dg.d);});},_Dh=function(_Di,_Dj,_Dk,_Dl,_Dm,_Dn,_Do,_Dp){switch(B(_2(_Di,_Dm))){case 0:return false;case 1:switch(B(_2(_Dj,_Dn))){case 0:return false;case 1:switch(B(_2(_Dk,_Do))){case 0:return false;case 1:return new F(function(){return _e(_Dl,_Dp);});break;default:return true;}break;default:return true;}break;default:return true;}},_Dq=function(_Dr,_Ds){var _Dt=E(_Dr),_Du=E(_Ds);return new F(function(){return _Dh(_Dt.a,_Dt.b,_Dt.c,_Dt.d,_Du.a,_Du.b,_Du.c,_Du.d);});},_Dv=function(_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD){switch(B(_2(_Dw,_DA))){case 0:return 0;case 1:switch(B(_2(_Dx,_DB))){case 0:return 0;case 1:switch(B(_2(_Dy,_DC))){case 0:return 0;case 1:return new F(function(){return _2(_Dz,_DD);});break;default:return 2;}break;default:return 2;}break;default:return 2;}},_DE=function(_DF,_DG){var _DH=E(_DF),_DI=E(_DG);return new F(function(){return _Dv(_DH.a,_DH.b,_DH.c,_DH.d,_DI.a,_DI.b,_DI.c,_DI.d);});},_DJ=function(_DK,_DL){var _DM=E(_DK),_DN=E(_DL);switch(B(_2(_DM.a,_DN.a))){case 0:return E(_DN);case 1:switch(B(_2(_DM.b,_DN.b))){case 0:return E(_DN);case 1:switch(B(_2(_DM.c,_DN.c))){case 0:return E(_DN);case 1:return (!B(_lm(_DM.d,_DN.d)))?E(_DM):E(_DN);default:return E(_DM);}break;default:return E(_DM);}break;default:return E(_DM);}},_DO=function(_DP,_DQ){var _DR=E(_DP),_DS=E(_DQ);switch(B(_2(_DR.a,_DS.a))){case 0:return E(_DR);case 1:switch(B(_2(_DR.b,_DS.b))){case 0:return E(_DR);case 1:switch(B(_2(_DR.c,_DS.c))){case 0:return E(_DR);case 1:return (!B(_lm(_DR.d,_DS.d)))?E(_DS):E(_DR);default:return E(_DS);}break;default:return E(_DS);}break;default:return E(_DS);}},_DT={_:0,a:_Cs,b:_DE,c:_CC,d:_CQ,e:_Dc,f:_Dq,g:_DJ,h:_DO},_DU=function(_DV,_DW,_DX,_DY){if(!B(_C1(_DV,_DX))){return false;}else{return new F(function(){return _C1(_DW,_DY);});}},_DZ=function(_E0,_E1){var _E2=E(_E0),_E3=E(_E1);return new F(function(){return _DU(_E2.a,_E2.b,_E3.a,_E3.b);});},_E4=function(_E5,_E6,_E7,_E8){return (!B(_C1(_E5,_E7)))?true:(!B(_C1(_E6,_E8)))?true:false;},_E9=function(_Ea,_Eb){var _Ec=E(_Ea),_Ed=E(_Eb);return new F(function(){return _E4(_Ec.a,_Ec.b,_Ed.a,_Ed.b);});},_Ee=new T2(0,_DZ,_E9),_Ef=function(_Eg,_Eh,_Ei,_Ej){switch(B(_2(_Eg,_Ei))){case 0:return 0;case 1:return new F(function(){return _2(_Eh,_Ej);});break;default:return 2;}},_Ek=function(_El,_Em){var _En=E(_El),_Eo=E(_Em);return new F(function(){return _Ef(_En.a,_En.b,_Eo.a,_Eo.b);});},_Ep=function(_Eq,_Er,_Es,_Et){switch(B(_2(_Eq,_Es))){case 0:return true;case 1:return new F(function(){return _co(_Er,_Et);});break;default:return false;}},_Eu=function(_Ev,_Ew){var _Ex=E(_Ev),_Ey=E(_Ew);return new F(function(){return _Ep(_Ex.a,_Ex.b,_Ey.a,_Ey.b);});},_Ez=function(_EA,_EB,_EC,_ED){switch(B(_2(_EA,_EC))){case 0:return true;case 1:return new F(function(){return _lm(_EB,_ED);});break;default:return false;}},_EE=function(_EF,_EG){var _EH=E(_EF),_EI=E(_EG);return new F(function(){return _Ez(_EH.a,_EH.b,_EI.a,_EI.b);});},_EJ=function(_EK,_EL,_EM,_EN){switch(B(_2(_EK,_EM))){case 0:return false;case 1:return new F(function(){return _CV(_EL,_EN);});break;default:return true;}},_EO=function(_EP,_EQ){var _ER=E(_EP),_ES=E(_EQ);return new F(function(){return _EJ(_ER.a,_ER.b,_ES.a,_ES.b);});},_ET=function(_EU,_EV,_EW,_EX){switch(B(_2(_EU,_EW))){case 0:return false;case 1:return new F(function(){return _e(_EV,_EX);});break;default:return true;}},_EY=function(_EZ,_F0){var _F1=E(_EZ),_F2=E(_F0);return new F(function(){return _ET(_F1.a,_F1.b,_F2.a,_F2.b);});},_F3=function(_F4,_F5){var _F6=E(_F4),_F7=E(_F5);switch(B(_2(_F6.a,_F7.a))){case 0:return E(_F7);case 1:return (!B(_lm(_F6.b,_F7.b)))?E(_F6):E(_F7);default:return E(_F6);}},_F8=function(_F9,_Fa){var _Fb=E(_F9),_Fc=E(_Fa);switch(B(_2(_Fb.a,_Fc.a))){case 0:return E(_Fb);case 1:return (!B(_lm(_Fb.b,_Fc.b)))?E(_Fc):E(_Fb);default:return E(_Fc);}},_Fd={_:0,a:_Ee,b:_Ek,c:_Eu,d:_EE,e:_EO,f:_EY,g:_F3,h:_F8},_Fe=function(_Ff,_Fg,_Fh,_Fi){if(!B(_C1(_Ff,_Fh))){return false;}else{return new F(function(){return _C1(_Fg,_Fi);});}},_Fj=function(_Fk,_Fl){var _Fm=E(_Fk),_Fn=E(_Fl);return new F(function(){return _Fe(_Fm.a,_Fm.b,_Fn.a,_Fn.b);});},_Fo=function(_Fp,_Fq,_Fr,_Fs){return (!B(_C1(_Fp,_Fr)))?true:(!B(_C1(_Fq,_Fs)))?true:false;},_Ft=function(_Fu,_Fv){var _Fw=E(_Fu),_Fx=E(_Fv);return new F(function(){return _Fo(_Fw.a,_Fw.b,_Fx.a,_Fx.b);});},_Fy=new T2(0,_Fj,_Ft),_Fz=function(_FA,_FB,_FC,_FD){switch(B(_2(_FA,_FC))){case 0:return 0;case 1:return new F(function(){return _2(_FB,_FD);});break;default:return 2;}},_FE=function(_FF,_FG){var _FH=E(_FF),_FI=E(_FG);return new F(function(){return _Fz(_FH.a,_FH.b,_FI.a,_FI.b);});},_FJ=function(_FK,_FL,_FM,_FN){switch(B(_2(_FK,_FM))){case 0:return true;case 1:return new F(function(){return _co(_FL,_FN);});break;default:return false;}},_FO=function(_FP,_FQ){var _FR=E(_FP),_FS=E(_FQ);return new F(function(){return _FJ(_FR.a,_FR.b,_FS.a,_FS.b);});},_FT=function(_FU,_FV,_FW,_FX){switch(B(_2(_FU,_FW))){case 0:return true;case 1:return new F(function(){return _lm(_FV,_FX);});break;default:return false;}},_FY=function(_FZ,_G0){var _G1=E(_FZ),_G2=E(_G0);return new F(function(){return _FT(_G1.a,_G1.b,_G2.a,_G2.b);});},_G3=function(_G4,_G5,_G6,_G7){switch(B(_2(_G4,_G6))){case 0:return false;case 1:return new F(function(){return _CV(_G5,_G7);});break;default:return true;}},_G8=function(_G9,_Ga){var _Gb=E(_G9),_Gc=E(_Ga);return new F(function(){return _G3(_Gb.a,_Gb.b,_Gc.a,_Gc.b);});},_Gd=function(_Ge,_Gf,_Gg,_Gh){switch(B(_2(_Ge,_Gg))){case 0:return false;case 1:return new F(function(){return _e(_Gf,_Gh);});break;default:return true;}},_Gi=function(_Gj,_Gk){var _Gl=E(_Gj),_Gm=E(_Gk);return new F(function(){return _Gd(_Gl.a,_Gl.b,_Gm.a,_Gm.b);});},_Gn=function(_Go,_Gp){var _Gq=E(_Go),_Gr=E(_Gp);switch(B(_2(_Gq.a,_Gr.a))){case 0:return E(_Gr);case 1:return (!B(_lm(_Gq.b,_Gr.b)))?E(_Gq):E(_Gr);default:return E(_Gq);}},_Gs=function(_Gt,_Gu){var _Gv=E(_Gt),_Gw=E(_Gu);switch(B(_2(_Gv.a,_Gw.a))){case 0:return E(_Gv);case 1:return (!B(_lm(_Gv.b,_Gw.b)))?E(_Gw):E(_Gv);default:return E(_Gw);}},_Gx={_:0,a:_Fy,b:_FE,c:_FO,d:_FY,e:_G8,f:_Gi,g:_Gn,h:_Gs},_Gy=function(_Gz,_GA){var _GB=E(_Gz),_GC=E(_GA);return (!B(_C1(_GB.a,_GC.a)))?true:(!B(_C1(_GB.b,_GC.b)))?true:(!B(_C1(_GB.c,_GC.c)))?true:false;},_GD=function(_GE,_GF,_GG,_GH,_GI,_GJ){if(!B(_C1(_GE,_GH))){return false;}else{if(!B(_C1(_GF,_GI))){return false;}else{return new F(function(){return _C1(_GG,_GJ);});}}},_GK=function(_GL,_GM){var _GN=E(_GL),_GO=E(_GM);return new F(function(){return _GD(_GN.a,_GN.b,_GN.c,_GO.a,_GO.b,_GO.c);});},_GP=new T2(0,_GK,_Gy),_GQ=function(_GR,_GS,_GT,_GU,_GV,_GW){switch(B(_2(_GR,_GU))){case 0:return true;case 1:switch(B(_2(_GS,_GV))){case 0:return true;case 1:return new F(function(){return _co(_GT,_GW);});break;default:return false;}break;default:return false;}},_GX=function(_GY,_GZ){var _H0=E(_GY),_H1=E(_GZ);return new F(function(){return _GQ(_H0.a,_H0.b,_H0.c,_H1.a,_H1.b,_H1.c);});},_H2=function(_H3,_H4,_H5,_H6,_H7,_H8){switch(B(_2(_H3,_H6))){case 0:return true;case 1:switch(B(_2(_H4,_H7))){case 0:return true;case 1:return new F(function(){return _lm(_H5,_H8);});break;default:return false;}break;default:return false;}},_H9=function(_Ha,_Hb){var _Hc=E(_Ha),_Hd=E(_Hb);return new F(function(){return _H2(_Hc.a,_Hc.b,_Hc.c,_Hd.a,_Hd.b,_Hd.c);});},_He=function(_Hf,_Hg,_Hh,_Hi,_Hj,_Hk){switch(B(_2(_Hf,_Hi))){case 0:return false;case 1:switch(B(_2(_Hg,_Hj))){case 0:return false;case 1:return new F(function(){return _CV(_Hh,_Hk);});break;default:return true;}break;default:return true;}},_Hl=function(_Hm,_Hn){var _Ho=E(_Hm),_Hp=E(_Hn);return new F(function(){return _He(_Ho.a,_Ho.b,_Ho.c,_Hp.a,_Hp.b,_Hp.c);});},_Hq=function(_Hr,_Hs,_Ht,_Hu,_Hv,_Hw){switch(B(_2(_Hr,_Hu))){case 0:return false;case 1:switch(B(_2(_Hs,_Hv))){case 0:return false;case 1:return new F(function(){return _e(_Ht,_Hw);});break;default:return true;}break;default:return true;}},_Hx=function(_Hy,_Hz){var _HA=E(_Hy),_HB=E(_Hz);return new F(function(){return _Hq(_HA.a,_HA.b,_HA.c,_HB.a,_HB.b,_HB.c);});},_HC=function(_HD,_HE,_HF,_HG,_HH,_HI){switch(B(_2(_HD,_HG))){case 0:return 0;case 1:switch(B(_2(_HE,_HH))){case 0:return 0;case 1:return new F(function(){return _2(_HF,_HI);});break;default:return 2;}break;default:return 2;}},_HJ=function(_HK,_HL){var _HM=E(_HK),_HN=E(_HL);return new F(function(){return _HC(_HM.a,_HM.b,_HM.c,_HN.a,_HN.b,_HN.c);});},_HO=function(_HP,_HQ){var _HR=E(_HP),_HS=E(_HQ);switch(B(_2(_HR.a,_HS.a))){case 0:return E(_HS);case 1:switch(B(_2(_HR.b,_HS.b))){case 0:return E(_HS);case 1:return (!B(_lm(_HR.c,_HS.c)))?E(_HR):E(_HS);default:return E(_HR);}break;default:return E(_HR);}},_HT=function(_HU,_HV){var _HW=E(_HU),_HX=E(_HV);switch(B(_2(_HW.a,_HX.a))){case 0:return E(_HW);case 1:switch(B(_2(_HW.b,_HX.b))){case 0:return E(_HW);case 1:return (!B(_lm(_HW.c,_HX.c)))?E(_HX):E(_HW);default:return E(_HX);}break;default:return E(_HX);}},_HY={_:0,a:_GP,b:_HJ,c:_GX,d:_H9,e:_Hl,f:_Hx,g:_HO,h:_HT},_HZ=__Z,_I0=__Z,_I1=function(_I2){return E(E(_I2).b);},_I3=function(_I4,_I5,_I6){var _I7=E(_I5);if(!_I7._){return E(_I6);}else{var _I8=function(_I9,_Ia){while(1){var _Ib=E(_Ia);if(!_Ib._){var _Ic=_Ib.b,_Id=_Ib.e;switch(B(A3(_I1,_I4,_I9,_Ic))){case 0:return new F(function(){return _2B(_Ic,_Ib.c,B(_I8(_I9,_Ib.d)),_Id);});break;case 1:return E(_Id);default:_Ia=_Id;continue;}}else{return new T0(1);}}};return new F(function(){return _I8(_I7.a,_I6);});}},_Ie=function(_If,_Ig,_Ih){var _Ii=E(_Ig);if(!_Ii._){return E(_Ih);}else{var _Ij=function(_Ik,_Il){while(1){var _Im=E(_Il);if(!_Im._){var _In=_Im.b,_Io=_Im.d;switch(B(A3(_I1,_If,_In,_Ik))){case 0:return new F(function(){return _2B(_In,_Im.c,_Io,B(_Ij(_Ik,_Im.e)));});break;case 1:return E(_Io);default:_Il=_Io;continue;}}else{return new T0(1);}}};return new F(function(){return _Ij(_Ii.a,_Ih);});}},_Ip=function(_Iq,_Ir,_Is,_It){var _Iu=E(_Ir),_Iv=E(_It);if(!_Iv._){var _Iw=_Iv.b,_Ix=_Iv.c,_Iy=_Iv.d,_Iz=_Iv.e;switch(B(A3(_I1,_Iq,_Iu,_Iw))){case 0:return new F(function(){return _1h(_Iw,_Ix,B(_Ip(_Iq,_Iu,_Is,_Iy)),_Iz);});break;case 1:return E(_Iv);default:return new F(function(){return _q(_Iw,_Ix,_Iy,B(_Ip(_Iq,_Iu,_Is,_Iz)));});}}else{return new T5(0,1,E(_Iu),_Is,E(_0),E(_0));}},_IA=function(_IB,_IC,_ID,_IE){return new F(function(){return _Ip(_IB,_IC,_ID,_IE);});},_IF=function(_IG){return E(E(_IG).d);},_IH=function(_II){return E(E(_II).f);},_IJ=function(_IK,_IL,_IM,_IN){var _IO=E(_IL);if(!_IO._){var _IP=E(_IM);if(!_IP._){return E(_IN);}else{var _IQ=function(_IR,_IS){while(1){var _IT=E(_IS);if(!_IT._){if(!B(A3(_IH,_IK,_IT.b,_IR))){return E(_IT);}else{_IS=_IT.d;continue;}}else{return new T0(1);}}};return new F(function(){return _IQ(_IP.a,_IN);});}}else{var _IU=_IO.a,_IV=E(_IM);if(!_IV._){var _IW=function(_IX,_IY){while(1){var _IZ=E(_IY);if(!_IZ._){if(!B(A3(_IF,_IK,_IZ.b,_IX))){return E(_IZ);}else{_IY=_IZ.e;continue;}}else{return new T0(1);}}};return new F(function(){return _IW(_IU,_IN);});}else{var _J0=function(_J1,_J2,_J3){while(1){var _J4=E(_J3);if(!_J4._){var _J5=_J4.b;if(!B(A3(_IF,_IK,_J5,_J1))){if(!B(A3(_IH,_IK,_J5,_J2))){return E(_J4);}else{_J3=_J4.d;continue;}}else{_J3=_J4.e;continue;}}else{return new T0(1);}}};return new F(function(){return _J0(_IU,_IV.a,_IN);});}}},_J6=function(_J7,_J8,_J9,_Ja,_Jb){var _Jc=E(_Jb);if(!_Jc._){var _Jd=_Jc.b,_Je=_Jc.c,_Jf=_Jc.d,_Jg=_Jc.e,_Jh=E(_Ja);if(!_Jh._){var _Ji=_Jh.b,_Jj=function(_Jk){var _Jl=new T1(1,E(_Ji));return new F(function(){return _2B(_Ji,_Jh.c,B(_J6(_J7,_J8,_Jl,_Jh.d,B(_IJ(_J7,_J8,_Jl,_Jc)))),B(_J6(_J7,_Jl,_J9,_Jh.e,B(_IJ(_J7,_Jl,_J9,_Jc)))));});};if(!E(_Jf)._){return new F(function(){return _Jj(_);});}else{if(!E(_Jg)._){return new F(function(){return _Jj(_);});}else{return new F(function(){return _IA(_J7,_Jd,_Je,_Jh);});}}}else{return new F(function(){return _2B(_Jd,_Je,B(_I3(_J7,_J8,_Jf)),B(_Ie(_J7,_J9,_Jg)));});}}else{return E(_Ja);}},_Jm=function(_Jn,_Jo,_Jp,_Jq,_Jr,_Js,_Jt,_Ju,_Jv,_Jw,_Jx,_Jy,_Jz){var _JA=function(_JB){var _JC=new T1(1,E(_Jr));return new F(function(){return _2B(_Jr,_Js,B(_J6(_Jn,_Jo,_JC,_Jt,B(_IJ(_Jn,_Jo,_JC,new T5(0,_Jv,E(_Jw),_Jx,E(_Jy),E(_Jz)))))),B(_J6(_Jn,_JC,_Jp,_Ju,B(_IJ(_Jn,_JC,_Jp,new T5(0,_Jv,E(_Jw),_Jx,E(_Jy),E(_Jz)))))));});};if(!E(_Jy)._){return new F(function(){return _JA(_);});}else{if(!E(_Jz)._){return new F(function(){return _JA(_);});}else{return new F(function(){return _IA(_Jn,_Jw,_Jx,new T5(0,_Jq,E(_Jr),_Js,E(_Jt),E(_Ju)));});}}},_JD=function(_JE,_JF,_JG){var _JH=E(_JF);if(!_JH._){return E(_JG);}else{var _JI=function(_JJ,_JK){while(1){var _JL=E(_JK);if(!_JL._){var _JM=_JL.b,_JN=_JL.d;switch(B(A3(_I1,_JE,_JJ,_JM))){case 0:return new F(function(){return _6C(_JM,B(_JI(_JJ,_JL.c)),_JN);});break;case 1:return E(_JN);default:_JK=_JN;continue;}}else{return new T0(1);}}};return new F(function(){return _JI(_JH.a,_JG);});}},_JO=function(_JP,_JQ,_JR){var _JS=E(_JQ);if(!_JS._){return E(_JR);}else{var _JT=function(_JU,_JV){while(1){var _JW=E(_JV);if(!_JW._){var _JX=_JW.b,_JY=_JW.c;switch(B(A3(_I1,_JP,_JX,_JU))){case 0:return new F(function(){return _6C(_JX,_JY,B(_JT(_JU,_JW.d)));});break;case 1:return E(_JY);default:_JV=_JY;continue;}}else{return new T0(1);}}};return new F(function(){return _JT(_JS.a,_JR);});}},_JZ=function(_K0,_K1,_K2){var _K3=E(_K1),_K4=E(_K2);if(!_K4._){var _K5=_K4.b,_K6=_K4.c,_K7=_K4.d;switch(B(A3(_I1,_K0,_K3,_K5))){case 0:return new F(function(){return _5q(_K5,B(_JZ(_K0,_K3,_K6)),_K7);});break;case 1:return E(_K4);default:return new F(function(){return _4G(_K5,_K6,B(_JZ(_K0,_K3,_K7)));});}}else{return new T4(0,1,E(_K3),E(_4B),E(_4B));}},_K8=function(_K9,_Ka,_Kb){return new F(function(){return _JZ(_K9,_Ka,_Kb);});},_Kc=function(_Kd,_Ke,_Kf,_Kg){var _Kh=E(_Ke);if(!_Kh._){var _Ki=E(_Kf);if(!_Ki._){return E(_Kg);}else{var _Kj=function(_Kk,_Kl){while(1){var _Km=E(_Kl);if(!_Km._){if(!B(A3(_IH,_Kd,_Km.b,_Kk))){return E(_Km);}else{_Kl=_Km.c;continue;}}else{return new T0(1);}}};return new F(function(){return _Kj(_Ki.a,_Kg);});}}else{var _Kn=_Kh.a,_Ko=E(_Kf);if(!_Ko._){var _Kp=function(_Kq,_Kr){while(1){var _Ks=E(_Kr);if(!_Ks._){if(!B(A3(_IF,_Kd,_Ks.b,_Kq))){return E(_Ks);}else{_Kr=_Ks.d;continue;}}else{return new T0(1);}}};return new F(function(){return _Kp(_Kn,_Kg);});}else{var _Kt=function(_Ku,_Kv,_Kw){while(1){var _Kx=E(_Kw);if(!_Kx._){var _Ky=_Kx.b;if(!B(A3(_IF,_Kd,_Ky,_Ku))){if(!B(A3(_IH,_Kd,_Ky,_Kv))){return E(_Kx);}else{_Kw=_Kx.c;continue;}}else{_Kw=_Kx.d;continue;}}else{return new T0(1);}}};return new F(function(){return _Kt(_Kn,_Ko.a,_Kg);});}}},_Kz=function(_KA,_KB,_KC,_KD,_KE){var _KF=E(_KE);if(!_KF._){var _KG=_KF.b,_KH=_KF.c,_KI=_KF.d,_KJ=E(_KD);if(!_KJ._){var _KK=_KJ.b,_KL=function(_KM){var _KN=new T1(1,E(_KK));return new F(function(){return _6C(_KK,B(_Kz(_KA,_KB,_KN,_KJ.c,B(_Kc(_KA,_KB,_KN,_KF)))),B(_Kz(_KA,_KN,_KC,_KJ.d,B(_Kc(_KA,_KN,_KC,_KF)))));});};if(!E(_KH)._){return new F(function(){return _KL(_);});}else{if(!E(_KI)._){return new F(function(){return _KL(_);});}else{return new F(function(){return _K8(_KA,_KG,_KJ);});}}}else{return new F(function(){return _6C(_KG,B(_JD(_KA,_KB,_KH)),B(_JO(_KA,_KC,_KI)));});}}else{return E(_KD);}},_KO=function(_KP,_KQ,_KR,_KS,_KT,_KU,_KV,_KW,_KX,_KY,_KZ){var _L0=function(_L1){var _L2=new T1(1,E(_KT));return new F(function(){return _6C(_KT,B(_Kz(_KP,_KQ,_L2,_KU,B(_Kc(_KP,_KQ,_L2,new T4(0,_KW,E(_KX),E(_KY),E(_KZ)))))),B(_Kz(_KP,_L2,_KR,_KV,B(_Kc(_KP,_L2,_KR,new T4(0,_KW,E(_KX),E(_KY),E(_KZ)))))));});};if(!E(_KY)._){return new F(function(){return _L0(_);});}else{if(!E(_KZ)._){return new F(function(){return _L0(_);});}else{return new F(function(){return _K8(_KP,_KX,new T4(0,_KS,E(_KT),E(_KU),E(_KV)));});}}},_L3=function(_L4,_L5,_L6,_L7,_L8,_L9,_La,_Lb){return new T4(0,new T(function(){var _Lc=E(_L4);if(!_Lc._){var _Ld=E(_L8);if(!_Ld._){return B(_KO(_DT,_I0,_I0,_Lc.a,_Lc.b,_Lc.c,_Lc.d,_Ld.a,_Ld.b,_Ld.c,_Ld.d));}else{return E(_Lc);}}else{return E(_L8);}}),new T(function(){var _Le=E(_L5);if(!_Le._){var _Lf=E(_L9);if(!_Lf._){return B(_KO(_HY,_I0,_I0,_Le.a,_Le.b,_Le.c,_Le.d,_Lf.a,_Lf.b,_Lf.c,_Lf.d));}else{return E(_Le);}}else{return E(_L9);}}),new T(function(){var _Lg=E(_L6);if(!_Lg._){var _Lh=E(_La);if(!_Lh._){return B(_Jm(_Gx,_HZ,_HZ,_Lg.a,_Lg.b,_Lg.c,_Lg.d,_Lg.e,_Lh.a,_Lh.b,_Lh.c,_Lh.d,_Lh.e));}else{return E(_Lg);}}else{return E(_La);}}),new T(function(){var _Li=E(_L7);if(!_Li._){var _Lj=E(_Lb);if(!_Lj._){return B(_Jm(_Fd,_HZ,_HZ,_Li.a,_Li.b,_Li.c,_Li.d,_Li.e,_Lj.a,_Lj.b,_Lj.c,_Lj.d,_Lj.e));}else{return E(_Li);}}else{return E(_Lb);}}));},_Lk=function(_Ll,_Lm){while(1){var _Ln=E(_Ll),_Lo=E(_Lm);if(!_Lo._){switch(B(_2(_Ln,_Lo.b))){case 0:_Ll=_Ln;_Lm=_Lo.d;continue;case 1:return new T1(1,_Lo.c);default:_Ll=_Ln;_Lm=_Lo.e;continue;}}else{return __Z;}}},_Lp=function(_Lq,_Lr,_Ls){while(1){var _Lt=E(_Ls);if(!_Lt._){var _Lu=_Lt.d,_Lv=_Lt.e,_Lw=E(_Lt.b);switch(B(_2(_Lq,_Lw.a))){case 0:_Ls=_Lu;continue;case 1:switch(B(_2(_Lr,_Lw.b))){case 0:_Ls=_Lu;continue;case 1:return new T1(1,_Lt.c);default:_Ls=_Lv;continue;}break;default:_Ls=_Lv;continue;}}else{return __Z;}}},_Lx=function(_Ly){return new T1(0,0);},_Lz=new T(function(){return B(_Lx(_));}),_LA=function(_LB,_LC,_LD){while(1){var _LE=E(_LD);switch(_LE._){case 0:var _LF=B(_Lk(_LE.a,_LB));if(!_LF._){return E(_Lz);}else{var _LG=E(E(_LF.a).b);return (_LG._==0)?E(_LG.a):E(_Lz);}break;case 1:return new F(function(){return _ji(B(_LA(_LB,_LC,_LE.a)),B(_LA(_LB,_LC,_LE.b)));});break;case 2:return E(_LE.a);default:var _LH=B(_Lp(_LE.a,_LE.b,_LC));if(!_LH._){_LD=_LE.c;continue;}else{return E(_LH.a);}}}},_LI=function(_LJ,_LK){var _LL=E(_LJ);return new F(function(){return _LA(_LL.a,_LL.b,_LK);});},_LM=function(_LN,_LO){var _LP=E(_LN);switch(_LP._){case 1:var _LQ=_LP.a,_LR=E(_LO),_LS=_LR.a;return (!B(_BW(_LQ,_LS)))?new T4(0,new T4(0,1,E(new T4(0,_LQ,_LP.b,new T(function(){return B(_LA(_LS,_LR.b,_LP.c));}),_LP.e)),E(_4B),E(_4B)),_4B,_0,_0):new T4(0,_4B,_4B,_0,_0);case 2:var _LT=_LP.a,_LU=B(_BR(_LT,E(_LO).a));if(!_LU._){return new T4(0,_4B,_4B,_0,_0);}else{var _LV=E(_LU.a),_LW=E(_LV.b);return (_LW._==0)?new T4(0,_4B,new T4(0,1,E(new T3(0,_LT,_LV.a,_LW.a)),E(_4B),E(_4B)),_0,_0):new T4(0,_4B,_4B,_0,_0);}break;case 3:return new T4(0,_4B,_4B,new T5(0,1,E(new T2(0,_LP.a,_LP.c)),new T(function(){return B(_LI(_LO,_LP.d));}),E(_0),E(_0)),_0);case 4:var _LX=B(_LM(_LP.a,_LO)),_LY=B(_LM(_LP.b,_LO));return new F(function(){return _L3(_LX.a,_LX.b,_LX.c,_LX.d,_LY.a,_LY.b,_LY.c,_LY.d);});break;default:return new T4(0,_4B,_4B,_0,_0);}},_LZ=function(_M0,_M1){var _M2=new T(function(){var _M3=new T(function(){return E(E(_M0).b);}),_M4=function(_M5,_M6){while(1){var _M7=B((function(_M8,_M9){var _Ma=E(_M9);if(!_Ma._){var _Mb=_Ma.e,_Mc=new T(function(){var _Md=E(_Ma.c),_Me=E(_Md.b);if(!_Me._){if(!B(_lm(_Me.b,_M3))){return B(_M4(_M8,_Mb));}else{return new T2(1,new T3(0,_Ma.b,_Md.a,_Me.a),new T(function(){return B(_M4(_M8,_Mb));}));}}else{return B(_M4(_M8,_Mb));}},1);_M5=_Mc;_M6=_Ma.d;return __continue;}else{return E(_M8);}})(_M5,_M6));if(_M7!=__continue){return _M7;}}};return B(_8f(B(_M4(_1,_M1))));});return new T4(0,_4B,_M2,_0,_0);},_Mf=function(_Mg,_Mh,_Mi,_Mj,_Mk){while(1){var _Ml=E(_Mg);if(!_Ml._){return new T4(0,_Mh,_Mi,_Mj,_Mk);}else{var _Mm=E(_Ml.a),_Mn=B(_L3(_Mh,_Mi,_Mj,_Mk,_Mm.a,_Mm.b,_Mm.c,_Mm.d));_Mg=_Ml.b;_Mh=_Mn.a;_Mi=_Mn.b;_Mj=_Mn.c;_Mk=_Mn.d;continue;}}},_Mo=function(_Mp,_Mq,_Mr,_Ms,_Mt,_Mu){var _Mv=E(_Mp),_Mw=B(_L3(_Mr,_Ms,_Mt,_Mu,_Mv.a,_Mv.b,_Mv.c,_Mv.d));return new F(function(){return _Mf(_Mq,_Mw.a,_Mw.b,_Mw.c,_Mw.d);});},_Mx=new T1(0,0),_My=function(_Mz){var _MA=E(_Mz);switch(_MA._){case 1:var _MB=B(_My(_MA.a));return new F(function(){return _Mo(new T(function(){var _MC=B(_My(_MA.b));return new T4(0,_MC.a,_MC.b,_MC.c,_MC.d);}),_1,_MB.a,_MB.b,_MB.c,_MB.d);});break;case 3:var _MD=B(_My(_MA.c));return new F(function(){return _L3(_4B,_4B,_0,new T5(0,1,E(new T2(0,_MA.a,_MA.b)),_Mx,E(_0),E(_0)),_MD.a,_MD.b,_MD.c,_MD.d);});break;default:return new T4(0,_4B,_4B,_0,_0);}},_ME=function(_MF,_MG,_MH,_MI,_MJ){while(1){var _MK=E(_MF);if(!_MK._){return new T4(0,_MG,_MH,_MI,_MJ);}else{var _ML=E(_MK.a),_MM=B(_L3(_MG,_MH,_MI,_MJ,_ML.a,_ML.b,_ML.c,_ML.d));_MF=_MK.b;_MG=_MM.a;_MH=_MM.b;_MI=_MM.c;_MJ=_MM.d;continue;}}},_MN=function(_MO,_MP,_MQ,_MR,_MS){while(1){var _MT=E(_MO);if(!_MT._){return new T4(0,_MP,_MQ,_MR,_MS);}else{var _MU=E(_MT.a),_MV=B(_L3(_MP,_MQ,_MR,_MS,_MU.a,_MU.b,_MU.c,_MU.d));_MO=_MT.b;_MP=_MV.a;_MQ=_MV.b;_MR=_MV.c;_MS=_MV.d;continue;}}},_MW=function(_MX,_MY,_MZ,_N0,_N1){while(1){var _N2=E(_MX);if(!_N2._){return new T4(0,_MY,_MZ,_N0,_N1);}else{var _N3=E(_N2.a),_N4=B(_L3(_MY,_MZ,_N0,_N1,_N3.a,_N3.b,_N3.c,_N3.d));_MX=_N2.b;_MY=_N4.a;_MZ=_N4.b;_N0=_N4.c;_N1=_N4.d;continue;}}},_N5=function(_N6,_N7,_N8){while(1){var _N9=E(_N8);if(!_N9._){var _Na=_N9.d,_Nb=_N9.e,_Nc=E(_N9.b);switch(B(_2(_N6,_Nc.a))){case 0:_N8=_Na;continue;case 1:switch(B(_2(_N7,_Nc.b))){case 0:_N8=_Na;continue;case 1:return true;default:_N8=_Nb;continue;}break;default:_N8=_Nb;continue;}}else{return false;}}},_Nd=function(_Ne,_Nf){var _Ng=B(_My(_Nf));return new T4(0,_Ng.a,_Ng.b,_Ng.c,_Ng.d);},_Nh=function(_Ni,_Nj){var _Nk=B(_Nl(_Ni,_Nj));return new T4(0,_Nk.a,_Nk.b,_Nk.c,_Nk.d);},_Nl=function(_Nm,_Nn){while(1){var _No=B((function(_Np,_Nq){var _Nr=E(_Nq);switch(_Nr._){case 1:var _Ns=B(_Nl(_Np,_Nr.a));return new F(function(){return _MW(new T2(1,new T(function(){return B(_Nh(_Np,_Nr.b));}),_1),_Ns.a,_Ns.b,_Ns.c,_Ns.d);});break;case 2:var _Nt=B(_Nl(_Np,_Nr.a));return new F(function(){return _MN(new T2(1,new T(function(){return B(_Nh(_Np,_Nr.b));}),_1),_Nt.a,_Nt.b,_Nt.c,_Nt.d);});break;case 3:var _Nu=_Np;_Nm=_Nu;_Nn=_Nr.a;return __continue;case 4:var _Nv=_Nr.a,_Nw=_Nr.b;return (!B(_N5(_Nv,_Nw,E(_Np).b)))?new T4(0,_4B,_4B,_0,new T5(0,1,E(new T2(0,_Nv,_Nw)),_Mx,E(_0),E(_0))):new T4(0,_4B,_4B,_0,_0);case 5:var _Nx=_Nr.a,_Ny=_Nr.b;return (!B(_N5(_Nx,_Ny,E(_Np).b)))?new T4(0,_4B,_4B,_0,new T5(0,1,E(new T2(0,_Nx,_Ny)),_Mx,E(_0),E(_0))):new T4(0,_4B,_4B,_0,_0);case 6:var _Nz=B(_My(_Nr.a));return new F(function(){return _ME(new T2(1,new T(function(){return B(_Nd(_Np,_Nr.b));}),_1),_Nz.a,_Nz.b,_Nz.c,_Nz.d);});break;default:return new T4(0,_4B,_4B,_0,_0);}})(_Nm,_Nn));if(_No!=__continue){return _No;}}},_NA=function(_NB,_NC,_ND,_NE,_NF){while(1){var _NG=E(_NB);if(!_NG._){return new T4(0,_NC,_ND,_NE,_NF);}else{var _NH=E(_NG.a),_NI=B(_L3(_NC,_ND,_NE,_NF,_NH.a,_NH.b,_NH.c,_NH.d));_NB=_NG.b;_NC=_NI.a;_ND=_NI.b;_NE=_NI.c;_NF=_NI.d;continue;}}},_NJ=function(_NK,_NL){var _NM=B(_NN(_NK,_NL));return new T4(0,_NM.a,_NM.b,_NM.c,_NM.d);},_NN=function(_NO,_NP){while(1){var _NQ=B((function(_NR,_NS){var _NT=E(_NS);switch(_NT._){case 0:return new T4(0,_4B,_4B,_0,_0);case 1:var _NU=B(_My(_NT.c)),_NV=B(_NN(_NR,_NT.f)),_NW=B(_L3(_NU.a,_NU.b,_NU.c,_NU.d,_NV.a,_NV.b,_NV.c,_NV.d)),_NX=B(_NN(_NR,_NT.g));return new F(function(){return _L3(_NW.a,_NW.b,_NW.c,_NW.d,_NX.a,_NX.b,_NX.c,_NX.d);});break;case 2:var _NY=_NR;_NO=_NY;_NP=_NT.b;return __continue;case 3:var _NZ=B(_My(_NT.d)),_O0=B(_NN(_NR,_NT.f));return new F(function(){return _L3(_NZ.a,_NZ.b,_NZ.c,_NZ.d,_O0.a,_O0.b,_O0.c,_O0.d);});break;case 4:var _O1=B(_NN(_NR,_NT.a));return new F(function(){return _NA(new T2(1,new T(function(){return B(_NJ(_NR,_NT.b));}),_1),_O1.a,_O1.b,_O1.c,_O1.d);});break;case 5:var _O2=B(_Nl(_NR,_NT.a)),_O3=B(_NN(_NR,_NT.b)),_O4=B(_L3(_O2.a,_O2.b,_O2.c,_O2.d,_O3.a,_O3.b,_O3.c,_O3.d)),_O5=B(_NN(_NR,_NT.c));return new F(function(){return _L3(_O4.a,_O4.b,_O4.c,_O4.d,_O5.a,_O5.b,_O5.c,_O5.d);});break;default:var _O6=B(_Nl(_NR,_NT.a)),_O7=B(_NN(_NR,_NT.c)),_O8=B(_L3(_O6.a,_O6.b,_O6.c,_O6.d,_O7.a,_O7.b,_O7.c,_O7.d)),_O9=B(_NN(_NR,_NT.d));return new F(function(){return _L3(_O8.a,_O8.b,_O8.c,_O8.d,_O9.a,_O9.b,_O9.c,_O9.d);});}})(_NO,_NP));if(_NQ!=__continue){return _NQ;}}},_Oa=function(_Ob,_Oc){var _Od=E(_Ob);if(!_Od._){var _Oe=_Od.a,_Of=E(_Oc);return (_Of._==0)?_Oe!=_Of.a:(I_compareInt(_Of.a,_Oe)==0)?false:true;}else{var _Og=_Od.a,_Oh=E(_Oc);return (_Oh._==0)?(I_compareInt(_Og,_Oh.a)==0)?false:true:(I_compare(_Og,_Oh.a)==0)?false:true;}},_Oi=new T2(0,_C1,_Oa),_Oj=function(_Ok,_Ol){return (!B(_lm(_Ok,_Ol)))?E(_Ok):E(_Ol);},_Om=function(_On,_Oo){return (!B(_lm(_On,_Oo)))?E(_Oo):E(_On);},_Op={_:0,a:_Oi,b:_2,c:_co,d:_lm,e:_CV,f:_e,g:_Oj,h:_Om},_Oq=function(_Or,_Os,_Ot,_Ou){while(1){var _Ov=E(_Ou);if(!_Ov._){var _Ow=_Ov.c,_Ox=_Ov.d,_Oy=E(_Ov.b);switch(B(_2(_Or,_Oy.a))){case 0:_Ou=_Ow;continue;case 1:switch(B(_2(_Os,_Oy.b))){case 0:_Ou=_Ow;continue;case 1:switch(B(_2(_Ot,_Oy.c))){case 0:_Ou=_Ow;continue;case 1:return true;default:_Ou=_Ox;continue;}break;default:_Ou=_Ox;continue;}break;default:_Ou=_Ox;continue;}}else{return false;}}},_Oz=function(_OA,_OB,_OC,_OD,_OE){var _OF=E(_OE);if(!_OF._){if(!B(_lm(_OF.b,_OB))){return false;}else{return new F(function(){return _Oq(_OC,_OD,_OF.a,E(_OA).b);});}}else{return false;}},_OG=function(_OH,_OI,_OJ,_OK,_OL){var _OM=E(_OL);if(!_OM._){var _ON=new T(function(){var _OO=B(_OG(_OM.a,_OM.b,_OM.c,_OM.d,_OM.e));return new T2(0,_OO.a,_OO.b);});return new T2(0,new T(function(){return E(E(_ON).a);}),new T(function(){return B(_1h(_OI,_OJ,_OK,E(_ON).b));}));}else{return new T2(0,new T2(0,_OI,_OJ),_OK);}},_OP=function(_OQ,_OR,_OS,_OT,_OU){var _OV=E(_OT);if(!_OV._){var _OW=new T(function(){var _OX=B(_OP(_OV.a,_OV.b,_OV.c,_OV.d,_OV.e));return new T2(0,_OX.a,_OX.b);});return new T2(0,new T(function(){return E(E(_OW).a);}),new T(function(){return B(_q(_OR,_OS,E(_OW).b,_OU));}));}else{return new T2(0,new T2(0,_OR,_OS),_OU);}},_OY=function(_OZ,_P0){var _P1=E(_OZ);if(!_P1._){var _P2=_P1.a,_P3=E(_P0);if(!_P3._){var _P4=_P3.a;if(_P2<=_P4){var _P5=B(_OP(_P4,_P3.b,_P3.c,_P3.d,_P3.e)),_P6=E(_P5.a);return new F(function(){return _1h(_P6.a,_P6.b,_P1,_P5.b);});}else{var _P7=B(_OG(_P2,_P1.b,_P1.c,_P1.d,_P1.e)),_P8=E(_P7.a);return new F(function(){return _q(_P8.a,_P8.b,_P7.b,_P3);});}}else{return E(_P1);}}else{return E(_P0);}},_P9=function(_Pa,_Pb,_Pc,_Pd,_Pe,_Pf){var _Pg=E(_Pa);if(!_Pg._){var _Ph=_Pg.a,_Pi=_Pg.b,_Pj=_Pg.c,_Pk=_Pg.d,_Pl=_Pg.e;if((imul(3,_Ph)|0)>=_Pb){if((imul(3,_Pb)|0)>=_Ph){return new F(function(){return _OY(_Pg,new T5(0,_Pb,E(_Pc),_Pd,E(_Pe),E(_Pf)));});}else{return new F(function(){return _q(_Pi,_Pj,_Pk,B(_P9(_Pl,_Pb,_Pc,_Pd,_Pe,_Pf)));});}}else{return new F(function(){return _1h(_Pc,_Pd,B(_Pm(_Ph,_Pi,_Pj,_Pk,_Pl,_Pe)),_Pf);});}}else{return new T5(0,_Pb,E(_Pc),_Pd,E(_Pe),E(_Pf));}},_Pm=function(_Pn,_Po,_Pp,_Pq,_Pr,_Ps){var _Pt=E(_Ps);if(!_Pt._){var _Pu=_Pt.a,_Pv=_Pt.b,_Pw=_Pt.c,_Px=_Pt.d,_Py=_Pt.e;if((imul(3,_Pn)|0)>=_Pu){if((imul(3,_Pu)|0)>=_Pn){return new F(function(){return _OY(new T5(0,_Pn,E(_Po),_Pp,E(_Pq),E(_Pr)),_Pt);});}else{return new F(function(){return _q(_Po,_Pp,_Pq,B(_P9(_Pr,_Pu,_Pv,_Pw,_Px,_Py)));});}}else{return new F(function(){return _1h(_Pv,_Pw,B(_Pm(_Pn,_Po,_Pp,_Pq,_Pr,_Px)),_Py);});}}else{return new T5(0,_Pn,E(_Po),_Pp,E(_Pq),E(_Pr));}},_Pz=function(_PA,_PB){var _PC=E(_PA);if(!_PC._){var _PD=_PC.a,_PE=_PC.b,_PF=_PC.c,_PG=_PC.d,_PH=_PC.e,_PI=E(_PB);if(!_PI._){var _PJ=_PI.a,_PK=_PI.b,_PL=_PI.c,_PM=_PI.d,_PN=_PI.e;if((imul(3,_PD)|0)>=_PJ){if((imul(3,_PJ)|0)>=_PD){return new F(function(){return _OY(_PC,_PI);});}else{return new F(function(){return _q(_PE,_PF,_PG,B(_P9(_PH,_PJ,_PK,_PL,_PM,_PN)));});}}else{return new F(function(){return _1h(_PK,_PL,B(_Pm(_PD,_PE,_PF,_PG,_PH,_PM)),_PN);});}}else{return E(_PC);}}else{return E(_PB);}},_PO=function(_PP,_PQ){var _PR=E(_PQ);if(!_PR._){var _PS=_PR.b,_PT=_PR.c,_PU=B(_PO(_PP,_PR.d)),_PV=_PU.a,_PW=_PU.b,_PX=B(_PO(_PP,_PR.e)),_PY=_PX.a,_PZ=_PX.b;return (!B(A2(_PP,_PS,_PT)))?new T2(0,B(_Pz(_PV,_PY)),B(_2B(_PS,_PT,_PW,_PZ))):new T2(0,B(_2B(_PS,_PT,_PV,_PY)),B(_Pz(_PW,_PZ)));}else{return new T2(0,_0,_0);}},_Q0=function(_Q1,_Q2){while(1){var _Q3=B((function(_Q4,_Q5){var _Q6=E(_Q5);if(!_Q6._){var _Q7=_Q6.e,_Q8=new T(function(){var _Q9=E(_Q6.c),_Qa=E(_Q9.b);if(!_Qa._){return new T2(1,new T3(5,_Q6.b,_Q9.a,_Qa.a),new T(function(){return B(_Q0(_Q4,_Q7));}));}else{return B(_Q0(_Q4,_Q7));}},1);_Q1=_Q8;_Q2=_Q6.d;return __continue;}else{return E(_Q4);}})(_Q1,_Q2));if(_Q3!=__continue){return _Q3;}}},_Qb=function(_Qc,_Qd){var _Qe=E(_Qd);return (_Qe._==0)?new T5(0,_Qe.a,E(_Qe.b),new T(function(){return B(A1(_Qc,_Qe.c));}),E(B(_Qb(_Qc,_Qe.d))),E(B(_Qb(_Qc,_Qe.e)))):new T0(1);},_Qf=new T0(2),_Qg=function(_Qh){var _Qi=E(_Qh);return (E(_Qi.b)._==0)?new T2(0,_Qi.a,_Qf):E(_Qi);},_Qj=function(_Qk,_Ql,_Qm){var _Qn=new T(function(){var _Qo=new T(function(){return E(E(_Qm).b);}),_Qp=B(_PO(function(_Qq,_Qr){var _Qs=E(_Qr);return new F(function(){return _Oz(_Qk,_Qo,_Qq,_Qs.a,_Qs.b);});},_Ql));return new T2(0,_Qp.a,_Qp.b);}),_Qt=new T(function(){return E(E(_Qn).a);});return new T2(0,new T(function(){var _Qu=B(_Qb(_Qg,_Qt));if(!_Qu._){var _Qv=E(E(_Qn).b);if(!_Qv._){return B(_Jm(_Op,_HZ,_HZ,_Qu.a,_Qu.b,_Qu.c,_Qu.d,_Qu.e,_Qv.a,_Qv.b,_Qv.c,_Qv.d,_Qv.e));}else{return E(_Qu);}}else{return E(E(_Qn).b);}}),new T(function(){return B(_Q0(_1,_Qt));}));},_Qw=function(_Qx,_Qy,_Qz,_QA){var _QB=E(_QA);if(!_QB._){var _QC=_QB.c,_QD=_QB.d,_QE=_QB.e,_QF=E(_QB.b);switch(B(_2(_Qx,_QF.a))){case 0:return new F(function(){return _1h(_QF,_QC,B(_Qw(_Qx,_Qy,_Qz,_QD)),_QE);});break;case 1:switch(B(_2(_Qy,_QF.b))){case 0:return new F(function(){return _1h(_QF,_QC,B(_Qw(_Qx,_Qy,_Qz,_QD)),_QE);});break;case 1:return new T5(0,_QB.a,E(new T2(0,_Qx,_Qy)),_Qz,E(_QD),E(_QE));default:return new F(function(){return _q(_QF,_QC,_QD,B(_Qw(_Qx,_Qy,_Qz,_QE)));});}break;default:return new F(function(){return _q(_QF,_QC,_QD,B(_Qw(_Qx,_Qy,_Qz,_QE)));});}}else{return new T5(0,1,E(new T2(0,_Qx,_Qy)),_Qz,E(_0),E(_0));}},_QG=function(_QH,_QI,_QJ){while(1){var _QK=E(_QJ);if(!_QK._){var _QL=_QK.d,_QM=_QK.e,_QN=E(_QK.b);switch(B(_2(_QH,_QN.a))){case 0:_QJ=_QL;continue;case 1:switch(B(_2(_QI,_QN.b))){case 0:_QJ=_QL;continue;case 1:return true;default:_QJ=_QM;continue;}break;default:_QJ=_QM;continue;}}else{return false;}}},_QO=function(_QP,_QQ,_QR){while(1){var _QS=B((function(_QT,_QU,_QV){var _QW=E(_QV);if(!_QW._){var _QX=_QW.c,_QY=_QW.e,_QZ=E(_QW.b),_R0=_QZ.a,_R1=_QZ.b,_R2=B(_QO(_QT,_QU,_QW.d)),_R3=_R2.a,_R4=_R2.b;if(!B(_QG(_R0,_R1,_R3))){_QP=new T(function(){return B(_Qw(_R0,_R1,_QX,_R3));});_QQ=new T2(1,new T3(7,_R0,_R1,_QX),_R4);_QR=_QY;return __continue;}else{_QP=_R3;_QQ=_R4;_QR=_QY;return __continue;}}else{return new T2(0,_QT,_QU);}})(_QP,_QQ,_QR));if(_QS!=__continue){return _QS;}}},_R5=function(_R6,_R7){while(1){var _R8=E(_R6);switch(_R8._){case 0:var _R9=E(_R7);if(!_R9._){return new F(function(){return _C1(_R8.a,_R9.a);});}else{return false;}break;case 1:var _Ra=E(_R7);if(_Ra._==1){if(!B(_R5(_R8.a,_Ra.a))){return false;}else{_R6=_R8.b;_R7=_Ra.b;continue;}}else{return false;}break;case 2:var _Rb=E(_R7);if(_Rb._==2){return new F(function(){return _C1(_R8.a,_Rb.a);});}else{return false;}break;default:var _Rc=E(_R7);if(_Rc._==3){if(!B(_C1(_R8.a,_Rc.a))){return false;}else{if(!B(_C1(_R8.b,_Rc.b))){return false;}else{_R6=_R8.c;_R7=_Rc.c;continue;}}}else{return false;}}}},_Rd=function(_Re,_Rf){while(1){var _Rg=E(_Re);switch(_Rg._){case 0:var _Rh=E(_Rf);if(!_Rh._){return new F(function(){return _C1(_Rg.a,_Rh.a);});}else{return false;}break;case 1:var _Ri=E(_Rf);if(_Ri._==1){if(!B(_Rd(_Rg.a,_Ri.a))){return false;}else{_Re=_Rg.b;_Rf=_Ri.b;continue;}}else{return false;}break;case 2:var _Rj=E(_Rf);if(_Rj._==2){if(!B(_Rd(_Rg.a,_Rj.a))){return false;}else{_Re=_Rg.b;_Rf=_Rj.b;continue;}}else{return false;}break;case 3:var _Rk=E(_Rf);if(_Rk._==3){_Re=_Rg.a;_Rf=_Rk.a;continue;}else{return false;}break;case 4:var _Rl=E(_Rf);if(_Rl._==4){if(!B(_C1(_Rg.a,_Rl.a))){return false;}else{if(!B(_C1(_Rg.b,_Rl.b))){return false;}else{return new F(function(){return _C1(_Rg.c,_Rl.c);});}}}else{return false;}break;case 5:var _Rm=E(_Rf);if(_Rm._==5){if(!B(_C1(_Rg.a,_Rm.a))){return false;}else{return new F(function(){return _C1(_Rg.b,_Rm.b);});}}else{return false;}break;case 6:var _Rn=E(_Rf);if(_Rn._==6){if(!B(_R5(_Rg.a,_Rn.a))){return false;}else{return new F(function(){return _R5(_Rg.b,_Rn.b);});}}else{return false;}break;case 7:return (E(_Rf)._==7)?true:false;default:return (E(_Rf)._==8)?true:false;}}},_Ro=function(_Rp,_Rq){while(1){var _Rr=E(_Rp);switch(_Rr._){case 0:return (E(_Rq)._==0)?true:false;case 1:var _Rs=E(_Rq);if(_Rs._==1){if(!B(_C1(_Rr.a,_Rs.a))){return false;}else{if(!B(_C1(_Rr.b,_Rs.b))){return false;}else{if(!B(_R5(_Rr.c,_Rs.c))){return false;}else{if(!B(_C1(_Rr.d,_Rs.d))){return false;}else{if(!B(_C1(_Rr.e,_Rs.e))){return false;}else{if(!B(_Ro(_Rr.f,_Rs.f))){return false;}else{_Rp=_Rr.g;_Rq=_Rs.g;continue;}}}}}}}else{return false;}break;case 2:var _Rt=E(_Rq);if(_Rt._==2){if(!B(_C1(_Rr.a,_Rt.a))){return false;}else{_Rp=_Rr.b;_Rq=_Rt.b;continue;}}else{return false;}break;case 3:var _Ru=E(_Rq);if(_Ru._==3){if(!B(_C1(_Rr.a,_Ru.a))){return false;}else{if(!B(_C1(_Rr.b,_Ru.b))){return false;}else{if(!B(_C1(_Rr.c,_Ru.c))){return false;}else{if(!B(_R5(_Rr.d,_Ru.d))){return false;}else{if(!B(_C1(_Rr.e,_Ru.e))){return false;}else{_Rp=_Rr.f;_Rq=_Ru.f;continue;}}}}}}else{return false;}break;case 4:var _Rv=E(_Rq);if(_Rv._==4){if(!B(_Ro(_Rr.a,_Rv.a))){return false;}else{_Rp=_Rr.b;_Rq=_Rv.b;continue;}}else{return false;}break;case 5:var _Rw=E(_Rq);if(_Rw._==5){if(!B(_Rd(_Rr.a,_Rw.a))){return false;}else{if(!B(_Ro(_Rr.b,_Rw.b))){return false;}else{_Rp=_Rr.c;_Rq=_Rw.c;continue;}}}else{return false;}break;default:var _Rx=E(_Rq);if(_Rx._==6){if(!B(_Rd(_Rr.a,_Rx.a))){return false;}else{if(!B(_C1(_Rr.b,_Rx.b))){return false;}else{if(!B(_Ro(_Rr.c,_Rx.c))){return false;}else{_Rp=_Rr.d;_Rq=_Rx.d;continue;}}}}else{return false;}}}},_Ry=new T2(0,_C1,_Oa),_Rz=function(_RA,_RB,_RC,_RD,_RE,_RF){return (!B(A3(_kQ,_RA,_RC,_RE)))?true:(!B(A3(_kQ,_RB,_RD,_RF)))?true:false;},_RG=function(_RH,_RI,_RJ,_RK){var _RL=E(_RJ),_RM=E(_RK);return new F(function(){return _Rz(_RH,_RI,_RL.a,_RL.b,_RM.a,_RM.b);});},_RN=function(_RO,_RP,_RQ,_RR,_RS,_RT){if(!B(A3(_kQ,_RO,_RQ,_RS))){return false;}else{return new F(function(){return A3(_kQ,_RP,_RR,_RT);});}},_RU=function(_RV,_RW,_RX,_RY){var _RZ=E(_RX),_S0=E(_RY);return new F(function(){return _RN(_RV,_RW,_RZ.a,_RZ.b,_S0.a,_S0.b);});},_S1=function(_S2,_S3){return new T2(0,function(_S4,_S5){return new F(function(){return _RU(_S2,_S3,_S4,_S5);});},function(_S4,_S5){return new F(function(){return _RG(_S2,_S3,_S4,_S5);});});},_S6=function(_S7,_S8,_S9){while(1){var _Sa=E(_S8);if(!_Sa._){return (E(_S9)._==0)?true:false;}else{var _Sb=E(_S9);if(!_Sb._){return false;}else{if(!B(A3(_kQ,_S7,_Sa.a,_Sb.a))){return false;}else{_S8=_Sa.b;_S9=_Sb.b;continue;}}}}},_Sc=function(_Sd,_Se){var _Sf=new T(function(){return B(_S1(_Sd,_Se));}),_Sg=function(_Sh,_Si){var _Sj=function(_Sk){var _Sl=function(_Sm){if(_Sk!=_Sm){return false;}else{return new F(function(){return _S6(_Sf,B(_c1(_1,_Sh)),B(_c1(_1,_Si)));});}},_Sn=E(_Si);if(!_Sn._){return new F(function(){return _Sl(_Sn.a);});}else{return new F(function(){return _Sl(0);});}},_So=E(_Sh);if(!_So._){return new F(function(){return _Sj(_So.a);});}else{return new F(function(){return _Sj(0);});}};return E(_Sg);},_Sp=new T(function(){return B(_Sc(_Ee,_Ry));}),_Sq=function(_Sr,_Ss){var _St=E(_Sr);switch(_St._){case 0:var _Su=E(_Ss);if(!_Su._){if(!B(_C1(_St.a,_Su.a))){return false;}else{return new F(function(){return _C1(_St.b,_Su.b);});}}else{return false;}break;case 1:return (E(_Ss)._==1)?true:false;default:return (E(_Ss)._==2)?true:false;}},_Sv=function(_Sw,_Sx,_Sy,_Sz){if(!B(_C1(_Sw,_Sy))){return false;}else{return new F(function(){return _Sq(_Sx,_Sz);});}},_SA=function(_SB,_SC){var _SD=E(_SB),_SE=E(_SC);return new F(function(){return _Sv(_SD.a,_SD.b,_SE.a,_SE.b);});},_SF=function(_SG,_SH,_SI,_SJ){if(!B(_C1(_SG,_SI))){return true;}else{var _SK=E(_SH);switch(_SK._){case 0:var _SL=E(_SJ);return (_SL._==0)?(!B(_C1(_SK.a,_SL.a)))?true:(!B(_C1(_SK.b,_SL.b)))?true:false:true;case 1:return (E(_SJ)._==1)?false:true;default:return (E(_SJ)._==2)?false:true;}}},_SM=function(_SN,_SO){var _SP=E(_SN),_SQ=E(_SO);return new F(function(){return _SF(_SP.a,_SP.b,_SQ.a,_SQ.b);});},_SR=new T2(0,_SA,_SM),_SS=new T(function(){return B(_Sc(_Oi,_SR));}),_ST=new T1(0,0),_SU=function(_SV,_SW,_SX){var _SY=function(_SZ,_T0){while(1){var _T1=B((function(_T2,_T3){var _T4=E(_T3);if(!_T4._){var _T5=new T(function(){return B(_SY(_T2,_T4.e));}),_T6=function(_T7){var _T8=E(_T4.c),_T9=E(_T8.b);if(!_T9._){if(!B(_C1(_T8.a,_SW))){return new F(function(){return A1(_T5,_T7);});}else{if(!B(_lm(_T9.b,_SX))){return new F(function(){return A1(_T5,new T(function(){return B(_ji(_T7,_T9.a));}));});}else{return new F(function(){return A1(_T5,_T7);});}}}else{return new F(function(){return A1(_T5,_T7);});}};_SZ=_T6;_T0=_T4.d;return __continue;}else{return E(_T2);}})(_SZ,_T0));if(_T1!=__continue){return _T1;}}};return new F(function(){return A3(_SY,_i9,_SV,_ST);});},_Ta=function(_Tb,_Tc,_Td,_Te,_Tf){while(1){var _Tg=E(_Tf);if(!_Tg._){var _Th=_Tg.c,_Ti=_Tg.d,_Tj=E(_Tg.b);switch(B(_2(_Tb,_Tj.a))){case 0:_Tf=_Th;continue;case 1:switch(B(_2(_Tc,_Tj.b))){case 0:_Tf=_Th;continue;case 1:switch(B(_2(_Td,_Tj.c))){case 0:_Tf=_Th;continue;case 1:switch(B(_2(_Te,_Tj.d))){case 0:_Tf=_Th;continue;case 1:return true;default:_Tf=_Ti;continue;}break;default:_Tf=_Ti;continue;}break;default:_Tf=_Ti;continue;}break;default:_Tf=_Ti;continue;}}else{return false;}}},_Tk=function(_Tl,_Tm,_Tn){while(1){var _To=E(_Tn);if(!_To._){var _Tp=_To.d,_Tq=_To.e,_Tr=E(_To.b);switch(B(_2(_Tl,_Tr.a))){case 0:_Tn=_Tp;continue;case 1:switch(B(_2(_Tm,_Tr.b))){case 0:_Tn=_Tp;continue;case 1:return new T1(1,_To.c);default:_Tn=_Tq;continue;}break;default:_Tn=_Tq;continue;}}else{return __Z;}}},_Ts=new T0(1),_Tt=__Z,_Tu=function(_Tv,_Tw,_Tx){return new F(function(){return _SU(E(_Tv).a,_Tw,_Tx);});},_Ty=function(_Tz,_TA,_TB){while(1){var _TC=E(_TA);switch(_TC._){case 0:return (!B(_lm(_TC.a,E(_TB).b)))?true:false;case 1:if(!B(_Ty(_Tz,_TC.a,_TB))){return false;}else{_TA=_TC.b;continue;}break;case 2:if(!B(_Ty(_Tz,_TC.a,_TB))){_TA=_TC.b;continue;}else{return true;}break;case 3:return (!B(_Ty(_Tz,_TC.a,_TB)))?true:false;case 4:var _TD=B(_Lp(_TC.a,_TC.b,E(_Tz).b));if(!_TD._){return false;}else{return new F(function(){return _C1(_TD.a,_TC.c);});}break;case 5:return new F(function(){return _QG(_TC.a,_TC.b,E(_Tz).b);});break;case 6:return new F(function(){return _e(B(_LI(_Tz,_TC.a)),B(_LI(_Tz,_TC.b)));});break;case 7:return true;default:return false;}}},_TE=new T(function(){return B(unCStr("attempt to discount when insufficient cash available"));}),_TF=new T(function(){return B(err(_TE));}),_TG=function(_TH,_TI){while(1){var _TJ=E(_TH);if(!_TJ._){var _TK=_TJ.a,_TL=E(_TI);if(!_TL._){var _TM=_TL.a,_TN=subC(_TK,_TM);if(!E(_TN.b)){return new T1(0,_TN.a);}else{_TH=new T1(1,I_fromInt(_TK));_TI=new T1(1,I_fromInt(_TM));continue;}}else{_TH=new T1(1,I_fromInt(_TK));_TI=_TL;continue;}}else{var _TO=E(_TI);if(!_TO._){_TH=_TJ;_TI=new T1(1,I_fromInt(_TO.a));continue;}else{return new T1(1,I_sub(_TJ.a,_TO.a));}}}},_TP=function(_TQ,_TR){var _TS=E(_TR);if(!_TS._){return (!B(_C1(_TQ,_ST)))?E(_TF):__Z;}else{var _TT=_TS.b,_TU=E(_TS.a),_TV=_TU.a,_TW=E(_TU.b),_TX=_TW.a,_TY=E(_TW.b);if(!_TY._){var _TZ=_TY.a,_U0=_TY.b;if(!B(_lm(_TQ,_TZ))){if(!B(_co(_TZ,_TQ))){return E(_TT);}else{var _U1=new T(function(){return B(_TP(new T(function(){return B(_TG(_TQ,_TZ));}),_TT));});return new T2(1,new T2(0,_TV,new T2(0,_TX,new T2(0,_ST,_U0))),_U1);}}else{return new T2(1,new T2(0,_TV,new T2(0,_TX,new T2(0,new T(function(){return B(_TG(_TZ,_TQ));}),_U0))),_1);}}else{return E(_TT);}}},_U2=function(_U3,_U4){var _U5=E(_U4);if(!_U5._){var _U6=_U5.b,_U7=_U5.c,_U8=_U5.d,_U9=_U5.e;if(!B(A2(_U3,_U6,_U7))){return new F(function(){return _Pz(B(_U2(_U3,_U8)),B(_U2(_U3,_U9)));});}else{return new F(function(){return _2B(_U6,_U7,B(_U2(_U3,_U8)),B(_U2(_U3,_U9)));});}}else{return new T0(1);}},_Ua=function(_Ub,_Uc,_Ud,_Ue){var _Uf=E(_Uc);if(!_Uf._){var _Ug=E(_Ue);if(!_Ug._){var _Uh=B(_2(_Uf.b,_Ug.b));if(_Uh==1){return new F(function(){return _2(_Ub,_Ud);});}else{return E(_Uh);}}else{return 0;}}else{return (E(_Ue)._==0)?2:1;}},_Ui=function(_Uj,_Uk){var _Ul=E(_Uj),_Um=E(_Uk);return new F(function(){return _Ua(_Ul.a,E(_Ul.b).b,_Um.a,E(_Um.b).b);});},_Un=new T2(1,_1,_1),_Uo=function(_Up,_Uq){var _Ur=function(_Us,_Ut){var _Uu=E(_Us);if(!_Uu._){return E(_Ut);}else{var _Uv=_Uu.a,_Uw=E(_Ut);if(!_Uw._){return E(_Uu);}else{var _Ux=_Uw.a;return (B(A2(_Up,_Uv,_Ux))==2)?new T2(1,_Ux,new T(function(){return B(_Ur(_Uu,_Uw.b));})):new T2(1,_Uv,new T(function(){return B(_Ur(_Uu.b,_Uw));}));}}},_Uy=function(_Uz){var _UA=E(_Uz);if(!_UA._){return __Z;}else{var _UB=E(_UA.b);return (_UB._==0)?E(_UA):new T2(1,new T(function(){return B(_Ur(_UA.a,_UB.a));}),new T(function(){return B(_Uy(_UB.b));}));}},_UC=new T(function(){return B(_UD(B(_Uy(_1))));}),_UD=function(_UE){while(1){var _UF=E(_UE);if(!_UF._){return E(_UC);}else{if(!E(_UF.b)._){return E(_UF.a);}else{_UE=B(_Uy(_UF));continue;}}}},_UG=new T(function(){return B(_UH(_1));}),_UI=function(_UJ,_UK,_UL){while(1){var _UM=B((function(_UN,_UO,_UP){var _UQ=E(_UP);if(!_UQ._){return new T2(1,new T2(1,_UN,_UO),_UG);}else{var _UR=_UQ.a;if(B(A2(_Up,_UN,_UR))==2){var _US=new T2(1,_UN,_UO);_UJ=_UR;_UK=_US;_UL=_UQ.b;return __continue;}else{return new T2(1,new T2(1,_UN,_UO),new T(function(){return B(_UH(_UQ));}));}}})(_UJ,_UK,_UL));if(_UM!=__continue){return _UM;}}},_UT=function(_UU,_UV,_UW){while(1){var _UX=B((function(_UY,_UZ,_V0){var _V1=E(_V0);if(!_V1._){return new T2(1,new T(function(){return B(A1(_UZ,new T2(1,_UY,_1)));}),_UG);}else{var _V2=_V1.a,_V3=_V1.b;switch(B(A2(_Up,_UY,_V2))){case 0:_UU=_V2;_UV=function(_V4){return new F(function(){return A1(_UZ,new T2(1,_UY,_V4));});};_UW=_V3;return __continue;case 1:_UU=_V2;_UV=function(_V5){return new F(function(){return A1(_UZ,new T2(1,_UY,_V5));});};_UW=_V3;return __continue;default:return new T2(1,new T(function(){return B(A1(_UZ,new T2(1,_UY,_1)));}),new T(function(){return B(_UH(_V1));}));}}})(_UU,_UV,_UW));if(_UX!=__continue){return _UX;}}},_UH=function(_V6){var _V7=E(_V6);if(!_V7._){return E(_Un);}else{var _V8=_V7.a,_V9=E(_V7.b);if(!_V9._){return new T2(1,_V7,_1);}else{var _Va=_V9.a,_Vb=_V9.b;if(B(A2(_Up,_V8,_Va))==2){return new F(function(){return _UI(_Va,new T2(1,_V8,_1),_Vb);});}else{return new F(function(){return _UT(_Va,function(_Vc){return new T2(1,_V8,_Vc);},_Vb);});}}}};return new F(function(){return _UD(B(_UH(_Uq)));});},_Vd=function(_Ve,_Vf,_Vg){var _Vh=B(_zV(B(_TP(_Vf,B(_Uo(_Ui,B(_c1(_1,B(_U2(function(_Vi,_Vj){return new F(function(){return A1(_Ve,_Vj);});},_Vg))))))))));if(!_Vh._){var _Vk=E(_Vg);if(!_Vk._){return new F(function(){return _Jm(_Op,_HZ,_HZ,_Vh.a,_Vh.b,_Vh.c,_Vh.d,_Vh.e,_Vk.a,_Vk.b,_Vk.c,_Vk.d,_Vk.e);});}else{return E(_Vh);}}else{return E(_Vg);}},_Vl=function(_Vm,_Vn,_Vo,_Vp){var _Vq=E(_Vp);return (_Vq._==0)?(!B(_C1(_Vo,_Vm)))?false:(!B(_lm(_Vq.b,_Vn)))?true:false:false;},_Vr=function(_Vs,_Vt,_Vu){var _Vv=E(_Vu);return new F(function(){return _Vl(_Vs,_Vt,_Vv.a,_Vv.b);});},_Vw=function(_Vx,_Vy,_Vz,_VA,_VB){var _VC=E(_Vx),_VD=new T(function(){return B(_Vd(function(_uz){return new F(function(){return _Vr(_Vy,_VA,_uz);});},_VB,_VC.a));});return new T2(0,_VD,_VC.b);},_VE=function(_VF,_VG,_VH,_VI){var _VJ=E(_VH);switch(_VJ._){case 0:return new T3(0,_VG,_Tt,_1);case 1:var _VK=_VJ.a,_VL=_VJ.b,_VM=_VJ.e,_VN=_VJ.g,_VO=E(_VI).b,_VP=B(_lm(_VM,_VO)),_VQ=new T(function(){var _VR=E(_VG);return B(_LA(_VR.a,_VR.b,_VJ.c));}),_VS=new T(function(){return B(_lm(_VJ.d,_VO));}),_VT=new T(function(){return B(_z3(_VK,new T2(0,_VL,new T(function(){if(!E(_VP)){if(!E(_VS)){return new T2(0,_VQ,_VM);}else{return new T0(1);}}else{return new T0(1);}})),E(_VG).a));});return (!E(_VP))?(!E(_VS))?(!B(_Ta(_VK,_VL,_VQ,_VM,E(_VF).a)))?new T3(0,_VG,_VJ,_1):new T3(0,new T(function(){return new T2(0,_VT,E(_VG).b);}),_VJ.f,new T2(1,new T4(3,_VK,_VL,_VQ,_VM),_1)):new T3(0,new T(function(){return new T2(0,_VT,E(_VG).b);}),_VN,_1):new T3(0,new T(function(){return new T2(0,_VT,E(_VG).b);}),_VN,_1);case 2:var _VU=_VJ.a,_VV=_VJ.b,_VW=E(_VG),_VX=_VW.a,_VY=B(_Lk(_VU,_VX));if(!_VY._){return new T3(0,_VW,_VJ,_1);}else{var _VZ=E(_VY.a),_W0=_VZ.a,_W1=E(_VZ.b);switch(_W1._){case 0:var _W2=_W1.a;return (!B(_lm(_W1.b,E(_VI).b)))?(!B(_Oq(_VU,_W0,_W2,E(_VF).b)))?new T3(0,_VW,_VJ,_1):new T3(0,new T2(0,new T(function(){return B(_z3(_VU,new T2(0,_W0,_Ts),_VX));}),_VW.b),_VV,new T2(1,new T3(4,_VU,_W0,_W2),_1)):new T3(0,_VW,_VV,_1);case 1:return new T3(0,_VW,_VV,new T2(1,new T2(6,_VU,_W0),_1));default:return new T3(0,_VW,_VV,_1);}}break;case 3:var _W3=_VJ.a,_W4=_VJ.b,_W5=_VJ.c,_W6=_VJ.f,_W7=E(_VI).b,_W8=new T(function(){var _W9=E(_VG);return B(_LA(_W9.a,_W9.b,_VJ.d));});if(!B(_lm(_VJ.e,_W7))){var _Wa=B(_Tk(_W3,_W5,E(_VF).c));return (_Wa._==0)?new T3(0,_VG,_VJ,_1):(!B(_C1(_Wa.a,_W8)))?new T3(0,_VG,_VJ,_1):(!B(_e(B(_Tu(_VG,_W4,_W7)),_W8)))?new T3(0,_VG,_W6,new T2(1,new T4(2,_W3,_W4,_W5,_W8),_1)):(!B(_e(_W8,_ST)))?new T3(0,_VG,_W6,new T2(1,new T4(2,_W3,_W4,_W5,_W8),_1)):new T3(0,new T(function(){return B(_Vw(_VG,_W4,_W5,_W7,_W8));}),_W6,new T2(1,new T4(0,_W3,_W4,_W5,_W8),_1));}else{return new T3(0,_VG,_W6,new T2(1,new T4(1,_W3,_W4,_W5,_W8),_1));}break;case 4:var _Wb=new T(function(){var _Wc=B(_VE(_VF,_VG,_VJ.a,_VI));return new T3(0,_Wc.a,_Wc.b,_Wc.c);}),_Wd=new T(function(){var _We=B(_VE(_VF,new T(function(){return E(E(_Wb).a);}),_VJ.b,_VI));return new T3(0,_We.a,_We.b,_We.c);}),_Wf=new T(function(){return B(_ce(E(_Wb).c,new T(function(){return E(E(_Wd).c);},1)));}),_Wg=new T(function(){var _Wh=E(_Wb).b,_Wi=E(_Wd).b,_Wj=function(_Wk){var _Wl=E(_Wi);switch(_Wl._){case 0:return E(_Wh);case 1:return new T2(4,_Wh,_Wl);case 2:return new T2(4,_Wh,_Wl);case 3:return new T2(4,_Wh,_Wl);case 4:return new T2(4,_Wh,_Wl);case 5:return new T2(4,_Wh,_Wl);default:return new T2(4,_Wh,_Wl);}};switch(E(_Wh)._){case 0:return E(_Wi);break;case 1:return B(_Wj(_));break;case 2:return B(_Wj(_));break;case 3:return B(_Wj(_));break;case 4:return B(_Wj(_));break;case 5:return B(_Wj(_));break;default:return B(_Wj(_));}});return new T3(0,new T(function(){return E(E(_Wd).a);}),_Wg,_Wf);case 5:return (!B(_Ty(_VG,_VJ.a,_VI)))?new T3(0,_VG,_VJ.c,_1):new T3(0,_VG,_VJ.b,_1);default:var _Wm=E(_VI);return (!B(_lm(_VJ.b,_Wm.b)))?(!B(_Ty(_VG,_VJ.a,_Wm)))?new T3(0,_VG,_VJ,_1):new T3(0,_VG,_VJ.c,_1):new T3(0,_VG,_VJ.d,_1);}},_Wn=function(_Wo,_Wp,_Wq,_Wr,_Ws){var _Wt=E(_Wr);switch(_Wt._){case 0:return new T3(0,new T2(0,_Wp,_Wq),_Tt,_1);case 1:var _Wu=_Wt.a,_Wv=_Wt.b,_Ww=_Wt.e,_Wx=_Wt.g,_Wy=E(_Ws).b,_Wz=B(_lm(_Ww,_Wy)),_WA=new T(function(){return B(_LA(_Wp,_Wq,_Wt.c));}),_WB=new T(function(){return B(_lm(_Wt.d,_Wy));}),_WC=new T(function(){return B(_z3(_Wu,new T2(0,_Wv,new T(function(){if(!E(_Wz)){if(!E(_WB)){return new T2(0,_WA,_Ww);}else{return new T0(1);}}else{return new T0(1);}})),_Wp));});return (!E(_Wz))?(!E(_WB))?(!B(_Ta(_Wu,_Wv,_WA,_Ww,E(_Wo).a)))?new T3(0,new T2(0,_Wp,_Wq),_Wt,_1):new T3(0,new T2(0,_WC,_Wq),_Wt.f,new T2(1,new T4(3,_Wu,_Wv,_WA,_Ww),_1)):new T3(0,new T2(0,_WC,_Wq),_Wx,_1):new T3(0,new T2(0,_WC,_Wq),_Wx,_1);case 2:var _WD=_Wt.a,_WE=_Wt.b,_WF=B(_Lk(_WD,_Wp));if(!_WF._){return new T3(0,new T2(0,_Wp,_Wq),_Wt,_1);}else{var _WG=E(_WF.a),_WH=_WG.a,_WI=E(_WG.b);switch(_WI._){case 0:var _WJ=_WI.a;return (!B(_lm(_WI.b,E(_Ws).b)))?(!B(_Oq(_WD,_WH,_WJ,E(_Wo).b)))?new T3(0,new T2(0,_Wp,_Wq),_Wt,_1):new T3(0,new T2(0,new T(function(){return B(_z3(_WD,new T2(0,_WH,_Ts),_Wp));}),_Wq),_WE,new T2(1,new T3(4,_WD,_WH,_WJ),_1)):new T3(0,new T2(0,_Wp,_Wq),_WE,_1);case 1:return new T3(0,new T2(0,_Wp,_Wq),_WE,new T2(1,new T2(6,_WD,_WH),_1));default:return new T3(0,new T2(0,_Wp,_Wq),_WE,_1);}}break;case 3:var _WK=_Wt.a,_WL=_Wt.b,_WM=_Wt.c,_WN=_Wt.f,_WO=E(_Ws).b,_WP=new T(function(){return B(_LA(_Wp,_Wq,_Wt.d));});if(!B(_lm(_Wt.e,_WO))){var _WQ=B(_Tk(_WK,_WM,E(_Wo).c));if(!_WQ._){return new T3(0,new T2(0,_Wp,_Wq),_Wt,_1);}else{if(!B(_C1(_WQ.a,_WP))){return new T3(0,new T2(0,_Wp,_Wq),_Wt,_1);}else{if(!B(_e(B(_SU(_Wp,_WL,_WO)),_WP))){return new T3(0,new T2(0,_Wp,_Wq),_WN,new T2(1,new T4(2,_WK,_WL,_WM,_WP),_1));}else{if(!B(_e(_WP,_ST))){return new T3(0,new T2(0,_Wp,_Wq),_WN,new T2(1,new T4(2,_WK,_WL,_WM,_WP),_1));}else{var _WR=new T(function(){return B(_Vd(function(_uz){return new F(function(){return _Vr(_WL,_WO,_uz);});},_WP,_Wp));});return new T3(0,new T2(0,_WR,_Wq),_WN,new T2(1,new T4(0,_WK,_WL,_WM,_WP),_1));}}}}}else{return new T3(0,new T2(0,_Wp,_Wq),_WN,new T2(1,new T4(1,_WK,_WL,_WM,_WP),_1));}break;case 4:var _WS=new T(function(){var _WT=B(_Wn(_Wo,_Wp,_Wq,_Wt.a,_Ws));return new T3(0,_WT.a,_WT.b,_WT.c);}),_WU=new T(function(){var _WV=B(_VE(_Wo,new T(function(){return E(E(_WS).a);}),_Wt.b,_Ws));return new T3(0,_WV.a,_WV.b,_WV.c);}),_WW=new T(function(){return B(_ce(E(_WS).c,new T(function(){return E(E(_WU).c);},1)));}),_WX=new T(function(){var _WY=E(_WS).b,_WZ=E(_WU).b,_X0=function(_X1){var _X2=E(_WZ);switch(_X2._){case 0:return E(_WY);case 1:return new T2(4,_WY,_X2);case 2:return new T2(4,_WY,_X2);case 3:return new T2(4,_WY,_X2);case 4:return new T2(4,_WY,_X2);case 5:return new T2(4,_WY,_X2);default:return new T2(4,_WY,_X2);}};switch(E(_WY)._){case 0:return E(_WZ);break;case 1:return B(_X0(_));break;case 2:return B(_X0(_));break;case 3:return B(_X0(_));break;case 4:return B(_X0(_));break;case 5:return B(_X0(_));break;default:return B(_X0(_));}});return new T3(0,new T(function(){return E(E(_WU).a);}),_WX,_WW);case 5:return (!B(_Ty(new T2(0,_Wp,_Wq),_Wt.a,_Ws)))?new T3(0,new T2(0,_Wp,_Wq),_Wt.c,_1):new T3(0,new T2(0,_Wp,_Wq),_Wt.b,_1);default:var _X3=E(_Ws);return (!B(_lm(_Wt.b,_X3.b)))?(!B(_Ty(new T2(0,_Wp,_Wq),_Wt.a,_X3)))?new T3(0,new T2(0,_Wp,_Wq),_Wt,_1):new T3(0,new T2(0,_Wp,_Wq),_Wt.c,_1):new T3(0,new T2(0,_Wp,_Wq),_Wt.d,_1);}},_X4=function(_X5,_X6,_X7,_X8,_X9,_Xa){var _Xb=B(_Wn(_X5,_X6,_X7,_X8,_X9)),_Xc=_Xb.b,_Xd=_Xb.c,_Xe=E(_Xb.a),_Xf=_Xe.a,_Xg=_Xe.b,_Xh=function(_Xi){return new F(function(){return _X4(_X5,_Xf,_Xg,_Xc,_X9,new T(function(){return B(_ce(_Xa,_Xd));}));});};if(!B(A2(_SS,_Xf,_X6))){return new F(function(){return _Xh(_);});}else{if(!B(A2(_Sp,_Xg,_X7))){return new F(function(){return _Xh(_);});}else{if(!B(_Ro(_Xc,_X8))){return new F(function(){return _Xh(_);});}else{if(!E(_Xd)._){return new T3(0,new T2(0,_X6,_X7),_X8,_Xa);}else{return new F(function(){return _Xh(_);});}}}}},_Xj=function(_Xk,_Xl,_Xm,_Xn){var _Xo=new T(function(){var _Xp=B(_Qj(_Xk,new T(function(){return E(E(_Xl).a);},1),_Xn));return new T2(0,_Xp.a,_Xp.b);}),_Xq=new T(function(){var _Xr=B(_QO(new T(function(){return E(E(_Xl).b);}),_1,E(_Xk).d));return new T2(0,_Xr.a,_Xr.b);}),_Xs=new T(function(){var _Xt=E(_Xl),_Xu=B(_X4(_Xk,new T(function(){return E(E(_Xo).a);}),new T(function(){return E(E(_Xq).a);}),_Xm,_Xn,_1));return new T3(0,_Xu.a,_Xu.b,_Xu.c);}),_Xv=new T(function(){var _Xw=new T(function(){return B(_ce(E(_Xo).b,new T(function(){return E(E(_Xs).c);},1)));},1);return B(_ce(E(_Xq).b,_Xw));});return new T3(0,new T(function(){return E(E(_Xs).a);}),new T(function(){return E(E(_Xs).b);}),_Xv);},_Xx=function(_Xy,_Xz,_XA,_XB,_XC){while(1){var _XD=E(_Xy);if(!_XD._){return new T4(0,_Xz,_XA,_XB,_XC);}else{var _XE=E(_XD.a),_XF=B(_L3(_Xz,_XA,_XB,_XC,_XE.a,_XE.b,_XE.c,_XE.d));_Xy=_XD.b;_Xz=_XF.a;_XA=_XF.b;_XB=_XF.c;_XC=_XF.d;continue;}}},_XG=function(_XH,_XI,_XJ,_XK,_XL,_XM){var _XN=E(_XH),_XO=B(_L3(_XJ,_XK,_XL,_XM,_XN.a,_XN.b,_XN.c,_XN.d));return new F(function(){return _Xx(_XI,_XO.a,_XO.b,_XO.c,_XO.d);});},_XP=function(_XQ,_XR,_XS,_XT){var _XU=B(_Xj(_XR,_XT,_XS,_XQ)),_XV=_XU.a,_XW=_XU.b,_XX=B(_LM(_XW,_XV));return new F(function(){return _XG(new T(function(){var _XY=B(_LZ(_XQ,E(_XV).a));return new T4(0,_XY.a,_XY.b,_XY.c,_XY.d);}),new T2(1,new T(function(){var _XZ=B(_NN(_XV,_XW));return new T4(0,_XZ.a,_XZ.b,_XZ.c,_XZ.d);}),_1),_XX.a,_XX.b,_XX.c,_XX.d);});},_Y0="(function (t) {return window[t].getValue()})",_Y1=new T(function(){return eval("(function () {return Blockly.Marlowe.workspaceToCode(demoWorkspace);})");}),_Y2=new T(function(){return B(unCStr("contractState"));}),_Y3=new T(function(){return B(unCStr("currBlock"));}),_Y4=new T(function(){return eval("(function (x) { var node = document.getElementById(x); while (node.hasChildNodes()) { node.removeChild(node.lastChild); } })");}),_Y5=new T(function(){return B(err(_bZ));}),_Y6=new T(function(){return B(err(_eR));}),_Y7=new T(function(){return B(A3(_sX,_tq,_ss,_yF));}),_Y8="(function (t) {return document.getElementById(t).value})",_Y9=new T(function(){return B(err(_bZ));}),_Ya=new T(function(){return B(err(_eR));}),_Yb=function(_uz){return new F(function(){return _sM(_wQ,_uz);});},_Yc=function(_Yd,_Ye){return new F(function(){return _tz(_Yb,_Ye);});},_Yf=new T(function(){return B(_tz(_Yb,_eU));}),_Yg=function(_uz){return new F(function(){return _g4(_Yf,_uz);});},_Yh=function(_Yi){var _Yj=new T(function(){return B(A3(_sM,_wQ,_Yi,_eU));});return function(_ue){return new F(function(){return _g4(_Yj,_ue);});};},_Yk=new T4(0,_Yh,_Yg,_Yb,_Yc),_Yl=new T(function(){return B(unCStr("NotRedeemed"));}),_Ym=function(_Yn,_Yo){return new F(function(){return A1(_Yo,_Ts);});},_Yp=new T(function(){return B(unCStr("ManuallyRedeemed"));}),_Yq=new T2(0,_Yp,_Ym),_Yr=function(_Ys,_Yt){return new F(function(){return A1(_Yt,_Qf);});},_Yu=new T(function(){return B(unCStr("ExpiredAndRedeemed"));}),_Yv=new T2(0,_Yu,_Yr),_Yw=new T2(1,_Yv,_1),_Yx=new T2(1,_Yq,_Yw),_Yy=function(_Yz,_YA,_YB){var _YC=E(_Yz);if(!_YC._){return new T0(2);}else{var _YD=E(_YC.a),_YE=_YD.a,_YF=new T(function(){return B(A2(_YD.b,_YA,_YB));}),_YG=new T(function(){return B(_rV(function(_YH){var _YI=E(_YH);switch(_YI._){case 3:return (!B(_gS(_YE,_YI.a)))?new T0(2):E(_YF);case 4:return (!B(_gS(_YE,_YI.a)))?new T0(2):E(_YF);default:return new T0(2);}}));}),_YJ=function(_YK){return E(_YG);};return new F(function(){return _ge(new T1(1,function(_YL){return new F(function(){return A2(_qC,_YL,_YJ);});}),new T(function(){return B(_Yy(_YC.b,_YA,_YB));}));});}},_YM=function(_YN,_YO){var _YP=new T(function(){if(E(_YN)>10){return new T0(2);}else{var _YQ=new T(function(){var _YR=new T(function(){var _YS=function(_YT){return new F(function(){return A3(_sX,_tq,_ui,function(_YU){return new F(function(){return A1(_YO,new T2(0,_YT,_YU));});});});};return B(A3(_sX,_tq,_ui,_YS));});return B(_rV(function(_YV){var _YW=E(_YV);return (_YW._==3)?(!B(_gS(_YW.a,_Yl)))?new T0(2):E(_YR):new T0(2);}));}),_YX=function(_YY){return E(_YQ);};return new T1(1,function(_YZ){return new F(function(){return A2(_qC,_YZ,_YX);});});}});return new F(function(){return _ge(B(_Yy(_Yx,_YN,_YO)),_YP);});},_Z0=function(_uz){return new F(function(){return _sM(_YM,_uz);});},_Z1=function(_Z2,_Z3){return new F(function(){return _tz(_Z0,_Z3);});},_Z4=new T(function(){return B(_tz(_Z0,_eU));}),_Z5=function(_uz){return new F(function(){return _g4(_Z4,_uz);});},_Z6=function(_Z7){var _Z8=new T(function(){return B(A3(_sM,_YM,_Z7,_eU));});return function(_ue){return new F(function(){return _g4(_Z8,_ue);});};},_Z9=new T4(0,_Z6,_Z5,_Z0,_Z1),_Za=function(_Zb,_Zc){return new F(function(){return _v4(_uh,_Z9,_Zc);});},_Zd=new T(function(){return B(_tz(_Za,_eU));}),_Ze=function(_uz){return new F(function(){return _g4(_Zd,_uz);});},_Zf=new T(function(){return B(_v4(_uh,_Z9,_eU));}),_Zg=function(_uz){return new F(function(){return _g4(_Zf,_uz);});},_Zh=function(_Zi,_uz){return new F(function(){return _Zg(_uz);});},_Zj=function(_Zk,_Zl){return new F(function(){return _tz(_Za,_Zl);});},_Zm=new T4(0,_Zh,_Ze,_Za,_Zj),_Zn=function(_Zo,_Zp){return new F(function(){return _v4(_Yk,_Zm,_Zp);});},_Zq=function(_Zr,_Zs){return new F(function(){return _tz(_Zn,_Zs);});},_Zt=new T(function(){return B(_tz(_Zq,_eU));}),_Zu=function(_vz){return new F(function(){return _g4(_Zt,_vz);});},_Zv=function(_Zw){return new F(function(){return _tz(_Zq,_Zw);});},_Zx=function(_Zy,_Zz){return new F(function(){return _Zv(_Zz);});},_ZA=new T(function(){return B(_tz(_Zn,_eU));}),_ZB=function(_vz){return new F(function(){return _g4(_ZA,_vz);});},_ZC=function(_ZD,_vz){return new F(function(){return _ZB(_vz);});},_ZE=new T4(0,_ZC,_Zu,_Zq,_Zx),_ZF=new T(function(){return B(_v4(_ZE,_vJ,_yF));}),_ZG=new T1(0,42),_ZH=new T(function(){return B(unCStr("actions"));}),_ZI=function(_ZJ){while(1){var _ZK=B((function(_ZL){var _ZM=E(_ZL);if(!_ZM._){return __Z;}else{var _ZN=_ZM.b,_ZO=E(_ZM.a);if(!E(_ZO.b)._){return new T2(1,_ZO.a,new T(function(){return B(_ZI(_ZN));}));}else{_ZJ=_ZN;return __continue;}}})(_ZJ));if(_ZK!=__continue){return _ZK;}}},_ZP=new T(function(){return B(err(_bZ));}),_ZQ=new T(function(){return B(err(_eR));}),_ZR=new T(function(){return B(unCStr("ConstMoney"));}),_ZS=new T(function(){return B(unCStr("AvailableMoney"));}),_ZT=new T(function(){return B(unCStr("AddMoney"));}),_ZU=new T(function(){return B(unCStr("MoneyFromChoice"));}),_ZV=function(_ZW,_ZX){var _ZY=new T(function(){var _ZZ=new T(function(){var _100=new T(function(){if(_ZW>10){return new T0(2);}else{var _101=new T(function(){var _102=new T(function(){var _103=function(_104){var _105=function(_106){return new F(function(){return A3(_sM,_107,_ui,function(_108){return new F(function(){return A1(_ZX,new T3(3,_104,_106,_108));});});});};return new F(function(){return A3(_sX,_tq,_ui,_105);});};return B(A3(_sM,_uv,_ui,_103));});return B(_rV(function(_109){var _10a=E(_109);return (_10a._==3)?(!B(_gS(_10a.a,_ZU)))?new T0(2):E(_102):new T0(2);}));}),_10b=function(_10c){return E(_101);};return new T1(1,function(_10d){return new F(function(){return A2(_qC,_10d,_10b);});});}});if(_ZW>10){return B(_ge(_eT,_100));}else{var _10e=new T(function(){var _10f=new T(function(){return B(A3(_sX,_tq,_ui,function(_10g){return new F(function(){return A1(_ZX,new T1(2,_10g));});}));});return B(_rV(function(_10h){var _10i=E(_10h);return (_10i._==3)?(!B(_gS(_10i.a,_ZR)))?new T0(2):E(_10f):new T0(2);}));}),_10j=function(_10k){return E(_10e);};return B(_ge(new T1(1,function(_10l){return new F(function(){return A2(_qC,_10l,_10j);});}),_100));}});if(_ZW>10){return B(_ge(_eT,_ZZ));}else{var _10m=new T(function(){var _10n=new T(function(){var _10o=function(_10p){return new F(function(){return A3(_sM,_107,_ui,function(_10q){return new F(function(){return A1(_ZX,new T2(1,_10p,_10q));});});});};return B(A3(_sM,_107,_ui,_10o));});return B(_rV(function(_10r){var _10s=E(_10r);return (_10s._==3)?(!B(_gS(_10s.a,_ZT)))?new T0(2):E(_10n):new T0(2);}));}),_10t=function(_10u){return E(_10m);};return B(_ge(new T1(1,function(_10v){return new F(function(){return A2(_qC,_10v,_10t);});}),_ZZ));}});if(_ZW>10){return new F(function(){return _ge(_eT,_ZY);});}else{var _10w=new T(function(){var _10x=new T(function(){return B(A3(_sM,_wQ,_ui,function(_10y){return new F(function(){return A1(_ZX,new T1(0,_10y));});}));});return B(_rV(function(_10z){var _10A=E(_10z);return (_10A._==3)?(!B(_gS(_10A.a,_ZS)))?new T0(2):E(_10x):new T0(2);}));}),_10B=function(_10C){return E(_10w);};return new F(function(){return _ge(new T1(1,function(_10D){return new F(function(){return A2(_qC,_10D,_10B);});}),_ZY);});}},_107=function(_10E,_10F){return new F(function(){return _ZV(E(_10E),_10F);});},_10G=new T0(7),_10H=function(_10I,_10J){return new F(function(){return A1(_10J,_10G);});},_10K=new T(function(){return B(unCStr("TrueObs"));}),_10L=new T2(0,_10K,_10H),_10M=new T0(8),_10N=function(_10O,_10P){return new F(function(){return A1(_10P,_10M);});},_10Q=new T(function(){return B(unCStr("FalseObs"));}),_10R=new T2(0,_10Q,_10N),_10S=new T2(1,_10R,_1),_10T=new T2(1,_10L,_10S),_10U=new T(function(){return B(unCStr("ValueGE"));}),_10V=new T(function(){return B(unCStr("PersonChoseSomething"));}),_10W=new T(function(){return B(unCStr("PersonChoseThis"));}),_10X=new T(function(){return B(unCStr("BelowTimeout"));}),_10Y=new T(function(){return B(unCStr("AndObs"));}),_10Z=new T(function(){return B(unCStr("OrObs"));}),_110=new T(function(){return B(unCStr("NotObs"));}),_111=function(_112,_113){var _114=new T(function(){var _115=E(_112),_116=new T(function(){var _117=new T(function(){var _118=new T(function(){var _119=new T(function(){var _11a=new T(function(){var _11b=new T(function(){if(_115>10){return new T0(2);}else{var _11c=new T(function(){var _11d=new T(function(){var _11e=function(_11f){return new F(function(){return A3(_sM,_107,_ui,function(_11g){return new F(function(){return A1(_113,new T2(6,_11f,_11g));});});});};return B(A3(_sM,_107,_ui,_11e));});return B(_rV(function(_11h){var _11i=E(_11h);return (_11i._==3)?(!B(_gS(_11i.a,_10U)))?new T0(2):E(_11d):new T0(2);}));}),_11j=function(_11k){return E(_11c);};return new T1(1,function(_11l){return new F(function(){return A2(_qC,_11l,_11j);});});}});if(_115>10){return B(_ge(_eT,_11b));}else{var _11m=new T(function(){var _11n=new T(function(){var _11o=function(_11p){return new F(function(){return A3(_sX,_tq,_ui,function(_11q){return new F(function(){return A1(_113,new T2(5,_11p,_11q));});});});};return B(A3(_sM,_uv,_ui,_11o));});return B(_rV(function(_11r){var _11s=E(_11r);return (_11s._==3)?(!B(_gS(_11s.a,_10V)))?new T0(2):E(_11n):new T0(2);}));}),_11t=function(_11u){return E(_11m);};return B(_ge(new T1(1,function(_11v){return new F(function(){return A2(_qC,_11v,_11t);});}),_11b));}});if(_115>10){return B(_ge(_eT,_11a));}else{var _11w=new T(function(){var _11x=new T(function(){var _11y=function(_11z){var _11A=function(_11B){return new F(function(){return A3(_sX,_tq,_ui,function(_11C){return new F(function(){return A1(_113,new T3(4,_11z,_11B,_11C));});});});};return new F(function(){return A3(_sX,_tq,_ui,_11A);});};return B(A3(_sM,_uv,_ui,_11y));});return B(_rV(function(_11D){var _11E=E(_11D);return (_11E._==3)?(!B(_gS(_11E.a,_10W)))?new T0(2):E(_11x):new T0(2);}));}),_11F=function(_11G){return E(_11w);};return B(_ge(new T1(1,function(_11H){return new F(function(){return A2(_qC,_11H,_11F);});}),_11a));}});if(_115>10){return B(_ge(_eT,_119));}else{var _11I=new T(function(){var _11J=new T(function(){return B(A3(_sM,_111,_ui,function(_11K){return new F(function(){return A1(_113,new T1(3,_11K));});}));});return B(_rV(function(_11L){var _11M=E(_11L);return (_11M._==3)?(!B(_gS(_11M.a,_110)))?new T0(2):E(_11J):new T0(2);}));}),_11N=function(_11O){return E(_11I);};return B(_ge(new T1(1,function(_11P){return new F(function(){return A2(_qC,_11P,_11N);});}),_119));}});if(_115>10){return B(_ge(_eT,_118));}else{var _11Q=new T(function(){var _11R=new T(function(){var _11S=function(_11T){return new F(function(){return A3(_sM,_111,_ui,function(_11U){return new F(function(){return A1(_113,new T2(2,_11T,_11U));});});});};return B(A3(_sM,_111,_ui,_11S));});return B(_rV(function(_11V){var _11W=E(_11V);return (_11W._==3)?(!B(_gS(_11W.a,_10Z)))?new T0(2):E(_11R):new T0(2);}));}),_11X=function(_11Y){return E(_11Q);};return B(_ge(new T1(1,function(_11Z){return new F(function(){return A2(_qC,_11Z,_11X);});}),_118));}});if(_115>10){return B(_ge(_eT,_117));}else{var _120=new T(function(){var _121=new T(function(){var _122=function(_123){return new F(function(){return A3(_sM,_111,_ui,function(_124){return new F(function(){return A1(_113,new T2(1,_123,_124));});});});};return B(A3(_sM,_111,_ui,_122));});return B(_rV(function(_125){var _126=E(_125);return (_126._==3)?(!B(_gS(_126.a,_10Y)))?new T0(2):E(_121):new T0(2);}));}),_127=function(_128){return E(_120);};return B(_ge(new T1(1,function(_129){return new F(function(){return A2(_qC,_129,_127);});}),_117));}});if(_115>10){return B(_ge(_eT,_116));}else{var _12a=new T(function(){var _12b=new T(function(){return B(A3(_sX,_tq,_ui,function(_12c){return new F(function(){return A1(_113,new T1(0,_12c));});}));});return B(_rV(function(_12d){var _12e=E(_12d);return (_12e._==3)?(!B(_gS(_12e.a,_10X)))?new T0(2):E(_12b):new T0(2);}));}),_12f=function(_12g){return E(_12a);};return B(_ge(new T1(1,function(_12h){return new F(function(){return A2(_qC,_12h,_12f);});}),_116));}});return new F(function(){return _ge(B(_Yy(_10T,_112,_113)),_114);});},_12i=new T(function(){return B(unCStr("Null"));}),_12j=new T(function(){return B(unCStr("CommitCash"));}),_12k=new T(function(){return B(unCStr("RedeemCC"));}),_12l=new T(function(){return B(unCStr("Pay"));}),_12m=new T(function(){return B(unCStr("Both"));}),_12n=new T(function(){return B(unCStr("Choice"));}),_12o=new T(function(){return B(unCStr("When"));}),_12p=function(_12q,_12r){var _12s=new T(function(){var _12t=new T(function(){return B(A1(_12r,_Tt));});return B(_rV(function(_12u){var _12v=E(_12u);return (_12v._==3)?(!B(_gS(_12v.a,_12i)))?new T0(2):E(_12t):new T0(2);}));}),_12w=function(_12x){return E(_12s);},_12y=new T(function(){var _12z=E(_12q),_12A=new T(function(){var _12B=new T(function(){var _12C=new T(function(){var _12D=new T(function(){var _12E=new T(function(){if(_12z>10){return new T0(2);}else{var _12F=new T(function(){var _12G=new T(function(){var _12H=function(_12I){var _12J=function(_12K){var _12L=function(_12M){return new F(function(){return A3(_sM,_12p,_ui,function(_12N){return new F(function(){return A1(_12r,new T4(6,_12I,_12K,_12M,_12N));});});});};return new F(function(){return A3(_sM,_12p,_ui,_12L);});};return new F(function(){return A3(_sX,_tq,_ui,_12J);});};return B(A3(_sM,_111,_ui,_12H));});return B(_rV(function(_12O){var _12P=E(_12O);return (_12P._==3)?(!B(_gS(_12P.a,_12o)))?new T0(2):E(_12G):new T0(2);}));}),_12Q=function(_12R){return E(_12F);};return new T1(1,function(_12S){return new F(function(){return A2(_qC,_12S,_12Q);});});}});if(_12z>10){return B(_ge(_eT,_12E));}else{var _12T=new T(function(){var _12U=new T(function(){var _12V=function(_12W){var _12X=function(_12Y){return new F(function(){return A3(_sM,_12p,_ui,function(_12Z){return new F(function(){return A1(_12r,new T3(5,_12W,_12Y,_12Z));});});});};return new F(function(){return A3(_sM,_12p,_ui,_12X);});};return B(A3(_sM,_111,_ui,_12V));});return B(_rV(function(_130){var _131=E(_130);return (_131._==3)?(!B(_gS(_131.a,_12n)))?new T0(2):E(_12U):new T0(2);}));}),_132=function(_133){return E(_12T);};return B(_ge(new T1(1,function(_134){return new F(function(){return A2(_qC,_134,_132);});}),_12E));}});if(_12z>10){return B(_ge(_eT,_12D));}else{var _135=new T(function(){var _136=new T(function(){var _137=function(_138){return new F(function(){return A3(_sM,_12p,_ui,function(_139){return new F(function(){return A1(_12r,new T2(4,_138,_139));});});});};return B(A3(_sM,_12p,_ui,_137));});return B(_rV(function(_13a){var _13b=E(_13a);return (_13b._==3)?(!B(_gS(_13b.a,_12m)))?new T0(2):E(_136):new T0(2);}));}),_13c=function(_13d){return E(_135);};return B(_ge(new T1(1,function(_13e){return new F(function(){return A2(_qC,_13e,_13c);});}),_12D));}});if(_12z>10){return B(_ge(_eT,_12C));}else{var _13f=new T(function(){var _13g=new T(function(){var _13h=function(_13i){var _13j=function(_13k){var _13l=function(_13m){var _13n=function(_13o){var _13p=function(_13q){return new F(function(){return A3(_sM,_12p,_ui,function(_13r){return new F(function(){return A1(_12r,new T6(3,_13i,_13k,_13m,_13o,_13q,_13r));});});});};return new F(function(){return A3(_sX,_tq,_ui,_13p);});};return new F(function(){return A3(_sM,_107,_ui,_13n);});};return new F(function(){return A3(_sX,_tq,_ui,_13l);});};return new F(function(){return A3(_sX,_tq,_ui,_13j);});};return B(A3(_sM,_vW,_ui,_13h));});return B(_rV(function(_13s){var _13t=E(_13s);return (_13t._==3)?(!B(_gS(_13t.a,_12l)))?new T0(2):E(_13g):new T0(2);}));}),_13u=function(_13v){return E(_13f);};return B(_ge(new T1(1,function(_13w){return new F(function(){return A2(_qC,_13w,_13u);});}),_12C));}});if(_12z>10){return B(_ge(_eT,_12B));}else{var _13x=new T(function(){var _13y=new T(function(){var _13z=function(_13A){return new F(function(){return A3(_sM,_12p,_ui,function(_13B){return new F(function(){return A1(_12r,new T2(2,_13A,_13B));});});});};return B(A3(_sM,_wQ,_ui,_13z));});return B(_rV(function(_13C){var _13D=E(_13C);return (_13D._==3)?(!B(_gS(_13D.a,_12k)))?new T0(2):E(_13y):new T0(2);}));}),_13E=function(_13F){return E(_13x);};return B(_ge(new T1(1,function(_13G){return new F(function(){return A2(_qC,_13G,_13E);});}),_12B));}});if(_12z>10){return B(_ge(_eT,_12A));}else{var _13H=new T(function(){var _13I=new T(function(){var _13J=function(_13K){var _13L=function(_13M){var _13N=function(_13O){var _13P=function(_13Q){var _13R=function(_13S){var _13T=function(_13U){return new F(function(){return A3(_sM,_12p,_ui,function(_13V){return new F(function(){return A1(_12r,{_:1,a:_13K,b:_13M,c:_13O,d:_13Q,e:_13S,f:_13U,g:_13V});});});});};return new F(function(){return A3(_sM,_12p,_ui,_13T);});};return new F(function(){return A3(_sX,_tq,_ui,_13R);});};return new F(function(){return A3(_sX,_tq,_ui,_13P);});};return new F(function(){return A3(_sM,_107,_ui,_13N);});};return new F(function(){return A3(_sX,_tq,_ui,_13L);});};return B(A3(_sM,_wQ,_ui,_13J));});return B(_rV(function(_13W){var _13X=E(_13W);return (_13X._==3)?(!B(_gS(_13X.a,_12j)))?new T0(2):E(_13I):new T0(2);}));}),_13Y=function(_13Z){return E(_13H);};return B(_ge(new T1(1,function(_140){return new F(function(){return A2(_qC,_140,_13Y);});}),_12A));}});return new F(function(){return _ge(new T1(1,function(_141){return new F(function(){return A2(_qC,_141,_12w);});}),_12y);});},_142=new T(function(){return B(A3(_sM,_12p,_ss,_yF));}),_143=function(_144,_){var _145=__app0(E(_Y1)),_146=eval(E(_Y8)),_147=__app1(E(_146),toJSStr(E(_Y3))),_148=eval(E(_Y0)),_149=__app1(E(_148),toJSStr(E(_Y2))),_14a=__app1(E(_Y4),toJSStr(_ZH)),_14b=new T(function(){var _14c=B(_ZI(B(_g4(_ZF,new T(function(){var _14d=String(_149);return fromJSStr(_14d);})))));if(!_14c._){return E(_Ya);}else{if(!E(_14c.b)._){var _14e=E(_14c.a);return new T2(0,new T(function(){return B(_zV(_14e.a));}),new T(function(){return B(_4n(_14e.b));}));}else{return E(_Y9);}}}),_14f=new T(function(){var _14g=B(_ZI(B(_g4(_142,new T(function(){var _14h=String(_145);return fromJSStr(_14h);})))));if(!_14g._){return E(_ZQ);}else{if(!E(_14g.b)._){return E(_14g.a);}else{return E(_ZP);}}}),_14i=new T(function(){var _14j=B(_ZI(B(_g4(_Y7,new T(function(){var _14k=String(_147);return fromJSStr(_14k);})))));if(!_14j._){return E(_Y6);}else{if(!E(_14j.b)._){return E(_14j.a);}else{return E(_Y5);}}}),_14l=B(_XP(new T2(0,_ZG,_14i),_144,_14f,_14b));return new F(function(){return _BJ(_14l.a,_14l.b,_14l.c,_14l.d,_);});},_14m=new T(function(){return B(unCStr("contractInput"));}),_14n="(function (t, s) {window[t].setValue(s)})",_14o=function(_14p,_14q,_){var _14r=eval(E(_14n)),_14s=__app2(E(_14r),toJSStr(E(_14p)),toJSStr(E(_14q)));return new F(function(){return _A6(_);});},_14t=function(_14u,_14v,_14w,_){var _14x=E(_14m),_14y=toJSStr(_14x),_14z=eval(E(_Y0)),_14A=__app1(E(_14z),_14y),_14B=B(_ZI(B(_g4(_yK,new T(function(){var _14C=String(_14A);return fromJSStr(_14C);})))));if(!_14B._){return E(_eS);}else{if(!E(_14B.b)._){var _14D=E(_14B.a),_14E=new T(function(){return B(_8Q(new T(function(){return B(_jG(E(_14w)));}),new T(function(){return B(_jG(E(_14u)));}),new T(function(){return B(_jG(E(_14v)));}),B(_9V(_14D.c))));},1),_14F=B(_eC(new T(function(){return B(_bH(_14D.a));},1),new T(function(){return B(_8f(_14D.b));},1),_14E,new T(function(){return B(_4n(_14D.d));},1))),_14G=B(_14o(_14x,new T2(1,_14F.a,_14F.b),_)),_14H=__app1(E(_14z),_14y),_14I=new T(function(){var _14J=B(_ZI(B(_g4(_yK,new T(function(){var _14K=String(_14H);return fromJSStr(_14K);})))));if(!_14J._){return E(_eS);}else{if(!E(_14J.b)._){var _14L=E(_14J.a);return new T4(0,new T(function(){return B(_bH(_14L.a));}),new T(function(){return B(_8f(_14L.b));}),new T(function(){return B(_9V(_14L.c));}),new T(function(){return B(_4n(_14L.d));}));}else{return E(_eQ);}}});return new F(function(){return _143(_14I,_);});}else{return E(_eQ);}}},_14M=function(_14N,_14O,_14P,_14Q){var _14R=E(_14Q);if(!_14R._){var _14S=_14R.c,_14T=_14R.d,_14U=E(_14R.b);switch(B(_2(_14N,_14U.a))){case 0:return new F(function(){return _5q(_14U,B(_14M(_14N,_14O,_14P,_14S)),_14T);});break;case 1:switch(B(_2(_14O,_14U.b))){case 0:return new F(function(){return _5q(_14U,B(_14M(_14N,_14O,_14P,_14S)),_14T);});break;case 1:switch(B(_2(_14P,_14U.c))){case 0:return new F(function(){return _5q(_14U,B(_14M(_14N,_14O,_14P,_14S)),_14T);});break;case 1:return new T4(0,_14R.a,E(new T3(0,_14N,_14O,_14P)),E(_14S),E(_14T));default:return new F(function(){return _4G(_14U,_14S,B(_14M(_14N,_14O,_14P,_14T)));});}break;default:return new F(function(){return _4G(_14U,_14S,B(_14M(_14N,_14O,_14P,_14T)));});}break;default:return new F(function(){return _4G(_14U,_14S,B(_14M(_14N,_14O,_14P,_14T)));});}}else{return new T4(0,1,E(new T3(0,_14N,_14O,_14P)),E(_4B),E(_4B));}},_14V=function(_14W,_14X,_14Y,_){var _14Z=E(_14m),_150=toJSStr(_14Z),_151=eval(E(_Y0)),_152=__app1(E(_151),_150),_153=B(_ZI(B(_g4(_yK,new T(function(){var _154=String(_152);return fromJSStr(_154);})))));if(!_153._){return E(_eS);}else{if(!E(_153.b)._){var _155=E(_153.a),_156=new T(function(){return B(_14M(new T(function(){return B(_jG(E(_14Y)));}),new T(function(){return B(_jG(E(_14W)));}),new T(function(){return B(_jG(E(_14X)));}),B(_8f(_155.b))));},1),_157=B(_eC(new T(function(){return B(_bH(_155.a));},1),_156,new T(function(){return B(_9V(_155.c));},1),new T(function(){return B(_4n(_155.d));},1))),_158=B(_14o(_14Z,new T2(1,_157.a,_157.b),_)),_159=__app1(E(_151),_150),_15a=new T(function(){var _15b=B(_ZI(B(_g4(_yK,new T(function(){var _15c=String(_159);return fromJSStr(_15c);})))));if(!_15b._){return E(_eS);}else{if(!E(_15b.b)._){var _15d=E(_15b.a);return new T4(0,new T(function(){return B(_bH(_15d.a));}),new T(function(){return B(_8f(_15d.b));}),new T(function(){return B(_9V(_15d.c));}),new T(function(){return B(_4n(_15d.d));}));}else{return E(_eQ);}}});return new F(function(){return _143(_15a,_);});}else{return E(_eQ);}}},_15e=function(_15f,_15g,_15h,_15i,_){var _15j=E(_14m),_15k=toJSStr(_15j),_15l=eval(E(_Y0)),_15m=__app1(E(_15l),_15k),_15n=B(_ZI(B(_g4(_yK,new T(function(){var _15o=String(_15m);return fromJSStr(_15o);})))));if(!_15n._){return E(_eS);}else{if(!E(_15n.b)._){var _15p=E(_15n.a),_15q=new T(function(){return B(_aA(new T(function(){return B(_jG(E(_15h)));}),new T(function(){return B(_jG(E(_15f)));}),new T(function(){return B(_jG(E(_15g)));}),new T(function(){return B(_jG(E(_15i)));}),B(_bH(_15p.a))));},1),_15r=B(_eC(_15q,new T(function(){return B(_8f(_15p.b));},1),new T(function(){return B(_9V(_15p.c));},1),new T(function(){return B(_4n(_15p.d));},1))),_15s=B(_14o(_15j,new T2(1,_15r.a,_15r.b),_)),_15t=__app1(E(_15l),_15k),_15u=new T(function(){var _15v=B(_ZI(B(_g4(_yK,new T(function(){var _15w=String(_15t);return fromJSStr(_15w);})))));if(!_15v._){return E(_eS);}else{if(!E(_15v.b)._){var _15x=E(_15v.a);return new T4(0,new T(function(){return B(_bH(_15x.a));}),new T(function(){return B(_8f(_15x.b));}),new T(function(){return B(_9V(_15x.c));}),new T(function(){return B(_4n(_15x.d));}));}else{return E(_eQ);}}});return new F(function(){return _143(_15u,_);});}else{return E(_eQ);}}},_15y=new T(function(){return B(err(_eR));}),_15z=new T(function(){return B(unCStr("SICC"));}),_15A=new T(function(){return B(unCStr("SIRC"));}),_15B=new T(function(){return B(unCStr("SIP"));}),_15C=11,_15D=function(_15E,_15F){var _15G=new T(function(){var _15H=new T(function(){if(_15E>10){return new T0(2);}else{var _15I=new T(function(){var _15J=new T(function(){var _15K=function(_15L){var _15M=function(_15N){return new F(function(){return A3(_sX,_tq,_15C,function(_15O){return new F(function(){return A1(_15F,new T3(2,_15L,_15N,_15O));});});});};return new F(function(){return A3(_sX,_tq,_15C,_15M);});};return B(A3(_sM,_vW,_15C,_15K));});return B(_rV(function(_15P){var _15Q=E(_15P);return (_15Q._==3)?(!B(_gS(_15Q.a,_15B)))?new T0(2):E(_15J):new T0(2);}));}),_15R=function(_15S){return E(_15I);};return new T1(1,function(_15T){return new F(function(){return A2(_qC,_15T,_15R);});});}});if(_15E>10){return B(_ge(_eT,_15H));}else{var _15U=new T(function(){var _15V=new T(function(){var _15W=function(_15X){var _15Y=function(_15Z){return new F(function(){return A3(_sX,_tq,_15C,function(_160){return new F(function(){return A1(_15F,new T3(1,_15X,_15Z,_160));});});});};return new F(function(){return A3(_sX,_tq,_15C,_15Y);});};return B(A3(_sM,_wQ,_15C,_15W));});return B(_rV(function(_161){var _162=E(_161);return (_162._==3)?(!B(_gS(_162.a,_15A)))?new T0(2):E(_15V):new T0(2);}));}),_163=function(_164){return E(_15U);};return B(_ge(new T1(1,function(_165){return new F(function(){return A2(_qC,_165,_163);});}),_15H));}});if(_15E>10){return new F(function(){return _ge(_eT,_15G);});}else{var _166=new T(function(){var _167=new T(function(){var _168=function(_169){var _16a=function(_16b){var _16c=function(_16d){return new F(function(){return A3(_sX,_tq,_15C,function(_16e){return new F(function(){return A1(_15F,new T4(0,_169,_16b,_16d,_16e));});});});};return new F(function(){return A3(_sX,_tq,_15C,_16c);});};return new F(function(){return A3(_sX,_tq,_15C,_16a);});};return B(A3(_sM,_wQ,_15C,_168));});return B(_rV(function(_16f){var _16g=E(_16f);return (_16g._==3)?(!B(_gS(_16g.a,_15z)))?new T0(2):E(_167):new T0(2);}));}),_16h=function(_16i){return E(_166);};return new F(function(){return _ge(new T1(1,function(_16j){return new F(function(){return A2(_qC,_16j,_16h);});}),_15G);});}},_16k=function(_16l,_16m){return new F(function(){return _15D(E(_16l),_16m);});},_16n=new T(function(){return B(A3(_sM,_16k,_ss,_yF));}),_16o=function(_16p){var _16q=B(_ZI(B(_g4(_16n,_16p))));if(!_16q._){return E(_15y);}else{if(!E(_16q.b)._){var _16r=E(_16q.a);switch(_16r._){case 0:var _16s=new T(function(){return B(_bX(_16r.d));}),_16t=new T(function(){return B(_bX(_16r.a));}),_16u=new T(function(){return B(_bX(_16r.c));}),_16v=new T(function(){return B(_bX(_16r.b));});return function(_ue){return new F(function(){return _15e(_16v,_16u,_16t,_16s,_ue);});};case 1:var _16w=new T(function(){return B(_bX(_16r.a));}),_16x=new T(function(){return B(_bX(_16r.c));}),_16y=new T(function(){return B(_bX(_16r.b));});return function(_ue){return new F(function(){return _14V(_16y,_16x,_16w,_ue);});};default:var _16z=new T(function(){return B(_bX(_16r.a));}),_16A=new T(function(){return B(_bX(_16r.c));}),_16B=new T(function(){return B(_bX(_16r.b));});return function(_ue){return new F(function(){return _14t(_16B,_16A,_16z,_ue);});};}}else{return E(_c0);}}},_16C=function(_16D,_16E,_16F,_){var _16G=E(_14m),_16H=toJSStr(_16G),_16I=eval(E(_Y0)),_16J=__app1(E(_16I),_16H),_16K=B(_ZI(B(_g4(_yK,new T(function(){var _16L=String(_16J);return fromJSStr(_16L);})))));if(!_16K._){return E(_eS);}else{if(!E(_16K.b)._){var _16M=E(_16K.a),_16N=new T(function(){return B(_3i(new T(function(){return B(_jG(E(_16F)));}),new T(function(){return B(_jG(E(_16D)));}),new T(function(){return B(_jG(E(_16E)));}),B(_4n(_16M.d))));},1),_16O=B(_eC(new T(function(){return B(_bH(_16M.a));},1),new T(function(){return B(_8f(_16M.b));},1),new T(function(){return B(_9V(_16M.c));},1),_16N)),_16P=B(_14o(_16G,new T2(1,_16O.a,_16O.b),_)),_16Q=__app1(E(_16I),_16H),_16R=new T(function(){var _16S=B(_ZI(B(_g4(_yK,new T(function(){var _16T=String(_16Q);return fromJSStr(_16T);})))));if(!_16S._){return E(_eS);}else{if(!E(_16S.b)._){var _16U=E(_16S.a);return new T4(0,new T(function(){return B(_bH(_16U.a));}),new T(function(){return B(_8f(_16U.b));}),new T(function(){return B(_9V(_16U.c));}),new T(function(){return B(_4n(_16U.d));}));}else{return E(_eQ);}}});return new F(function(){return _143(_16R,_);});}else{return E(_eQ);}}},_16V=new T(function(){return B(err(_bZ));}),_16W=new T(function(){return B(err(_eR));}),_16X=new T(function(){return B(_v4(_uI,_uh,_yF));}),_16Y=function(_16Z,_170){var _171=new T(function(){var _172=B(_ZI(B(_g4(_16X,_16Z))));if(!_172._){return E(_16W);}else{if(!E(_172.b)._){var _173=E(_172.a);return new T2(0,_173.a,_173.b);}else{return E(_16V);}}}),_174=new T(function(){return B(_bU(E(_171).a));}),_175=new T(function(){return B(_bU(E(_171).b));});return function(_ue){return new F(function(){return _16C(_175,_170,_174,_ue);});};},_176=new T1(0,1),_177=function(_178,_179){var _17a=E(_178);return new T2(0,_17a,new T(function(){var _17b=B(_177(B(_ji(_17a,_179)),_179));return new T2(1,_17b.a,_17b.b);}));},_17c=function(_17d){var _17e=B(_177(_17d,_176));return new T2(1,_17e.a,_17e.b);},_17f=function(_17g,_17h){var _17i=B(_177(_17g,new T(function(){return B(_TG(_17h,_17g));})));return new T2(1,_17i.a,_17i.b);},_17j=new T1(0,0),_17k=function(_17l,_17m,_17n){if(!B(_e(_17m,_17j))){var _17o=function(_17p){return (!B(_co(_17p,_17n)))?new T2(1,_17p,new T(function(){return B(_17o(B(_ji(_17p,_17m))));})):__Z;};return new F(function(){return _17o(_17l);});}else{var _17q=function(_17r){return (!B(_CV(_17r,_17n)))?new T2(1,_17r,new T(function(){return B(_17q(B(_ji(_17r,_17m))));})):__Z;};return new F(function(){return _17q(_17l);});}},_17s=function(_17t,_17u,_17v){return new F(function(){return _17k(_17t,B(_TG(_17u,_17t)),_17v);});},_17w=function(_17x,_17y){return new F(function(){return _17k(_17x,_176,_17y);});},_17z=function(_17A){return new F(function(){return _bU(_17A);});},_17B=function(_17C){return new F(function(){return _TG(_17C,_176);});},_17D=function(_17E){return new F(function(){return _ji(_17E,_176);});},_17F=function(_17G){return new F(function(){return _jG(E(_17G));});},_17H={_:0,a:_17D,b:_17B,c:_17F,d:_17z,e:_17c,f:_17f,g:_17w,h:_17s},_17I=function(_17J,_17K){if(_17J<=0){if(_17J>=0){return new F(function(){return quot(_17J,_17K);});}else{if(_17K<=0){return new F(function(){return quot(_17J,_17K);});}else{return quot(_17J+1|0,_17K)-1|0;}}}else{if(_17K>=0){if(_17J>=0){return new F(function(){return quot(_17J,_17K);});}else{if(_17K<=0){return new F(function(){return quot(_17J,_17K);});}else{return quot(_17J+1|0,_17K)-1|0;}}}else{return quot(_17J-1|0,_17K)-1|0;}}},_17L=function(_17M,_17N){while(1){var _17O=E(_17M);if(!_17O._){var _17P=E(_17O.a);if(_17P==( -2147483648)){_17M=new T1(1,I_fromInt( -2147483648));continue;}else{var _17Q=E(_17N);if(!_17Q._){return new T1(0,B(_17I(_17P,_17Q.a)));}else{_17M=new T1(1,I_fromInt(_17P));_17N=_17Q;continue;}}}else{var _17R=_17O.a,_17S=E(_17N);return (_17S._==0)?new T1(1,I_div(_17R,I_fromInt(_17S.a))):new T1(1,I_div(_17R,_17S.a));}}},_17T=new T(function(){return B(unCStr("base"));}),_17U=new T(function(){return B(unCStr("GHC.Exception"));}),_17V=new T(function(){return B(unCStr("ArithException"));}),_17W=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_17T,_17U,_17V),_17X=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_17W,_1,_1),_17Y=function(_17Z){return E(_17X);},_180=function(_181){var _182=E(_181);return new F(function(){return _f5(B(_f3(_182.a)),_17Y,_182.b);});},_183=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_184=new T(function(){return B(unCStr("denormal"));}),_185=new T(function(){return B(unCStr("divide by zero"));}),_186=new T(function(){return B(unCStr("loss of precision"));}),_187=new T(function(){return B(unCStr("arithmetic underflow"));}),_188=new T(function(){return B(unCStr("arithmetic overflow"));}),_189=function(_18a,_18b){switch(E(_18a)){case 0:return new F(function(){return _ce(_188,_18b);});break;case 1:return new F(function(){return _ce(_187,_18b);});break;case 2:return new F(function(){return _ce(_186,_18b);});break;case 3:return new F(function(){return _ce(_185,_18b);});break;case 4:return new F(function(){return _ce(_184,_18b);});break;default:return new F(function(){return _ce(_183,_18b);});}},_18c=function(_18d){return new F(function(){return _189(_18d,_1);});},_18e=function(_18f,_18g,_18h){return new F(function(){return _189(_18g,_18h);});},_18i=function(_18j,_18k){return new F(function(){return _dQ(_189,_18j,_18k);});},_18l=new T3(0,_18e,_18c,_18i),_18m=new T(function(){return new T5(0,_17Y,_18l,_18n,_180,_18c);}),_18n=function(_fE){return new T2(0,_18m,_fE);},_18o=3,_18p=new T(function(){return B(_18n(_18o));}),_18q=new T(function(){return die(_18p);}),_18r=new T1(0,0),_18s=function(_18t,_18u){if(!B(_C1(_18u,_18r))){return new F(function(){return _17L(_18t,_18u);});}else{return E(_18q);}},_18v=function(_18w,_18x){var _18y=_18w%_18x;if(_18w<=0){if(_18w>=0){return E(_18y);}else{if(_18x<=0){return E(_18y);}else{var _18z=E(_18y);return (_18z==0)?0:_18z+_18x|0;}}}else{if(_18x>=0){if(_18w>=0){return E(_18y);}else{if(_18x<=0){return E(_18y);}else{var _18A=E(_18y);return (_18A==0)?0:_18A+_18x|0;}}}else{var _18B=E(_18y);return (_18B==0)?0:_18B+_18x|0;}}},_18C=function(_18D,_18E){while(1){var _18F=E(_18D);if(!_18F._){var _18G=E(_18F.a);if(_18G==( -2147483648)){_18D=new T1(1,I_fromInt( -2147483648));continue;}else{var _18H=E(_18E);if(!_18H._){var _18I=_18H.a;return new T2(0,new T1(0,B(_17I(_18G,_18I))),new T1(0,B(_18v(_18G,_18I))));}else{_18D=new T1(1,I_fromInt(_18G));_18E=_18H;continue;}}}else{var _18J=E(_18E);if(!_18J._){_18D=_18F;_18E=new T1(1,I_fromInt(_18J.a));continue;}else{var _18K=I_divMod(_18F.a,_18J.a);return new T2(0,new T1(1,_18K.a),new T1(1,_18K.b));}}}},_18L=function(_18M,_18N){if(!B(_C1(_18N,_18r))){var _18O=B(_18C(_18M,_18N));return new T2(0,_18O.a,_18O.b);}else{return E(_18q);}},_18P=function(_18Q,_18R){while(1){var _18S=E(_18Q);if(!_18S._){var _18T=E(_18S.a);if(_18T==( -2147483648)){_18Q=new T1(1,I_fromInt( -2147483648));continue;}else{var _18U=E(_18R);if(!_18U._){return new T1(0,B(_18v(_18T,_18U.a)));}else{_18Q=new T1(1,I_fromInt(_18T));_18R=_18U;continue;}}}else{var _18V=_18S.a,_18W=E(_18R);return (_18W._==0)?new T1(1,I_mod(_18V,I_fromInt(_18W.a))):new T1(1,I_mod(_18V,_18W.a));}}},_18X=function(_18Y,_18Z){if(!B(_C1(_18Z,_18r))){return new F(function(){return _18P(_18Y,_18Z);});}else{return E(_18q);}},_190=function(_191,_192){while(1){var _193=E(_191);if(!_193._){var _194=E(_193.a);if(_194==( -2147483648)){_191=new T1(1,I_fromInt( -2147483648));continue;}else{var _195=E(_192);if(!_195._){return new T1(0,quot(_194,_195.a));}else{_191=new T1(1,I_fromInt(_194));_192=_195;continue;}}}else{var _196=_193.a,_197=E(_192);return (_197._==0)?new T1(0,I_toInt(I_quot(_196,I_fromInt(_197.a)))):new T1(1,I_quot(_196,_197.a));}}},_198=function(_199,_19a){if(!B(_C1(_19a,_18r))){return new F(function(){return _190(_199,_19a);});}else{return E(_18q);}},_19b=function(_19c,_19d){while(1){var _19e=E(_19c);if(!_19e._){var _19f=E(_19e.a);if(_19f==( -2147483648)){_19c=new T1(1,I_fromInt( -2147483648));continue;}else{var _19g=E(_19d);if(!_19g._){var _19h=_19g.a;return new T2(0,new T1(0,quot(_19f,_19h)),new T1(0,_19f%_19h));}else{_19c=new T1(1,I_fromInt(_19f));_19d=_19g;continue;}}}else{var _19i=E(_19d);if(!_19i._){_19c=_19e;_19d=new T1(1,I_fromInt(_19i.a));continue;}else{var _19j=I_quotRem(_19e.a,_19i.a);return new T2(0,new T1(1,_19j.a),new T1(1,_19j.b));}}}},_19k=function(_19l,_19m){if(!B(_C1(_19m,_18r))){var _19n=B(_19b(_19l,_19m));return new T2(0,_19n.a,_19n.b);}else{return E(_18q);}},_19o=function(_19p,_19q){while(1){var _19r=E(_19p);if(!_19r._){var _19s=E(_19r.a);if(_19s==( -2147483648)){_19p=new T1(1,I_fromInt( -2147483648));continue;}else{var _19t=E(_19q);if(!_19t._){return new T1(0,_19s%_19t.a);}else{_19p=new T1(1,I_fromInt(_19s));_19q=_19t;continue;}}}else{var _19u=_19r.a,_19v=E(_19q);return (_19v._==0)?new T1(1,I_rem(_19u,I_fromInt(_19v.a))):new T1(1,I_rem(_19u,_19v.a));}}},_19w=function(_19x,_19y){if(!B(_C1(_19y,_18r))){return new F(function(){return _19o(_19x,_19y);});}else{return E(_18q);}},_19z=function(_19A){return E(_19A);},_19B=function(_19C){return E(_19C);},_19D=function(_19E){var _19F=E(_19E);if(!_19F._){var _19G=E(_19F.a);return (_19G==( -2147483648))?E(_jr):(_19G<0)?new T1(0, -_19G):E(_19F);}else{var _19H=_19F.a;return (I_compareInt(_19H,0)>=0)?E(_19F):new T1(1,I_negate(_19H));}},_19I=new T1(0,0),_19J=new T1(0, -1),_19K=function(_19L){var _19M=E(_19L);if(!_19M._){var _19N=_19M.a;return (_19N>=0)?(E(_19N)==0)?E(_19I):E(_jg):E(_19J);}else{var _19O=I_compareInt(_19M.a,0);return (_19O<=0)?(E(_19O)==0)?E(_19I):E(_19J):E(_jg);}},_19P={_:0,a:_ji,b:_TG,c:_jM,d:_js,e:_19D,f:_19K,g:_19B},_19Q={_:0,a:_Ry,b:_2,c:_co,d:_lm,e:_CV,f:_e,g:_Oj,h:_Om},_19R=new T1(0,1),_19S=function(_19T){return new T2(0,E(_19T),E(_19R));},_19U=new T3(0,_19P,_19Q,_19S),_19V={_:0,a:_19U,b:_17H,c:_198,d:_19w,e:_18s,f:_18X,g:_19k,h:_18L,i:_19z},_19W=new T(function(){return B(unCStr("head"));}),_19X=new T(function(){return B(_dn(_19W));}),_19Y=function(_19Z){return new F(function(){return _cz(0,_19Z,_1);});},_1a0=new T(function(){return B(unCStr("IdentPay"));}),_1a1=new T(function(){return B(unCStr("ValueGE"));}),_1a2=new T(function(){return B(unCStr("PersonChoseSomething"));}),_1a3=new T(function(){return B(unCStr("PersonChoseThis"));}),_1a4=new T(function(){return B(unCStr("NotObs"));}),_1a5=new T(function(){return B(unCStr("OrObs"));}),_1a6=new T(function(){return B(unCStr("AndObs"));}),_1a7=new T(function(){return B(unCStr("BelowTimeout"));}),_1a8=new T(function(){return B(unCStr("When"));}),_1a9=new T(function(){return B(unCStr("Choice"));}),_1aa=new T(function(){return B(unCStr("Both"));}),_1ab=new T(function(){return B(unCStr("IdentChoice"));}),_1ac=new T(function(){return B(unCStr("Pay"));}),_1ad=new T(function(){return B(unCStr("RedeemCC"));}),_1ae=new T(function(){return B(unCStr("CommitCash"));}),_1af=new T(function(){return B(unCStr("Null"));}),_1ag=new T(function(){return B(unCStr("IdentCC"));}),_1ah=new T(function(){return B(unCStr("MoneyFromChoice"));}),_1ai=new T(function(){return B(unCStr("ConstMoney"));}),_1aj=new T(function(){return B(unCStr("AddMoney"));}),_1ak=new T(function(){return B(unCStr("AvailableMoney"));}),_1al=new T(function(){return B(unCStr("FalseObs"));}),_1am=new T(function(){return B(unCStr("TrueObs"));}),_1an=function(_1ao){var _1ap=E(_1ao);switch(_1ap._){case 0:var _1aq=E(_1ap.a);switch(_1aq._){case 0:return new T2(0,_1af,_1);case 1:return new T2(0,_1ae,new T2(1,new T1(3,_1aq.a),new T2(1,new T1(6,_1aq.b),new T2(1,new T1(2,_1aq.c),new T2(1,new T1(6,_1aq.d),new T2(1,new T1(6,_1aq.e),new T2(1,new T1(0,_1aq.f),new T2(1,new T1(0,_1aq.g),_1))))))));case 2:return new T2(0,_1ad,new T2(1,new T1(3,_1aq.a),new T2(1,new T1(0,_1aq.b),_1)));case 3:return new T2(0,_1ac,new T2(1,new T1(5,_1aq.a),new T2(1,new T1(6,_1aq.b),new T2(1,new T1(6,_1aq.c),new T2(1,new T1(2,_1aq.d),new T2(1,new T1(6,_1aq.e),new T2(1,new T1(0,_1aq.f),_1)))))));case 4:return new T2(0,_1aa,new T2(1,new T1(0,_1aq.a),new T2(1,new T1(0,_1aq.b),_1)));case 5:return new T2(0,_1a9,new T2(1,new T1(1,_1aq.a),new T2(1,new T1(0,_1aq.b),new T2(1,new T1(0,_1aq.c),_1))));default:return new T2(0,_1a8,new T2(1,new T1(1,_1aq.a),new T2(1,new T1(6,_1aq.b),new T2(1,new T1(0,_1aq.c),new T2(1,new T1(0,_1aq.d),_1)))));}break;case 1:var _1ar=E(_1ap.a);switch(_1ar._){case 0:return new T2(0,_1a7,new T2(1,new T1(6,_1ar.a),_1));case 1:return new T2(0,_1a6,new T2(1,new T1(1,_1ar.a),new T2(1,new T1(1,_1ar.b),_1)));case 2:return new T2(0,_1a5,new T2(1,new T1(1,_1ar.a),new T2(1,new T1(1,_1ar.b),_1)));case 3:return new T2(0,_1a4,new T2(1,new T1(1,_1ar.a),_1));case 4:return new T2(0,_1a3,new T2(1,new T1(4,_1ar.a),new T2(1,new T1(6,_1ar.b),new T2(1,new T1(6,_1ar.c),_1))));case 5:return new T2(0,_1a2,new T2(1,new T1(4,_1ar.a),new T2(1,new T1(6,_1ar.b),_1)));case 6:return new T2(0,_1a1,new T2(1,new T1(2,_1ar.a),new T2(1,new T1(2,_1ar.b),_1)));case 7:return new T2(0,_1am,_1);default:return new T2(0,_1al,_1);}break;case 2:var _1as=E(_1ap.a);switch(_1as._){case 0:return new T2(0,_1ak,new T2(1,new T1(3,_1as.a),_1));case 1:return new T2(0,_1aj,new T2(1,new T1(2,_1as.a),new T2(1,new T1(2,_1as.b),_1)));case 2:return new T2(0,_1ai,new T2(1,new T1(6,_1as.a),_1));default:return new T2(0,_1ah,new T2(1,new T1(4,_1as.a),new T2(1,new T1(6,_1as.b),new T2(1,new T1(2,_1as.c),_1))));}break;case 3:return new T2(0,_1ag,new T2(1,new T1(6,_1ap.a),_1));case 4:return new T2(0,_1ab,new T2(1,new T1(6,_1ap.a),_1));case 5:return new T2(0,_1a0,new T2(1,new T1(6,_1ap.a),_1));default:return new T2(0,new T(function(){return B(_19Y(_1ap.a));}),_1);}},_1at=function(_1au){var _1av=B(_1an(_1au)),_1aw=_1av.a,_1ax=E(_1av.b);if(!_1ax._){return new T1(0,new T2(0,_1aw,_1));}else{switch(E(_1au)._){case 0:return new T1(2,new T2(0,_1aw,_1ax));case 1:return new T1(2,new T2(0,_1aw,_1ax));case 2:return new T1(2,new T2(0,_1aw,_1ax));default:return new T1(1,new T2(0,_1aw,_1ax));}}},_1ay=function(_1az){return E(E(_1az).a);},_1aA=function(_1aB){return E(E(_1aB).a);},_1aC=function(_1aD){return E(E(_1aD).b);},_1aE=function(_1aF){return E(E(_1aF).b);},_1aG=function(_1aH){return E(E(_1aH).g);},_1aI=new T1(0,0),_1aJ=new T1(0,1),_1aK=function(_1aL,_1aM,_1aN){var _1aO=B(_1ay(_1aL)),_1aP=new T(function(){return B(_1aA(_1aO));});if(!B(A3(_IF,B(_1aC(_1aO)),_1aM,new T(function(){return B(A2(_1aG,_1aP,_1aI));})))){var _1aQ=E(_1aN);if(!_1aQ._){return __Z;}else{var _1aR=new T(function(){var _1aS=new T(function(){return B(A3(_1aE,_1aP,_1aM,new T(function(){return B(A2(_1aG,_1aP,_1aJ));})));});return B(_1aK(_1aL,_1aS,_1aQ.b));});return new T2(1,_1aQ.a,_1aR);}}else{return __Z;}},_1aT=function(_1aU,_1aV){var _1aW=E(_1aV);if(!_1aW._){return __Z;}else{var _1aX=_1aW.a,_1aY=new T(function(){var _1aZ=B(_fF(new T(function(){return B(A1(_1aU,_1aX));}),_1aW.b));return new T2(0,_1aZ.a,_1aZ.b);});return new T2(1,new T2(1,_1aX,new T(function(){return E(E(_1aY).a);})),new T(function(){return B(_1aT(_1aU,E(_1aY).b));}));}},_1b0=function(_1b1){var _1b2=E(_1b1);if(!_1b2._){return __Z;}else{return new F(function(){return _ce(_1b2.a,new T(function(){return B(_1b0(_1b2.b));},1));});}},_1b3=new T(function(){return B(unCStr("\n"));}),_1b4=new T1(0,1),_1b5=function(_1b6,_1b7){return (E(_1b6)._==2)?false:(E(_1b7)._==2)?false:true;},_1b8=function(_1b9,_1ba){var _1bb=E(_1ba);return (_1bb._==0)?__Z:new T2(1,_1b9,new T2(1,_1bb.a,new T(function(){return B(_1b8(_1b9,_1bb.b));})));},_1bc=new T(function(){return B(unCStr("tail"));}),_1bd=new T(function(){return B(_dn(_1bc));}),_1be=new T(function(){return B(unCStr(")"));}),_1bf=new T1(0,0),_1bg=function(_1bh,_1bi){var _1bj=E(_1bi);switch(_1bj._){case 0:var _1bk=E(_1bj.a);return new F(function(){return _1bl(_1bf,_1bk.a,_1bk.b);});break;case 1:return new F(function(){return unAppCStr("(",new T(function(){var _1bm=E(_1bj.a);return B(_ce(B(_1bl(_1bf,_1bm.a,_1bm.b)),_1be));}));});break;default:var _1bn=new T(function(){var _1bo=E(_1bj.a);return B(_ce(B(_1bl(new T(function(){return B(_ji(_1bh,_1b4));},1),_1bo.a,_1bo.b)),_1be));});return new F(function(){return unAppCStr("(",_1bn);});}},_1bp=function(_1bq){return E(E(_1bq).a);},_1br=function(_1bs,_1bt){var _1bu=new T(function(){return B(A2(_1aG,_1bs,_1aJ));}),_1bv=function(_1bw,_1bx){while(1){var _1by=E(_1bw);if(!_1by._){return E(_1bx);}else{var _1bz=B(A3(_1bp,_1bs,_1bx,_1bu));_1bw=_1by.b;_1bx=_1bz;continue;}}};return new F(function(){return _1bv(_1bt,new T(function(){return B(A2(_1aG,_1bs,_1aI));}));});},_1bA=32,_1bB=new T(function(){return new T2(1,_1bA,_1bB);}),_1bl=function(_1bC,_1bD,_1bE){var _1bF=E(_1bE);if(!_1bF._){return E(_1bD);}else{var _1bG=new T(function(){return B(_ji(B(_ji(_1bC,B(_1br(_19P,_1bD)))),_1b4));}),_1bH=new T(function(){return B(_1aT(_1b5,B(_jC(_1at,_1bF))));}),_1bI=new T(function(){var _1bJ=E(_1bH);if(!_1bJ._){return E(_1bd);}else{var _1bK=new T(function(){return B(_1aK(_19V,_1bG,_1bB));}),_1bL=function(_1bM){var _1bN=new T(function(){var _1bO=function(_1bP){var _1bQ=E(_1bP);if(!_1bQ._){return __Z;}else{var _1bR=new T(function(){return B(_ce(B(_1bg(_1bG,_1bQ.a)),new T(function(){return B(_1bO(_1bQ.b));},1)));});return new T2(1,_1bA,_1bR);}},_1bS=B(_1bO(_1bM));if(!_1bS._){return __Z;}else{return E(_1bS.b);}},1);return new F(function(){return _ce(_1bK,_1bN);});};return B(_1b8(_1b3,B(_jC(_1bL,_1bJ.b))));}}),_1bT=new T(function(){var _1bU=new T(function(){var _1bV=E(_1bH);if(!_1bV._){return E(_19X);}else{var _1bW=function(_1bX){var _1bY=E(_1bX);if(!_1bY._){return __Z;}else{var _1bZ=new T(function(){return B(_ce(B(_1bg(_1bG,_1bY.a)),new T(function(){return B(_1bW(_1bY.b));},1)));});return new T2(1,_1bA,_1bZ);}};return B(_1bW(_1bV.a));}},1);return B(_ce(_1bD,_1bU));});return new F(function(){return _1b0(new T2(1,_1bT,_1bI));});}},_1c0=new T(function(){return B(_1bl(_1bf,_1af,_1));}),_1c1=function(_1c2,_){return new T(function(){var _1c3=B(_ZI(B(_g4(_142,_1c2))));if(!_1c3._){return E(_ZQ);}else{if(!E(_1c3.b)._){var _1c4=E(_1c3.a);switch(_1c4._){case 0:return E(_1c0);break;case 1:return B(_1bl(_1bf,_1ae,new T2(1,new T1(3,_1c4.a),new T2(1,new T1(6,_1c4.b),new T2(1,new T1(2,_1c4.c),new T2(1,new T1(6,_1c4.d),new T2(1,new T1(6,_1c4.e),new T2(1,new T1(0,_1c4.f),new T2(1,new T1(0,_1c4.g),_1)))))))));break;case 2:return B(_1bl(_1bf,_1ad,new T2(1,new T1(3,_1c4.a),new T2(1,new T1(0,_1c4.b),_1))));break;case 3:return B(_1bl(_1bf,_1ac,new T2(1,new T1(5,_1c4.a),new T2(1,new T1(6,_1c4.b),new T2(1,new T1(6,_1c4.c),new T2(1,new T1(2,_1c4.d),new T2(1,new T1(6,_1c4.e),new T2(1,new T1(0,_1c4.f),_1))))))));break;case 4:return B(_1bl(_1bf,_1aa,new T2(1,new T1(0,_1c4.a),new T2(1,new T1(0,_1c4.b),_1))));break;case 5:return B(_1bl(_1bf,_1a9,new T2(1,new T1(1,_1c4.a),new T2(1,new T1(0,_1c4.b),new T2(1,new T1(0,_1c4.c),_1)))));break;default:return B(_1bl(_1bf,_1a8,new T2(1,new T1(1,_1c4.a),new T2(1,new T1(6,_1c4.b),new T2(1,new T1(0,_1c4.c),new T2(1,new T1(0,_1c4.d),_1))))));}}else{return E(_ZP);}}});},_1c5=new T(function(){return B(unCStr("codeArea"));}),_1c6=function(_){var _1c7=__app0(E(_Y1)),_1c8=B(_1c1(new T(function(){var _1c9=String(_1c7);return fromJSStr(_1c9);}),_)),_1ca=B(_14o(_1c5,_1c8,_)),_1cb=eval(E(_Y0)),_1cc=__app1(E(_1cb),toJSStr(E(_14m))),_1cd=new T(function(){var _1ce=B(_ZI(B(_g4(_yK,new T(function(){var _1cf=String(_1cc);return fromJSStr(_1cf);})))));if(!_1ce._){return E(_eS);}else{if(!E(_1ce.b)._){var _1cg=E(_1ce.a);return new T4(0,new T(function(){return B(_bH(_1cg.a));}),new T(function(){return B(_8f(_1cg.b));}),new T(function(){return B(_9V(_1cg.c));}),new T(function(){return B(_4n(_1cg.d));}));}else{return E(_eQ);}}});return new F(function(){return _143(_1cd,_);});},_1ch="(function (b) { return (b.inputList.length); })",_1ci="(function (b, x) { return (b.inputList[x]); })",_1cj=function(_1ck,_1cl,_){var _1cm=eval(E(_1ci)),_1cn=__app2(E(_1cm),_1ck,_1cl);return new T1(0,_1cn);},_1co=function(_1cp,_1cq,_1cr,_){var _1cs=E(_1cr);if(!_1cs._){return _1;}else{var _1ct=B(_1cj(_1cp,E(_1cs.a),_)),_1cu=B(_1co(_1cp,_,_1cs.b,_));return new T2(1,_1ct,_1cu);}},_1cv=function(_1cw,_1cx){if(_1cw<=_1cx){var _1cy=function(_1cz){return new T2(1,_1cz,new T(function(){if(_1cz!=_1cx){return B(_1cy(_1cz+1|0));}else{return __Z;}}));};return new F(function(){return _1cy(_1cw);});}else{return __Z;}},_1cA=function(_1cB,_){var _1cC=eval(E(_1ch)),_1cD=__app1(E(_1cC),_1cB),_1cE=Number(_1cD),_1cF=jsTrunc(_1cE);return new F(function(){return _1co(_1cB,_,new T(function(){return B(_1cv(0,_1cF-1|0));}),_);});},_1cG="(function (y, ip) {y.previousConnection.connect(ip.connection);})",_1cH="(function (x) { return x.name; })",_1cI=new T(function(){return B(unCStr("\""));}),_1cJ=function(_1cK){return new F(function(){return err(B(unAppCStr("No input matches \"",new T(function(){return B(_ce(_1cK,_1cI));}))));});},_1cL=function(_1cM,_1cN,_){var _1cO=E(_1cN);if(!_1cO._){return new F(function(){return _1cJ(_1cM);});}else{var _1cP=E(_1cO.a),_1cQ=E(_1cH),_1cR=eval(_1cQ),_1cS=__app1(E(_1cR),E(_1cP.a)),_1cT=String(_1cS);if(!B(_gS(fromJSStr(_1cT),_1cM))){var _1cU=function(_1cV,_1cW,_){while(1){var _1cX=E(_1cW);if(!_1cX._){return new F(function(){return _1cJ(_1cV);});}else{var _1cY=E(_1cX.a),_1cZ=eval(_1cQ),_1d0=__app1(E(_1cZ),E(_1cY.a)),_1d1=String(_1d0);if(!B(_gS(fromJSStr(_1d1),_1cV))){_1cW=_1cX.b;continue;}else{return _1cY;}}}};return new F(function(){return _1cU(_1cM,_1cO.b,_);});}else{return _1cP;}}},_1d2=function(_1d3,_1d4,_1d5,_){var _1d6=B(_1cA(_1d4,_)),_1d7=B(_1cL(_1d3,_1d6,_)),_1d8=eval(E(_1cG)),_1d9=__app2(E(_1d8),E(E(_1d5).a),E(E(_1d7).a));return new F(function(){return _A6(_);});},_1da="(function (y, ip) {y.outputConnection.connect(ip.connection);})",_1db=function(_1dc,_1dd,_1de,_){var _1df=B(_1cA(_1dd,_)),_1dg=B(_1cL(_1dc,_1df,_)),_1dh=eval(E(_1da)),_1di=__app2(E(_1dh),E(E(_1de).a),E(E(_1dg).a));return new F(function(){return _A6(_);});},_1dj=function(_1dk){return new F(function(){return err(B(unAppCStr("No fieldrow matches \"",new T(function(){return B(_ce(_1dk,_1cI));}))));});},_1dl=function(_1dm,_1dn,_){var _1do=E(_1dn);if(!_1do._){return new F(function(){return _1dj(_1dm);});}else{var _1dp=E(_1do.a),_1dq=E(_1cH),_1dr=eval(_1dq),_1ds=__app1(E(_1dr),E(_1dp.a)),_1dt=String(_1ds);if(!B(_gS(fromJSStr(_1dt),_1dm))){var _1du=function(_1dv,_1dw,_){while(1){var _1dx=E(_1dw);if(!_1dx._){return new F(function(){return _1dj(_1dv);});}else{var _1dy=E(_1dx.a),_1dz=eval(_1dq),_1dA=__app1(E(_1dz),E(_1dy.a)),_1dB=String(_1dA);if(!B(_gS(fromJSStr(_1dB),_1dv))){_1dw=_1dx.b;continue;}else{return _1dy;}}}};return new F(function(){return _1du(_1dm,_1do.b,_);});}else{return _1dp;}}},_1dC="(function (b) { return (b.fieldRow.length); })",_1dD="(function (b, x) { return (b.fieldRow[x]); })",_1dE=function(_1dF,_1dG,_){var _1dH=eval(E(_1dD)),_1dI=__app2(E(_1dH),_1dF,_1dG);return new T1(0,_1dI);},_1dJ=function(_1dK,_1dL,_1dM,_){var _1dN=E(_1dM);if(!_1dN._){return _1;}else{var _1dO=B(_1dE(_1dK,E(_1dN.a),_)),_1dP=B(_1dJ(_1dK,_,_1dN.b,_));return new T2(1,_1dO,_1dP);}},_1dQ=function(_1dR,_){var _1dS=eval(E(_1dC)),_1dT=__app1(E(_1dS),_1dR),_1dU=Number(_1dT),_1dV=jsTrunc(_1dU);return new F(function(){return _1dJ(_1dR,_,new T(function(){return B(_1cv(0,_1dV-1|0));}),_);});},_1dW=function(_1dX,_){var _1dY=E(_1dX);if(!_1dY._){return _1;}else{var _1dZ=B(_1dQ(E(E(_1dY.a).a),_)),_1e0=B(_1dW(_1dY.b,_));return new T2(1,_1dZ,_1e0);}},_1e1=function(_1e2){var _1e3=E(_1e2);if(!_1e3._){return __Z;}else{return new F(function(){return _ce(_1e3.a,new T(function(){return B(_1e1(_1e3.b));},1));});}},_1e4=function(_1e5,_1e6,_){var _1e7=B(_1cA(_1e6,_)),_1e8=B(_1dW(_1e7,_));return new F(function(){return _1dl(_1e5,B(_1e1(_1e8)),_);});},_1e9=function(_1ea,_1eb,_1ec,_){var _1ed=B(_1cA(_1eb,_)),_1ee=B(_1cL(_1ea,_1ed,_)),_1ef=eval(E(_1da)),_1eg=__app2(E(_1ef),E(E(_1ec).a),E(E(_1ee).a));return new F(function(){return _A6(_);});},_1eh=new T(function(){return B(unCStr("contract_commitcash"));}),_1ei=new T(function(){return B(unCStr("contract_redeemcc"));}),_1ej=new T(function(){return B(unCStr("contract_pay"));}),_1ek=new T(function(){return B(unCStr("contract_both"));}),_1el=new T(function(){return B(unCStr("contract_choice"));}),_1em=new T(function(){return B(unCStr("contract_when"));}),_1en="(function (x) {var c = demoWorkspace.newBlock(x); c.initSvg(); return c;})",_1eo=function(_1ep,_){var _1eq=eval(E(_1en)),_1er=__app1(E(_1eq),toJSStr(E(_1ep)));return new T1(0,_1er);},_1es=new T(function(){return B(unCStr("payer_id"));}),_1et=new T(function(){return B(unCStr("pay_id"));}),_1eu=new T(function(){return B(unCStr("ccommit_id"));}),_1ev=new T(function(){return B(unCStr("end_expiration"));}),_1ew=new T(function(){return B(unCStr("start_expiration"));}),_1ex=new T(function(){return B(unCStr("person_id"));}),_1ey=new T(function(){return B(unCStr("contract_null"));}),_1ez=new T(function(){return B(unCStr("contract2"));}),_1eA=new T(function(){return B(unCStr("contract1"));}),_1eB=new T(function(){return B(unCStr("observation"));}),_1eC=new T(function(){return B(unCStr("timeout"));}),_1eD=new T(function(){return B(unCStr("contract"));}),_1eE=new T(function(){return B(unCStr("expiration"));}),_1eF=new T(function(){return B(unCStr("ammount"));}),_1eG=new T(function(){return B(unCStr("payee_id"));}),_1eH=new T(function(){return B(unCStr("value_available_money"));}),_1eI=new T(function(){return B(unCStr("value_add_money"));}),_1eJ=new T(function(){return B(unCStr("value_const_money"));}),_1eK=new T(function(){return B(unCStr("money_from_choice"));}),_1eL=new T(function(){return B(unCStr("value2"));}),_1eM=new T(function(){return B(unCStr("value1"));}),_1eN=new T(function(){return B(unCStr("choice_id"));}),_1eO=new T(function(){return B(unCStr("default"));}),_1eP=new T(function(){return B(unCStr("money"));}),_1eQ=new T(function(){return B(unCStr("commit_id"));}),_1eR="(function (b, s) { return (b.setText(s)); })",_1eS=function(_1eT,_){var _1eU=E(_1eT);switch(_1eU._){case 0:var _1eV=B(_1eo(_1eH,_)),_1eW=E(_1eV),_1eX=B(_1e4(_1eQ,E(_1eW.a),_)),_1eY=eval(E(_1eR)),_1eZ=__app2(E(_1eY),E(E(_1eX).a),toJSStr(B(_cz(0,_1eU.a,_1))));return _1eW;case 1:var _1f0=B(_1eS(_1eU.a,_)),_1f1=B(_1eS(_1eU.b,_)),_1f2=B(_1eo(_1eI,_)),_1f3=E(_1f2),_1f4=E(_1f3.a),_1f5=B(_1db(_1eM,_1f4,_1f0,_)),_1f6=B(_1db(_1eL,_1f4,_1f1,_));return _1f3;case 2:var _1f7=B(_1eo(_1eJ,_)),_1f8=E(_1f7),_1f9=B(_1e4(_1eP,E(_1f8.a),_)),_1fa=eval(E(_1eR)),_1fb=__app2(E(_1fa),E(E(_1f9).a),toJSStr(B(_cz(0,_1eU.a,_1))));return _1f8;default:var _1fc=B(_1eS(_1eU.c,_)),_1fd=B(_1eo(_1eK,_)),_1fe=E(_1fd),_1ff=E(_1fe.a),_1fg=B(_1e4(_1eN,_1ff,_)),_1fh=eval(E(_1eR)),_1fi=__app2(E(_1fh),E(E(_1fg).a),toJSStr(B(_cz(0,_1eU.a,_1)))),_1fj=B(_1e4(_1ex,_1ff,_)),_1fk=__app2(E(_1fh),E(E(_1fj).a),toJSStr(B(_cz(0,_1eU.b,_1)))),_1fl=B(_1db(_1eO,_1ff,_1fc,_));return _1fe;}},_1fm=new T(function(){return B(unCStr("observation_personchosethis"));}),_1fn=new T(function(){return B(unCStr("observation_personchosesomething"));}),_1fo=new T(function(){return B(unCStr("observation_value_ge"));}),_1fp=new T(function(){return B(unCStr("observation_trueobs"));}),_1fq=new T(function(){return B(unCStr("observation_falseobs"));}),_1fr=new T(function(){return B(unCStr("observation_belowtimeout"));}),_1fs=new T(function(){return B(unCStr("observation_andobs"));}),_1ft=new T(function(){return B(unCStr("observation_orobs"));}),_1fu=new T(function(){return B(unCStr("observation_notobs"));}),_1fv=new T(function(){return B(unCStr("person"));}),_1fw=new T(function(){return B(unCStr("choice_value"));}),_1fx=new T(function(){return B(unCStr("observation2"));}),_1fy=new T(function(){return B(unCStr("observation1"));}),_1fz=new T(function(){return B(unCStr("block_number"));}),_1fA=function(_1fB,_){var _1fC=E(_1fB);switch(_1fC._){case 0:var _1fD=B(_1eo(_1fr,_)),_1fE=E(_1fD),_1fF=B(_1e4(_1fz,E(_1fE.a),_)),_1fG=eval(E(_1eR)),_1fH=__app2(E(_1fG),E(E(_1fF).a),toJSStr(B(_cz(0,_1fC.a,_1))));return _1fE;case 1:var _1fI=B(_1fA(_1fC.a,_)),_1fJ=B(_1fA(_1fC.b,_)),_1fK=B(_1eo(_1fs,_)),_1fL=E(_1fK),_1fM=E(_1fL.a),_1fN=B(_1e9(_1fy,_1fM,_1fI,_)),_1fO=B(_1e9(_1fx,_1fM,_1fJ,_));return _1fL;case 2:var _1fP=B(_1fA(_1fC.a,_)),_1fQ=B(_1fA(_1fC.b,_)),_1fR=B(_1eo(_1ft,_)),_1fS=E(_1fR),_1fT=E(_1fS.a),_1fU=B(_1e9(_1fy,_1fT,_1fP,_)),_1fV=B(_1e9(_1fx,_1fT,_1fQ,_));return _1fS;case 3:var _1fW=B(_1fA(_1fC.a,_)),_1fX=B(_1eo(_1fu,_)),_1fY=E(_1fX),_1fZ=B(_1e9(_1eB,E(_1fY.a),_1fW,_));return _1fY;case 4:var _1g0=B(_1eo(_1fm,_)),_1g1=E(_1g0),_1g2=E(_1g1.a),_1g3=B(_1e4(_1eN,_1g2,_)),_1g4=eval(E(_1eR)),_1g5=__app2(E(_1g4),E(E(_1g3).a),toJSStr(B(_cz(0,_1fC.a,_1)))),_1g6=B(_1e4(_1fv,_1g2,_)),_1g7=__app2(E(_1g4),E(E(_1g6).a),toJSStr(B(_cz(0,_1fC.b,_1)))),_1g8=B(_1e4(_1fw,_1g2,_)),_1g9=__app2(E(_1g4),E(E(_1g8).a),toJSStr(B(_cz(0,_1fC.c,_1))));return _1g1;case 5:var _1ga=B(_1eo(_1fn,_)),_1gb=E(_1ga),_1gc=E(_1gb.a),_1gd=B(_1e4(_1eN,_1gc,_)),_1ge=eval(E(_1eR)),_1gf=__app2(E(_1ge),E(E(_1gd).a),toJSStr(B(_cz(0,_1fC.a,_1)))),_1gg=B(_1e4(_1fv,_1gc,_)),_1gh=__app2(E(_1ge),E(E(_1gg).a),toJSStr(B(_cz(0,_1fC.b,_1))));return _1gb;case 6:var _1gi=B(_1eS(_1fC.a,_)),_1gj=B(_1eS(_1fC.b,_)),_1gk=B(_1eo(_1fo,_)),_1gl=E(_1gk),_1gm=E(_1gl.a),_1gn=B(_1db(_1eM,_1gm,_1gi,_)),_1go=B(_1db(_1eL,_1gm,_1gj,_));return _1gl;case 7:return new F(function(){return _1eo(_1fp,_);});break;default:return new F(function(){return _1eo(_1fq,_);});}},_1gp=function(_1gq,_){var _1gr=E(_1gq);switch(_1gr._){case 0:return new F(function(){return _1eo(_1ey,_);});break;case 1:var _1gs=B(_1gp(_1gr.f,_)),_1gt=B(_1gp(_1gr.g,_)),_1gu=B(_1eS(_1gr.c,_)),_1gv=B(_1eo(_1eh,_)),_1gw=E(_1gv),_1gx=E(_1gw.a),_1gy=B(_1e4(_1eu,_1gx,_)),_1gz=eval(E(_1eR)),_1gA=__app2(E(_1gz),E(E(_1gy).a),toJSStr(B(_cz(0,_1gr.a,_1)))),_1gB=B(_1e4(_1ex,_1gx,_)),_1gC=__app2(E(_1gz),E(E(_1gB).a),toJSStr(B(_cz(0,_1gr.b,_1)))),_1gD=B(_1db(_1eF,_1gx,_1gu,_)),_1gE=B(_1e4(_1ew,_1gx,_)),_1gF=__app2(E(_1gz),E(E(_1gE).a),toJSStr(B(_cz(0,_1gr.d,_1)))),_1gG=B(_1e4(_1ev,_1gx,_)),_1gH=__app2(E(_1gz),E(E(_1gG).a),toJSStr(B(_cz(0,_1gr.e,_1)))),_1gI=B(_1d2(_1eA,_1gx,_1gs,_)),_1gJ=B(_1d2(_1ez,_1gx,_1gt,_));return _1gw;case 2:var _1gK=B(_1gp(_1gr.b,_)),_1gL=B(_1eo(_1ei,_)),_1gM=E(_1gL),_1gN=E(_1gM.a),_1gO=B(_1e4(_1eu,_1gN,_)),_1gP=eval(E(_1eR)),_1gQ=__app2(E(_1gP),E(E(_1gO).a),toJSStr(B(_cz(0,_1gr.a,_1)))),_1gR=B(_1d2(_1eD,_1gN,_1gK,_));return _1gM;case 3:var _1gS=B(_1gp(_1gr.f,_)),_1gT=B(_1eo(_1ej,_)),_1gU=B(_1eS(_1gr.d,_)),_1gV=E(_1gT),_1gW=E(_1gV.a),_1gX=B(_1e4(_1et,_1gW,_)),_1gY=eval(E(_1eR)),_1gZ=__app2(E(_1gY),E(E(_1gX).a),toJSStr(B(_cz(0,_1gr.a,_1)))),_1h0=B(_1e4(_1es,_1gW,_)),_1h1=__app2(E(_1gY),E(E(_1h0).a),toJSStr(B(_cz(0,_1gr.b,_1)))),_1h2=B(_1e4(_1eG,_1gW,_)),_1h3=__app2(E(_1gY),E(E(_1h2).a),toJSStr(B(_cz(0,_1gr.c,_1)))),_1h4=B(_1db(_1eF,_1gW,_1gU,_)),_1h5=B(_1e4(_1eE,_1gW,_)),_1h6=__app2(E(_1gY),E(E(_1h5).a),toJSStr(B(_cz(0,_1gr.e,_1)))),_1h7=B(_1d2(_1eD,_1gW,_1gS,_));return _1gV;case 4:var _1h8=B(_1gp(_1gr.a,_)),_1h9=B(_1gp(_1gr.b,_)),_1ha=B(_1eo(_1ek,_)),_1hb=E(_1ha),_1hc=E(_1hb.a),_1hd=B(_1d2(_1eA,_1hc,_1h8,_)),_1he=B(_1d2(_1ez,_1hc,_1h9,_));return _1hb;case 5:var _1hf=B(_1fA(_1gr.a,_)),_1hg=B(_1gp(_1gr.b,_)),_1hh=B(_1gp(_1gr.c,_)),_1hi=B(_1eo(_1el,_)),_1hj=E(_1hi),_1hk=E(_1hj.a),_1hl=B(_1e9(_1eB,_1hk,_1hf,_)),_1hm=B(_1d2(_1eA,_1hk,_1hg,_)),_1hn=B(_1d2(_1ez,_1hk,_1hh,_));return _1hj;default:var _1ho=B(_1fA(_1gr.a,_)),_1hp=B(_1gp(_1gr.c,_)),_1hq=B(_1gp(_1gr.d,_)),_1hr=B(_1eo(_1em,_)),_1hs=E(_1hr),_1ht=E(_1hs.a),_1hu=B(_1e4(_1eC,_1ht,_)),_1hv=eval(E(_1eR)),_1hw=__app2(E(_1hv),E(E(_1hu).a),toJSStr(B(_cz(0,_1gr.b,_1)))),_1hx=B(_1e9(_1eB,_1ht,_1ho,_)),_1hy=B(_1d2(_1eA,_1ht,_1hp,_)),_1hz=B(_1d2(_1ez,_1ht,_1hq,_));return _1hs;}},_1hA=new T(function(){return eval("(function () {var i; var b = demoWorkspace.getAllBlocks(); for (i = b.length - 1; i > 0; --i) { if (b[i] !== undefined) { b[i].dispose() } };})");}),_1hB=new T(function(){return eval("(function() {return (demoWorkspace.getAllBlocks()[0]);})");}),_1hC=new T(function(){return B(unCStr("base_contract"));}),_1hD=new T(function(){return eval("(function() { demoWorkspace.render(); onresize(); })");}),_1hE=function(_1hF,_){var _1hG=__app0(E(_1hA)),_1hH=__app0(E(_1hB)),_1hI=B(_ZI(B(_g4(_142,_1hF))));if(!_1hI._){return E(_ZQ);}else{if(!E(_1hI.b)._){var _1hJ=B(_1gp(_1hI.a,_)),_1hK=B(_1d2(_1hC,_1hH,_1hJ,_)),_1hL=__app0(E(_1hD)),_1hM=eval(E(_Y0)),_1hN=__app1(E(_1hM),toJSStr(E(_14m))),_1hO=new T(function(){var _1hP=B(_ZI(B(_g4(_yK,new T(function(){var _1hQ=String(_1hN);return fromJSStr(_1hQ);})))));if(!_1hP._){return E(_eS);}else{if(!E(_1hP.b)._){var _1hR=E(_1hP.a);return new T4(0,new T(function(){return B(_bH(_1hR.a));}),new T(function(){return B(_8f(_1hR.b));}),new T(function(){return B(_9V(_1hR.c));}),new T(function(){return B(_4n(_1hR.d));}));}else{return E(_eQ);}}});return new F(function(){return _143(_1hO,_);});}else{return E(_ZP);}}},_1hS=function(_){var _1hT=eval(E(_Y0)),_1hU=__app1(E(_1hT),toJSStr(E(_1c5)));return new F(function(){return _1hE(new T(function(){var _1hV=String(_1hU);return fromJSStr(_1hV);}),_);});},_1hW=new T(function(){return B(unCStr("contractOutput"));}),_1hX=new T(function(){return B(unCStr("([], [], [], [])"));}),_1hY=new T(function(){return B(unCStr("([], [])"));}),_1hZ=new T1(0,0),_1i0=new T(function(){return B(_cz(0,_1hZ,_1));}),_1i1="(function (t, s) {document.getElementById(t).value = s})",_1i2=function(_1i3,_1i4,_){var _1i5=eval(E(_1i1)),_1i6=__app2(E(_1i5),toJSStr(E(_1i3)),toJSStr(E(_1i4)));return new F(function(){return _A6(_);});},_1i7=function(_){var _1i8=__app0(E(_1hA)),_1i9=B(_14o(_1c5,_1,_)),_1ia=B(_1i2(_Y3,_1i0,_)),_1ib=B(_14o(_Y2,_1hY,_)),_1ic=B(_14o(_14m,_1hX,_));return new F(function(){return _14o(_1hW,_1,_);});},_1id=new T1(0,1000),_1ie=new T1(2,_1id),_1if=new T1(0,3),_1ig=new T1(0,_1if),_1ih=new T1(0,4),_1ii=new T1(0,_1ih),_1ij=new T2(1,_1ig,_1ii),_1ik=new T1(0,2),_1il=new T1(0,_1ik),_1im=new T1(0,1),_1in=new T1(0,_1im),_1io=new T2(1,_1in,_1il),_1ip=new T2(1,_1io,_1ij),_1iq=new T2(6,_1ip,_1ie),_1ir=new T1(0,20),_1is=new T1(0,5),_1it=new T6(3,_1ik,_1ik,_1is,_1il,_1ir,_Tt),_1iu=new T6(3,_1im,_1im,_1is,_1in,_1ir,_Tt),_1iv=new T2(4,_1iu,_1it),_1iw=new T6(3,_1if,_1if,_1is,_1ig,_1ir,_Tt),_1ix=new T6(3,_1ih,_1ih,_1is,_1ii,_1ir,_Tt),_1iy=new T2(4,_1iw,_1ix),_1iz=new T2(4,_1iv,_1iy),_1iA=new T3(5,_1iq,_1iz,_Tt),_1iB=new T1(0,10),_1iC=new T4(6,_10M,_1iB,_Tt,_1iA),_1iD=new T1(0,_1iC),_1iE=new T2(1,_1iD,_1),_1iF=new T1(0,0),_1iG=new T1(2,_1iF),_1iH=new T3(3,_1ih,_1ih,_1iG),_1iI={_:1,a:_1ih,b:_1ih,c:_1iH,d:_1iB,e:_1ir,f:_Tt,g:_Tt},_1iJ=new T1(2,_1im),_1iK=new T2(6,_1iH,_1iJ),_1iL=new T2(5,_1ih,_1ih),_1iM=new T2(1,_1iL,_1iK),_1iN=new T4(6,_1iM,_1iB,_1iI,_Tt),_1iO=new T3(3,_1if,_1if,_1iG),_1iP={_:1,a:_1if,b:_1if,c:_1iO,d:_1iB,e:_1ir,f:_Tt,g:_Tt},_1iQ=new T2(6,_1iO,_1iJ),_1iR=new T2(5,_1if,_1if),_1iS=new T2(1,_1iR,_1iQ),_1iT=new T4(6,_1iS,_1iB,_1iP,_Tt),_1iU=new T2(4,_1iT,_1iN),_1iV=new T3(3,_1ik,_1ik,_1iG),_1iW={_:1,a:_1ik,b:_1ik,c:_1iV,d:_1iB,e:_1ir,f:_Tt,g:_Tt},_1iX=new T2(6,_1iV,_1iJ),_1iY=new T2(5,_1ik,_1ik),_1iZ=new T2(1,_1iY,_1iX),_1j0=new T4(6,_1iZ,_1iB,_1iW,_Tt),_1j1=new T3(3,_1im,_1im,_1iG),_1j2={_:1,a:_1im,b:_1im,c:_1j1,d:_1iB,e:_1ir,f:_Tt,g:_Tt},_1j3=new T2(6,_1j1,_1iJ),_1j4=new T2(5,_1im,_1im),_1j5=new T2(1,_1j4,_1j3),_1j6=new T4(6,_1j5,_1iB,_1j2,_Tt),_1j7=new T2(4,_1j6,_1j0),_1j8=new T2(4,_1j7,_1iU),_1j9=new T1(0,_1j8),_1ja=new T2(1,_1j9,_1iE),_1jb=new T(function(){return B(_1bl(_1bf,_1aa,_1ja));}),_1jc=function(_){var _1jd=B(_1i7(_)),_1je=B(_14o(_1c5,_1jb,_)),_1jf=eval(E(_Y0)),_1jg=__app1(E(_1jf),toJSStr(E(_1c5)));return new F(function(){return _1hE(new T(function(){var _1jh=String(_1jg);return fromJSStr(_1jh);}),_);});},_1ji=new T1(0,1),_1jj=new T1(3,_1ji),_1jk=new T1(6,_1ji),_1jl=new T1(0,100),_1jm=new T1(2,_1jl),_1jn=new T1(2,_1jm),_1jo=new T1(0,10),_1jp=new T1(6,_1jo),_1jq=new T1(0,200),_1jr=new T1(6,_1jq),_1js=new T1(0,20),_1jt=new T1(2,_1js),_1ju=new T1(0,2),_1jv=new T2(2,_1ji,_Tt),_1jw=new T2(2,_1ju,_Tt),_1jx=new T2(4,_1jv,_1jw),_1jy=new T6(3,_1ji,_1ju,_1ji,_1jt,_1jq,_1jx),_1jz=new T2(5,_1ji,_1ji),_1jA=new T4(6,_1jz,_1jl,_1jx,_1jy),_1jB={_:1,a:_1ju,b:_1ju,c:_1jt,d:_1js,e:_1jq,f:_1jA,g:_1jv},_1jC=new T1(0,_1jB),_1jD=new T1(0,_Tt),_1jE=new T2(1,_1jD,_1),_1jF=new T2(1,_1jC,_1jE),_1jG=new T2(1,_1jr,_1jF),_1jH=new T2(1,_1jp,_1jG),_1jI=new T2(1,_1jn,_1jH),_1jJ=new T2(1,_1jk,_1jI),_1jK=new T2(1,_1jj,_1jJ),_1jL=new T(function(){return B(_1bl(_1bf,_1ae,_1jK));}),_1jM=function(_){var _1jN=B(_1i7(_)),_1jO=B(_14o(_1c5,_1jL,_)),_1jP=eval(E(_Y0)),_1jQ=__app1(E(_1jP),toJSStr(E(_1c5)));return new F(function(){return _1hE(new T(function(){var _1jR=String(_1jQ);return fromJSStr(_1jR);}),_);});},_1jS=new T1(0,1),_1jT=new T1(3,_1jS),_1jU=new T1(6,_1jS),_1jV=new T1(0,450),_1jW=new T1(2,_1jV),_1jX=new T1(2,_1jW),_1jY=new T1(0,10),_1jZ=new T1(6,_1jY),_1k0=new T1(0,100),_1k1=new T1(6,_1k0),_1k2=new T1(0,90),_1k3=new T1(0,3),_1k4=new T1(0,0),_1k5=new T3(4,_1k3,_1k3,_1k4),_1k6=new T1(0,2),_1k7=new T3(4,_1k6,_1k6,_1k4),_1k8=new T2(1,_1k7,_1k5),_1k9=new T2(2,_1k7,_1k5),_1ka=new T3(4,_1jS,_1jS,_1k4),_1kb=new T2(1,_1ka,_1k9),_1kc=new T2(2,_1kb,_1k8),_1kd=new T3(4,_1k3,_1k3,_1jS),_1ke=new T3(4,_1k6,_1k6,_1jS),_1kf=new T2(1,_1ke,_1kd),_1kg=new T2(2,_1ke,_1kd),_1kh=new T3(4,_1jS,_1jS,_1jS),_1ki=new T2(1,_1kh,_1kg),_1kj=new T2(2,_1ki,_1kf),_1kk=new T2(2,_1kc,_1kj),_1kl=new T2(2,_1jS,_Tt),_1km=new T1(0,_1jS),_1kn=new T6(3,_1jS,_1jS,_1k6,_1km,_1k0,_1kl),_1ko=new T3(5,_1kj,_1kn,_1kl),_1kp=new T4(6,_1kk,_1k2,_1ko,_1kl),_1kq=new T1(0,_1kp),_1kr=new T2(1,_1kq,_1jE),_1ks=new T2(1,_1k1,_1kr),_1kt=new T2(1,_1jZ,_1ks),_1ku=new T2(1,_1jX,_1kt),_1kv=new T2(1,_1jU,_1ku),_1kw=new T2(1,_1jT,_1kv),_1kx=new T(function(){return B(_1bl(_1bf,_1ae,_1kw));}),_1ky=function(_){var _1kz=B(_1i7(_)),_1kA=B(_14o(_1c5,_1kx,_)),_1kB=eval(E(_Y0)),_1kC=__app1(E(_1kB),toJSStr(E(_1c5)));return new F(function(){return _1hE(new T(function(){var _1kD=String(_1kC);return fromJSStr(_1kD);}),_);});},_1kE=new T(function(){return B(unCStr("NotRedeemed "));}),_1kF=function(_1kG,_1kH,_1kI){var _1kJ=E(_1kH);switch(_1kJ._){case 0:var _1kK=function(_1kL){return new F(function(){return _cz(11,_1kJ.a,new T2(1,_cJ,new T(function(){return B(_cz(11,_1kJ.b,_1kL));})));});};if(E(_1kG)<11){return new F(function(){return _ce(_1kE,new T(function(){return B(_1kK(_1kI));},1));});}else{var _1kM=new T(function(){return B(_ce(_1kE,new T(function(){return B(_1kK(new T2(1,_cw,_1kI)));},1)));});return new T2(1,_cx,_1kM);}break;case 1:return new F(function(){return _ce(_Yp,_1kI);});break;default:return new F(function(){return _ce(_Yu,_1kI);});}},_1kN=0,_1kO=function(_1kP,_1kQ,_1kR){var _1kS=new T(function(){var _1kT=function(_1kU){var _1kV=E(_1kQ),_1kW=new T(function(){return B(A3(_dr,_c9,new T2(1,function(_1kX){return new F(function(){return _cz(0,_1kV.a,_1kX);});},new T2(1,function(_vz){return new F(function(){return _1kF(_1kN,_1kV.b,_vz);});},_1)),new T2(1,_cw,_1kU)));});return new T2(1,_cx,_1kW);};return B(A3(_dr,_c9,new T2(1,function(_1kY){return new F(function(){return _cE(0,_1kP,_1kY);});},new T2(1,_1kT,_1)),new T2(1,_cw,_1kR)));});return new T2(0,_cx,_1kS);},_1kZ=function(_1l0,_1l1){var _1l2=E(_1l0),_1l3=B(_1kO(_1l2.a,_1l2.b,_1l1));return new T2(1,_1l3.a,_1l3.b);},_1l4=function(_1l5,_1l6){return new F(function(){return _dQ(_1kZ,_1l5,_1l6);});},_1l7=new T(function(){return B(unCStr("ChoiceMade "));}),_1l8=new T(function(){return B(unCStr("DuplicateRedeem "));}),_1l9=new T(function(){return B(unCStr("ExpiredCommitRedeemed "));}),_1la=new T(function(){return B(unCStr("CommitRedeemed "));}),_1lb=new T(function(){return B(unCStr("SuccessfulCommit "));}),_1lc=new T(function(){return B(unCStr("FailedPay "));}),_1ld=new T(function(){return B(unCStr("ExpiredPay "));}),_1le=new T(function(){return B(unCStr("SuccessfulPay "));}),_1lf=function(_1lg,_1lh,_1li){var _1lj=E(_1lh);switch(_1lj._){case 0:var _1lk=function(_1ll){var _1lm=new T(function(){var _1ln=new T(function(){return B(_cz(11,_1lj.c,new T2(1,_cJ,new T(function(){return B(_cz(11,_1lj.d,_1ll));}))));});return B(_cz(11,_1lj.b,new T2(1,_cJ,_1ln)));});return new F(function(){return _dg(11,_1lj.a,new T2(1,_cJ,_1lm));});};if(_1lg<11){return new F(function(){return _ce(_1le,new T(function(){return B(_1lk(_1li));},1));});}else{var _1lo=new T(function(){return B(_ce(_1le,new T(function(){return B(_1lk(new T2(1,_cw,_1li)));},1)));});return new T2(1,_cx,_1lo);}break;case 1:var _1lp=function(_1lq){var _1lr=new T(function(){var _1ls=new T(function(){return B(_cz(11,_1lj.c,new T2(1,_cJ,new T(function(){return B(_cz(11,_1lj.d,_1lq));}))));});return B(_cz(11,_1lj.b,new T2(1,_cJ,_1ls)));});return new F(function(){return _dg(11,_1lj.a,new T2(1,_cJ,_1lr));});};if(_1lg<11){return new F(function(){return _ce(_1ld,new T(function(){return B(_1lp(_1li));},1));});}else{var _1lt=new T(function(){return B(_ce(_1ld,new T(function(){return B(_1lp(new T2(1,_cw,_1li)));},1)));});return new T2(1,_cx,_1lt);}break;case 2:var _1lu=function(_1lv){var _1lw=new T(function(){var _1lx=new T(function(){return B(_cz(11,_1lj.c,new T2(1,_cJ,new T(function(){return B(_cz(11,_1lj.d,_1lv));}))));});return B(_cz(11,_1lj.b,new T2(1,_cJ,_1lx)));});return new F(function(){return _dg(11,_1lj.a,new T2(1,_cJ,_1lw));});};if(_1lg<11){return new F(function(){return _ce(_1lc,new T(function(){return B(_1lu(_1li));},1));});}else{var _1ly=new T(function(){return B(_ce(_1lc,new T(function(){return B(_1lu(new T2(1,_cw,_1li)));},1)));});return new T2(1,_cx,_1ly);}break;case 3:var _1lz=function(_1lA){var _1lB=new T(function(){var _1lC=new T(function(){return B(_cz(11,_1lj.c,new T2(1,_cJ,new T(function(){return B(_cz(11,_1lj.d,_1lA));}))));});return B(_cz(11,_1lj.b,new T2(1,_cJ,_1lC)));});return new F(function(){return _cE(11,_1lj.a,new T2(1,_cJ,_1lB));});};if(_1lg<11){return new F(function(){return _ce(_1lb,new T(function(){return B(_1lz(_1li));},1));});}else{var _1lD=new T(function(){return B(_ce(_1lb,new T(function(){return B(_1lz(new T2(1,_cw,_1li)));},1)));});return new T2(1,_cx,_1lD);}break;case 4:var _1lE=function(_1lF){var _1lG=new T(function(){var _1lH=new T(function(){return B(_cz(11,_1lj.b,new T2(1,_cJ,new T(function(){return B(_cz(11,_1lj.c,_1lF));}))));});return B(_cE(11,_1lj.a,new T2(1,_cJ,_1lH)));},1);return new F(function(){return _ce(_1la,_1lG);});};if(_1lg<11){return new F(function(){return _1lE(_1li);});}else{return new T2(1,_cx,new T(function(){return B(_1lE(new T2(1,_cw,_1li)));}));}break;case 5:var _1lI=function(_1lJ){var _1lK=new T(function(){var _1lL=new T(function(){return B(_cz(11,_1lj.b,new T2(1,_cJ,new T(function(){return B(_cz(11,_1lj.c,_1lJ));}))));});return B(_cE(11,_1lj.a,new T2(1,_cJ,_1lL)));},1);return new F(function(){return _ce(_1l9,_1lK);});};if(_1lg<11){return new F(function(){return _1lI(_1li);});}else{return new T2(1,_cx,new T(function(){return B(_1lI(new T2(1,_cw,_1li)));}));}break;case 6:var _1lM=function(_1lN){return new F(function(){return _cE(11,_1lj.a,new T2(1,_cJ,new T(function(){return B(_cz(11,_1lj.b,_1lN));})));});};if(_1lg<11){return new F(function(){return _ce(_1l8,new T(function(){return B(_1lM(_1li));},1));});}else{var _1lO=new T(function(){return B(_ce(_1l8,new T(function(){return B(_1lM(new T2(1,_cw,_1li)));},1)));});return new T2(1,_cx,_1lO);}break;default:var _1lP=function(_1lQ){var _1lR=new T(function(){var _1lS=new T(function(){return B(_cz(11,_1lj.b,new T2(1,_cJ,new T(function(){return B(_cz(11,_1lj.c,_1lQ));}))));});return B(_e5(11,_1lj.a,new T2(1,_cJ,_1lS)));},1);return new F(function(){return _ce(_1l7,_1lR);});};if(_1lg<11){return new F(function(){return _1lP(_1li);});}else{return new T2(1,_cx,new T(function(){return B(_1lP(new T2(1,_cw,_1li)));}));}}},_1lT=new T(function(){return eval("(function (x) { alert(x) ; })");}),_1lU=function(_1lV,_1lW){var _1lX=E(_1lV),_1lY=E(_1lW);if(!_1lY._){var _1lZ=_1lY.b,_1m0=_1lY.c,_1m1=_1lY.d;switch(B(_2(_1lX,_1lZ))){case 0:return new F(function(){return _5q(_1lZ,B(_1lU(_1lX,_1m0)),_1m1);});break;case 1:return new T4(0,_1lY.a,E(_1lX),E(_1m0),E(_1m1));default:return new F(function(){return _4G(_1lZ,_1m0,B(_1lU(_1lX,_1m1)));});}}else{return new T4(0,1,E(_1lX),E(_4B),E(_4B));}},_1m2=function(_1m3,_1m4){while(1){var _1m5=E(_1m3),_1m6=E(_1m4);if(!_1m6._){switch(B(_2(_1m5,_1m6.b))){case 0:_1m3=_1m5;_1m4=_1m6.c;continue;case 1:return true;default:_1m3=_1m5;_1m4=_1m6.d;continue;}}else{return false;}}},_1m7=function(_1m8,_1m9,_1ma){var _1mb=function(_1mc,_1md){while(1){var _1me=E(_1mc),_1mf=E(_1md);if(!_1mf._){switch(B(A3(_I1,_1m8,_1me,_1mf.b))){case 0:_1mc=_1me;_1md=_1mf.c;continue;case 1:return true;default:_1mc=_1me;_1md=_1mf.d;continue;}}else{return false;}}};return new F(function(){return _1mb(_1m9,_1ma);});},_1mg=function(_1mh,_1mi,_1mj,_1mk){var _1ml=E(_1mk);if(!_1ml._){var _1mm=new T(function(){var _1mn=B(_1mg(_1ml.a,_1ml.b,_1ml.c,_1ml.d));return new T2(0,_1mn.a,_1mn.b);});return new T2(0,new T(function(){return E(E(_1mm).a);}),new T(function(){return B(_5q(_1mi,_1mj,E(_1mm).b));}));}else{return new T2(0,_1mi,_1mj);}},_1mo=function(_1mp,_1mq,_1mr,_1ms){var _1mt=E(_1mr);if(!_1mt._){var _1mu=new T(function(){var _1mv=B(_1mo(_1mt.a,_1mt.b,_1mt.c,_1mt.d));return new T2(0,_1mv.a,_1mv.b);});return new T2(0,new T(function(){return E(E(_1mu).a);}),new T(function(){return B(_4G(_1mq,E(_1mu).b,_1ms));}));}else{return new T2(0,_1mq,_1ms);}},_1mw=function(_1mx,_1my){var _1mz=E(_1mx);if(!_1mz._){var _1mA=_1mz.a,_1mB=E(_1my);if(!_1mB._){var _1mC=_1mB.a;if(_1mA<=_1mC){var _1mD=B(_1mo(_1mC,_1mB.b,_1mB.c,_1mB.d));return new F(function(){return _5q(_1mD.a,_1mz,_1mD.b);});}else{var _1mE=B(_1mg(_1mA,_1mz.b,_1mz.c,_1mz.d));return new F(function(){return _4G(_1mE.a,_1mE.b,_1mB);});}}else{return E(_1mz);}}else{return E(_1my);}},_1mF=function(_1mG,_1mH,_1mI,_1mJ,_1mK){var _1mL=E(_1mG);if(!_1mL._){var _1mM=_1mL.a,_1mN=_1mL.b,_1mO=_1mL.c,_1mP=_1mL.d;if((imul(3,_1mM)|0)>=_1mH){if((imul(3,_1mH)|0)>=_1mM){return new F(function(){return _1mw(_1mL,new T4(0,_1mH,E(_1mI),E(_1mJ),E(_1mK)));});}else{return new F(function(){return _4G(_1mN,_1mO,B(_1mF(_1mP,_1mH,_1mI,_1mJ,_1mK)));});}}else{return new F(function(){return _5q(_1mI,B(_1mQ(_1mM,_1mN,_1mO,_1mP,_1mJ)),_1mK);});}}else{return new T4(0,_1mH,E(_1mI),E(_1mJ),E(_1mK));}},_1mQ=function(_1mR,_1mS,_1mT,_1mU,_1mV){var _1mW=E(_1mV);if(!_1mW._){var _1mX=_1mW.a,_1mY=_1mW.b,_1mZ=_1mW.c,_1n0=_1mW.d;if((imul(3,_1mR)|0)>=_1mX){if((imul(3,_1mX)|0)>=_1mR){return new F(function(){return _1mw(new T4(0,_1mR,E(_1mS),E(_1mT),E(_1mU)),_1mW);});}else{return new F(function(){return _4G(_1mS,_1mT,B(_1mF(_1mU,_1mX,_1mY,_1mZ,_1n0)));});}}else{return new F(function(){return _5q(_1mY,B(_1mQ(_1mR,_1mS,_1mT,_1mU,_1mZ)),_1n0);});}}else{return new T4(0,_1mR,E(_1mS),E(_1mT),E(_1mU));}},_1n1=function(_1n2,_1n3){var _1n4=E(_1n2);if(!_1n4._){var _1n5=_1n4.a,_1n6=_1n4.b,_1n7=_1n4.c,_1n8=_1n4.d,_1n9=E(_1n3);if(!_1n9._){var _1na=_1n9.a,_1nb=_1n9.b,_1nc=_1n9.c,_1nd=_1n9.d;if((imul(3,_1n5)|0)>=_1na){if((imul(3,_1na)|0)>=_1n5){return new F(function(){return _1mw(_1n4,_1n9);});}else{return new F(function(){return _4G(_1n6,_1n7,B(_1mF(_1n8,_1na,_1nb,_1nc,_1nd)));});}}else{return new F(function(){return _5q(_1nb,B(_1mQ(_1n5,_1n6,_1n7,_1n8,_1nc)),_1nd);});}}else{return E(_1n4);}}else{return E(_1n3);}},_1ne=function(_1nf,_1ng,_1nh,_1ni,_1nj){var _1nk=E(_1nj);if(!_1nk._){var _1nl=E(_1ni);if(!_1nl._){var _1nm=_1nl.b,_1nn=new T1(1,E(_1nm)),_1no=B(_1ne(_1nf,_1nn,_1nh,_1nl.d,B(_Kc(_1nf,_1nn,_1nh,_1nk)))),_1np=B(_1ne(_1nf,_1ng,_1nn,_1nl.c,B(_Kc(_1nf,_1ng,_1nn,_1nk))));if(!B(_1m7(_1nf,_1nm,_1nk))){return new F(function(){return _1n1(_1np,_1no);});}else{return new F(function(){return _6C(_1nm,_1np,_1no);});}}else{return new T0(1);}}else{return new T0(1);}},_1nq=function(_1nr,_1ns,_1nt,_1nu,_1nv,_1nw,_1nx,_1ny,_1nz,_1nA,_1nB){var _1nC=new T1(1,E(_1nv)),_1nD=B(_1ne(_1nr,_1nC,_1nt,_1nx,B(_Kc(_1nr,_1nC,_1nt,new T4(0,_1ny,E(_1nz),E(_1nA),E(_1nB)))))),_1nE=B(_1ne(_1nr,_1ns,_1nC,_1nw,B(_Kc(_1nr,_1ns,_1nC,new T4(0,_1ny,E(_1nz),E(_1nA),E(_1nB))))));if(!B(_1m7(_1nr,_1nv,new T4(0,_1ny,E(_1nz),E(_1nA),E(_1nB))))){return new F(function(){return _1n1(_1nE,_1nD);});}else{return new F(function(){return _6C(_1nv,_1nE,_1nD);});}},_1nF=function(_1nG,_1nH,_1nI,_1nJ){var _1nK=function(_1nL){var _1nM=E(_1nH);if(!_1nM._){var _1nN=E(_1nJ);return (_1nN._==0)?(B(_1nq(_Gx,_I0,_I0,_1nM.a,_1nM.b,_1nM.c,_1nM.d,_1nN.a,_1nN.b,_1nN.c,_1nN.d))._==0)?false:true:true;}else{return true;}},_1nO=E(_1nG);if(!_1nO._){var _1nP=E(_1nI);if(!_1nP._){if(!B(_1nq(_Op,_I0,_I0,_1nO.a,_1nO.b,_1nO.c,_1nO.d,_1nP.a,_1nP.b,_1nP.c,_1nP.d))._){return false;}else{return new F(function(){return _1nK(_);});}}else{return new F(function(){return _1nK(_);});}}else{return new F(function(){return _1nK(_);});}},_1nQ=function(_1nR,_1nS,_1nT,_1nU){return new T2(0,new T(function(){var _1nV=E(_1nR);if(!_1nV._){var _1nW=E(_1nT);if(!_1nW._){return B(_KO(_Op,_I0,_I0,_1nV.a,_1nV.b,_1nV.c,_1nV.d,_1nW.a,_1nW.b,_1nW.c,_1nW.d));}else{return E(_1nV);}}else{return E(_1nT);}}),new T(function(){var _1nX=E(_1nS);if(!_1nX._){var _1nY=E(_1nU);if(!_1nY._){return B(_KO(_Gx,_I0,_I0,_1nX.a,_1nX.b,_1nX.c,_1nX.d,_1nY.a,_1nY.b,_1nY.c,_1nY.d));}else{return E(_1nX);}}else{return E(_1nU);}}));},_1nZ=function(_1o0,_1o1,_1o2){var _1o3=E(_1o2);if(!_1o3._){var _1o4=_1o3.c,_1o5=_1o3.d,_1o6=E(_1o3.b);switch(B(_2(_1o0,_1o6.a))){case 0:return new F(function(){return _5q(_1o6,B(_1nZ(_1o0,_1o1,_1o4)),_1o5);});break;case 1:switch(B(_2(_1o1,_1o6.b))){case 0:return new F(function(){return _5q(_1o6,B(_1nZ(_1o0,_1o1,_1o4)),_1o5);});break;case 1:return new T4(0,_1o3.a,E(new T2(0,_1o0,_1o1)),E(_1o4),E(_1o5));default:return new F(function(){return _4G(_1o6,_1o4,B(_1nZ(_1o0,_1o1,_1o5)));});}break;default:return new F(function(){return _4G(_1o6,_1o4,B(_1nZ(_1o0,_1o1,_1o5)));});}}else{return new T4(0,1,E(new T2(0,_1o0,_1o1)),E(_4B),E(_4B));}},_1o7=function(_1o8,_1o9,_1oa){while(1){var _1ob=E(_1oa);if(!_1ob._){var _1oc=_1ob.c,_1od=_1ob.d,_1oe=E(_1ob.b);switch(B(_2(_1o8,_1oe.a))){case 0:_1oa=_1oc;continue;case 1:switch(B(_2(_1o9,_1oe.b))){case 0:_1oa=_1oc;continue;case 1:return true;default:_1oa=_1od;continue;}break;default:_1oa=_1od;continue;}}else{return false;}}},_1of=function(_1og,_1oh,_1oi){var _1oj=E(_1oi);if(!_1oj._){return __Z;}else{var _1ok=E(_1oj.a),_1ol=_1ok.b;return (!B(_1o7(_1og,_1oh,_1ol)))?new T1(1,new T2(0,_1ok.a,new T(function(){return B(_1nZ(_1og,_1oh,_1ol));}))):__Z;}},_1om=function(_1on,_1oo){var _1op=E(_1on);if(!_1op._){return __Z;}else{var _1oq=E(_1oo);if(!_1oq._){return __Z;}else{var _1or=E(_1op.a),_1os=_1or.a,_1ot=_1or.b,_1ou=E(_1oq.a),_1ov=_1ou.a,_1ow=_1ou.b;return (!B(_1nF(_1os,_1ot,_1ov,_1ow)))?__Z:new T1(1,new T(function(){var _1ox=B(_1nQ(_1os,_1ot,_1ov,_1ow));return new T2(0,_1ox.a,_1ox.b);}));}}},_1oy=new T2(0,_4B,_4B),_1oz=new T1(1,_1oy),_1oA=function(_1oB){while(1){var _1oC=B((function(_1oD){var _1oE=E(_1oD);switch(_1oE._){case 0:return E(_1oz);case 1:var _1oF=_1oE.a,_1oG=B(_1oA(_1oE.f));if(!_1oG._){return __Z;}else{var _1oH=B(_1oA(_1oE.g));if(!_1oH._){return __Z;}else{var _1oI=E(_1oG.a),_1oJ=_1oI.a,_1oK=_1oI.b,_1oL=E(_1oH.a),_1oM=_1oL.a,_1oN=_1oL.b;if(!B(_1nF(_1oJ,_1oK,_1oM,_1oN))){return __Z;}else{var _1oO=B(_1nQ(_1oJ,_1oK,_1oM,_1oN)),_1oP=_1oO.a;return (!B(_1m2(_1oF,_1oP)))?new T1(1,new T2(0,new T(function(){return B(_1lU(_1oF,_1oP));}),_1oO.b)):__Z;}}}break;case 2:_1oB=_1oE.b;return __continue;case 3:return new F(function(){return _1of(_1oE.a,_1oE.c,B(_1oA(_1oE.f)));});break;case 4:return new F(function(){return _1om(B(_1oA(_1oE.a)),new T(function(){return B(_1oA(_1oE.b));},1));});break;case 5:return new F(function(){return _1om(B(_1oA(_1oE.b)),new T(function(){return B(_1oA(_1oE.c));},1));});break;default:return new F(function(){return _1om(B(_1oA(_1oE.c)),new T(function(){return B(_1oA(_1oE.d));},1));});}})(_1oB));if(_1oC!=__continue){return _1oC;}}},_1oQ=new T(function(){return B(unCStr("Badly formed contract: Identifiers are not unique!"));}),_1oR=new T1(0,1),_1oS=new T(function(){return B(unAppCStr("[]",_1));}),_1oT=new T2(1,_dO,_1),_1oU=function(_1oV){var _1oW=E(_1oV);if(!_1oW._){return E(_1oT);}else{var _1oX=new T(function(){return B(_1lf(0,_1oW.a,new T(function(){return B(_1oU(_1oW.b));})));});return new T2(1,_c8,_1oX);}},_1oY=function(_){var _1oZ=E(_14m),_1p0=toJSStr(_1oZ),_1p1=eval(E(_Y0)),_1p2=_1p1,_1p3=__app1(E(_1p2),_1p0),_1p4=E(_Y2),_1p5=__app1(E(_1p2),toJSStr(_1p4)),_1p6=__app0(E(_Y1)),_1p7=new T(function(){var _1p8=B(_ZI(B(_g4(_142,new T(function(){var _1p9=String(_1p6);return fromJSStr(_1p9);})))));if(!_1p8._){return E(_ZQ);}else{if(!E(_1p8.b)._){return E(_1p8.a);}else{return E(_ZP);}}}),_1pa=E(_Y3),_1pb=eval(E(_Y8)),_1pc=__app1(E(_1pb),toJSStr(_1pa)),_1pd=new T(function(){var _1pe=B(_ZI(B(_g4(_Y7,new T(function(){var _1pf=String(_1pc);return fromJSStr(_1pf);})))));if(!_1pe._){return E(_Y6);}else{if(!E(_1pe.b)._){return E(_1pe.a);}else{return E(_Y5);}}});if(!B(_1oA(_1p7))._){var _1pg=__app1(E(_1lT),toJSStr(_1oQ));return new F(function(){return _A6(_);});}else{var _1ph=new T(function(){var _1pi=B(_ZI(B(_g4(_ZF,new T(function(){var _1pj=String(_1p5);return fromJSStr(_1pj);})))));if(!_1pi._){return E(_Ya);}else{if(!E(_1pi.b)._){var _1pk=E(_1pi.a);return new T2(0,new T(function(){return B(_zV(_1pk.a));}),new T(function(){return B(_4n(_1pk.b));}));}else{return E(_Y9);}}}),_1pl=new T(function(){var _1pm=B(_ZI(B(_g4(_yK,new T(function(){var _1pn=String(_1p3);return fromJSStr(_1pn);})))));if(!_1pm._){return E(_eS);}else{if(!E(_1pm.b)._){var _1po=E(_1pm.a);return new T4(0,new T(function(){return B(_bH(_1po.a));}),new T(function(){return B(_8f(_1po.b));}),new T(function(){return B(_9V(_1po.c));}),new T(function(){return B(_4n(_1po.d));}));}else{return E(_eQ);}}}),_1pp=B(_Xj(_1pl,_1ph,_1p7,new T2(0,_ZG,_1pd))),_1pq=function(_,_1pr){var _1ps=function(_,_1pt){var _1pu=E(_1pp.a),_1pv=new T(function(){var _1pw=new T(function(){return B(_c1(_1,_1pu.b));}),_1px=new T(function(){return B(_c1(_1,_1pu.a));});return B(A3(_dr,_c9,new T2(1,function(_1py){return new F(function(){return _1l4(_1px,_1py);});},new T2(1,function(_1pz){return new F(function(){return _er(_1pw,_1pz);});},_1)),_eu));}),_1pA=B(_14o(_1p4,new T2(1,_cx,_1pv),_)),_1pB=B(_14o(_1oZ,_1hX,_)),_1pC=B(_1i2(_1pa,B(_cz(0,B(_ji(_1pd,_1oR)),_1)),_)),_1pD=__app1(E(_1p2),toJSStr(E(_1c5))),_1pE=B(_1hE(new T(function(){var _1pF=String(_1pD);return fromJSStr(_1pF);}),_)),_1pG=__app1(E(_1p2),_1p0),_1pH=new T(function(){var _1pI=B(_ZI(B(_g4(_yK,new T(function(){var _1pJ=String(_1pG);return fromJSStr(_1pJ);})))));if(!_1pI._){return E(_eS);}else{if(!E(_1pI.b)._){var _1pK=E(_1pI.a);return new T4(0,new T(function(){return B(_bH(_1pK.a));}),new T(function(){return B(_8f(_1pK.b));}),new T(function(){return B(_9V(_1pK.c));}),new T(function(){return B(_4n(_1pK.d));}));}else{return E(_eQ);}}});return new F(function(){return _143(_1pH,_);});},_1pL=E(_1pp.b);switch(_1pL._){case 0:var _1pM=B(_14o(_1c5,_1c0,_));return new F(function(){return _1ps(_,_1pM);});break;case 1:var _1pN=B(_14o(_1c5,B(_1bl(_1bf,_1ae,new T2(1,new T1(3,_1pL.a),new T2(1,new T1(6,_1pL.b),new T2(1,new T1(2,_1pL.c),new T2(1,new T1(6,_1pL.d),new T2(1,new T1(6,_1pL.e),new T2(1,new T1(0,_1pL.f),new T2(1,new T1(0,_1pL.g),_1))))))))),_));return new F(function(){return _1ps(_,_1pN);});break;case 2:var _1pO=B(_14o(_1c5,B(_1bl(_1bf,_1ad,new T2(1,new T1(3,_1pL.a),new T2(1,new T1(0,_1pL.b),_1)))),_));return new F(function(){return _1ps(_,_1pO);});break;case 3:var _1pP=B(_14o(_1c5,B(_1bl(_1bf,_1ac,new T2(1,new T1(5,_1pL.a),new T2(1,new T1(6,_1pL.b),new T2(1,new T1(6,_1pL.c),new T2(1,new T1(2,_1pL.d),new T2(1,new T1(6,_1pL.e),new T2(1,new T1(0,_1pL.f),_1)))))))),_));return new F(function(){return _1ps(_,_1pP);});break;case 4:var _1pQ=B(_14o(_1c5,B(_1bl(_1bf,_1aa,new T2(1,new T1(0,_1pL.a),new T2(1,new T1(0,_1pL.b),_1)))),_));return new F(function(){return _1ps(_,_1pQ);});break;case 5:var _1pR=B(_14o(_1c5,B(_1bl(_1bf,_1a9,new T2(1,new T1(1,_1pL.a),new T2(1,new T1(0,_1pL.b),new T2(1,new T1(0,_1pL.c),_1))))),_));return new F(function(){return _1ps(_,_1pR);});break;default:var _1pS=B(_14o(_1c5,B(_1bl(_1bf,_1a8,new T2(1,new T1(1,_1pL.a),new T2(1,new T1(6,_1pL.b),new T2(1,new T1(0,_1pL.c),new T2(1,new T1(0,_1pL.d),_1)))))),_));return new F(function(){return _1ps(_,_1pS);});}},_1pT=E(_1pp.c);if(!_1pT._){var _1pU=B(_14o(_1hW,_1oS,_));return new F(function(){return _1pq(_,_1pU);});}else{var _1pV=new T(function(){return B(_1lf(0,_1pT.a,new T(function(){return B(_1oU(_1pT.b));})));}),_1pW=B(_14o(_1hW,new T2(1,_dP,_1pV),_));return new F(function(){return _1pq(_,_1pW);});}}},_1pX=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1pY=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1pZ=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1q0=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1q1=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1q2=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1q3=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1q4=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1q5=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1q6=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1q7=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1q8=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1q9=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qa=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qb=function(_){return new F(function(){return __jsNull();});},_1qc=function(_1qd){var _1qe=B(A1(_1qd,_));return E(_1qe);},_1qf=new T(function(){return B(_1qc(_1qb));}),_1qg=new T(function(){return E(_1qf);}),_1qh=function(_){var _1qi=eval(E(_Y0)),_1qj=__app1(E(_1qi),toJSStr(E(_14m))),_1qk=new T(function(){var _1ql=B(_ZI(B(_g4(_yK,new T(function(){var _1qm=String(_1qj);return fromJSStr(_1qm);})))));if(!_1ql._){return E(_eS);}else{if(!E(_1ql.b)._){var _1qn=E(_1ql.a);return new T4(0,new T(function(){return B(_bH(_1qn.a));}),new T(function(){return B(_8f(_1qn.b));}),new T(function(){return B(_9V(_1qn.c));}),new T(function(){return B(_4n(_1qn.d));}));}else{return E(_eQ);}}});return new F(function(){return _143(_1qk,_);});},_1qo=function(_){var _1qp=eval(E(_Y0)),_1qq=__app1(E(_1qp),toJSStr(E(_1c5))),_1qr=B(_1hE(new T(function(){var _1qs=String(_1qq);return fromJSStr(_1qs);}),_)),_1qt=__createJSFunc(0,function(_){var _1qu=B(_1i7(_));return _1qg;}),_1qv=__app2(E(_1q7),"clear_workspace",_1qt),_1qw=__createJSFunc(0,function(_){var _1qx=B(_1c6(_));return _1qg;}),_1qy=__app2(E(_1q6),"b2c",_1qw),_1qz=__createJSFunc(0,function(_){var _1qA=B(_1hS(_));return _1qg;}),_1qB=__app2(E(_1q5),"c2b",_1qz),_1qC=function(_1qD){var _1qE=new T(function(){var _1qF=Number(E(_1qD));return jsTrunc(_1qF);}),_1qG=function(_1qH){var _1qI=new T(function(){var _1qJ=Number(E(_1qH));return jsTrunc(_1qJ);}),_1qK=function(_1qL){var _1qM=new T(function(){var _1qN=Number(E(_1qL));return jsTrunc(_1qN);}),_1qO=function(_1qP,_){var _1qQ=B(_15e(_1qE,_1qI,_1qM,new T(function(){var _1qR=Number(E(_1qP));return jsTrunc(_1qR);},1),_));return _1qg;};return E(_1qO);};return E(_1qK);};return E(_1qG);},_1qS=__createJSFunc(5,E(_1qC)),_1qT=__app2(E(_1q4),"commit",_1qS),_1qU=function(_1qV){var _1qW=new T(function(){var _1qX=Number(E(_1qV));return jsTrunc(_1qX);}),_1qY=function(_1qZ){var _1r0=new T(function(){var _1r1=Number(E(_1qZ));return jsTrunc(_1r1);}),_1r2=function(_1r3,_){var _1r4=B(_14V(_1qW,_1r0,new T(function(){var _1r5=Number(E(_1r3));return jsTrunc(_1r5);},1),_));return _1qg;};return E(_1r2);};return E(_1qY);},_1r6=__createJSFunc(4,E(_1qU)),_1r7=__app2(E(_1q3),"redeem",_1r6),_1r8=function(_1r9){var _1ra=new T(function(){var _1rb=Number(E(_1r9));return jsTrunc(_1rb);}),_1rc=function(_1rd){var _1re=new T(function(){var _1rf=Number(E(_1rd));return jsTrunc(_1rf);}),_1rg=function(_1rh,_){var _1ri=B(_14t(_1ra,_1re,new T(function(){var _1rj=Number(E(_1rh));return jsTrunc(_1rj);},1),_));return _1qg;};return E(_1rg);};return E(_1rc);},_1rk=__createJSFunc(4,E(_1r8)),_1rl=__app2(E(_1q2),"claim",_1rk),_1rm=function(_1rn){var _1ro=new T(function(){var _1rp=Number(E(_1rn));return jsTrunc(_1rp);}),_1rq=function(_1rr){var _1rs=new T(function(){var _1rt=Number(E(_1rr));return jsTrunc(_1rt);}),_1ru=function(_1rv,_){var _1rw=B(_16C(_1ro,_1rs,new T(function(){var _1rx=Number(E(_1rv));return jsTrunc(_1rx);},1),_));return _1qg;};return E(_1ru);};return E(_1rq);},_1ry=__createJSFunc(4,E(_1rm)),_1rz=__app2(E(_1q1),"choose",_1ry),_1rA=__createJSFunc(0,function(_){var _1rB=B(_1oY(_));return _1qg;}),_1rC=__app2(E(_1q0),"execute",_1rA),_1rD=__createJSFunc(0,function(_){var _1rE=B(_1qh(_));return _1qg;}),_1rF=__app2(E(_1pZ),"refreshActions",_1rD),_1rG=function(_1rH,_){var _1rI=B(A2(_16o,new T(function(){var _1rJ=String(E(_1rH));return fromJSStr(_1rJ);}),_));return _1qg;},_1rK=__createJSFunc(2,E(_1rG)),_1rL=__app2(E(_1pY),"addAction",_1rK),_1rM=function(_1rN){var _1rO=new T(function(){var _1rP=String(E(_1rN));return fromJSStr(_1rP);}),_1rQ=function(_1rR,_){var _1rS=B(A3(_16Y,_1rO,new T(function(){var _1rT=Number(E(_1rR));return jsTrunc(_1rT);}),_));return _1qg;};return E(_1rQ);},_1rU=__createJSFunc(3,E(_1rM)),_1rV=__app2(E(_1pX),"addActionWithNum",_1rU),_1rW=__createJSFunc(0,function(_){var _1rX=B(_1jM(_));return _1qg;}),_1rY=__app2(E(_1qa),"depositIncentive",_1rW),_1rZ=__createJSFunc(0,function(_){var _1s0=B(_1jc(_));return _1qg;}),_1s1=__app2(E(_1q9),"crowdFunding",_1rZ),_1s2=__createJSFunc(0,function(_){var _1s3=B(_1ky(_));return _1qg;}),_1s4=__app2(E(_1q8),"escrow",_1s2),_1s5=__app1(E(_1qp),toJSStr(E(_14m))),_1s6=new T(function(){var _1s7=B(_ZI(B(_g4(_yK,new T(function(){var _1s8=String(_1s5);return fromJSStr(_1s8);})))));if(!_1s7._){return E(_eS);}else{if(!E(_1s7.b)._){var _1s9=E(_1s7.a);return new T4(0,new T(function(){return B(_bH(_1s9.a));}),new T(function(){return B(_8f(_1s9.b));}),new T(function(){return B(_9V(_1s9.c));}),new T(function(){return B(_4n(_1s9.d));}));}else{return E(_eQ);}}}),_1sa=B(_143(_1s6,_));return _bT;},_1sb=function(_){return new F(function(){return _1qo(_);});};
var hasteMain = function() {B(A(_1sb, [0]));};window.onload = hasteMain;
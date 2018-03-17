"use strict";
var __haste_prog_id = '2ebdc9232d7ec2d4da8b1ce06b6977e3a183613aeefda0e2788641138074d69b';
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

var _0=new T0(1),_1=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_2=function(_3){return new F(function(){return err(_1);});},_4=new T(function(){return B(_2(_));}),_5=function(_6,_7,_8){var _9=E(_8);if(!_9._){var _a=_9.a,_b=E(_7);if(!_b._){var _c=_b.a,_d=_b.b;if(_c<=(imul(3,_a)|0)){return new T4(0,(1+_c|0)+_a|0,E(_6),E(_b),E(_9));}else{var _e=E(_b.c);if(!_e._){var _f=_e.a,_g=E(_b.d);if(!_g._){var _h=_g.a,_i=_g.b,_j=_g.c;if(_h>=(imul(2,_f)|0)){var _k=function(_l){var _m=E(_g.d);return (_m._==0)?new T4(0,(1+_c|0)+_a|0,E(_i),E(new T4(0,(1+_f|0)+_l|0,E(_d),E(_e),E(_j))),E(new T4(0,(1+_a|0)+_m.a|0,E(_6),E(_m),E(_9)))):new T4(0,(1+_c|0)+_a|0,E(_i),E(new T4(0,(1+_f|0)+_l|0,E(_d),E(_e),E(_j))),E(new T4(0,1+_a|0,E(_6),E(_0),E(_9))));},_n=E(_j);if(!_n._){return new F(function(){return _k(_n.a);});}else{return new F(function(){return _k(0);});}}else{return new T4(0,(1+_c|0)+_a|0,E(_d),E(_e),E(new T4(0,(1+_a|0)+_h|0,E(_6),E(_g),E(_9))));}}else{return E(_4);}}else{return E(_4);}}}else{return new T4(0,1+_a|0,E(_6),E(_0),E(_9));}}else{var _o=E(_7);if(!_o._){var _p=_o.a,_q=_o.b,_r=_o.d,_s=E(_o.c);if(!_s._){var _t=_s.a,_u=E(_r);if(!_u._){var _v=_u.a,_w=_u.b,_x=_u.c;if(_v>=(imul(2,_t)|0)){var _y=function(_z){var _A=E(_u.d);return (_A._==0)?new T4(0,1+_p|0,E(_w),E(new T4(0,(1+_t|0)+_z|0,E(_q),E(_s),E(_x))),E(new T4(0,1+_A.a|0,E(_6),E(_A),E(_0)))):new T4(0,1+_p|0,E(_w),E(new T4(0,(1+_t|0)+_z|0,E(_q),E(_s),E(_x))),E(new T4(0,1,E(_6),E(_0),E(_0))));},_B=E(_x);if(!_B._){return new F(function(){return _y(_B.a);});}else{return new F(function(){return _y(0);});}}else{return new T4(0,1+_p|0,E(_q),E(_s),E(new T4(0,1+_v|0,E(_6),E(_u),E(_0))));}}else{return new T4(0,3,E(_q),E(_s),E(new T4(0,1,E(_6),E(_0),E(_0))));}}else{var _C=E(_r);return (_C._==0)?new T4(0,3,E(_C.b),E(new T4(0,1,E(_q),E(_0),E(_0))),E(new T4(0,1,E(_6),E(_0),E(_0)))):new T4(0,2,E(_6),E(_o),E(_0));}}else{return new T4(0,1,E(_6),E(_0),E(_0));}}},_D=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_E=function(_F){return new F(function(){return err(_D);});},_G=new T(function(){return B(_E(_));}),_H=function(_I,_J,_K){var _L=E(_J);if(!_L._){var _M=_L.a,_N=E(_K);if(!_N._){var _O=_N.a,_P=_N.b;if(_O<=(imul(3,_M)|0)){return new T4(0,(1+_M|0)+_O|0,E(_I),E(_L),E(_N));}else{var _Q=E(_N.c);if(!_Q._){var _R=_Q.a,_S=_Q.b,_T=_Q.c,_U=E(_N.d);if(!_U._){var _V=_U.a;if(_R>=(imul(2,_V)|0)){var _W=function(_X){var _Y=E(_I),_Z=E(_Q.d);return (_Z._==0)?new T4(0,(1+_M|0)+_O|0,E(_S),E(new T4(0,(1+_M|0)+_X|0,E(_Y),E(_L),E(_T))),E(new T4(0,(1+_V|0)+_Z.a|0,E(_P),E(_Z),E(_U)))):new T4(0,(1+_M|0)+_O|0,E(_S),E(new T4(0,(1+_M|0)+_X|0,E(_Y),E(_L),E(_T))),E(new T4(0,1+_V|0,E(_P),E(_0),E(_U))));},_10=E(_T);if(!_10._){return new F(function(){return _W(_10.a);});}else{return new F(function(){return _W(0);});}}else{return new T4(0,(1+_M|0)+_O|0,E(_P),E(new T4(0,(1+_M|0)+_R|0,E(_I),E(_L),E(_Q))),E(_U));}}else{return E(_G);}}else{return E(_G);}}}else{return new T4(0,1+_M|0,E(_I),E(_L),E(_0));}}else{var _11=E(_K);if(!_11._){var _12=_11.a,_13=_11.b,_14=_11.d,_15=E(_11.c);if(!_15._){var _16=_15.a,_17=_15.b,_18=_15.c,_19=E(_14);if(!_19._){var _1a=_19.a;if(_16>=(imul(2,_1a)|0)){var _1b=function(_1c){var _1d=E(_I),_1e=E(_15.d);return (_1e._==0)?new T4(0,1+_12|0,E(_17),E(new T4(0,1+_1c|0,E(_1d),E(_0),E(_18))),E(new T4(0,(1+_1a|0)+_1e.a|0,E(_13),E(_1e),E(_19)))):new T4(0,1+_12|0,E(_17),E(new T4(0,1+_1c|0,E(_1d),E(_0),E(_18))),E(new T4(0,1+_1a|0,E(_13),E(_0),E(_19))));},_1f=E(_18);if(!_1f._){return new F(function(){return _1b(_1f.a);});}else{return new F(function(){return _1b(0);});}}else{return new T4(0,1+_12|0,E(_13),E(new T4(0,1+_16|0,E(_I),E(_0),E(_15))),E(_19));}}else{return new T4(0,3,E(_17),E(new T4(0,1,E(_I),E(_0),E(_0))),E(new T4(0,1,E(_13),E(_0),E(_0))));}}else{var _1g=E(_14);return (_1g._==0)?new T4(0,3,E(_13),E(new T4(0,1,E(_I),E(_0),E(_0))),E(_1g)):new T4(0,2,E(_I),E(_0),E(_11));}}else{return new T4(0,1,E(_I),E(_0),E(_0));}}},_1h=function(_1i,_1j,_1k,_1l,_1m){var _1n=E(_1m);if(!_1n._){var _1o=_1n.c,_1p=_1n.d,_1q=E(_1n.b),_1r=E(_1i),_1s=E(_1q.a);if(_1r>=_1s){if(_1r!=_1s){return new F(function(){return _H(_1q,_1o,B(_1h(_1r,_1j,_1k,_1l,_1p)));});}else{var _1t=E(_1j),_1u=E(_1q.b);if(_1t>=_1u){if(_1t!=_1u){return new F(function(){return _H(_1q,_1o,B(_1h(_1r,_1t,_1k,_1l,_1p)));});}else{var _1v=E(_1k),_1w=E(_1q.c);if(_1v>=_1w){if(_1v!=_1w){return new F(function(){return _H(_1q,_1o,B(_1h(_1r,_1t,_1v,_1l,_1p)));});}else{var _1x=E(_1l),_1y=E(_1q.d);if(_1x>=_1y){if(_1x!=_1y){return new F(function(){return _H(_1q,_1o,B(_1h(_1r,_1t,_1v,_1x,_1p)));});}else{return new T4(0,_1n.a,E(new T4(0,_1r,_1t,_1v,_1x)),E(_1o),E(_1p));}}else{return new F(function(){return _5(_1q,B(_1h(_1r,_1t,_1v,_1x,_1o)),_1p);});}}}else{return new F(function(){return _5(_1q,B(_1h(_1r,_1t,_1v,_1l,_1o)),_1p);});}}}else{return new F(function(){return _5(_1q,B(_1h(_1r,_1t,_1k,_1l,_1o)),_1p);});}}}else{return new F(function(){return _5(_1q,B(_1h(_1r,_1j,_1k,_1l,_1o)),_1p);});}}else{return new T4(0,1,E(new T4(0,_1i,_1j,_1k,_1l)),E(_0),E(_0));}},_1z=function(_1A,_1B){while(1){var _1C=E(_1B);if(!_1C._){return E(_1A);}else{var _1D=E(_1C.a),_1E=B(_1h(_1D.a,_1D.b,_1D.c,_1D.d,_1A));_1A=_1E;_1B=_1C.b;continue;}}},_1F=function(_1G,_1H,_1I,_1J,_1K,_1L){return new F(function(){return _1z(B(_1h(_1H,_1I,_1J,_1K,_1G)),_1L);});},_1M=__Z,_1N=function(_1O){return new T4(0,1,E(_1O),E(_0),E(_0));},_1P=function(_1Q,_1R){var _1S=E(_1R);if(!_1S._){return new F(function(){return _H(_1S.b,_1S.c,B(_1P(_1Q,_1S.d)));});}else{return new F(function(){return _1N(_1Q);});}},_1T=function(_1U,_1V){var _1W=E(_1V);if(!_1W._){return new F(function(){return _5(_1W.b,B(_1T(_1U,_1W.c)),_1W.d);});}else{return new F(function(){return _1N(_1U);});}},_1X=function(_1Y,_1Z,_20,_21,_22){return new F(function(){return _H(_20,_21,B(_1P(_1Y,_22)));});},_23=function(_24,_25,_26,_27,_28){return new F(function(){return _5(_26,B(_1T(_24,_27)),_28);});},_29=function(_2a,_2b,_2c,_2d,_2e,_2f){var _2g=E(_2b);if(!_2g._){var _2h=_2g.a,_2i=_2g.b,_2j=_2g.c,_2k=_2g.d;if((imul(3,_2h)|0)>=_2c){if((imul(3,_2c)|0)>=_2h){return new T4(0,(_2h+_2c|0)+1|0,E(_2a),E(_2g),E(new T4(0,_2c,E(_2d),E(_2e),E(_2f))));}else{return new F(function(){return _H(_2i,_2j,B(_29(_2a,_2k,_2c,_2d,_2e,_2f)));});}}else{return new F(function(){return _5(_2d,B(_2l(_2a,_2h,_2i,_2j,_2k,_2e)),_2f);});}}else{return new F(function(){return _23(_2a,_2c,_2d,_2e,_2f);});}},_2l=function(_2m,_2n,_2o,_2p,_2q,_2r){var _2s=E(_2r);if(!_2s._){var _2t=_2s.a,_2u=_2s.b,_2v=_2s.c,_2w=_2s.d;if((imul(3,_2n)|0)>=_2t){if((imul(3,_2t)|0)>=_2n){return new T4(0,(_2n+_2t|0)+1|0,E(_2m),E(new T4(0,_2n,E(_2o),E(_2p),E(_2q))),E(_2s));}else{return new F(function(){return _H(_2o,_2p,B(_29(_2m,_2q,_2t,_2u,_2v,_2w)));});}}else{return new F(function(){return _5(_2u,B(_2l(_2m,_2n,_2o,_2p,_2q,_2v)),_2w);});}}else{return new F(function(){return _1X(_2m,_2n,_2o,_2p,_2q);});}},_2x=function(_2y,_2z,_2A){var _2B=E(_2z);if(!_2B._){var _2C=_2B.a,_2D=_2B.b,_2E=_2B.c,_2F=_2B.d,_2G=E(_2A);if(!_2G._){var _2H=_2G.a,_2I=_2G.b,_2J=_2G.c,_2K=_2G.d;if((imul(3,_2C)|0)>=_2H){if((imul(3,_2H)|0)>=_2C){return new T4(0,(_2C+_2H|0)+1|0,E(_2y),E(_2B),E(_2G));}else{return new F(function(){return _H(_2D,_2E,B(_29(_2y,_2F,_2H,_2I,_2J,_2K)));});}}else{return new F(function(){return _5(_2I,B(_2l(_2y,_2C,_2D,_2E,_2F,_2J)),_2K);});}}else{return new F(function(){return _1X(_2y,_2C,_2D,_2E,_2F);});}}else{return new F(function(){return _1T(_2y,_2A);});}},_2L=function(_2M,_2N){var _2O=E(_2N);if(!_2O._){return new T3(0,_0,_1M,_1M);}else{var _2P=_2O.a,_2Q=E(_2M);if(_2Q==1){var _2R=E(_2O.b);if(!_2R._){return new T3(0,new T(function(){return new T4(0,1,E(_2P),E(_0),E(_0));}),_1M,_1M);}else{var _2S=E(_2P),_2T=E(_2S.a),_2U=E(_2R.a),_2V=E(_2U.a);if(_2T>=_2V){if(_2T!=_2V){return new T3(0,new T4(0,1,E(_2S),E(_0),E(_0)),_1M,_2R);}else{var _2W=E(_2S.b),_2X=E(_2U.b);if(_2W>=_2X){if(_2W!=_2X){return new T3(0,new T4(0,1,E(_2S),E(_0),E(_0)),_1M,_2R);}else{var _2Y=E(_2S.c),_2Z=E(_2U.c);return (_2Y>=_2Z)?(_2Y!=_2Z)?new T3(0,new T4(0,1,E(_2S),E(_0),E(_0)),_1M,_2R):(E(_2S.d)<E(_2U.d))?new T3(0,new T4(0,1,E(_2S),E(_0),E(_0)),_2R,_1M):new T3(0,new T4(0,1,E(_2S),E(_0),E(_0)),_1M,_2R):new T3(0,new T4(0,1,E(_2S),E(_0),E(_0)),_2R,_1M);}}else{return new T3(0,new T4(0,1,E(_2S),E(_0),E(_0)),_2R,_1M);}}}else{return new T3(0,new T4(0,1,E(_2S),E(_0),E(_0)),_2R,_1M);}}}else{var _30=B(_2L(_2Q>>1,_2O)),_31=_30.a,_32=_30.c,_33=E(_30.b);if(!_33._){return new T3(0,_31,_1M,_32);}else{var _34=_33.a,_35=E(_33.b);if(!_35._){return new T3(0,new T(function(){return B(_1P(_34,_31));}),_1M,_32);}else{var _36=E(_34),_37=E(_36.a),_38=E(_35.a),_39=E(_38.a);if(_37>=_39){if(_37!=_39){return new T3(0,_31,_1M,_33);}else{var _3a=E(_36.b),_3b=E(_38.b);if(_3a>=_3b){if(_3a!=_3b){return new T3(0,_31,_1M,_33);}else{var _3c=E(_36.c),_3d=E(_38.c);if(_3c>=_3d){if(_3c!=_3d){return new T3(0,_31,_1M,_33);}else{if(E(_36.d)<E(_38.d)){var _3e=B(_2L(_2Q>>1,_35));return new T3(0,new T(function(){return B(_2x(_36,_31,_3e.a));}),_3e.b,_3e.c);}else{return new T3(0,_31,_1M,_33);}}}else{var _3f=B(_2L(_2Q>>1,_35));return new T3(0,new T(function(){return B(_2x(_36,_31,_3f.a));}),_3f.b,_3f.c);}}}else{var _3g=B(_2L(_2Q>>1,_35));return new T3(0,new T(function(){return B(_2x(_36,_31,_3g.a));}),_3g.b,_3g.c);}}}else{var _3h=B(_2L(_2Q>>1,_35));return new T3(0,new T(function(){return B(_2x(_36,_31,_3h.a));}),_3h.b,_3h.c);}}}}}},_3i=function(_3j,_3k,_3l){var _3m=E(_3l);if(!_3m._){return E(_3k);}else{var _3n=_3m.a,_3o=E(_3m.b);if(!_3o._){return new F(function(){return _1P(_3n,_3k);});}else{var _3p=E(_3n),_3q=_3p.b,_3r=_3p.c,_3s=_3p.d,_3t=E(_3p.a),_3u=E(_3o.a),_3v=E(_3u.a),_3w=function(_3x){var _3y=B(_2L(_3j,_3o)),_3z=_3y.a,_3A=E(_3y.c);if(!_3A._){return new F(function(){return _3i(_3j<<1,B(_2x(_3p,_3k,_3z)),_3y.b);});}else{return new F(function(){return _1z(B(_2x(_3p,_3k,_3z)),_3A);});}};if(_3t>=_3v){if(_3t!=_3v){return new F(function(){return _1F(_3k,_3t,_3q,_3r,_3s,_3o);});}else{var _3B=E(_3q),_3C=E(_3u.b);if(_3B>=_3C){if(_3B!=_3C){return new F(function(){return _1F(_3k,_3t,_3B,_3r,_3s,_3o);});}else{var _3D=E(_3r),_3E=E(_3u.c);if(_3D>=_3E){if(_3D!=_3E){return new F(function(){return _1F(_3k,_3t,_3B,_3D,_3s,_3o);});}else{var _3F=E(_3s);if(_3F<E(_3u.d)){return new F(function(){return _3w(_);});}else{return new F(function(){return _1F(_3k,_3t,_3B,_3D,_3F,_3o);});}}}else{return new F(function(){return _3w(_);});}}}else{return new F(function(){return _3w(_);});}}}else{return new F(function(){return _3w(_);});}}}},_3G=function(_3H){var _3I=E(_3H);if(!_3I._){return new T0(1);}else{var _3J=_3I.a,_3K=E(_3I.b);if(!_3K._){return new T4(0,1,E(_3J),E(_0),E(_0));}else{var _3L=_3K.b,_3M=E(_3J),_3N=E(_3M.a),_3O=E(_3K.a),_3P=_3O.b,_3Q=_3O.c,_3R=_3O.d,_3S=E(_3O.a);if(_3N>=_3S){if(_3N!=_3S){return new F(function(){return _1F(new T4(0,1,E(_3M),E(_0),E(_0)),_3S,_3P,_3Q,_3R,_3L);});}else{var _3T=E(_3M.b),_3U=E(_3P);if(_3T>=_3U){if(_3T!=_3U){return new F(function(){return _1F(new T4(0,1,E(_3M),E(_0),E(_0)),_3S,_3U,_3Q,_3R,_3L);});}else{var _3V=E(_3M.c),_3W=E(_3Q);if(_3V>=_3W){if(_3V!=_3W){return new F(function(){return _1F(new T4(0,1,E(_3M),E(_0),E(_0)),_3S,_3U,_3W,_3R,_3L);});}else{var _3X=E(_3R);if(E(_3M.d)<_3X){return new F(function(){return _3i(1,new T4(0,1,E(_3M),E(_0),E(_0)),_3K);});}else{return new F(function(){return _1F(new T4(0,1,E(_3M),E(_0),E(_0)),_3S,_3U,_3W,_3X,_3L);});}}}else{return new F(function(){return _3i(1,new T4(0,1,E(_3M),E(_0),E(_0)),_3K);});}}}else{return new F(function(){return _3i(1,new T4(0,1,E(_3M),E(_0),E(_0)),_3K);});}}}else{return new F(function(){return _3i(1,new T4(0,1,E(_3M),E(_0),E(_0)),_3K);});}}}},_3Y=function(_3Z,_40,_41,_42,_43){var _44=E(_3Z);if(_44==1){var _45=E(_43);if(!_45._){return new T3(0,new T4(0,1,E(new T3(0,_40,_41,_42)),E(_0),E(_0)),_1M,_1M);}else{var _46=E(_40),_47=E(_45.a),_48=E(_47.a);if(_46>=_48){if(_46!=_48){return new T3(0,new T4(0,1,E(new T3(0,_46,_41,_42)),E(_0),E(_0)),_1M,_45);}else{var _49=E(_47.b);return (_41>=_49)?(_41!=_49)?new T3(0,new T4(0,1,E(new T3(0,_46,_41,_42)),E(_0),E(_0)),_1M,_45):(_42<E(_47.c))?new T3(0,new T4(0,1,E(new T3(0,_46,_41,_42)),E(_0),E(_0)),_45,_1M):new T3(0,new T4(0,1,E(new T3(0,_46,_41,_42)),E(_0),E(_0)),_1M,_45):new T3(0,new T4(0,1,E(new T3(0,_46,_41,_42)),E(_0),E(_0)),_45,_1M);}}else{return new T3(0,new T4(0,1,E(new T3(0,_46,_41,_42)),E(_0),E(_0)),_45,_1M);}}}else{var _4a=B(_3Y(_44>>1,_40,_41,_42,_43)),_4b=_4a.a,_4c=_4a.c,_4d=E(_4a.b);if(!_4d._){return new T3(0,_4b,_1M,_4c);}else{var _4e=_4d.a,_4f=E(_4d.b);if(!_4f._){return new T3(0,new T(function(){return B(_1P(_4e,_4b));}),_1M,_4c);}else{var _4g=_4f.b,_4h=E(_4e),_4i=E(_4h.a),_4j=E(_4f.a),_4k=_4j.b,_4l=_4j.c,_4m=E(_4j.a);if(_4i>=_4m){if(_4i!=_4m){return new T3(0,_4b,_1M,_4d);}else{var _4n=E(_4h.b),_4o=E(_4k);if(_4n>=_4o){if(_4n!=_4o){return new T3(0,_4b,_1M,_4d);}else{var _4p=E(_4l);if(E(_4h.c)<_4p){var _4q=B(_3Y(_44>>1,_4m,_4o,_4p,_4g));return new T3(0,new T(function(){return B(_2x(_4h,_4b,_4q.a));}),_4q.b,_4q.c);}else{return new T3(0,_4b,_1M,_4d);}}}else{var _4r=B(_4s(_44>>1,_4m,_4o,_4l,_4g));return new T3(0,new T(function(){return B(_2x(_4h,_4b,_4r.a));}),_4r.b,_4r.c);}}}else{var _4t=B(_4u(_44>>1,_4m,_4k,_4l,_4g));return new T3(0,new T(function(){return B(_2x(_4h,_4b,_4t.a));}),_4t.b,_4t.c);}}}}},_4s=function(_4v,_4w,_4x,_4y,_4z){var _4A=E(_4v);if(_4A==1){var _4B=E(_4z);if(!_4B._){return new T3(0,new T4(0,1,E(new T3(0,_4w,_4x,_4y)),E(_0),E(_0)),_1M,_1M);}else{var _4C=E(_4w),_4D=E(_4B.a),_4E=E(_4D.a);if(_4C>=_4E){if(_4C!=_4E){return new T3(0,new T4(0,1,E(new T3(0,_4C,_4x,_4y)),E(_0),E(_0)),_1M,_4B);}else{var _4F=E(_4D.b);if(_4x>=_4F){if(_4x!=_4F){return new T3(0,new T4(0,1,E(new T3(0,_4C,_4x,_4y)),E(_0),E(_0)),_1M,_4B);}else{var _4G=E(_4y);return (_4G<E(_4D.c))?new T3(0,new T4(0,1,E(new T3(0,_4C,_4x,_4G)),E(_0),E(_0)),_4B,_1M):new T3(0,new T4(0,1,E(new T3(0,_4C,_4x,_4G)),E(_0),E(_0)),_1M,_4B);}}else{return new T3(0,new T4(0,1,E(new T3(0,_4C,_4x,_4y)),E(_0),E(_0)),_4B,_1M);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_4C,_4x,_4y)),E(_0),E(_0)),_4B,_1M);}}}else{var _4H=B(_4s(_4A>>1,_4w,_4x,_4y,_4z)),_4I=_4H.a,_4J=_4H.c,_4K=E(_4H.b);if(!_4K._){return new T3(0,_4I,_1M,_4J);}else{var _4L=_4K.a,_4M=E(_4K.b);if(!_4M._){return new T3(0,new T(function(){return B(_1P(_4L,_4I));}),_1M,_4J);}else{var _4N=_4M.b,_4O=E(_4L),_4P=E(_4O.a),_4Q=E(_4M.a),_4R=_4Q.b,_4S=_4Q.c,_4T=E(_4Q.a);if(_4P>=_4T){if(_4P!=_4T){return new T3(0,_4I,_1M,_4K);}else{var _4U=E(_4O.b),_4V=E(_4R);if(_4U>=_4V){if(_4U!=_4V){return new T3(0,_4I,_1M,_4K);}else{var _4W=E(_4S);if(E(_4O.c)<_4W){var _4X=B(_3Y(_4A>>1,_4T,_4V,_4W,_4N));return new T3(0,new T(function(){return B(_2x(_4O,_4I,_4X.a));}),_4X.b,_4X.c);}else{return new T3(0,_4I,_1M,_4K);}}}else{var _4Y=B(_4s(_4A>>1,_4T,_4V,_4S,_4N));return new T3(0,new T(function(){return B(_2x(_4O,_4I,_4Y.a));}),_4Y.b,_4Y.c);}}}else{var _4Z=B(_4u(_4A>>1,_4T,_4R,_4S,_4N));return new T3(0,new T(function(){return B(_2x(_4O,_4I,_4Z.a));}),_4Z.b,_4Z.c);}}}}},_4u=function(_50,_51,_52,_53,_54){var _55=E(_50);if(_55==1){var _56=E(_54);if(!_56._){return new T3(0,new T4(0,1,E(new T3(0,_51,_52,_53)),E(_0),E(_0)),_1M,_1M);}else{var _57=E(_51),_58=E(_56.a),_59=E(_58.a);if(_57>=_59){if(_57!=_59){return new T3(0,new T4(0,1,E(new T3(0,_57,_52,_53)),E(_0),E(_0)),_1M,_56);}else{var _5a=E(_52),_5b=E(_58.b);if(_5a>=_5b){if(_5a!=_5b){return new T3(0,new T4(0,1,E(new T3(0,_57,_5a,_53)),E(_0),E(_0)),_1M,_56);}else{var _5c=E(_53);return (_5c<E(_58.c))?new T3(0,new T4(0,1,E(new T3(0,_57,_5a,_5c)),E(_0),E(_0)),_56,_1M):new T3(0,new T4(0,1,E(new T3(0,_57,_5a,_5c)),E(_0),E(_0)),_1M,_56);}}else{return new T3(0,new T4(0,1,E(new T3(0,_57,_5a,_53)),E(_0),E(_0)),_56,_1M);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_57,_52,_53)),E(_0),E(_0)),_56,_1M);}}}else{var _5d=B(_4u(_55>>1,_51,_52,_53,_54)),_5e=_5d.a,_5f=_5d.c,_5g=E(_5d.b);if(!_5g._){return new T3(0,_5e,_1M,_5f);}else{var _5h=_5g.a,_5i=E(_5g.b);if(!_5i._){return new T3(0,new T(function(){return B(_1P(_5h,_5e));}),_1M,_5f);}else{var _5j=_5i.b,_5k=E(_5h),_5l=E(_5k.a),_5m=E(_5i.a),_5n=_5m.b,_5o=_5m.c,_5p=E(_5m.a);if(_5l>=_5p){if(_5l!=_5p){return new T3(0,_5e,_1M,_5g);}else{var _5q=E(_5k.b),_5r=E(_5n);if(_5q>=_5r){if(_5q!=_5r){return new T3(0,_5e,_1M,_5g);}else{var _5s=E(_5o);if(E(_5k.c)<_5s){var _5t=B(_3Y(_55>>1,_5p,_5r,_5s,_5j));return new T3(0,new T(function(){return B(_2x(_5k,_5e,_5t.a));}),_5t.b,_5t.c);}else{return new T3(0,_5e,_1M,_5g);}}}else{var _5u=B(_4s(_55>>1,_5p,_5r,_5o,_5j));return new T3(0,new T(function(){return B(_2x(_5k,_5e,_5u.a));}),_5u.b,_5u.c);}}}else{var _5v=B(_4u(_55>>1,_5p,_5n,_5o,_5j));return new T3(0,new T(function(){return B(_2x(_5k,_5e,_5v.a));}),_5v.b,_5v.c);}}}}},_5w=function(_5x,_5y,_5z,_5A,_5B){var _5C=E(_5B);if(!_5C._){var _5D=_5C.c,_5E=_5C.d,_5F=E(_5C.b),_5G=E(_5F.a);if(_5x>=_5G){if(_5x!=_5G){return new F(function(){return _H(_5F,_5D,B(_5w(_5x,_,_5z,_5A,_5E)));});}else{var _5H=E(_5F.b);if(_5z>=_5H){if(_5z!=_5H){return new F(function(){return _H(_5F,_5D,B(_5w(_5x,_,_5z,_5A,_5E)));});}else{var _5I=E(_5F.c);if(_5A>=_5I){if(_5A!=_5I){return new F(function(){return _H(_5F,_5D,B(_5w(_5x,_,_5z,_5A,_5E)));});}else{return new T4(0,_5C.a,E(new T3(0,_5x,_5z,_5A)),E(_5D),E(_5E));}}else{return new F(function(){return _5(_5F,B(_5w(_5x,_,_5z,_5A,_5D)),_5E);});}}}else{return new F(function(){return _5(_5F,B(_5w(_5x,_,_5z,_5A,_5D)),_5E);});}}}else{return new F(function(){return _5(_5F,B(_5w(_5x,_,_5z,_5A,_5D)),_5E);});}}else{return new T4(0,1,E(new T3(0,_5x,_5z,_5A)),E(_0),E(_0));}},_5J=function(_5K,_5L,_5M,_5N,_5O){var _5P=E(_5O);if(!_5P._){var _5Q=_5P.c,_5R=_5P.d,_5S=E(_5P.b),_5T=E(_5S.a);if(_5K>=_5T){if(_5K!=_5T){return new F(function(){return _H(_5S,_5Q,B(_5J(_5K,_,_5M,_5N,_5R)));});}else{var _5U=E(_5S.b);if(_5M>=_5U){if(_5M!=_5U){return new F(function(){return _H(_5S,_5Q,B(_5J(_5K,_,_5M,_5N,_5R)));});}else{var _5V=E(_5N),_5W=E(_5S.c);if(_5V>=_5W){if(_5V!=_5W){return new F(function(){return _H(_5S,_5Q,B(_5w(_5K,_,_5M,_5V,_5R)));});}else{return new T4(0,_5P.a,E(new T3(0,_5K,_5M,_5V)),E(_5Q),E(_5R));}}else{return new F(function(){return _5(_5S,B(_5w(_5K,_,_5M,_5V,_5Q)),_5R);});}}}else{return new F(function(){return _5(_5S,B(_5J(_5K,_,_5M,_5N,_5Q)),_5R);});}}}else{return new F(function(){return _5(_5S,B(_5J(_5K,_,_5M,_5N,_5Q)),_5R);});}}else{return new T4(0,1,E(new T3(0,_5K,_5M,_5N)),E(_0),E(_0));}},_5X=function(_5Y,_5Z,_60,_61,_62){var _63=E(_62);if(!_63._){var _64=_63.c,_65=_63.d,_66=E(_63.b),_67=E(_66.a);if(_5Y>=_67){if(_5Y!=_67){return new F(function(){return _H(_66,_64,B(_5X(_5Y,_,_60,_61,_65)));});}else{var _68=E(_60),_69=E(_66.b);if(_68>=_69){if(_68!=_69){return new F(function(){return _H(_66,_64,B(_5J(_5Y,_,_68,_61,_65)));});}else{var _6a=E(_61),_6b=E(_66.c);if(_6a>=_6b){if(_6a!=_6b){return new F(function(){return _H(_66,_64,B(_5w(_5Y,_,_68,_6a,_65)));});}else{return new T4(0,_63.a,E(new T3(0,_5Y,_68,_6a)),E(_64),E(_65));}}else{return new F(function(){return _5(_66,B(_5w(_5Y,_,_68,_6a,_64)),_65);});}}}else{return new F(function(){return _5(_66,B(_5J(_5Y,_,_68,_61,_64)),_65);});}}}else{return new F(function(){return _5(_66,B(_5X(_5Y,_,_60,_61,_64)),_65);});}}else{return new T4(0,1,E(new T3(0,_5Y,_60,_61)),E(_0),E(_0));}},_6c=function(_6d,_6e,_6f,_6g){var _6h=E(_6g);if(!_6h._){var _6i=_6h.c,_6j=_6h.d,_6k=E(_6h.b),_6l=E(_6d),_6m=E(_6k.a);if(_6l>=_6m){if(_6l!=_6m){return new F(function(){return _H(_6k,_6i,B(_5X(_6l,_,_6e,_6f,_6j)));});}else{var _6n=E(_6e),_6o=E(_6k.b);if(_6n>=_6o){if(_6n!=_6o){return new F(function(){return _H(_6k,_6i,B(_5J(_6l,_,_6n,_6f,_6j)));});}else{var _6p=E(_6f),_6q=E(_6k.c);if(_6p>=_6q){if(_6p!=_6q){return new F(function(){return _H(_6k,_6i,B(_5w(_6l,_,_6n,_6p,_6j)));});}else{return new T4(0,_6h.a,E(new T3(0,_6l,_6n,_6p)),E(_6i),E(_6j));}}else{return new F(function(){return _5(_6k,B(_5w(_6l,_,_6n,_6p,_6i)),_6j);});}}}else{return new F(function(){return _5(_6k,B(_5J(_6l,_,_6n,_6f,_6i)),_6j);});}}}else{return new F(function(){return _5(_6k,B(_5X(_6l,_,_6e,_6f,_6i)),_6j);});}}else{return new T4(0,1,E(new T3(0,_6d,_6e,_6f)),E(_0),E(_0));}},_6r=function(_6s,_6t){while(1){var _6u=E(_6t);if(!_6u._){return E(_6s);}else{var _6v=E(_6u.a),_6w=B(_6c(_6v.a,_6v.b,_6v.c,_6s));_6s=_6w;_6t=_6u.b;continue;}}},_6x=function(_6y,_6z,_6A,_6B,_6C){return new F(function(){return _6r(B(_6c(_6z,_6A,_6B,_6y)),_6C);});},_6D=function(_6E,_6F,_6G){var _6H=E(_6F);return new F(function(){return _6r(B(_6c(_6H.a,_6H.b,_6H.c,_6E)),_6G);});},_6I=function(_6J,_6K,_6L){var _6M=E(_6L);if(!_6M._){return E(_6K);}else{var _6N=_6M.a,_6O=E(_6M.b);if(!_6O._){return new F(function(){return _1P(_6N,_6K);});}else{var _6P=E(_6N),_6Q=_6P.b,_6R=_6P.c,_6S=E(_6P.a),_6T=E(_6O.a),_6U=_6T.b,_6V=_6T.c,_6W=E(_6T.a),_6X=function(_6Y){var _6Z=B(_4u(_6J,_6W,_6U,_6V,_6O.b)),_70=_6Z.a,_71=E(_6Z.c);if(!_71._){return new F(function(){return _6I(_6J<<1,B(_2x(_6P,_6K,_70)),_6Z.b);});}else{return new F(function(){return _6D(B(_2x(_6P,_6K,_70)),_71.a,_71.b);});}};if(_6S>=_6W){if(_6S!=_6W){return new F(function(){return _6x(_6K,_6S,_6Q,_6R,_6O);});}else{var _72=E(_6Q),_73=E(_6U);if(_72>=_73){if(_72!=_73){return new F(function(){return _6x(_6K,_6S,_72,_6R,_6O);});}else{var _74=E(_6R);if(_74<E(_6V)){return new F(function(){return _6X(_);});}else{return new F(function(){return _6x(_6K,_6S,_72,_74,_6O);});}}}else{return new F(function(){return _6X(_);});}}}else{return new F(function(){return _6X(_);});}}}},_75=function(_76,_77,_78,_79,_7a,_7b){var _7c=E(_7b);if(!_7c._){return new F(function(){return _1P(new T3(0,_78,_79,_7a),_77);});}else{var _7d=E(_78),_7e=E(_7c.a),_7f=_7e.b,_7g=_7e.c,_7h=E(_7e.a),_7i=function(_7j){var _7k=B(_4u(_76,_7h,_7f,_7g,_7c.b)),_7l=_7k.a,_7m=E(_7k.c);if(!_7m._){return new F(function(){return _6I(_76<<1,B(_2x(new T3(0,_7d,_79,_7a),_77,_7l)),_7k.b);});}else{return new F(function(){return _6D(B(_2x(new T3(0,_7d,_79,_7a),_77,_7l)),_7m.a,_7m.b);});}};if(_7d>=_7h){if(_7d!=_7h){return new F(function(){return _6x(_77,_7d,_79,_7a,_7c);});}else{var _7n=E(_7f);if(_79>=_7n){if(_79!=_7n){return new F(function(){return _6x(_77,_7d,_79,_7a,_7c);});}else{var _7o=E(_7a);if(_7o<E(_7g)){return new F(function(){return _7i(_);});}else{return new F(function(){return _6x(_77,_7d,_79,_7o,_7c);});}}}else{return new F(function(){return _7i(_);});}}}else{return new F(function(){return _7i(_);});}}},_7p=function(_7q,_7r,_7s,_7t,_7u,_7v){var _7w=E(_7v);if(!_7w._){return new F(function(){return _1P(new T3(0,_7s,_7t,_7u),_7r);});}else{var _7x=E(_7s),_7y=E(_7w.a),_7z=_7y.b,_7A=_7y.c,_7B=E(_7y.a),_7C=function(_7D){var _7E=B(_4u(_7q,_7B,_7z,_7A,_7w.b)),_7F=_7E.a,_7G=E(_7E.c);if(!_7G._){return new F(function(){return _6I(_7q<<1,B(_2x(new T3(0,_7x,_7t,_7u),_7r,_7F)),_7E.b);});}else{return new F(function(){return _6D(B(_2x(new T3(0,_7x,_7t,_7u),_7r,_7F)),_7G.a,_7G.b);});}};if(_7x>=_7B){if(_7x!=_7B){return new F(function(){return _6x(_7r,_7x,_7t,_7u,_7w);});}else{var _7H=E(_7z);if(_7t>=_7H){if(_7t!=_7H){return new F(function(){return _6x(_7r,_7x,_7t,_7u,_7w);});}else{if(_7u<E(_7A)){return new F(function(){return _7C(_);});}else{return new F(function(){return _6x(_7r,_7x,_7t,_7u,_7w);});}}}else{return new F(function(){return _7C(_);});}}}else{return new F(function(){return _7C(_);});}}},_7I=function(_7J,_7K,_7L,_7M,_7N,_7O){var _7P=E(_7O);if(!_7P._){return new F(function(){return _1P(new T3(0,_7L,_7M,_7N),_7K);});}else{var _7Q=E(_7L),_7R=E(_7P.a),_7S=_7R.b,_7T=_7R.c,_7U=E(_7R.a),_7V=function(_7W){var _7X=B(_4u(_7J,_7U,_7S,_7T,_7P.b)),_7Y=_7X.a,_7Z=E(_7X.c);if(!_7Z._){return new F(function(){return _6I(_7J<<1,B(_2x(new T3(0,_7Q,_7M,_7N),_7K,_7Y)),_7X.b);});}else{return new F(function(){return _6D(B(_2x(new T3(0,_7Q,_7M,_7N),_7K,_7Y)),_7Z.a,_7Z.b);});}};if(_7Q>=_7U){if(_7Q!=_7U){return new F(function(){return _6x(_7K,_7Q,_7M,_7N,_7P);});}else{var _80=E(_7M),_81=E(_7S);if(_80>=_81){if(_80!=_81){return new F(function(){return _6x(_7K,_7Q,_80,_7N,_7P);});}else{var _82=E(_7N);if(_82<E(_7T)){return new F(function(){return _7V(_);});}else{return new F(function(){return _6x(_7K,_7Q,_80,_82,_7P);});}}}else{return new F(function(){return _7V(_);});}}}else{return new F(function(){return _7V(_);});}}},_83=function(_84){var _85=E(_84);if(!_85._){return new T0(1);}else{var _86=_85.a,_87=E(_85.b);if(!_87._){return new T4(0,1,E(_86),E(_0),E(_0));}else{var _88=_87.b,_89=E(_86),_8a=E(_89.a),_8b=E(_87.a),_8c=_8b.b,_8d=_8b.c,_8e=E(_8b.a);if(_8a>=_8e){if(_8a!=_8e){return new F(function(){return _6x(new T4(0,1,E(_89),E(_0),E(_0)),_8e,_8c,_8d,_88);});}else{var _8f=E(_89.b),_8g=E(_8c);if(_8f>=_8g){if(_8f!=_8g){return new F(function(){return _6x(new T4(0,1,E(_89),E(_0),E(_0)),_8e,_8g,_8d,_88);});}else{var _8h=E(_8d);if(E(_89.c)<_8h){return new F(function(){return _7p(1,new T4(0,1,E(_89),E(_0),E(_0)),_8e,_8g,_8h,_88);});}else{return new F(function(){return _6x(new T4(0,1,E(_89),E(_0),E(_0)),_8e,_8g,_8h,_88);});}}}else{return new F(function(){return _75(1,new T4(0,1,E(_89),E(_0),E(_0)),_8e,_8g,_8d,_88);});}}}else{return new F(function(){return _7I(1,new T4(0,1,E(_89),E(_0),E(_0)),_8e,_8c,_8d,_88);});}}}},_8i=new T0(1),_8j=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_8k=function(_8l){return new F(function(){return err(_8j);});},_8m=new T(function(){return B(_8k(_));}),_8n=function(_8o,_8p,_8q,_8r){var _8s=E(_8q);if(!_8s._){var _8t=_8s.a,_8u=E(_8r);if(!_8u._){var _8v=_8u.a,_8w=_8u.b,_8x=_8u.c;if(_8v<=(imul(3,_8t)|0)){return new T5(0,(1+_8t|0)+_8v|0,E(_8o),_8p,E(_8s),E(_8u));}else{var _8y=E(_8u.d);if(!_8y._){var _8z=_8y.a,_8A=_8y.b,_8B=_8y.c,_8C=_8y.d,_8D=E(_8u.e);if(!_8D._){var _8E=_8D.a;if(_8z>=(imul(2,_8E)|0)){var _8F=function(_8G){var _8H=E(_8o),_8I=E(_8y.e);return (_8I._==0)?new T5(0,(1+_8t|0)+_8v|0,E(_8A),_8B,E(new T5(0,(1+_8t|0)+_8G|0,E(_8H),_8p,E(_8s),E(_8C))),E(new T5(0,(1+_8E|0)+_8I.a|0,E(_8w),_8x,E(_8I),E(_8D)))):new T5(0,(1+_8t|0)+_8v|0,E(_8A),_8B,E(new T5(0,(1+_8t|0)+_8G|0,E(_8H),_8p,E(_8s),E(_8C))),E(new T5(0,1+_8E|0,E(_8w),_8x,E(_8i),E(_8D))));},_8J=E(_8C);if(!_8J._){return new F(function(){return _8F(_8J.a);});}else{return new F(function(){return _8F(0);});}}else{return new T5(0,(1+_8t|0)+_8v|0,E(_8w),_8x,E(new T5(0,(1+_8t|0)+_8z|0,E(_8o),_8p,E(_8s),E(_8y))),E(_8D));}}else{return E(_8m);}}else{return E(_8m);}}}else{return new T5(0,1+_8t|0,E(_8o),_8p,E(_8s),E(_8i));}}else{var _8K=E(_8r);if(!_8K._){var _8L=_8K.a,_8M=_8K.b,_8N=_8K.c,_8O=_8K.e,_8P=E(_8K.d);if(!_8P._){var _8Q=_8P.a,_8R=_8P.b,_8S=_8P.c,_8T=_8P.d,_8U=E(_8O);if(!_8U._){var _8V=_8U.a;if(_8Q>=(imul(2,_8V)|0)){var _8W=function(_8X){var _8Y=E(_8o),_8Z=E(_8P.e);return (_8Z._==0)?new T5(0,1+_8L|0,E(_8R),_8S,E(new T5(0,1+_8X|0,E(_8Y),_8p,E(_8i),E(_8T))),E(new T5(0,(1+_8V|0)+_8Z.a|0,E(_8M),_8N,E(_8Z),E(_8U)))):new T5(0,1+_8L|0,E(_8R),_8S,E(new T5(0,1+_8X|0,E(_8Y),_8p,E(_8i),E(_8T))),E(new T5(0,1+_8V|0,E(_8M),_8N,E(_8i),E(_8U))));},_90=E(_8T);if(!_90._){return new F(function(){return _8W(_90.a);});}else{return new F(function(){return _8W(0);});}}else{return new T5(0,1+_8L|0,E(_8M),_8N,E(new T5(0,1+_8Q|0,E(_8o),_8p,E(_8i),E(_8P))),E(_8U));}}else{return new T5(0,3,E(_8R),_8S,E(new T5(0,1,E(_8o),_8p,E(_8i),E(_8i))),E(new T5(0,1,E(_8M),_8N,E(_8i),E(_8i))));}}else{var _91=E(_8O);return (_91._==0)?new T5(0,3,E(_8M),_8N,E(new T5(0,1,E(_8o),_8p,E(_8i),E(_8i))),E(_91)):new T5(0,2,E(_8o),_8p,E(_8i),E(_8K));}}else{return new T5(0,1,E(_8o),_8p,E(_8i),E(_8i));}}},_92=function(_93,_94){return new T5(0,1,E(_93),_94,E(_8i),E(_8i));},_95=function(_96,_97,_98){var _99=E(_98);if(!_99._){return new F(function(){return _8n(_99.b,_99.c,_99.d,B(_95(_96,_97,_99.e)));});}else{return new F(function(){return _92(_96,_97);});}},_9a=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_9b=function(_9c){return new F(function(){return err(_9a);});},_9d=new T(function(){return B(_9b(_));}),_9e=function(_9f,_9g,_9h,_9i){var _9j=E(_9i);if(!_9j._){var _9k=_9j.a,_9l=E(_9h);if(!_9l._){var _9m=_9l.a,_9n=_9l.b,_9o=_9l.c;if(_9m<=(imul(3,_9k)|0)){return new T5(0,(1+_9m|0)+_9k|0,E(_9f),_9g,E(_9l),E(_9j));}else{var _9p=E(_9l.d);if(!_9p._){var _9q=_9p.a,_9r=E(_9l.e);if(!_9r._){var _9s=_9r.a,_9t=_9r.b,_9u=_9r.c,_9v=_9r.d;if(_9s>=(imul(2,_9q)|0)){var _9w=function(_9x){var _9y=E(_9r.e);return (_9y._==0)?new T5(0,(1+_9m|0)+_9k|0,E(_9t),_9u,E(new T5(0,(1+_9q|0)+_9x|0,E(_9n),_9o,E(_9p),E(_9v))),E(new T5(0,(1+_9k|0)+_9y.a|0,E(_9f),_9g,E(_9y),E(_9j)))):new T5(0,(1+_9m|0)+_9k|0,E(_9t),_9u,E(new T5(0,(1+_9q|0)+_9x|0,E(_9n),_9o,E(_9p),E(_9v))),E(new T5(0,1+_9k|0,E(_9f),_9g,E(_8i),E(_9j))));},_9z=E(_9v);if(!_9z._){return new F(function(){return _9w(_9z.a);});}else{return new F(function(){return _9w(0);});}}else{return new T5(0,(1+_9m|0)+_9k|0,E(_9n),_9o,E(_9p),E(new T5(0,(1+_9k|0)+_9s|0,E(_9f),_9g,E(_9r),E(_9j))));}}else{return E(_9d);}}else{return E(_9d);}}}else{return new T5(0,1+_9k|0,E(_9f),_9g,E(_8i),E(_9j));}}else{var _9A=E(_9h);if(!_9A._){var _9B=_9A.a,_9C=_9A.b,_9D=_9A.c,_9E=_9A.e,_9F=E(_9A.d);if(!_9F._){var _9G=_9F.a,_9H=E(_9E);if(!_9H._){var _9I=_9H.a,_9J=_9H.b,_9K=_9H.c,_9L=_9H.d;if(_9I>=(imul(2,_9G)|0)){var _9M=function(_9N){var _9O=E(_9H.e);return (_9O._==0)?new T5(0,1+_9B|0,E(_9J),_9K,E(new T5(0,(1+_9G|0)+_9N|0,E(_9C),_9D,E(_9F),E(_9L))),E(new T5(0,1+_9O.a|0,E(_9f),_9g,E(_9O),E(_8i)))):new T5(0,1+_9B|0,E(_9J),_9K,E(new T5(0,(1+_9G|0)+_9N|0,E(_9C),_9D,E(_9F),E(_9L))),E(new T5(0,1,E(_9f),_9g,E(_8i),E(_8i))));},_9P=E(_9L);if(!_9P._){return new F(function(){return _9M(_9P.a);});}else{return new F(function(){return _9M(0);});}}else{return new T5(0,1+_9B|0,E(_9C),_9D,E(_9F),E(new T5(0,1+_9I|0,E(_9f),_9g,E(_9H),E(_8i))));}}else{return new T5(0,3,E(_9C),_9D,E(_9F),E(new T5(0,1,E(_9f),_9g,E(_8i),E(_8i))));}}else{var _9Q=E(_9E);return (_9Q._==0)?new T5(0,3,E(_9Q.b),_9Q.c,E(new T5(0,1,E(_9C),_9D,E(_8i),E(_8i))),E(new T5(0,1,E(_9f),_9g,E(_8i),E(_8i)))):new T5(0,2,E(_9f),_9g,E(_9A),E(_8i));}}else{return new T5(0,1,E(_9f),_9g,E(_8i),E(_8i));}}},_9R=function(_9S,_9T,_9U){var _9V=E(_9U);if(!_9V._){return new F(function(){return _9e(_9V.b,_9V.c,B(_9R(_9S,_9T,_9V.d)),_9V.e);});}else{return new F(function(){return _92(_9S,_9T);});}},_9W=function(_9X,_9Y,_9Z,_a0,_a1,_a2,_a3){return new F(function(){return _9e(_a0,_a1,B(_9R(_9X,_9Y,_a2)),_a3);});},_a4=function(_a5,_a6,_a7,_a8,_a9,_aa,_ab,_ac){var _ad=E(_a7);if(!_ad._){var _ae=_ad.a,_af=_ad.b,_ag=_ad.c,_ah=_ad.d,_ai=_ad.e;if((imul(3,_ae)|0)>=_a8){if((imul(3,_a8)|0)>=_ae){return new T5(0,(_ae+_a8|0)+1|0,E(_a5),_a6,E(_ad),E(new T5(0,_a8,E(_a9),_aa,E(_ab),E(_ac))));}else{return new F(function(){return _8n(_af,_ag,_ah,B(_a4(_a5,_a6,_ai,_a8,_a9,_aa,_ab,_ac)));});}}else{return new F(function(){return _9e(_a9,_aa,B(_aj(_a5,_a6,_ae,_af,_ag,_ah,_ai,_ab)),_ac);});}}else{return new F(function(){return _9W(_a5,_a6,_a8,_a9,_aa,_ab,_ac);});}},_aj=function(_ak,_al,_am,_an,_ao,_ap,_aq,_ar){var _as=E(_ar);if(!_as._){var _at=_as.a,_au=_as.b,_av=_as.c,_aw=_as.d,_ax=_as.e;if((imul(3,_am)|0)>=_at){if((imul(3,_at)|0)>=_am){return new T5(0,(_am+_at|0)+1|0,E(_ak),_al,E(new T5(0,_am,E(_an),_ao,E(_ap),E(_aq))),E(_as));}else{return new F(function(){return _8n(_an,_ao,_ap,B(_a4(_ak,_al,_aq,_at,_au,_av,_aw,_ax)));});}}else{return new F(function(){return _9e(_au,_av,B(_aj(_ak,_al,_am,_an,_ao,_ap,_aq,_aw)),_ax);});}}else{return new F(function(){return _95(_ak,_al,new T5(0,_am,E(_an),_ao,E(_ap),E(_aq)));});}},_ay=function(_az,_aA,_aB,_aC){var _aD=E(_aB);if(!_aD._){var _aE=_aD.a,_aF=_aD.b,_aG=_aD.c,_aH=_aD.d,_aI=_aD.e,_aJ=E(_aC);if(!_aJ._){var _aK=_aJ.a,_aL=_aJ.b,_aM=_aJ.c,_aN=_aJ.d,_aO=_aJ.e;if((imul(3,_aE)|0)>=_aK){if((imul(3,_aK)|0)>=_aE){return new T5(0,(_aE+_aK|0)+1|0,E(_az),_aA,E(_aD),E(_aJ));}else{return new F(function(){return _8n(_aF,_aG,_aH,B(_a4(_az,_aA,_aI,_aK,_aL,_aM,_aN,_aO)));});}}else{return new F(function(){return _9e(_aL,_aM,B(_aj(_az,_aA,_aE,_aF,_aG,_aH,_aI,_aN)),_aO);});}}else{return new F(function(){return _95(_az,_aA,_aD);});}}else{return new F(function(){return _9R(_az,_aA,_aC);});}},_aP=function(_aQ,_aR,_aS,_aT,_aU){var _aV=E(_aQ);if(_aV==1){var _aW=E(_aU);if(!_aW._){return new T3(0,new T5(0,1,E(new T2(0,_aR,_aS)),_aT,E(_8i),E(_8i)),_1M,_1M);}else{var _aX=E(E(_aW.a).a),_aY=E(_aR),_aZ=E(_aX.a);return (_aY>=_aZ)?(_aY!=_aZ)?new T3(0,new T5(0,1,E(new T2(0,_aY,_aS)),_aT,E(_8i),E(_8i)),_1M,_aW):(_aS<E(_aX.b))?new T3(0,new T5(0,1,E(new T2(0,_aY,_aS)),_aT,E(_8i),E(_8i)),_aW,_1M):new T3(0,new T5(0,1,E(new T2(0,_aY,_aS)),_aT,E(_8i),E(_8i)),_1M,_aW):new T3(0,new T5(0,1,E(new T2(0,_aY,_aS)),_aT,E(_8i),E(_8i)),_aW,_1M);}}else{var _b0=B(_aP(_aV>>1,_aR,_aS,_aT,_aU)),_b1=_b0.a,_b2=_b0.c,_b3=E(_b0.b);if(!_b3._){return new T3(0,_b1,_1M,_b2);}else{var _b4=E(_b3.a),_b5=_b4.a,_b6=_b4.b,_b7=E(_b3.b);if(!_b7._){return new T3(0,new T(function(){return B(_95(_b5,_b6,_b1));}),_1M,_b2);}else{var _b8=_b7.b,_b9=E(_b7.a),_ba=_b9.b,_bb=E(_b5),_bc=E(_b9.a),_bd=_bc.b,_be=E(_bb.a),_bf=E(_bc.a);if(_be>=_bf){if(_be!=_bf){return new T3(0,_b1,_1M,_b3);}else{var _bg=E(_bd);if(E(_bb.b)<_bg){var _bh=B(_aP(_aV>>1,_bf,_bg,_ba,_b8));return new T3(0,new T(function(){return B(_ay(_bb,_b6,_b1,_bh.a));}),_bh.b,_bh.c);}else{return new T3(0,_b1,_1M,_b3);}}}else{var _bi=B(_bj(_aV>>1,_bf,_bd,_ba,_b8));return new T3(0,new T(function(){return B(_ay(_bb,_b6,_b1,_bi.a));}),_bi.b,_bi.c);}}}}},_bj=function(_bk,_bl,_bm,_bn,_bo){var _bp=E(_bk);if(_bp==1){var _bq=E(_bo);if(!_bq._){return new T3(0,new T5(0,1,E(new T2(0,_bl,_bm)),_bn,E(_8i),E(_8i)),_1M,_1M);}else{var _br=E(E(_bq.a).a),_bs=E(_bl),_bt=E(_br.a);if(_bs>=_bt){if(_bs!=_bt){return new T3(0,new T5(0,1,E(new T2(0,_bs,_bm)),_bn,E(_8i),E(_8i)),_1M,_bq);}else{var _bu=E(_bm);return (_bu<E(_br.b))?new T3(0,new T5(0,1,E(new T2(0,_bs,_bu)),_bn,E(_8i),E(_8i)),_bq,_1M):new T3(0,new T5(0,1,E(new T2(0,_bs,_bu)),_bn,E(_8i),E(_8i)),_1M,_bq);}}else{return new T3(0,new T5(0,1,E(new T2(0,_bs,_bm)),_bn,E(_8i),E(_8i)),_bq,_1M);}}}else{var _bv=B(_bj(_bp>>1,_bl,_bm,_bn,_bo)),_bw=_bv.a,_bx=_bv.c,_by=E(_bv.b);if(!_by._){return new T3(0,_bw,_1M,_bx);}else{var _bz=E(_by.a),_bA=_bz.a,_bB=_bz.b,_bC=E(_by.b);if(!_bC._){return new T3(0,new T(function(){return B(_95(_bA,_bB,_bw));}),_1M,_bx);}else{var _bD=_bC.b,_bE=E(_bC.a),_bF=_bE.b,_bG=E(_bA),_bH=E(_bE.a),_bI=_bH.b,_bJ=E(_bG.a),_bK=E(_bH.a);if(_bJ>=_bK){if(_bJ!=_bK){return new T3(0,_bw,_1M,_by);}else{var _bL=E(_bI);if(E(_bG.b)<_bL){var _bM=B(_aP(_bp>>1,_bK,_bL,_bF,_bD));return new T3(0,new T(function(){return B(_ay(_bG,_bB,_bw,_bM.a));}),_bM.b,_bM.c);}else{return new T3(0,_bw,_1M,_by);}}}else{var _bN=B(_bj(_bp>>1,_bK,_bI,_bF,_bD));return new T3(0,new T(function(){return B(_ay(_bG,_bB,_bw,_bN.a));}),_bN.b,_bN.c);}}}}},_bO=function(_bP,_bQ,_bR,_bS,_bT){var _bU=E(_bT);if(!_bU._){var _bV=_bU.c,_bW=_bU.d,_bX=_bU.e,_bY=E(_bU.b),_bZ=E(_bY.a);if(_bP>=_bZ){if(_bP!=_bZ){return new F(function(){return _8n(_bY,_bV,_bW,B(_bO(_bP,_,_bR,_bS,_bX)));});}else{var _c0=E(_bY.b);if(_bR>=_c0){if(_bR!=_c0){return new F(function(){return _8n(_bY,_bV,_bW,B(_bO(_bP,_,_bR,_bS,_bX)));});}else{return new T5(0,_bU.a,E(new T2(0,_bP,_bR)),_bS,E(_bW),E(_bX));}}else{return new F(function(){return _9e(_bY,_bV,B(_bO(_bP,_,_bR,_bS,_bW)),_bX);});}}}else{return new F(function(){return _9e(_bY,_bV,B(_bO(_bP,_,_bR,_bS,_bW)),_bX);});}}else{return new T5(0,1,E(new T2(0,_bP,_bR)),_bS,E(_8i),E(_8i));}},_c1=function(_c2,_c3,_c4,_c5,_c6){var _c7=E(_c6);if(!_c7._){var _c8=_c7.c,_c9=_c7.d,_ca=_c7.e,_cb=E(_c7.b),_cc=E(_cb.a);if(_c2>=_cc){if(_c2!=_cc){return new F(function(){return _8n(_cb,_c8,_c9,B(_c1(_c2,_,_c4,_c5,_ca)));});}else{var _cd=E(_c4),_ce=E(_cb.b);if(_cd>=_ce){if(_cd!=_ce){return new F(function(){return _8n(_cb,_c8,_c9,B(_bO(_c2,_,_cd,_c5,_ca)));});}else{return new T5(0,_c7.a,E(new T2(0,_c2,_cd)),_c5,E(_c9),E(_ca));}}else{return new F(function(){return _9e(_cb,_c8,B(_bO(_c2,_,_cd,_c5,_c9)),_ca);});}}}else{return new F(function(){return _9e(_cb,_c8,B(_c1(_c2,_,_c4,_c5,_c9)),_ca);});}}else{return new T5(0,1,E(new T2(0,_c2,_c4)),_c5,E(_8i),E(_8i));}},_cf=function(_cg,_ch,_ci,_cj){var _ck=E(_cj);if(!_ck._){var _cl=_ck.c,_cm=_ck.d,_cn=_ck.e,_co=E(_ck.b),_cp=E(_cg),_cq=E(_co.a);if(_cp>=_cq){if(_cp!=_cq){return new F(function(){return _8n(_co,_cl,_cm,B(_c1(_cp,_,_ch,_ci,_cn)));});}else{var _cr=E(_ch),_cs=E(_co.b);if(_cr>=_cs){if(_cr!=_cs){return new F(function(){return _8n(_co,_cl,_cm,B(_bO(_cp,_,_cr,_ci,_cn)));});}else{return new T5(0,_ck.a,E(new T2(0,_cp,_cr)),_ci,E(_cm),E(_cn));}}else{return new F(function(){return _9e(_co,_cl,B(_bO(_cp,_,_cr,_ci,_cm)),_cn);});}}}else{return new F(function(){return _9e(_co,_cl,B(_c1(_cp,_,_ch,_ci,_cm)),_cn);});}}else{return new T5(0,1,E(new T2(0,_cg,_ch)),_ci,E(_8i),E(_8i));}},_ct=function(_cu,_cv){while(1){var _cw=E(_cv);if(!_cw._){return E(_cu);}else{var _cx=E(_cw.a),_cy=E(_cx.a),_cz=B(_cf(_cy.a,_cy.b,_cx.b,_cu));_cu=_cz;_cv=_cw.b;continue;}}},_cA=function(_cB,_cC,_cD,_cE,_cF){return new F(function(){return _ct(B(_cf(_cC,_cD,_cE,_cB)),_cF);});},_cG=function(_cH,_cI,_cJ){var _cK=E(_cI),_cL=E(_cK.a);return new F(function(){return _ct(B(_cf(_cL.a,_cL.b,_cK.b,_cH)),_cJ);});},_cM=function(_cN,_cO,_cP){var _cQ=E(_cP);if(!_cQ._){return E(_cO);}else{var _cR=E(_cQ.a),_cS=_cR.a,_cT=_cR.b,_cU=E(_cQ.b);if(!_cU._){return new F(function(){return _95(_cS,_cT,_cO);});}else{var _cV=E(_cU.a),_cW=E(_cS),_cX=_cW.b,_cY=E(_cV.a),_cZ=_cY.b,_d0=E(_cW.a),_d1=E(_cY.a),_d2=function(_d3){var _d4=B(_bj(_cN,_d1,_cZ,_cV.b,_cU.b)),_d5=_d4.a,_d6=E(_d4.c);if(!_d6._){return new F(function(){return _cM(_cN<<1,B(_ay(_cW,_cT,_cO,_d5)),_d4.b);});}else{return new F(function(){return _cG(B(_ay(_cW,_cT,_cO,_d5)),_d6.a,_d6.b);});}};if(_d0>=_d1){if(_d0!=_d1){return new F(function(){return _cA(_cO,_d0,_cX,_cT,_cU);});}else{var _d7=E(_cX);if(_d7<E(_cZ)){return new F(function(){return _d2(_);});}else{return new F(function(){return _cA(_cO,_d0,_d7,_cT,_cU);});}}}else{return new F(function(){return _d2(_);});}}}},_d8=function(_d9,_da,_db,_dc,_dd,_de){var _df=E(_de);if(!_df._){return new F(function(){return _95(new T2(0,_db,_dc),_dd,_da);});}else{var _dg=E(_df.a),_dh=E(_dg.a),_di=_dh.b,_dj=E(_db),_dk=E(_dh.a),_dl=function(_dm){var _dn=B(_bj(_d9,_dk,_di,_dg.b,_df.b)),_do=_dn.a,_dp=E(_dn.c);if(!_dp._){return new F(function(){return _cM(_d9<<1,B(_ay(new T2(0,_dj,_dc),_dd,_da,_do)),_dn.b);});}else{return new F(function(){return _cG(B(_ay(new T2(0,_dj,_dc),_dd,_da,_do)),_dp.a,_dp.b);});}};if(_dj>=_dk){if(_dj!=_dk){return new F(function(){return _cA(_da,_dj,_dc,_dd,_df);});}else{if(_dc<E(_di)){return new F(function(){return _dl(_);});}else{return new F(function(){return _cA(_da,_dj,_dc,_dd,_df);});}}}else{return new F(function(){return _dl(_);});}}},_dq=function(_dr,_ds,_dt,_du,_dv,_dw){var _dx=E(_dw);if(!_dx._){return new F(function(){return _95(new T2(0,_dt,_du),_dv,_ds);});}else{var _dy=E(_dx.a),_dz=E(_dy.a),_dA=_dz.b,_dB=E(_dt),_dC=E(_dz.a),_dD=function(_dE){var _dF=B(_bj(_dr,_dC,_dA,_dy.b,_dx.b)),_dG=_dF.a,_dH=E(_dF.c);if(!_dH._){return new F(function(){return _cM(_dr<<1,B(_ay(new T2(0,_dB,_du),_dv,_ds,_dG)),_dF.b);});}else{return new F(function(){return _cG(B(_ay(new T2(0,_dB,_du),_dv,_ds,_dG)),_dH.a,_dH.b);});}};if(_dB>=_dC){if(_dB!=_dC){return new F(function(){return _cA(_ds,_dB,_du,_dv,_dx);});}else{var _dI=E(_du);if(_dI<E(_dA)){return new F(function(){return _dD(_);});}else{return new F(function(){return _cA(_ds,_dB,_dI,_dv,_dx);});}}}else{return new F(function(){return _dD(_);});}}},_dJ=function(_dK){var _dL=E(_dK);if(!_dL._){return new T0(1);}else{var _dM=E(_dL.a),_dN=_dM.a,_dO=_dM.b,_dP=E(_dL.b);if(!_dP._){return new T5(0,1,E(_dN),_dO,E(_8i),E(_8i));}else{var _dQ=_dP.b,_dR=E(_dP.a),_dS=_dR.b,_dT=E(_dN),_dU=E(_dR.a),_dV=_dU.b,_dW=E(_dT.a),_dX=E(_dU.a);if(_dW>=_dX){if(_dW!=_dX){return new F(function(){return _cA(new T5(0,1,E(_dT),_dO,E(_8i),E(_8i)),_dX,_dV,_dS,_dQ);});}else{var _dY=E(_dV);if(E(_dT.b)<_dY){return new F(function(){return _d8(1,new T5(0,1,E(_dT),_dO,E(_8i),E(_8i)),_dX,_dY,_dS,_dQ);});}else{return new F(function(){return _cA(new T5(0,1,E(_dT),_dO,E(_8i),E(_8i)),_dX,_dY,_dS,_dQ);});}}}else{return new F(function(){return _dq(1,new T5(0,1,E(_dT),_dO,E(_8i),E(_8i)),_dX,_dV,_dS,_dQ);});}}}},_dZ=function(_e0,_e1,_e2,_e3,_e4){var _e5=E(_e0);if(_e5==1){var _e6=E(_e4);if(!_e6._){return new T3(0,new T5(0,1,E(new T2(0,_e1,_e2)),_e3,E(_8i),E(_8i)),_1M,_1M);}else{var _e7=E(E(_e6.a).a),_e8=E(_e1),_e9=E(_e7.a);return (_e8>=_e9)?(_e8!=_e9)?new T3(0,new T5(0,1,E(new T2(0,_e8,_e2)),_e3,E(_8i),E(_8i)),_1M,_e6):(_e2<E(_e7.b))?new T3(0,new T5(0,1,E(new T2(0,_e8,_e2)),_e3,E(_8i),E(_8i)),_e6,_1M):new T3(0,new T5(0,1,E(new T2(0,_e8,_e2)),_e3,E(_8i),E(_8i)),_1M,_e6):new T3(0,new T5(0,1,E(new T2(0,_e8,_e2)),_e3,E(_8i),E(_8i)),_e6,_1M);}}else{var _ea=B(_dZ(_e5>>1,_e1,_e2,_e3,_e4)),_eb=_ea.a,_ec=_ea.c,_ed=E(_ea.b);if(!_ed._){return new T3(0,_eb,_1M,_ec);}else{var _ee=E(_ed.a),_ef=_ee.a,_eg=_ee.b,_eh=E(_ed.b);if(!_eh._){return new T3(0,new T(function(){return B(_95(_ef,_eg,_eb));}),_1M,_ec);}else{var _ei=_eh.b,_ej=E(_eh.a),_ek=_ej.b,_el=E(_ef),_em=E(_ej.a),_en=_em.b,_eo=E(_el.a),_ep=E(_em.a);if(_eo>=_ep){if(_eo!=_ep){return new T3(0,_eb,_1M,_ed);}else{var _eq=E(_en);if(E(_el.b)<_eq){var _er=B(_dZ(_e5>>1,_ep,_eq,_ek,_ei));return new T3(0,new T(function(){return B(_ay(_el,_eg,_eb,_er.a));}),_er.b,_er.c);}else{return new T3(0,_eb,_1M,_ed);}}}else{var _es=B(_et(_e5>>1,_ep,_en,_ek,_ei));return new T3(0,new T(function(){return B(_ay(_el,_eg,_eb,_es.a));}),_es.b,_es.c);}}}}},_et=function(_eu,_ev,_ew,_ex,_ey){var _ez=E(_eu);if(_ez==1){var _eA=E(_ey);if(!_eA._){return new T3(0,new T5(0,1,E(new T2(0,_ev,_ew)),_ex,E(_8i),E(_8i)),_1M,_1M);}else{var _eB=E(E(_eA.a).a),_eC=E(_ev),_eD=E(_eB.a);if(_eC>=_eD){if(_eC!=_eD){return new T3(0,new T5(0,1,E(new T2(0,_eC,_ew)),_ex,E(_8i),E(_8i)),_1M,_eA);}else{var _eE=E(_ew);return (_eE<E(_eB.b))?new T3(0,new T5(0,1,E(new T2(0,_eC,_eE)),_ex,E(_8i),E(_8i)),_eA,_1M):new T3(0,new T5(0,1,E(new T2(0,_eC,_eE)),_ex,E(_8i),E(_8i)),_1M,_eA);}}else{return new T3(0,new T5(0,1,E(new T2(0,_eC,_ew)),_ex,E(_8i),E(_8i)),_eA,_1M);}}}else{var _eF=B(_et(_ez>>1,_ev,_ew,_ex,_ey)),_eG=_eF.a,_eH=_eF.c,_eI=E(_eF.b);if(!_eI._){return new T3(0,_eG,_1M,_eH);}else{var _eJ=E(_eI.a),_eK=_eJ.a,_eL=_eJ.b,_eM=E(_eI.b);if(!_eM._){return new T3(0,new T(function(){return B(_95(_eK,_eL,_eG));}),_1M,_eH);}else{var _eN=_eM.b,_eO=E(_eM.a),_eP=_eO.b,_eQ=E(_eK),_eR=E(_eO.a),_eS=_eR.b,_eT=E(_eQ.a),_eU=E(_eR.a);if(_eT>=_eU){if(_eT!=_eU){return new T3(0,_eG,_1M,_eI);}else{var _eV=E(_eS);if(E(_eQ.b)<_eV){var _eW=B(_dZ(_ez>>1,_eU,_eV,_eP,_eN));return new T3(0,new T(function(){return B(_ay(_eQ,_eL,_eG,_eW.a));}),_eW.b,_eW.c);}else{return new T3(0,_eG,_1M,_eI);}}}else{var _eX=B(_et(_ez>>1,_eU,_eS,_eP,_eN));return new T3(0,new T(function(){return B(_ay(_eQ,_eL,_eG,_eX.a));}),_eX.b,_eX.c);}}}}},_eY=function(_eZ,_f0,_f1,_f2,_f3){var _f4=E(_f3);if(!_f4._){var _f5=_f4.c,_f6=_f4.d,_f7=_f4.e,_f8=E(_f4.b),_f9=E(_f8.a);if(_eZ>=_f9){if(_eZ!=_f9){return new F(function(){return _8n(_f8,_f5,_f6,B(_eY(_eZ,_,_f1,_f2,_f7)));});}else{var _fa=E(_f8.b);if(_f1>=_fa){if(_f1!=_fa){return new F(function(){return _8n(_f8,_f5,_f6,B(_eY(_eZ,_,_f1,_f2,_f7)));});}else{return new T5(0,_f4.a,E(new T2(0,_eZ,_f1)),_f2,E(_f6),E(_f7));}}else{return new F(function(){return _9e(_f8,_f5,B(_eY(_eZ,_,_f1,_f2,_f6)),_f7);});}}}else{return new F(function(){return _9e(_f8,_f5,B(_eY(_eZ,_,_f1,_f2,_f6)),_f7);});}}else{return new T5(0,1,E(new T2(0,_eZ,_f1)),_f2,E(_8i),E(_8i));}},_fb=function(_fc,_fd,_fe,_ff,_fg){var _fh=E(_fg);if(!_fh._){var _fi=_fh.c,_fj=_fh.d,_fk=_fh.e,_fl=E(_fh.b),_fm=E(_fl.a);if(_fc>=_fm){if(_fc!=_fm){return new F(function(){return _8n(_fl,_fi,_fj,B(_fb(_fc,_,_fe,_ff,_fk)));});}else{var _fn=E(_fe),_fo=E(_fl.b);if(_fn>=_fo){if(_fn!=_fo){return new F(function(){return _8n(_fl,_fi,_fj,B(_eY(_fc,_,_fn,_ff,_fk)));});}else{return new T5(0,_fh.a,E(new T2(0,_fc,_fn)),_ff,E(_fj),E(_fk));}}else{return new F(function(){return _9e(_fl,_fi,B(_eY(_fc,_,_fn,_ff,_fj)),_fk);});}}}else{return new F(function(){return _9e(_fl,_fi,B(_fb(_fc,_,_fe,_ff,_fj)),_fk);});}}else{return new T5(0,1,E(new T2(0,_fc,_fe)),_ff,E(_8i),E(_8i));}},_fp=function(_fq,_fr,_fs,_ft){var _fu=E(_ft);if(!_fu._){var _fv=_fu.c,_fw=_fu.d,_fx=_fu.e,_fy=E(_fu.b),_fz=E(_fq),_fA=E(_fy.a);if(_fz>=_fA){if(_fz!=_fA){return new F(function(){return _8n(_fy,_fv,_fw,B(_fb(_fz,_,_fr,_fs,_fx)));});}else{var _fB=E(_fr),_fC=E(_fy.b);if(_fB>=_fC){if(_fB!=_fC){return new F(function(){return _8n(_fy,_fv,_fw,B(_eY(_fz,_,_fB,_fs,_fx)));});}else{return new T5(0,_fu.a,E(new T2(0,_fz,_fB)),_fs,E(_fw),E(_fx));}}else{return new F(function(){return _9e(_fy,_fv,B(_eY(_fz,_,_fB,_fs,_fw)),_fx);});}}}else{return new F(function(){return _9e(_fy,_fv,B(_fb(_fz,_,_fr,_fs,_fw)),_fx);});}}else{return new T5(0,1,E(new T2(0,_fq,_fr)),_fs,E(_8i),E(_8i));}},_fD=function(_fE,_fF){while(1){var _fG=E(_fF);if(!_fG._){return E(_fE);}else{var _fH=E(_fG.a),_fI=E(_fH.a),_fJ=B(_fp(_fI.a,_fI.b,_fH.b,_fE));_fE=_fJ;_fF=_fG.b;continue;}}},_fK=function(_fL,_fM,_fN,_fO,_fP){return new F(function(){return _fD(B(_fp(_fM,_fN,_fO,_fL)),_fP);});},_fQ=function(_fR,_fS,_fT){var _fU=E(_fS),_fV=E(_fU.a);return new F(function(){return _fD(B(_fp(_fV.a,_fV.b,_fU.b,_fR)),_fT);});},_fW=function(_fX,_fY,_fZ){var _g0=E(_fZ);if(!_g0._){return E(_fY);}else{var _g1=E(_g0.a),_g2=_g1.a,_g3=_g1.b,_g4=E(_g0.b);if(!_g4._){return new F(function(){return _95(_g2,_g3,_fY);});}else{var _g5=E(_g4.a),_g6=E(_g2),_g7=_g6.b,_g8=E(_g5.a),_g9=_g8.b,_ga=E(_g6.a),_gb=E(_g8.a),_gc=function(_gd){var _ge=B(_et(_fX,_gb,_g9,_g5.b,_g4.b)),_gf=_ge.a,_gg=E(_ge.c);if(!_gg._){return new F(function(){return _fW(_fX<<1,B(_ay(_g6,_g3,_fY,_gf)),_ge.b);});}else{return new F(function(){return _fQ(B(_ay(_g6,_g3,_fY,_gf)),_gg.a,_gg.b);});}};if(_ga>=_gb){if(_ga!=_gb){return new F(function(){return _fK(_fY,_ga,_g7,_g3,_g4);});}else{var _gh=E(_g7);if(_gh<E(_g9)){return new F(function(){return _gc(_);});}else{return new F(function(){return _fK(_fY,_ga,_gh,_g3,_g4);});}}}else{return new F(function(){return _gc(_);});}}}},_gi=function(_gj,_gk,_gl,_gm,_gn,_go){var _gp=E(_go);if(!_gp._){return new F(function(){return _95(new T2(0,_gl,_gm),_gn,_gk);});}else{var _gq=E(_gp.a),_gr=E(_gq.a),_gs=_gr.b,_gt=E(_gl),_gu=E(_gr.a),_gv=function(_gw){var _gx=B(_et(_gj,_gu,_gs,_gq.b,_gp.b)),_gy=_gx.a,_gz=E(_gx.c);if(!_gz._){return new F(function(){return _fW(_gj<<1,B(_ay(new T2(0,_gt,_gm),_gn,_gk,_gy)),_gx.b);});}else{return new F(function(){return _fQ(B(_ay(new T2(0,_gt,_gm),_gn,_gk,_gy)),_gz.a,_gz.b);});}};if(_gt>=_gu){if(_gt!=_gu){return new F(function(){return _fK(_gk,_gt,_gm,_gn,_gp);});}else{var _gA=E(_gm);if(_gA<E(_gs)){return new F(function(){return _gv(_);});}else{return new F(function(){return _fK(_gk,_gt,_gA,_gn,_gp);});}}}else{return new F(function(){return _gv(_);});}}},_gB=function(_gC,_gD,_gE,_gF,_gG,_gH){var _gI=E(_gH);if(!_gI._){return new F(function(){return _95(new T2(0,_gE,_gF),_gG,_gD);});}else{var _gJ=E(_gI.a),_gK=E(_gJ.a),_gL=_gK.b,_gM=E(_gE),_gN=E(_gK.a),_gO=function(_gP){var _gQ=B(_et(_gC,_gN,_gL,_gJ.b,_gI.b)),_gR=_gQ.a,_gS=E(_gQ.c);if(!_gS._){return new F(function(){return _fW(_gC<<1,B(_ay(new T2(0,_gM,_gF),_gG,_gD,_gR)),_gQ.b);});}else{return new F(function(){return _fQ(B(_ay(new T2(0,_gM,_gF),_gG,_gD,_gR)),_gS.a,_gS.b);});}};if(_gM>=_gN){if(_gM!=_gN){return new F(function(){return _fK(_gD,_gM,_gF,_gG,_gI);});}else{if(_gF<E(_gL)){return new F(function(){return _gO(_);});}else{return new F(function(){return _fK(_gD,_gM,_gF,_gG,_gI);});}}}else{return new F(function(){return _gO(_);});}}},_gT=function(_gU){var _gV=E(_gU);if(!_gV._){return new T0(1);}else{var _gW=E(_gV.a),_gX=_gW.a,_gY=_gW.b,_gZ=E(_gV.b);if(!_gZ._){return new T5(0,1,E(_gX),_gY,E(_8i),E(_8i));}else{var _h0=_gZ.b,_h1=E(_gZ.a),_h2=_h1.b,_h3=E(_gX),_h4=E(_h1.a),_h5=_h4.b,_h6=E(_h3.a),_h7=E(_h4.a);if(_h6>=_h7){if(_h6!=_h7){return new F(function(){return _fK(new T5(0,1,E(_h3),_gY,E(_8i),E(_8i)),_h7,_h5,_h2,_h0);});}else{var _h8=E(_h5);if(E(_h3.b)<_h8){return new F(function(){return _gB(1,new T5(0,1,E(_h3),_gY,E(_8i),E(_8i)),_h7,_h8,_h2,_h0);});}else{return new F(function(){return _fK(new T5(0,1,E(_h3),_gY,E(_8i),E(_8i)),_h7,_h8,_h2,_h0);});}}}else{return new F(function(){return _gi(1,new T5(0,1,E(_h3),_gY,E(_8i),E(_8i)),_h7,_h5,_h2,_h0);});}}}},_h9=0,_ha=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_hb=new T(function(){return B(err(_ha));}),_hc=function(_hd,_he){while(1){var _hf=B((function(_hg,_hh){var _hi=E(_hh);if(!_hi._){_hd=new T2(1,new T2(0,_hi.b,_hi.c),new T(function(){return B(_hc(_hg,_hi.e));}));_he=_hi.d;return __continue;}else{return E(_hg);}})(_hd,_he));if(_hf!=__continue){return _hf;}}},_hj=44,_hk=function(_hl,_hm,_hn){return new F(function(){return A1(_hl,new T2(1,_hj,new T(function(){return B(A1(_hm,_hn));})));});},_ho=new T(function(){return B(unCStr("CC "));}),_hp=new T(function(){return B(unCStr("IdentCC "));}),_hq=function(_hr,_hs){var _ht=E(_hr);return (_ht._==0)?E(_hs):new T2(1,_ht.a,new T(function(){return B(_hq(_ht.b,_hs));}));},_hu=function(_hv,_hw){var _hx=jsShowI(_hv);return new F(function(){return _hq(fromJSStr(_hx),_hw);});},_hy=41,_hz=40,_hA=function(_hB,_hC,_hD){if(_hC>=0){return new F(function(){return _hu(_hC,_hD);});}else{if(_hB<=6){return new F(function(){return _hu(_hC,_hD);});}else{return new T2(1,_hz,new T(function(){var _hE=jsShowI(_hC);return B(_hq(fromJSStr(_hE),new T2(1,_hy,_hD)));}));}}},_hF=function(_hG,_hH,_hI){if(_hG<11){return new F(function(){return _hq(_hp,new T(function(){return B(_hA(11,E(_hH),_hI));},1));});}else{var _hJ=new T(function(){return B(_hq(_hp,new T(function(){return B(_hA(11,E(_hH),new T2(1,_hy,_hI)));},1)));});return new T2(1,_hz,_hJ);}},_hK=32,_hL=function(_hM,_hN,_hO,_hP,_hQ,_hR){var _hS=function(_hT){var _hU=new T(function(){var _hV=new T(function(){return B(_hA(11,E(_hP),new T2(1,_hK,new T(function(){return B(_hA(11,E(_hQ),_hT));}))));});return B(_hA(11,E(_hO),new T2(1,_hK,_hV)));});return new F(function(){return _hF(11,_hN,new T2(1,_hK,_hU));});};if(_hM<11){return new F(function(){return _hq(_ho,new T(function(){return B(_hS(_hR));},1));});}else{var _hW=new T(function(){return B(_hq(_ho,new T(function(){return B(_hS(new T2(1,_hy,_hR)));},1)));});return new T2(1,_hz,_hW);}},_hX=function(_hY,_hZ){var _i0=E(_hY);return new F(function(){return _hL(0,_i0.a,_i0.b,_i0.c,_i0.d,_hZ);});},_i1=new T(function(){return B(unCStr("RC "));}),_i2=function(_i3,_i4,_i5,_i6,_i7){var _i8=function(_i9){var _ia=new T(function(){var _ib=new T(function(){return B(_hA(11,E(_i5),new T2(1,_hK,new T(function(){return B(_hA(11,E(_i6),_i9));}))));});return B(_hF(11,_i4,new T2(1,_hK,_ib)));},1);return new F(function(){return _hq(_i1,_ia);});};if(_i3<11){return new F(function(){return _i8(_i7);});}else{return new T2(1,_hz,new T(function(){return B(_i8(new T2(1,_hy,_i7)));}));}},_ic=function(_id,_ie){var _if=E(_id);return new F(function(){return _i2(0,_if.a,_if.b,_if.c,_ie);});},_ig=new T(function(){return B(unCStr("IdentPay "));}),_ih=function(_ii,_ij,_ik){if(_ii<11){return new F(function(){return _hq(_ig,new T(function(){return B(_hA(11,E(_ij),_ik));},1));});}else{var _il=new T(function(){return B(_hq(_ig,new T(function(){return B(_hA(11,E(_ij),new T2(1,_hy,_ik)));},1)));});return new T2(1,_hz,_il);}},_im=new T(function(){return B(unCStr(": empty list"));}),_in=new T(function(){return B(unCStr("Prelude."));}),_io=function(_ip){return new F(function(){return err(B(_hq(_in,new T(function(){return B(_hq(_ip,_im));},1))));});},_iq=new T(function(){return B(unCStr("foldr1"));}),_ir=new T(function(){return B(_io(_iq));}),_is=function(_it,_iu){var _iv=E(_iu);if(!_iv._){return E(_ir);}else{var _iw=_iv.a,_ix=E(_iv.b);if(!_ix._){return E(_iw);}else{return new F(function(){return A2(_it,_iw,new T(function(){return B(_is(_it,_ix));}));});}}},_iy=function(_iz,_iA,_iB){var _iC=new T(function(){var _iD=function(_iE){var _iF=E(_iz),_iG=new T(function(){return B(A3(_is,_hk,new T2(1,function(_iH){return new F(function(){return _ih(0,_iF.a,_iH);});},new T2(1,function(_iI){return new F(function(){return _hA(0,E(_iF.b),_iI);});},_1M)),new T2(1,_hy,_iE)));});return new T2(1,_hz,_iG);};return B(A3(_is,_hk,new T2(1,_iD,new T2(1,function(_iJ){return new F(function(){return _hA(0,E(_iA),_iJ);});},_1M)),new T2(1,_hy,_iB)));});return new T2(0,_hz,_iC);},_iK=function(_iL,_iM){var _iN=E(_iL),_iO=B(_iy(_iN.a,_iN.b,_iM));return new T2(1,_iO.a,_iO.b);},_iP=93,_iQ=91,_iR=function(_iS,_iT,_iU){var _iV=E(_iT);if(!_iV._){return new F(function(){return unAppCStr("[]",_iU);});}else{var _iW=new T(function(){var _iX=new T(function(){var _iY=function(_iZ){var _j0=E(_iZ);if(!_j0._){return E(new T2(1,_iP,_iU));}else{var _j1=new T(function(){return B(A2(_iS,_j0.a,new T(function(){return B(_iY(_j0.b));})));});return new T2(1,_hj,_j1);}};return B(_iY(_iV.b));});return B(A2(_iS,_iV.a,_iX));});return new T2(1,_iQ,_iW);}},_j2=function(_j3,_j4){return new F(function(){return _iR(_iK,_j3,_j4);});},_j5=new T(function(){return B(unCStr("IdentChoice "));}),_j6=function(_j7,_j8,_j9){if(_j7<11){return new F(function(){return _hq(_j5,new T(function(){return B(_hA(11,E(_j8),_j9));},1));});}else{var _ja=new T(function(){return B(_hq(_j5,new T(function(){return B(_hA(11,E(_j8),new T2(1,_hy,_j9)));},1)));});return new T2(1,_hz,_ja);}},_jb=function(_jc,_jd,_je){var _jf=new T(function(){var _jg=function(_jh){var _ji=E(_jc),_jj=new T(function(){return B(A3(_is,_hk,new T2(1,function(_jk){return new F(function(){return _j6(0,_ji.a,_jk);});},new T2(1,function(_jl){return new F(function(){return _hA(0,E(_ji.b),_jl);});},_1M)),new T2(1,_hy,_jh)));});return new T2(1,_hz,_jj);};return B(A3(_is,_hk,new T2(1,_jg,new T2(1,function(_jm){return new F(function(){return _hA(0,E(_jd),_jm);});},_1M)),new T2(1,_hy,_je)));});return new T2(0,_hz,_jf);},_jn=function(_jo,_jp){var _jq=E(_jo),_jr=B(_jb(_jq.a,_jq.b,_jp));return new T2(1,_jr.a,_jr.b);},_js=function(_jt,_ju){return new F(function(){return _iR(_jn,_jt,_ju);});},_jv=new T2(1,_hy,_1M),_jw=function(_jx,_jy){while(1){var _jz=B((function(_jA,_jB){var _jC=E(_jB);if(!_jC._){_jx=new T2(1,_jC.b,new T(function(){return B(_jw(_jA,_jC.d));}));_jy=_jC.c;return __continue;}else{return E(_jA);}})(_jx,_jy));if(_jz!=__continue){return _jz;}}},_jD=function(_jE,_jF,_jG,_jH){var _jI=new T(function(){var _jJ=new T(function(){return B(_hc(_1M,_jH));}),_jK=new T(function(){return B(_hc(_1M,_jG));}),_jL=new T(function(){return B(_jw(_1M,_jF));}),_jM=new T(function(){return B(_jw(_1M,_jE));});return B(A3(_is,_hk,new T2(1,function(_jN){return new F(function(){return _iR(_hX,_jM,_jN);});},new T2(1,function(_jO){return new F(function(){return _iR(_ic,_jL,_jO);});},new T2(1,function(_jP){return new F(function(){return _j2(_jK,_jP);});},new T2(1,function(_jQ){return new F(function(){return _js(_jJ,_jQ);});},_1M)))),_jv));});return new T2(0,_hz,_jI);},_jR=new T(function(){return B(err(_ha));}),_jS=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_jT=new T(function(){return B(err(_jS));}),_jU=new T0(2),_jV=function(_jW){return new T2(3,_jW,_jU);},_jX=new T(function(){return B(unCStr("base"));}),_jY=new T(function(){return B(unCStr("Control.Exception.Base"));}),_jZ=new T(function(){return B(unCStr("PatternMatchFail"));}),_k0=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_jX,_jY,_jZ),_k1=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_k0,_1M,_1M),_k2=function(_k3){return E(_k1);},_k4=function(_k5){return E(E(_k5).a);},_k6=function(_k7,_k8,_k9){var _ka=B(A1(_k7,_)),_kb=B(A1(_k8,_)),_kc=hs_eqWord64(_ka.a,_kb.a);if(!_kc){return __Z;}else{var _kd=hs_eqWord64(_ka.b,_kb.b);return (!_kd)?__Z:new T1(1,_k9);}},_ke=function(_kf){var _kg=E(_kf);return new F(function(){return _k6(B(_k4(_kg.a)),_k2,_kg.b);});},_kh=function(_ki){return E(E(_ki).a);},_kj=function(_kk){return new T2(0,_kl,_kk);},_km=function(_kn,_ko){return new F(function(){return _hq(E(_kn).a,_ko);});},_kp=function(_kq,_kr){return new F(function(){return _iR(_km,_kq,_kr);});},_ks=function(_kt,_ku,_kv){return new F(function(){return _hq(E(_ku).a,_kv);});},_kw=new T3(0,_ks,_kh,_kp),_kl=new T(function(){return new T5(0,_k2,_kw,_kj,_ke,_kh);}),_kx=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_ky=function(_kz){return E(E(_kz).c);},_kA=function(_kB,_kC){return new F(function(){return die(new T(function(){return B(A2(_ky,_kC,_kB));}));});},_kD=function(_kE,_kF){return new F(function(){return _kA(_kE,_kF);});},_kG=function(_kH,_kI){var _kJ=E(_kI);if(!_kJ._){return new T2(0,_1M,_1M);}else{var _kK=_kJ.a;if(!B(A1(_kH,_kK))){return new T2(0,_1M,_kJ);}else{var _kL=new T(function(){var _kM=B(_kG(_kH,_kJ.b));return new T2(0,_kM.a,_kM.b);});return new T2(0,new T2(1,_kK,new T(function(){return E(E(_kL).a);})),new T(function(){return E(E(_kL).b);}));}}},_kN=32,_kO=new T(function(){return B(unCStr("\n"));}),_kP=function(_kQ){return (E(_kQ)==124)?false:true;},_kR=function(_kS,_kT){var _kU=B(_kG(_kP,B(unCStr(_kS)))),_kV=_kU.a,_kW=function(_kX,_kY){var _kZ=new T(function(){var _l0=new T(function(){return B(_hq(_kT,new T(function(){return B(_hq(_kY,_kO));},1)));});return B(unAppCStr(": ",_l0));},1);return new F(function(){return _hq(_kX,_kZ);});},_l1=E(_kU.b);if(!_l1._){return new F(function(){return _kW(_kV,_1M);});}else{if(E(_l1.a)==124){return new F(function(){return _kW(_kV,new T2(1,_kN,_l1.b));});}else{return new F(function(){return _kW(_kV,_1M);});}}},_l2=function(_l3){return new F(function(){return _kD(new T1(0,new T(function(){return B(_kR(_l3,_kx));})),_kl);});},_l4=new T(function(){return B(_l2("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_l5=function(_l6,_l7){while(1){var _l8=B((function(_l9,_la){var _lb=E(_l9);switch(_lb._){case 0:var _lc=E(_la);if(!_lc._){return __Z;}else{_l6=B(A1(_lb.a,_lc.a));_l7=_lc.b;return __continue;}break;case 1:var _ld=B(A1(_lb.a,_la)),_le=_la;_l6=_ld;_l7=_le;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_lb.a,_la),new T(function(){return B(_l5(_lb.b,_la));}));default:return E(_lb.a);}})(_l6,_l7));if(_l8!=__continue){return _l8;}}},_lf=function(_lg,_lh){var _li=function(_lj){var _lk=E(_lh);if(_lk._==3){return new T2(3,_lk.a,new T(function(){return B(_lf(_lg,_lk.b));}));}else{var _ll=E(_lg);if(_ll._==2){return E(_lk);}else{var _lm=E(_lk);if(_lm._==2){return E(_ll);}else{var _ln=function(_lo){var _lp=E(_lm);if(_lp._==4){var _lq=function(_lr){return new T1(4,new T(function(){return B(_hq(B(_l5(_ll,_lr)),_lp.a));}));};return new T1(1,_lq);}else{var _ls=E(_ll);if(_ls._==1){var _lt=_ls.a,_lu=E(_lp);if(!_lu._){return new T1(1,function(_lv){return new F(function(){return _lf(B(A1(_lt,_lv)),_lu);});});}else{var _lw=function(_lx){return new F(function(){return _lf(B(A1(_lt,_lx)),new T(function(){return B(A1(_lu.a,_lx));}));});};return new T1(1,_lw);}}else{var _ly=E(_lp);if(!_ly._){return E(_l4);}else{var _lz=function(_lA){return new F(function(){return _lf(_ls,new T(function(){return B(A1(_ly.a,_lA));}));});};return new T1(1,_lz);}}}},_lB=E(_ll);switch(_lB._){case 1:var _lC=E(_lm);if(_lC._==4){var _lD=function(_lE){return new T1(4,new T(function(){return B(_hq(B(_l5(B(A1(_lB.a,_lE)),_lE)),_lC.a));}));};return new T1(1,_lD);}else{return new F(function(){return _ln(_);});}break;case 4:var _lF=_lB.a,_lG=E(_lm);switch(_lG._){case 0:var _lH=function(_lI){var _lJ=new T(function(){return B(_hq(_lF,new T(function(){return B(_l5(_lG,_lI));},1)));});return new T1(4,_lJ);};return new T1(1,_lH);case 1:var _lK=function(_lL){var _lM=new T(function(){return B(_hq(_lF,new T(function(){return B(_l5(B(A1(_lG.a,_lL)),_lL));},1)));});return new T1(4,_lM);};return new T1(1,_lK);default:return new T1(4,new T(function(){return B(_hq(_lF,_lG.a));}));}break;default:return new F(function(){return _ln(_);});}}}}},_lN=E(_lg);switch(_lN._){case 0:var _lO=E(_lh);if(!_lO._){var _lP=function(_lQ){return new F(function(){return _lf(B(A1(_lN.a,_lQ)),new T(function(){return B(A1(_lO.a,_lQ));}));});};return new T1(0,_lP);}else{return new F(function(){return _li(_);});}break;case 3:return new T2(3,_lN.a,new T(function(){return B(_lf(_lN.b,_lh));}));default:return new F(function(){return _li(_);});}},_lR=new T(function(){return B(unCStr("("));}),_lS=new T(function(){return B(unCStr(")"));}),_lT=function(_lU,_lV){while(1){var _lW=E(_lU);if(!_lW._){return (E(_lV)._==0)?true:false;}else{var _lX=E(_lV);if(!_lX._){return false;}else{if(E(_lW.a)!=E(_lX.a)){return false;}else{_lU=_lW.b;_lV=_lX.b;continue;}}}}},_lY=function(_lZ,_m0){return E(_lZ)!=E(_m0);},_m1=function(_m2,_m3){return E(_m2)==E(_m3);},_m4=new T2(0,_m1,_lY),_m5=function(_m6,_m7){while(1){var _m8=E(_m6);if(!_m8._){return (E(_m7)._==0)?true:false;}else{var _m9=E(_m7);if(!_m9._){return false;}else{if(E(_m8.a)!=E(_m9.a)){return false;}else{_m6=_m8.b;_m7=_m9.b;continue;}}}}},_ma=function(_mb,_mc){return (!B(_m5(_mb,_mc)))?true:false;},_md=new T2(0,_m5,_ma),_me=function(_mf,_mg){var _mh=E(_mf);switch(_mh._){case 0:return new T1(0,function(_mi){return new F(function(){return _me(B(A1(_mh.a,_mi)),_mg);});});case 1:return new T1(1,function(_mj){return new F(function(){return _me(B(A1(_mh.a,_mj)),_mg);});});case 2:return new T0(2);case 3:return new F(function(){return _lf(B(A1(_mg,_mh.a)),new T(function(){return B(_me(_mh.b,_mg));}));});break;default:var _mk=function(_ml){var _mm=E(_ml);if(!_mm._){return __Z;}else{var _mn=E(_mm.a);return new F(function(){return _hq(B(_l5(B(A1(_mg,_mn.a)),_mn.b)),new T(function(){return B(_mk(_mm.b));},1));});}},_mo=B(_mk(_mh.a));return (_mo._==0)?new T0(2):new T1(4,_mo);}},_mp=function(_mq,_mr){var _ms=E(_mq);if(!_ms){return new F(function(){return A1(_mr,_h9);});}else{var _mt=new T(function(){return B(_mp(_ms-1|0,_mr));});return new T1(0,function(_mu){return E(_mt);});}},_mv=function(_mw,_mx,_my){var _mz=new T(function(){return B(A1(_mw,_jV));}),_mA=function(_mB,_mC,_mD,_mE){while(1){var _mF=B((function(_mG,_mH,_mI,_mJ){var _mK=E(_mG);switch(_mK._){case 0:var _mL=E(_mH);if(!_mL._){return new F(function(){return A1(_mx,_mJ);});}else{var _mM=_mI+1|0,_mN=_mJ;_mB=B(A1(_mK.a,_mL.a));_mC=_mL.b;_mD=_mM;_mE=_mN;return __continue;}break;case 1:var _mO=B(A1(_mK.a,_mH)),_mP=_mH,_mM=_mI,_mN=_mJ;_mB=_mO;_mC=_mP;_mD=_mM;_mE=_mN;return __continue;case 2:return new F(function(){return A1(_mx,_mJ);});break;case 3:var _mQ=new T(function(){return B(_me(_mK,_mJ));});return new F(function(){return _mp(_mI,function(_mR){return E(_mQ);});});break;default:return new F(function(){return _me(_mK,_mJ);});}})(_mB,_mC,_mD,_mE));if(_mF!=__continue){return _mF;}}};return function(_mS){return new F(function(){return _mA(_mz,_mS,0,_my);});};},_mT=function(_mU){return new F(function(){return A1(_mU,_1M);});},_mV=function(_mW,_mX){var _mY=function(_mZ){var _n0=E(_mZ);if(!_n0._){return E(_mT);}else{var _n1=_n0.a;if(!B(A1(_mW,_n1))){return E(_mT);}else{var _n2=new T(function(){return B(_mY(_n0.b));}),_n3=function(_n4){var _n5=new T(function(){return B(A1(_n2,function(_n6){return new F(function(){return A1(_n4,new T2(1,_n1,_n6));});}));});return new T1(0,function(_n7){return E(_n5);});};return E(_n3);}}};return function(_n8){return new F(function(){return A2(_mY,_n8,_mX);});};},_n9=new T0(6),_na=function(_nb){return E(_nb);},_nc=new T(function(){return B(unCStr("valDig: Bad base"));}),_nd=new T(function(){return B(err(_nc));}),_ne=function(_nf,_ng){var _nh=function(_ni,_nj){var _nk=E(_ni);if(!_nk._){var _nl=new T(function(){return B(A1(_nj,_1M));});return function(_nm){return new F(function(){return A1(_nm,_nl);});};}else{var _nn=E(_nk.a),_no=function(_np){var _nq=new T(function(){return B(_nh(_nk.b,function(_nr){return new F(function(){return A1(_nj,new T2(1,_np,_nr));});}));}),_ns=function(_nt){var _nu=new T(function(){return B(A1(_nq,_nt));});return new T1(0,function(_nv){return E(_nu);});};return E(_ns);};switch(E(_nf)){case 8:if(48>_nn){var _nw=new T(function(){return B(A1(_nj,_1M));});return function(_nx){return new F(function(){return A1(_nx,_nw);});};}else{if(_nn>55){var _ny=new T(function(){return B(A1(_nj,_1M));});return function(_nz){return new F(function(){return A1(_nz,_ny);});};}else{return new F(function(){return _no(_nn-48|0);});}}break;case 10:if(48>_nn){var _nA=new T(function(){return B(A1(_nj,_1M));});return function(_nB){return new F(function(){return A1(_nB,_nA);});};}else{if(_nn>57){var _nC=new T(function(){return B(A1(_nj,_1M));});return function(_nD){return new F(function(){return A1(_nD,_nC);});};}else{return new F(function(){return _no(_nn-48|0);});}}break;case 16:if(48>_nn){if(97>_nn){if(65>_nn){var _nE=new T(function(){return B(A1(_nj,_1M));});return function(_nF){return new F(function(){return A1(_nF,_nE);});};}else{if(_nn>70){var _nG=new T(function(){return B(A1(_nj,_1M));});return function(_nH){return new F(function(){return A1(_nH,_nG);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{if(_nn>102){if(65>_nn){var _nI=new T(function(){return B(A1(_nj,_1M));});return function(_nJ){return new F(function(){return A1(_nJ,_nI);});};}else{if(_nn>70){var _nK=new T(function(){return B(A1(_nj,_1M));});return function(_nL){return new F(function(){return A1(_nL,_nK);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{return new F(function(){return _no((_nn-97|0)+10|0);});}}}else{if(_nn>57){if(97>_nn){if(65>_nn){var _nM=new T(function(){return B(A1(_nj,_1M));});return function(_nN){return new F(function(){return A1(_nN,_nM);});};}else{if(_nn>70){var _nO=new T(function(){return B(A1(_nj,_1M));});return function(_nP){return new F(function(){return A1(_nP,_nO);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{if(_nn>102){if(65>_nn){var _nQ=new T(function(){return B(A1(_nj,_1M));});return function(_nR){return new F(function(){return A1(_nR,_nQ);});};}else{if(_nn>70){var _nS=new T(function(){return B(A1(_nj,_1M));});return function(_nT){return new F(function(){return A1(_nT,_nS);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{return new F(function(){return _no((_nn-97|0)+10|0);});}}}else{return new F(function(){return _no(_nn-48|0);});}}break;default:return E(_nd);}}},_nU=function(_nV){var _nW=E(_nV);if(!_nW._){return new T0(2);}else{return new F(function(){return A1(_ng,_nW);});}};return function(_nX){return new F(function(){return A3(_nh,_nX,_na,_nU);});};},_nY=16,_nZ=8,_o0=function(_o1){var _o2=function(_o3){return new F(function(){return A1(_o1,new T1(5,new T2(0,_nZ,_o3)));});},_o4=function(_o5){return new F(function(){return A1(_o1,new T1(5,new T2(0,_nY,_o5)));});},_o6=function(_o7){switch(E(_o7)){case 79:return new T1(1,B(_ne(_nZ,_o2)));case 88:return new T1(1,B(_ne(_nY,_o4)));case 111:return new T1(1,B(_ne(_nZ,_o2)));case 120:return new T1(1,B(_ne(_nY,_o4)));default:return new T0(2);}};return function(_o8){return (E(_o8)==48)?E(new T1(0,_o6)):new T0(2);};},_o9=function(_oa){return new T1(0,B(_o0(_oa)));},_ob=__Z,_oc=function(_od){return new F(function(){return A1(_od,_ob);});},_oe=function(_of){return new F(function(){return A1(_of,_ob);});},_og=10,_oh=new T1(0,1),_oi=new T1(0,2147483647),_oj=function(_ok,_ol){while(1){var _om=E(_ok);if(!_om._){var _on=_om.a,_oo=E(_ol);if(!_oo._){var _op=_oo.a,_oq=addC(_on,_op);if(!E(_oq.b)){return new T1(0,_oq.a);}else{_ok=new T1(1,I_fromInt(_on));_ol=new T1(1,I_fromInt(_op));continue;}}else{_ok=new T1(1,I_fromInt(_on));_ol=_oo;continue;}}else{var _or=E(_ol);if(!_or._){_ok=_om;_ol=new T1(1,I_fromInt(_or.a));continue;}else{return new T1(1,I_add(_om.a,_or.a));}}}},_os=new T(function(){return B(_oj(_oi,_oh));}),_ot=function(_ou){var _ov=E(_ou);if(!_ov._){var _ow=E(_ov.a);return (_ow==( -2147483648))?E(_os):new T1(0, -_ow);}else{return new T1(1,I_negate(_ov.a));}},_ox=new T1(0,10),_oy=function(_oz,_oA){while(1){var _oB=E(_oz);if(!_oB._){return E(_oA);}else{var _oC=_oA+1|0;_oz=_oB.b;_oA=_oC;continue;}}},_oD=function(_oE,_oF){var _oG=E(_oF);return (_oG._==0)?__Z:new T2(1,new T(function(){return B(A1(_oE,_oG.a));}),new T(function(){return B(_oD(_oE,_oG.b));}));},_oH=function(_oI){return new T1(0,_oI);},_oJ=function(_oK){return new F(function(){return _oH(E(_oK));});},_oL=new T(function(){return B(unCStr("this should not happen"));}),_oM=new T(function(){return B(err(_oL));}),_oN=function(_oO,_oP){while(1){var _oQ=E(_oO);if(!_oQ._){var _oR=_oQ.a,_oS=E(_oP);if(!_oS._){var _oT=_oS.a;if(!(imul(_oR,_oT)|0)){return new T1(0,imul(_oR,_oT)|0);}else{_oO=new T1(1,I_fromInt(_oR));_oP=new T1(1,I_fromInt(_oT));continue;}}else{_oO=new T1(1,I_fromInt(_oR));_oP=_oS;continue;}}else{var _oU=E(_oP);if(!_oU._){_oO=_oQ;_oP=new T1(1,I_fromInt(_oU.a));continue;}else{return new T1(1,I_mul(_oQ.a,_oU.a));}}}},_oV=function(_oW,_oX){var _oY=E(_oX);if(!_oY._){return __Z;}else{var _oZ=E(_oY.b);return (_oZ._==0)?E(_oM):new T2(1,B(_oj(B(_oN(_oY.a,_oW)),_oZ.a)),new T(function(){return B(_oV(_oW,_oZ.b));}));}},_p0=new T1(0,0),_p1=function(_p2,_p3,_p4){while(1){var _p5=B((function(_p6,_p7,_p8){var _p9=E(_p8);if(!_p9._){return E(_p0);}else{if(!E(_p9.b)._){return E(_p9.a);}else{var _pa=E(_p7);if(_pa<=40){var _pb=function(_pc,_pd){while(1){var _pe=E(_pd);if(!_pe._){return E(_pc);}else{var _pf=B(_oj(B(_oN(_pc,_p6)),_pe.a));_pc=_pf;_pd=_pe.b;continue;}}};return new F(function(){return _pb(_p0,_p9);});}else{var _pg=B(_oN(_p6,_p6));if(!(_pa%2)){var _ph=B(_oV(_p6,_p9));_p2=_pg;_p3=quot(_pa+1|0,2);_p4=_ph;return __continue;}else{var _ph=B(_oV(_p6,new T2(1,_p0,_p9)));_p2=_pg;_p3=quot(_pa+1|0,2);_p4=_ph;return __continue;}}}}})(_p2,_p3,_p4));if(_p5!=__continue){return _p5;}}},_pi=function(_pj,_pk){return new F(function(){return _p1(_pj,new T(function(){return B(_oy(_pk,0));},1),B(_oD(_oJ,_pk)));});},_pl=function(_pm){var _pn=new T(function(){var _po=new T(function(){var _pp=function(_pq){return new F(function(){return A1(_pm,new T1(1,new T(function(){return B(_pi(_ox,_pq));})));});};return new T1(1,B(_ne(_og,_pp)));}),_pr=function(_ps){if(E(_ps)==43){var _pt=function(_pu){return new F(function(){return A1(_pm,new T1(1,new T(function(){return B(_pi(_ox,_pu));})));});};return new T1(1,B(_ne(_og,_pt)));}else{return new T0(2);}},_pv=function(_pw){if(E(_pw)==45){var _px=function(_py){return new F(function(){return A1(_pm,new T1(1,new T(function(){return B(_ot(B(_pi(_ox,_py))));})));});};return new T1(1,B(_ne(_og,_px)));}else{return new T0(2);}};return B(_lf(B(_lf(new T1(0,_pv),new T1(0,_pr))),_po));});return new F(function(){return _lf(new T1(0,function(_pz){return (E(_pz)==101)?E(_pn):new T0(2);}),new T1(0,function(_pA){return (E(_pA)==69)?E(_pn):new T0(2);}));});},_pB=function(_pC){var _pD=function(_pE){return new F(function(){return A1(_pC,new T1(1,_pE));});};return function(_pF){return (E(_pF)==46)?new T1(1,B(_ne(_og,_pD))):new T0(2);};},_pG=function(_pH){return new T1(0,B(_pB(_pH)));},_pI=function(_pJ){var _pK=function(_pL){var _pM=function(_pN){return new T1(1,B(_mv(_pl,_oc,function(_pO){return new F(function(){return A1(_pJ,new T1(5,new T3(1,_pL,_pN,_pO)));});})));};return new T1(1,B(_mv(_pG,_oe,_pM)));};return new F(function(){return _ne(_og,_pK);});},_pP=function(_pQ){return new T1(1,B(_pI(_pQ)));},_pR=function(_pS){return E(E(_pS).a);},_pT=function(_pU,_pV,_pW){while(1){var _pX=E(_pW);if(!_pX._){return false;}else{if(!B(A3(_pR,_pU,_pV,_pX.a))){_pW=_pX.b;continue;}else{return true;}}}},_pY=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_pZ=function(_q0){return new F(function(){return _pT(_m4,_q0,_pY);});},_q1=false,_q2=true,_q3=function(_q4){var _q5=new T(function(){return B(A1(_q4,_nZ));}),_q6=new T(function(){return B(A1(_q4,_nY));});return function(_q7){switch(E(_q7)){case 79:return E(_q5);case 88:return E(_q6);case 111:return E(_q5);case 120:return E(_q6);default:return new T0(2);}};},_q8=function(_q9){return new T1(0,B(_q3(_q9)));},_qa=function(_qb){return new F(function(){return A1(_qb,_og);});},_qc=function(_qd){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_hA(9,_qd,_1M));}))));});},_qe=function(_qf){var _qg=E(_qf);if(!_qg._){return E(_qg.a);}else{return new F(function(){return I_toInt(_qg.a);});}},_qh=function(_qi,_qj){var _qk=E(_qi);if(!_qk._){var _ql=_qk.a,_qm=E(_qj);return (_qm._==0)?_ql<=_qm.a:I_compareInt(_qm.a,_ql)>=0;}else{var _qn=_qk.a,_qo=E(_qj);return (_qo._==0)?I_compareInt(_qn,_qo.a)<=0:I_compare(_qn,_qo.a)<=0;}},_qp=function(_qq){return new T0(2);},_qr=function(_qs){var _qt=E(_qs);if(!_qt._){return E(_qp);}else{var _qu=_qt.a,_qv=E(_qt.b);if(!_qv._){return E(_qu);}else{var _qw=new T(function(){return B(_qr(_qv));}),_qx=function(_qy){return new F(function(){return _lf(B(A1(_qu,_qy)),new T(function(){return B(A1(_qw,_qy));}));});};return E(_qx);}}},_qz=function(_qA,_qB){var _qC=function(_qD,_qE,_qF){var _qG=E(_qD);if(!_qG._){return new F(function(){return A1(_qF,_qA);});}else{var _qH=E(_qE);if(!_qH._){return new T0(2);}else{if(E(_qG.a)!=E(_qH.a)){return new T0(2);}else{var _qI=new T(function(){return B(_qC(_qG.b,_qH.b,_qF));});return new T1(0,function(_qJ){return E(_qI);});}}}};return function(_qK){return new F(function(){return _qC(_qA,_qK,_qB);});};},_qL=new T(function(){return B(unCStr("SO"));}),_qM=14,_qN=function(_qO){var _qP=new T(function(){return B(A1(_qO,_qM));});return new T1(1,B(_qz(_qL,function(_qQ){return E(_qP);})));},_qR=new T(function(){return B(unCStr("SOH"));}),_qS=1,_qT=function(_qU){var _qV=new T(function(){return B(A1(_qU,_qS));});return new T1(1,B(_qz(_qR,function(_qW){return E(_qV);})));},_qX=function(_qY){return new T1(1,B(_mv(_qT,_qN,_qY)));},_qZ=new T(function(){return B(unCStr("NUL"));}),_r0=0,_r1=function(_r2){var _r3=new T(function(){return B(A1(_r2,_r0));});return new T1(1,B(_qz(_qZ,function(_r4){return E(_r3);})));},_r5=new T(function(){return B(unCStr("STX"));}),_r6=2,_r7=function(_r8){var _r9=new T(function(){return B(A1(_r8,_r6));});return new T1(1,B(_qz(_r5,function(_ra){return E(_r9);})));},_rb=new T(function(){return B(unCStr("ETX"));}),_rc=3,_rd=function(_re){var _rf=new T(function(){return B(A1(_re,_rc));});return new T1(1,B(_qz(_rb,function(_rg){return E(_rf);})));},_rh=new T(function(){return B(unCStr("EOT"));}),_ri=4,_rj=function(_rk){var _rl=new T(function(){return B(A1(_rk,_ri));});return new T1(1,B(_qz(_rh,function(_rm){return E(_rl);})));},_rn=new T(function(){return B(unCStr("ENQ"));}),_ro=5,_rp=function(_rq){var _rr=new T(function(){return B(A1(_rq,_ro));});return new T1(1,B(_qz(_rn,function(_rs){return E(_rr);})));},_rt=new T(function(){return B(unCStr("ACK"));}),_ru=6,_rv=function(_rw){var _rx=new T(function(){return B(A1(_rw,_ru));});return new T1(1,B(_qz(_rt,function(_ry){return E(_rx);})));},_rz=new T(function(){return B(unCStr("BEL"));}),_rA=7,_rB=function(_rC){var _rD=new T(function(){return B(A1(_rC,_rA));});return new T1(1,B(_qz(_rz,function(_rE){return E(_rD);})));},_rF=new T(function(){return B(unCStr("BS"));}),_rG=8,_rH=function(_rI){var _rJ=new T(function(){return B(A1(_rI,_rG));});return new T1(1,B(_qz(_rF,function(_rK){return E(_rJ);})));},_rL=new T(function(){return B(unCStr("HT"));}),_rM=9,_rN=function(_rO){var _rP=new T(function(){return B(A1(_rO,_rM));});return new T1(1,B(_qz(_rL,function(_rQ){return E(_rP);})));},_rR=new T(function(){return B(unCStr("LF"));}),_rS=10,_rT=function(_rU){var _rV=new T(function(){return B(A1(_rU,_rS));});return new T1(1,B(_qz(_rR,function(_rW){return E(_rV);})));},_rX=new T(function(){return B(unCStr("VT"));}),_rY=11,_rZ=function(_s0){var _s1=new T(function(){return B(A1(_s0,_rY));});return new T1(1,B(_qz(_rX,function(_s2){return E(_s1);})));},_s3=new T(function(){return B(unCStr("FF"));}),_s4=12,_s5=function(_s6){var _s7=new T(function(){return B(A1(_s6,_s4));});return new T1(1,B(_qz(_s3,function(_s8){return E(_s7);})));},_s9=new T(function(){return B(unCStr("CR"));}),_sa=13,_sb=function(_sc){var _sd=new T(function(){return B(A1(_sc,_sa));});return new T1(1,B(_qz(_s9,function(_se){return E(_sd);})));},_sf=new T(function(){return B(unCStr("SI"));}),_sg=15,_sh=function(_si){var _sj=new T(function(){return B(A1(_si,_sg));});return new T1(1,B(_qz(_sf,function(_sk){return E(_sj);})));},_sl=new T(function(){return B(unCStr("DLE"));}),_sm=16,_sn=function(_so){var _sp=new T(function(){return B(A1(_so,_sm));});return new T1(1,B(_qz(_sl,function(_sq){return E(_sp);})));},_sr=new T(function(){return B(unCStr("DC1"));}),_ss=17,_st=function(_su){var _sv=new T(function(){return B(A1(_su,_ss));});return new T1(1,B(_qz(_sr,function(_sw){return E(_sv);})));},_sx=new T(function(){return B(unCStr("DC2"));}),_sy=18,_sz=function(_sA){var _sB=new T(function(){return B(A1(_sA,_sy));});return new T1(1,B(_qz(_sx,function(_sC){return E(_sB);})));},_sD=new T(function(){return B(unCStr("DC3"));}),_sE=19,_sF=function(_sG){var _sH=new T(function(){return B(A1(_sG,_sE));});return new T1(1,B(_qz(_sD,function(_sI){return E(_sH);})));},_sJ=new T(function(){return B(unCStr("DC4"));}),_sK=20,_sL=function(_sM){var _sN=new T(function(){return B(A1(_sM,_sK));});return new T1(1,B(_qz(_sJ,function(_sO){return E(_sN);})));},_sP=new T(function(){return B(unCStr("NAK"));}),_sQ=21,_sR=function(_sS){var _sT=new T(function(){return B(A1(_sS,_sQ));});return new T1(1,B(_qz(_sP,function(_sU){return E(_sT);})));},_sV=new T(function(){return B(unCStr("SYN"));}),_sW=22,_sX=function(_sY){var _sZ=new T(function(){return B(A1(_sY,_sW));});return new T1(1,B(_qz(_sV,function(_t0){return E(_sZ);})));},_t1=new T(function(){return B(unCStr("ETB"));}),_t2=23,_t3=function(_t4){var _t5=new T(function(){return B(A1(_t4,_t2));});return new T1(1,B(_qz(_t1,function(_t6){return E(_t5);})));},_t7=new T(function(){return B(unCStr("CAN"));}),_t8=24,_t9=function(_ta){var _tb=new T(function(){return B(A1(_ta,_t8));});return new T1(1,B(_qz(_t7,function(_tc){return E(_tb);})));},_td=new T(function(){return B(unCStr("EM"));}),_te=25,_tf=function(_tg){var _th=new T(function(){return B(A1(_tg,_te));});return new T1(1,B(_qz(_td,function(_ti){return E(_th);})));},_tj=new T(function(){return B(unCStr("SUB"));}),_tk=26,_tl=function(_tm){var _tn=new T(function(){return B(A1(_tm,_tk));});return new T1(1,B(_qz(_tj,function(_to){return E(_tn);})));},_tp=new T(function(){return B(unCStr("ESC"));}),_tq=27,_tr=function(_ts){var _tt=new T(function(){return B(A1(_ts,_tq));});return new T1(1,B(_qz(_tp,function(_tu){return E(_tt);})));},_tv=new T(function(){return B(unCStr("FS"));}),_tw=28,_tx=function(_ty){var _tz=new T(function(){return B(A1(_ty,_tw));});return new T1(1,B(_qz(_tv,function(_tA){return E(_tz);})));},_tB=new T(function(){return B(unCStr("GS"));}),_tC=29,_tD=function(_tE){var _tF=new T(function(){return B(A1(_tE,_tC));});return new T1(1,B(_qz(_tB,function(_tG){return E(_tF);})));},_tH=new T(function(){return B(unCStr("RS"));}),_tI=30,_tJ=function(_tK){var _tL=new T(function(){return B(A1(_tK,_tI));});return new T1(1,B(_qz(_tH,function(_tM){return E(_tL);})));},_tN=new T(function(){return B(unCStr("US"));}),_tO=31,_tP=function(_tQ){var _tR=new T(function(){return B(A1(_tQ,_tO));});return new T1(1,B(_qz(_tN,function(_tS){return E(_tR);})));},_tT=new T(function(){return B(unCStr("SP"));}),_tU=32,_tV=function(_tW){var _tX=new T(function(){return B(A1(_tW,_tU));});return new T1(1,B(_qz(_tT,function(_tY){return E(_tX);})));},_tZ=new T(function(){return B(unCStr("DEL"));}),_u0=127,_u1=function(_u2){var _u3=new T(function(){return B(A1(_u2,_u0));});return new T1(1,B(_qz(_tZ,function(_u4){return E(_u3);})));},_u5=new T2(1,_u1,_1M),_u6=new T2(1,_tV,_u5),_u7=new T2(1,_tP,_u6),_u8=new T2(1,_tJ,_u7),_u9=new T2(1,_tD,_u8),_ua=new T2(1,_tx,_u9),_ub=new T2(1,_tr,_ua),_uc=new T2(1,_tl,_ub),_ud=new T2(1,_tf,_uc),_ue=new T2(1,_t9,_ud),_uf=new T2(1,_t3,_ue),_ug=new T2(1,_sX,_uf),_uh=new T2(1,_sR,_ug),_ui=new T2(1,_sL,_uh),_uj=new T2(1,_sF,_ui),_uk=new T2(1,_sz,_uj),_ul=new T2(1,_st,_uk),_um=new T2(1,_sn,_ul),_un=new T2(1,_sh,_um),_uo=new T2(1,_sb,_un),_up=new T2(1,_s5,_uo),_uq=new T2(1,_rZ,_up),_ur=new T2(1,_rT,_uq),_us=new T2(1,_rN,_ur),_ut=new T2(1,_rH,_us),_uu=new T2(1,_rB,_ut),_uv=new T2(1,_rv,_uu),_uw=new T2(1,_rp,_uv),_ux=new T2(1,_rj,_uw),_uy=new T2(1,_rd,_ux),_uz=new T2(1,_r7,_uy),_uA=new T2(1,_r1,_uz),_uB=new T2(1,_qX,_uA),_uC=new T(function(){return B(_qr(_uB));}),_uD=34,_uE=new T1(0,1114111),_uF=92,_uG=39,_uH=function(_uI){var _uJ=new T(function(){return B(A1(_uI,_rA));}),_uK=new T(function(){return B(A1(_uI,_rG));}),_uL=new T(function(){return B(A1(_uI,_rM));}),_uM=new T(function(){return B(A1(_uI,_rS));}),_uN=new T(function(){return B(A1(_uI,_rY));}),_uO=new T(function(){return B(A1(_uI,_s4));}),_uP=new T(function(){return B(A1(_uI,_sa));}),_uQ=new T(function(){return B(A1(_uI,_uF));}),_uR=new T(function(){return B(A1(_uI,_uG));}),_uS=new T(function(){return B(A1(_uI,_uD));}),_uT=new T(function(){var _uU=function(_uV){var _uW=new T(function(){return B(_oH(E(_uV)));}),_uX=function(_uY){var _uZ=B(_pi(_uW,_uY));if(!B(_qh(_uZ,_uE))){return new T0(2);}else{return new F(function(){return A1(_uI,new T(function(){var _v0=B(_qe(_uZ));if(_v0>>>0>1114111){return B(_qc(_v0));}else{return _v0;}}));});}};return new T1(1,B(_ne(_uV,_uX)));},_v1=new T(function(){var _v2=new T(function(){return B(A1(_uI,_tO));}),_v3=new T(function(){return B(A1(_uI,_tI));}),_v4=new T(function(){return B(A1(_uI,_tC));}),_v5=new T(function(){return B(A1(_uI,_tw));}),_v6=new T(function(){return B(A1(_uI,_tq));}),_v7=new T(function(){return B(A1(_uI,_tk));}),_v8=new T(function(){return B(A1(_uI,_te));}),_v9=new T(function(){return B(A1(_uI,_t8));}),_va=new T(function(){return B(A1(_uI,_t2));}),_vb=new T(function(){return B(A1(_uI,_sW));}),_vc=new T(function(){return B(A1(_uI,_sQ));}),_vd=new T(function(){return B(A1(_uI,_sK));}),_ve=new T(function(){return B(A1(_uI,_sE));}),_vf=new T(function(){return B(A1(_uI,_sy));}),_vg=new T(function(){return B(A1(_uI,_ss));}),_vh=new T(function(){return B(A1(_uI,_sm));}),_vi=new T(function(){return B(A1(_uI,_sg));}),_vj=new T(function(){return B(A1(_uI,_qM));}),_vk=new T(function(){return B(A1(_uI,_ru));}),_vl=new T(function(){return B(A1(_uI,_ro));}),_vm=new T(function(){return B(A1(_uI,_ri));}),_vn=new T(function(){return B(A1(_uI,_rc));}),_vo=new T(function(){return B(A1(_uI,_r6));}),_vp=new T(function(){return B(A1(_uI,_qS));}),_vq=new T(function(){return B(A1(_uI,_r0));}),_vr=function(_vs){switch(E(_vs)){case 64:return E(_vq);case 65:return E(_vp);case 66:return E(_vo);case 67:return E(_vn);case 68:return E(_vm);case 69:return E(_vl);case 70:return E(_vk);case 71:return E(_uJ);case 72:return E(_uK);case 73:return E(_uL);case 74:return E(_uM);case 75:return E(_uN);case 76:return E(_uO);case 77:return E(_uP);case 78:return E(_vj);case 79:return E(_vi);case 80:return E(_vh);case 81:return E(_vg);case 82:return E(_vf);case 83:return E(_ve);case 84:return E(_vd);case 85:return E(_vc);case 86:return E(_vb);case 87:return E(_va);case 88:return E(_v9);case 89:return E(_v8);case 90:return E(_v7);case 91:return E(_v6);case 92:return E(_v5);case 93:return E(_v4);case 94:return E(_v3);case 95:return E(_v2);default:return new T0(2);}};return B(_lf(new T1(0,function(_vt){return (E(_vt)==94)?E(new T1(0,_vr)):new T0(2);}),new T(function(){return B(A1(_uC,_uI));})));});return B(_lf(new T1(1,B(_mv(_q8,_qa,_uU))),_v1));});return new F(function(){return _lf(new T1(0,function(_vu){switch(E(_vu)){case 34:return E(_uS);case 39:return E(_uR);case 92:return E(_uQ);case 97:return E(_uJ);case 98:return E(_uK);case 102:return E(_uO);case 110:return E(_uM);case 114:return E(_uP);case 116:return E(_uL);case 118:return E(_uN);default:return new T0(2);}}),_uT);});},_vv=function(_vw){return new F(function(){return A1(_vw,_h9);});},_vx=function(_vy){var _vz=E(_vy);if(!_vz._){return E(_vv);}else{var _vA=E(_vz.a),_vB=_vA>>>0,_vC=new T(function(){return B(_vx(_vz.b));});if(_vB>887){var _vD=u_iswspace(_vA);if(!E(_vD)){return E(_vv);}else{var _vE=function(_vF){var _vG=new T(function(){return B(A1(_vC,_vF));});return new T1(0,function(_vH){return E(_vG);});};return E(_vE);}}else{var _vI=E(_vB);if(_vI==32){var _vJ=function(_vK){var _vL=new T(function(){return B(A1(_vC,_vK));});return new T1(0,function(_vM){return E(_vL);});};return E(_vJ);}else{if(_vI-9>>>0>4){if(E(_vI)==160){var _vN=function(_vO){var _vP=new T(function(){return B(A1(_vC,_vO));});return new T1(0,function(_vQ){return E(_vP);});};return E(_vN);}else{return E(_vv);}}else{var _vR=function(_vS){var _vT=new T(function(){return B(A1(_vC,_vS));});return new T1(0,function(_vU){return E(_vT);});};return E(_vR);}}}}},_vV=function(_vW){var _vX=new T(function(){return B(_vV(_vW));}),_vY=function(_vZ){return (E(_vZ)==92)?E(_vX):new T0(2);},_w0=function(_w1){return E(new T1(0,_vY));},_w2=new T1(1,function(_w3){return new F(function(){return A2(_vx,_w3,_w0);});}),_w4=new T(function(){return B(_uH(function(_w5){return new F(function(){return A1(_vW,new T2(0,_w5,_q2));});}));}),_w6=function(_w7){var _w8=E(_w7);if(_w8==38){return E(_vX);}else{var _w9=_w8>>>0;if(_w9>887){var _wa=u_iswspace(_w8);return (E(_wa)==0)?new T0(2):E(_w2);}else{var _wb=E(_w9);return (_wb==32)?E(_w2):(_wb-9>>>0>4)?(E(_wb)==160)?E(_w2):new T0(2):E(_w2);}}};return new F(function(){return _lf(new T1(0,function(_wc){return (E(_wc)==92)?E(new T1(0,_w6)):new T0(2);}),new T1(0,function(_wd){var _we=E(_wd);if(E(_we)==92){return E(_w4);}else{return new F(function(){return A1(_vW,new T2(0,_we,_q1));});}}));});},_wf=function(_wg,_wh){var _wi=new T(function(){return B(A1(_wh,new T1(1,new T(function(){return B(A1(_wg,_1M));}))));}),_wj=function(_wk){var _wl=E(_wk),_wm=E(_wl.a);if(E(_wm)==34){if(!E(_wl.b)){return E(_wi);}else{return new F(function(){return _wf(function(_wn){return new F(function(){return A1(_wg,new T2(1,_wm,_wn));});},_wh);});}}else{return new F(function(){return _wf(function(_wo){return new F(function(){return A1(_wg,new T2(1,_wm,_wo));});},_wh);});}};return new F(function(){return _vV(_wj);});},_wp=new T(function(){return B(unCStr("_\'"));}),_wq=function(_wr){var _ws=u_iswalnum(_wr);if(!E(_ws)){return new F(function(){return _pT(_m4,_wr,_wp);});}else{return true;}},_wt=function(_wu){return new F(function(){return _wq(E(_wu));});},_wv=new T(function(){return B(unCStr(",;()[]{}`"));}),_ww=new T(function(){return B(unCStr("=>"));}),_wx=new T2(1,_ww,_1M),_wy=new T(function(){return B(unCStr("~"));}),_wz=new T2(1,_wy,_wx),_wA=new T(function(){return B(unCStr("@"));}),_wB=new T2(1,_wA,_wz),_wC=new T(function(){return B(unCStr("->"));}),_wD=new T2(1,_wC,_wB),_wE=new T(function(){return B(unCStr("<-"));}),_wF=new T2(1,_wE,_wD),_wG=new T(function(){return B(unCStr("|"));}),_wH=new T2(1,_wG,_wF),_wI=new T(function(){return B(unCStr("\\"));}),_wJ=new T2(1,_wI,_wH),_wK=new T(function(){return B(unCStr("="));}),_wL=new T2(1,_wK,_wJ),_wM=new T(function(){return B(unCStr("::"));}),_wN=new T2(1,_wM,_wL),_wO=new T(function(){return B(unCStr(".."));}),_wP=new T2(1,_wO,_wN),_wQ=function(_wR){var _wS=new T(function(){return B(A1(_wR,_n9));}),_wT=new T(function(){var _wU=new T(function(){var _wV=function(_wW){var _wX=new T(function(){return B(A1(_wR,new T1(0,_wW)));});return new T1(0,function(_wY){return (E(_wY)==39)?E(_wX):new T0(2);});};return B(_uH(_wV));}),_wZ=function(_x0){var _x1=E(_x0);switch(E(_x1)){case 39:return new T0(2);case 92:return E(_wU);default:var _x2=new T(function(){return B(A1(_wR,new T1(0,_x1)));});return new T1(0,function(_x3){return (E(_x3)==39)?E(_x2):new T0(2);});}},_x4=new T(function(){var _x5=new T(function(){return B(_wf(_na,_wR));}),_x6=new T(function(){var _x7=new T(function(){var _x8=new T(function(){var _x9=function(_xa){var _xb=E(_xa),_xc=u_iswalpha(_xb);return (E(_xc)==0)?(E(_xb)==95)?new T1(1,B(_mV(_wt,function(_xd){return new F(function(){return A1(_wR,new T1(3,new T2(1,_xb,_xd)));});}))):new T0(2):new T1(1,B(_mV(_wt,function(_xe){return new F(function(){return A1(_wR,new T1(3,new T2(1,_xb,_xe)));});})));};return B(_lf(new T1(0,_x9),new T(function(){return new T1(1,B(_mv(_o9,_pP,_wR)));})));}),_xf=function(_xg){return (!B(_pT(_m4,_xg,_pY)))?new T0(2):new T1(1,B(_mV(_pZ,function(_xh){var _xi=new T2(1,_xg,_xh);if(!B(_pT(_md,_xi,_wP))){return new F(function(){return A1(_wR,new T1(4,_xi));});}else{return new F(function(){return A1(_wR,new T1(2,_xi));});}})));};return B(_lf(new T1(0,_xf),_x8));});return B(_lf(new T1(0,function(_xj){if(!B(_pT(_m4,_xj,_wv))){return new T0(2);}else{return new F(function(){return A1(_wR,new T1(2,new T2(1,_xj,_1M)));});}}),_x7));});return B(_lf(new T1(0,function(_xk){return (E(_xk)==34)?E(_x5):new T0(2);}),_x6));});return B(_lf(new T1(0,function(_xl){return (E(_xl)==39)?E(new T1(0,_wZ)):new T0(2);}),_x4));});return new F(function(){return _lf(new T1(1,function(_xm){return (E(_xm)._==0)?E(_wS):new T0(2);}),_wT);});},_xn=0,_xo=function(_xp,_xq){var _xr=new T(function(){var _xs=new T(function(){var _xt=function(_xu){var _xv=new T(function(){var _xw=new T(function(){return B(A1(_xq,_xu));});return B(_wQ(function(_xx){var _xy=E(_xx);return (_xy._==2)?(!B(_lT(_xy.a,_lS)))?new T0(2):E(_xw):new T0(2);}));}),_xz=function(_xA){return E(_xv);};return new T1(1,function(_xB){return new F(function(){return A2(_vx,_xB,_xz);});});};return B(A2(_xp,_xn,_xt));});return B(_wQ(function(_xC){var _xD=E(_xC);return (_xD._==2)?(!B(_lT(_xD.a,_lR)))?new T0(2):E(_xs):new T0(2);}));}),_xE=function(_xF){return E(_xr);};return function(_xG){return new F(function(){return A2(_vx,_xG,_xE);});};},_xH=function(_xI,_xJ){var _xK=function(_xL){var _xM=new T(function(){return B(A1(_xI,_xL));}),_xN=function(_xO){return new F(function(){return _lf(B(A1(_xM,_xO)),new T(function(){return new T1(1,B(_xo(_xK,_xO)));}));});};return E(_xN);},_xP=new T(function(){return B(A1(_xI,_xJ));}),_xQ=function(_xR){return new F(function(){return _lf(B(A1(_xP,_xR)),new T(function(){return new T1(1,B(_xo(_xK,_xR)));}));});};return E(_xQ);},_xS=function(_xT,_xU){var _xV=function(_xW,_xX){var _xY=function(_xZ){return new F(function(){return A1(_xX,new T(function(){return  -E(_xZ);}));});},_y0=new T(function(){return B(_wQ(function(_y1){return new F(function(){return A3(_xT,_y1,_xW,_xY);});}));}),_y2=function(_y3){return E(_y0);},_y4=function(_y5){return new F(function(){return A2(_vx,_y5,_y2);});},_y6=new T(function(){return B(_wQ(function(_y7){var _y8=E(_y7);if(_y8._==4){var _y9=E(_y8.a);if(!_y9._){return new F(function(){return A3(_xT,_y8,_xW,_xX);});}else{if(E(_y9.a)==45){if(!E(_y9.b)._){return E(new T1(1,_y4));}else{return new F(function(){return A3(_xT,_y8,_xW,_xX);});}}else{return new F(function(){return A3(_xT,_y8,_xW,_xX);});}}}else{return new F(function(){return A3(_xT,_y8,_xW,_xX);});}}));}),_ya=function(_yb){return E(_y6);};return new T1(1,function(_yc){return new F(function(){return A2(_vx,_yc,_ya);});});};return new F(function(){return _xH(_xV,_xU);});},_yd=function(_ye){var _yf=E(_ye);if(!_yf._){var _yg=_yf.b,_yh=new T(function(){return B(_p1(new T(function(){return B(_oH(E(_yf.a)));}),new T(function(){return B(_oy(_yg,0));},1),B(_oD(_oJ,_yg))));});return new T1(1,_yh);}else{return (E(_yf.b)._==0)?(E(_yf.c)._==0)?new T1(1,new T(function(){return B(_pi(_ox,_yf.a));})):__Z:__Z;}},_yi=function(_yj,_yk){return new T0(2);},_yl=function(_ym){var _yn=E(_ym);if(_yn._==5){var _yo=B(_yd(_yn.a));if(!_yo._){return E(_yi);}else{var _yp=new T(function(){return B(_qe(_yo.a));});return function(_yq,_yr){return new F(function(){return A1(_yr,_yp);});};}}else{return E(_yi);}},_ys=function(_yt){return new F(function(){return _xS(_yl,_yt);});},_yu=new T(function(){return B(unCStr("["));}),_yv=function(_yw,_yx){var _yy=function(_yz,_yA){var _yB=new T(function(){return B(A1(_yA,_1M));}),_yC=new T(function(){var _yD=function(_yE){return new F(function(){return _yy(_q2,function(_yF){return new F(function(){return A1(_yA,new T2(1,_yE,_yF));});});});};return B(A2(_yw,_xn,_yD));}),_yG=new T(function(){return B(_wQ(function(_yH){var _yI=E(_yH);if(_yI._==2){var _yJ=E(_yI.a);if(!_yJ._){return new T0(2);}else{var _yK=_yJ.b;switch(E(_yJ.a)){case 44:return (E(_yK)._==0)?(!E(_yz))?new T0(2):E(_yC):new T0(2);case 93:return (E(_yK)._==0)?E(_yB):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_yL=function(_yM){return E(_yG);};return new T1(1,function(_yN){return new F(function(){return A2(_vx,_yN,_yL);});});},_yO=function(_yP,_yQ){return new F(function(){return _yR(_yQ);});},_yR=function(_yS){var _yT=new T(function(){var _yU=new T(function(){var _yV=new T(function(){var _yW=function(_yX){return new F(function(){return _yy(_q2,function(_yY){return new F(function(){return A1(_yS,new T2(1,_yX,_yY));});});});};return B(A2(_yw,_xn,_yW));});return B(_lf(B(_yy(_q1,_yS)),_yV));});return B(_wQ(function(_yZ){var _z0=E(_yZ);return (_z0._==2)?(!B(_lT(_z0.a,_yu)))?new T0(2):E(_yU):new T0(2);}));}),_z1=function(_z2){return E(_yT);};return new F(function(){return _lf(new T1(1,function(_z3){return new F(function(){return A2(_vx,_z3,_z1);});}),new T(function(){return new T1(1,B(_xo(_yO,_yS)));}));});};return new F(function(){return _yR(_yx);});},_z4=function(_z5,_z6){return new F(function(){return _yv(_ys,_z6);});},_z7=new T(function(){return B(_yv(_ys,_jV));}),_z8=function(_yt){return new F(function(){return _l5(_z7,_yt);});},_z9=function(_za){var _zb=new T(function(){return B(A3(_xS,_yl,_za,_jV));});return function(_zc){return new F(function(){return _l5(_zb,_zc);});};},_zd=new T4(0,_z9,_z8,_ys,_z4),_ze=11,_zf=new T(function(){return B(unCStr("IdentChoice"));}),_zg=function(_zh,_zi){if(_zh>10){return new T0(2);}else{var _zj=new T(function(){var _zk=new T(function(){return B(A3(_xS,_yl,_ze,function(_zl){return new F(function(){return A1(_zi,_zl);});}));});return B(_wQ(function(_zm){var _zn=E(_zm);return (_zn._==3)?(!B(_lT(_zn.a,_zf)))?new T0(2):E(_zk):new T0(2);}));}),_zo=function(_zp){return E(_zj);};return new T1(1,function(_zq){return new F(function(){return A2(_vx,_zq,_zo);});});}},_zr=function(_zs,_zt){return new F(function(){return _zg(E(_zs),_zt);});},_zu=function(_zv){return new F(function(){return _xH(_zr,_zv);});},_zw=function(_zx,_zy){return new F(function(){return _yv(_zu,_zy);});},_zz=new T(function(){return B(_yv(_zu,_jV));}),_zA=function(_zv){return new F(function(){return _l5(_zz,_zv);});},_zB=function(_zC){var _zD=new T(function(){return B(A3(_xH,_zr,_zC,_jV));});return function(_zc){return new F(function(){return _l5(_zD,_zc);});};},_zE=new T4(0,_zB,_zA,_zu,_zw),_zF=new T(function(){return B(unCStr(","));}),_zG=function(_zH){return E(E(_zH).c);},_zI=function(_zJ,_zK,_zL){var _zM=new T(function(){return B(_zG(_zK));}),_zN=new T(function(){return B(A2(_zG,_zJ,_zL));}),_zO=function(_zP){var _zQ=function(_zR){var _zS=new T(function(){var _zT=new T(function(){return B(A2(_zM,_zL,function(_zU){return new F(function(){return A1(_zP,new T2(0,_zR,_zU));});}));});return B(_wQ(function(_zV){var _zW=E(_zV);return (_zW._==2)?(!B(_lT(_zW.a,_zF)))?new T0(2):E(_zT):new T0(2);}));}),_zX=function(_zY){return E(_zS);};return new T1(1,function(_zZ){return new F(function(){return A2(_vx,_zZ,_zX);});});};return new F(function(){return A1(_zN,_zQ);});};return E(_zO);},_A0=function(_A1,_A2,_A3){var _A4=function(_yt){return new F(function(){return _zI(_A1,_A2,_yt);});},_A5=function(_A6,_A7){return new F(function(){return _A8(_A7);});},_A8=function(_A9){return new F(function(){return _lf(new T1(1,B(_xo(_A4,_A9))),new T(function(){return new T1(1,B(_xo(_A5,_A9)));}));});};return new F(function(){return _A8(_A3);});},_Aa=function(_Ab,_Ac){return new F(function(){return _A0(_zE,_zd,_Ac);});},_Ad=new T(function(){return B(_yv(_Aa,_jV));}),_Ae=function(_zv){return new F(function(){return _l5(_Ad,_zv);});},_Af=new T(function(){return B(_A0(_zE,_zd,_jV));}),_Ag=function(_zv){return new F(function(){return _l5(_Af,_zv);});},_Ah=function(_Ai,_zv){return new F(function(){return _Ag(_zv);});},_Aj=function(_Ak,_Al){return new F(function(){return _yv(_Aa,_Al);});},_Am=new T4(0,_Ah,_Ae,_Aa,_Aj),_An=function(_Ao,_Ap){return new F(function(){return _A0(_Am,_zd,_Ap);});},_Aq=function(_Ar,_As){return new F(function(){return _yv(_An,_As);});},_At=new T(function(){return B(_yv(_Aq,_jV));}),_Au=function(_Av){return new F(function(){return _l5(_At,_Av);});},_Aw=function(_Ax){return new F(function(){return _yv(_Aq,_Ax);});},_Ay=function(_Az,_AA){return new F(function(){return _Aw(_AA);});},_AB=new T(function(){return B(_yv(_An,_jV));}),_AC=function(_Av){return new F(function(){return _l5(_AB,_Av);});},_AD=function(_AE,_Av){return new F(function(){return _AC(_Av);});},_AF=new T4(0,_AD,_Au,_Aq,_Ay),_AG=new T(function(){return B(unCStr("IdentPay"));}),_AH=function(_AI,_AJ){if(_AI>10){return new T0(2);}else{var _AK=new T(function(){var _AL=new T(function(){return B(A3(_xS,_yl,_ze,function(_AM){return new F(function(){return A1(_AJ,_AM);});}));});return B(_wQ(function(_AN){var _AO=E(_AN);return (_AO._==3)?(!B(_lT(_AO.a,_AG)))?new T0(2):E(_AL):new T0(2);}));}),_AP=function(_AQ){return E(_AK);};return new T1(1,function(_AR){return new F(function(){return A2(_vx,_AR,_AP);});});}},_AS=function(_AT,_AU){return new F(function(){return _AH(E(_AT),_AU);});},_AV=function(_zv){return new F(function(){return _xH(_AS,_zv);});},_AW=function(_AX,_AY){return new F(function(){return _yv(_AV,_AY);});},_AZ=new T(function(){return B(_yv(_AV,_jV));}),_B0=function(_zv){return new F(function(){return _l5(_AZ,_zv);});},_B1=function(_B2){var _B3=new T(function(){return B(A3(_xH,_AS,_B2,_jV));});return function(_zc){return new F(function(){return _l5(_B3,_zc);});};},_B4=new T4(0,_B1,_B0,_AV,_AW),_B5=function(_B6,_B7){return new F(function(){return _A0(_B4,_zd,_B7);});},_B8=new T(function(){return B(_yv(_B5,_jV));}),_B9=function(_zv){return new F(function(){return _l5(_B8,_zv);});},_Ba=new T(function(){return B(_A0(_B4,_zd,_jV));}),_Bb=function(_zv){return new F(function(){return _l5(_Ba,_zv);});},_Bc=function(_Bd,_zv){return new F(function(){return _Bb(_zv);});},_Be=function(_Bf,_Bg){return new F(function(){return _yv(_B5,_Bg);});},_Bh=new T4(0,_Bc,_B9,_B5,_Be),_Bi=function(_Bj,_Bk){return new F(function(){return _A0(_Bh,_zd,_Bk);});},_Bl=function(_Bm,_Bn){return new F(function(){return _yv(_Bi,_Bn);});},_Bo=new T(function(){return B(_yv(_Bl,_jV));}),_Bp=function(_Av){return new F(function(){return _l5(_Bo,_Av);});},_Bq=function(_Br){return new F(function(){return _yv(_Bl,_Br);});},_Bs=function(_Bt,_Bu){return new F(function(){return _Bq(_Bu);});},_Bv=new T(function(){return B(_yv(_Bi,_jV));}),_Bw=function(_Av){return new F(function(){return _l5(_Bv,_Av);});},_Bx=function(_By,_Av){return new F(function(){return _Bw(_Av);});},_Bz=new T4(0,_Bx,_Bp,_Bl,_Bs),_BA=new T(function(){return B(unCStr("IdentCC"));}),_BB=function(_BC,_BD){if(_BC>10){return new T0(2);}else{var _BE=new T(function(){var _BF=new T(function(){return B(A3(_xS,_yl,_ze,function(_BG){return new F(function(){return A1(_BD,_BG);});}));});return B(_wQ(function(_BH){var _BI=E(_BH);return (_BI._==3)?(!B(_lT(_BI.a,_BA)))?new T0(2):E(_BF):new T0(2);}));}),_BJ=function(_BK){return E(_BE);};return new T1(1,function(_BL){return new F(function(){return A2(_vx,_BL,_BJ);});});}},_BM=function(_BN,_BO){return new F(function(){return _BB(E(_BN),_BO);});},_BP=new T(function(){return B(unCStr("RC"));}),_BQ=function(_BR,_BS){if(_BR>10){return new T0(2);}else{var _BT=new T(function(){var _BU=new T(function(){var _BV=function(_BW){var _BX=function(_BY){return new F(function(){return A3(_xS,_yl,_ze,function(_BZ){return new F(function(){return A1(_BS,new T3(0,_BW,_BY,_BZ));});});});};return new F(function(){return A3(_xS,_yl,_ze,_BX);});};return B(A3(_xH,_BM,_ze,_BV));});return B(_wQ(function(_C0){var _C1=E(_C0);return (_C1._==3)?(!B(_lT(_C1.a,_BP)))?new T0(2):E(_BU):new T0(2);}));}),_C2=function(_C3){return E(_BT);};return new T1(1,function(_C4){return new F(function(){return A2(_vx,_C4,_C2);});});}},_C5=function(_C6,_C7){return new F(function(){return _BQ(E(_C6),_C7);});},_C8=function(_zv){return new F(function(){return _xH(_C5,_zv);});},_C9=function(_Ca,_Cb){return new F(function(){return _yv(_C8,_Cb);});},_Cc=new T(function(){return B(_yv(_C9,_jV));}),_Cd=function(_Av){return new F(function(){return _l5(_Cc,_Av);});},_Ce=new T(function(){return B(_yv(_C8,_jV));}),_Cf=function(_Av){return new F(function(){return _l5(_Ce,_Av);});},_Cg=function(_Ch,_Av){return new F(function(){return _Cf(_Av);});},_Ci=function(_Cj,_Ck){return new F(function(){return _yv(_C9,_Ck);});},_Cl=new T4(0,_Cg,_Cd,_C9,_Ci),_Cm=new T(function(){return B(unCStr("CC"));}),_Cn=function(_Co,_Cp){if(_Co>10){return new T0(2);}else{var _Cq=new T(function(){var _Cr=new T(function(){var _Cs=function(_Ct){var _Cu=function(_Cv){var _Cw=function(_Cx){return new F(function(){return A3(_xS,_yl,_ze,function(_Cy){return new F(function(){return A1(_Cp,new T4(0,_Ct,_Cv,_Cx,_Cy));});});});};return new F(function(){return A3(_xS,_yl,_ze,_Cw);});};return new F(function(){return A3(_xS,_yl,_ze,_Cu);});};return B(A3(_xH,_BM,_ze,_Cs));});return B(_wQ(function(_Cz){var _CA=E(_Cz);return (_CA._==3)?(!B(_lT(_CA.a,_Cm)))?new T0(2):E(_Cr):new T0(2);}));}),_CB=function(_CC){return E(_Cq);};return new T1(1,function(_CD){return new F(function(){return A2(_vx,_CD,_CB);});});}},_CE=function(_CF,_CG){return new F(function(){return _Cn(E(_CF),_CG);});},_CH=function(_zv){return new F(function(){return _xH(_CE,_zv);});},_CI=function(_CJ,_CK){return new F(function(){return _yv(_CH,_CK);});},_CL=new T(function(){return B(_yv(_CI,_jV));}),_CM=function(_Av){return new F(function(){return _l5(_CL,_Av);});},_CN=new T(function(){return B(_yv(_CH,_jV));}),_CO=function(_Av){return new F(function(){return _l5(_CN,_Av);});},_CP=function(_CQ,_Av){return new F(function(){return _CO(_Av);});},_CR=function(_CS,_CT){return new F(function(){return _yv(_CI,_CT);});},_CU=new T4(0,_CP,_CM,_CI,_CR),_CV=function(_CW,_CX,_CY,_CZ,_D0){var _D1=new T(function(){return B(_zI(_CW,_CX,_D0));}),_D2=new T(function(){return B(_zG(_CZ));}),_D3=function(_D4){var _D5=function(_D6){var _D7=E(_D6),_D8=new T(function(){var _D9=new T(function(){var _Da=function(_Db){var _Dc=new T(function(){var _Dd=new T(function(){return B(A2(_D2,_D0,function(_De){return new F(function(){return A1(_D4,new T4(0,_D7.a,_D7.b,_Db,_De));});}));});return B(_wQ(function(_Df){var _Dg=E(_Df);return (_Dg._==2)?(!B(_lT(_Dg.a,_zF)))?new T0(2):E(_Dd):new T0(2);}));}),_Dh=function(_Di){return E(_Dc);};return new T1(1,function(_Dj){return new F(function(){return A2(_vx,_Dj,_Dh);});});};return B(A3(_zG,_CY,_D0,_Da));});return B(_wQ(function(_Dk){var _Dl=E(_Dk);return (_Dl._==2)?(!B(_lT(_Dl.a,_zF)))?new T0(2):E(_D9):new T0(2);}));}),_Dm=function(_Dn){return E(_D8);};return new T1(1,function(_Do){return new F(function(){return A2(_vx,_Do,_Dm);});});};return new F(function(){return A1(_D1,_D5);});};return E(_D3);},_Dp=function(_Dq,_Dr,_Ds,_Dt,_Du){var _Dv=function(_yt){return new F(function(){return _CV(_Dq,_Dr,_Ds,_Dt,_yt);});},_Dw=function(_Dx,_Dy){return new F(function(){return _Dz(_Dy);});},_Dz=function(_DA){return new F(function(){return _lf(new T1(1,B(_xo(_Dv,_DA))),new T(function(){return new T1(1,B(_xo(_Dw,_DA)));}));});};return new F(function(){return _Dz(_Du);});},_DB=function(_DC){var _DD=function(_DE){return E(new T2(3,_DC,_jU));};return new T1(1,function(_DF){return new F(function(){return A2(_vx,_DF,_DD);});});},_DG=new T(function(){return B(_Dp(_CU,_Cl,_Bz,_AF,_DB));}),_DH=function(_DI,_DJ,_DK,_DL){var _DM=E(_DI);if(_DM==1){var _DN=E(_DL);if(!_DN._){return new T3(0,new T(function(){var _DO=E(_DJ);return new T5(0,1,E(_DO),_DK,E(_8i),E(_8i));}),_1M,_1M);}else{var _DP=E(_DJ);return (_DP<E(E(_DN.a).a))?new T3(0,new T5(0,1,E(_DP),_DK,E(_8i),E(_8i)),_DN,_1M):new T3(0,new T5(0,1,E(_DP),_DK,E(_8i),E(_8i)),_1M,_DN);}}else{var _DQ=B(_DH(_DM>>1,_DJ,_DK,_DL)),_DR=_DQ.a,_DS=_DQ.c,_DT=E(_DQ.b);if(!_DT._){return new T3(0,_DR,_1M,_DS);}else{var _DU=E(_DT.a),_DV=_DU.a,_DW=_DU.b,_DX=E(_DT.b);if(!_DX._){return new T3(0,new T(function(){return B(_95(_DV,_DW,_DR));}),_1M,_DS);}else{var _DY=E(_DX.a),_DZ=E(_DV),_E0=E(_DY.a);if(_DZ<_E0){var _E1=B(_DH(_DM>>1,_E0,_DY.b,_DX.b));return new T3(0,new T(function(){return B(_ay(_DZ,_DW,_DR,_E1.a));}),_E1.b,_E1.c);}else{return new T3(0,_DR,_1M,_DT);}}}}},_E2=function(_E3,_E4,_E5){var _E6=E(_E5);if(!_E6._){var _E7=_E6.c,_E8=_E6.d,_E9=_E6.e,_Ea=E(_E6.b);if(_E3>=_Ea){if(_E3!=_Ea){return new F(function(){return _8n(_Ea,_E7,_E8,B(_E2(_E3,_E4,_E9)));});}else{return new T5(0,_E6.a,E(_E3),_E4,E(_E8),E(_E9));}}else{return new F(function(){return _9e(_Ea,_E7,B(_E2(_E3,_E4,_E8)),_E9);});}}else{return new T5(0,1,E(_E3),_E4,E(_8i),E(_8i));}},_Eb=function(_Ec,_Ed){while(1){var _Ee=E(_Ed);if(!_Ee._){return E(_Ec);}else{var _Ef=E(_Ee.a),_Eg=B(_E2(E(_Ef.a),_Ef.b,_Ec));_Ec=_Eg;_Ed=_Ee.b;continue;}}},_Eh=function(_Ei,_Ej,_Ek,_El){return new F(function(){return _Eb(B(_E2(E(_Ej),_Ek,_Ei)),_El);});},_Em=function(_En,_Eo,_Ep){var _Eq=E(_Eo);return new F(function(){return _Eb(B(_E2(E(_Eq.a),_Eq.b,_En)),_Ep);});},_Er=function(_Es,_Et,_Eu){while(1){var _Ev=E(_Eu);if(!_Ev._){return E(_Et);}else{var _Ew=E(_Ev.a),_Ex=_Ew.a,_Ey=_Ew.b,_Ez=E(_Ev.b);if(!_Ez._){return new F(function(){return _95(_Ex,_Ey,_Et);});}else{var _EA=E(_Ez.a),_EB=E(_Ex),_EC=E(_EA.a);if(_EB<_EC){var _ED=B(_DH(_Es,_EC,_EA.b,_Ez.b)),_EE=_ED.a,_EF=E(_ED.c);if(!_EF._){var _EG=_Es<<1,_EH=B(_ay(_EB,_Ey,_Et,_EE));_Es=_EG;_Et=_EH;_Eu=_ED.b;continue;}else{return new F(function(){return _Em(B(_ay(_EB,_Ey,_Et,_EE)),_EF.a,_EF.b);});}}else{return new F(function(){return _Eh(_Et,_EB,_Ey,_Ez);});}}}}},_EI=function(_EJ,_EK,_EL,_EM,_EN){var _EO=E(_EN);if(!_EO._){return new F(function(){return _95(_EL,_EM,_EK);});}else{var _EP=E(_EO.a),_EQ=E(_EL),_ER=E(_EP.a);if(_EQ<_ER){var _ES=B(_DH(_EJ,_ER,_EP.b,_EO.b)),_ET=_ES.a,_EU=E(_ES.c);if(!_EU._){return new F(function(){return _Er(_EJ<<1,B(_ay(_EQ,_EM,_EK,_ET)),_ES.b);});}else{return new F(function(){return _Em(B(_ay(_EQ,_EM,_EK,_ET)),_EU.a,_EU.b);});}}else{return new F(function(){return _Eh(_EK,_EQ,_EM,_EO);});}}},_EV=function(_EW){var _EX=E(_EW);if(!_EX._){return new T0(1);}else{var _EY=E(_EX.a),_EZ=_EY.a,_F0=_EY.b,_F1=E(_EX.b);if(!_F1._){var _F2=E(_EZ);return new T5(0,1,E(_F2),_F0,E(_8i),E(_8i));}else{var _F3=_F1.b,_F4=E(_F1.a),_F5=_F4.b,_F6=E(_EZ),_F7=E(_F4.a);if(_F6<_F7){return new F(function(){return _EI(1,new T5(0,1,E(_F6),_F0,E(_8i),E(_8i)),_F7,_F5,_F3);});}else{return new F(function(){return _Eh(new T5(0,1,E(_F6),_F0,E(_8i),E(_8i)),_F7,_F5,_F3);});}}}},_F8=function(_){return _h9;},_F9=new T(function(){return B(unCStr(": Choose"));}),_Fa=new T(function(){return eval("(function (x, y, z) {var r = document.getElementById(\'actions\').insertRow(); var c1 = r.insertCell(); c1.appendChild(document.createTextNode(x + \' \')); var input = document.createElement(\'input\'); input.type = \'number\'; var ch = \'ibox\' + r.childNodes.length; input.id = ch; input.value = 0; input.style.setProperty(\'width\', \'3em\'); c1.appendChild(input); c1.appendChild(document.createTextNode(\' \' + y)); var c2 = r.insertCell(); var btn = document.createElement(\'button\'); c2.appendChild(btn); btn.appendChild(document.createTextNode(\'Add action\')); btn.style.setProperty(\'width\', \'100%\'); btn.onclick = function () {Haste.addActionWithNum(z, document.getElementById(ch).value);};})");}),_Fb=function(_Fc,_Fd,_){var _Fe=new T(function(){return B(A3(_is,_hk,new T2(1,function(_Ff){return new F(function(){return _j6(0,_Fc,_Ff);});},new T2(1,function(_Fg){return new F(function(){return _hA(0,E(_Fd),_Fg);});},_1M)),_jv));}),_Fh=__app3(E(_Fa),toJSStr(B(unAppCStr("P",new T(function(){return B(_hq(B(_hA(0,E(_Fd),_1M)),_F9));})))),toJSStr(B(unAppCStr("for choice with id ",new T(function(){return B(_hA(0,E(_Fc),_1M));})))),toJSStr(new T2(1,_hz,_Fe)));return new F(function(){return _F8(_);});},_Fi=function(_Fj,_Fk,_){while(1){var _Fl=B((function(_Fm,_Fn,_){var _Fo=E(_Fn);if(!_Fo._){var _Fp=E(_Fo.b);_Fj=function(_){var _Fq=B(_Fb(_Fp.a,_Fp.b,_));return new F(function(){return _Fi(_Fm,_Fo.e,_);});};_Fk=_Fo.d;return __continue;}else{return new F(function(){return A1(_Fm,_);});}})(_Fj,_Fk,_));if(_Fl!=__continue){return _Fl;}}},_Fr=new T(function(){return B(unCStr("SIP "));}),_Fs=new T(function(){return B(unCStr("SIRC "));}),_Ft=new T(function(){return B(unCStr("SICC "));}),_Fu=function(_Fv,_Fw,_Fx){var _Fy=E(_Fw);switch(_Fy._){case 0:var _Fz=function(_FA){var _FB=new T(function(){var _FC=new T(function(){return B(_hA(11,E(_Fy.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_Fy.d),_FA));}))));});return B(_hA(11,E(_Fy.b),new T2(1,_hK,_FC)));});return new F(function(){return _hF(11,_Fy.a,new T2(1,_hK,_FB));});};if(_Fv<11){return new F(function(){return _hq(_Ft,new T(function(){return B(_Fz(_Fx));},1));});}else{var _FD=new T(function(){return B(_hq(_Ft,new T(function(){return B(_Fz(new T2(1,_hy,_Fx)));},1)));});return new T2(1,_hz,_FD);}break;case 1:var _FE=function(_FF){var _FG=new T(function(){var _FH=new T(function(){return B(_hA(11,E(_Fy.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_Fy.c),_FF));}))));});return B(_hF(11,_Fy.a,new T2(1,_hK,_FH)));},1);return new F(function(){return _hq(_Fs,_FG);});};if(_Fv<11){return new F(function(){return _FE(_Fx);});}else{return new T2(1,_hz,new T(function(){return B(_FE(new T2(1,_hy,_Fx)));}));}break;default:var _FI=function(_FJ){var _FK=new T(function(){var _FL=new T(function(){return B(_hA(11,E(_Fy.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_Fy.c),_FJ));}))));});return B(_ih(11,_Fy.a,new T2(1,_hK,_FL)));},1);return new F(function(){return _hq(_Fr,_FK);});};if(_Fv<11){return new F(function(){return _FI(_Fx);});}else{return new T2(1,_hz,new T(function(){return B(_FI(new T2(1,_hy,_Fx)));}));}}},_FM=new T(function(){return B(unCStr(" ADA"));}),_FN=new T(function(){return eval("(function (x, y) {var r = document.getElementById(\'actions\').insertRow(); var c1 = r.insertCell(); c1.appendChild(document.createTextNode(x)); var c2 = r.insertCell(); var btn = document.createElement(\'button\'); c2.appendChild(btn); btn.appendChild(document.createTextNode(\'Add action\')); btn.style.setProperty(\'width\', \'100%\'); btn.onclick = function () {Haste.addAction(y);};})");}),_FO=function(_FP,_FQ,_FR,_){var _FS=new T(function(){var _FT=new T(function(){var _FU=new T(function(){var _FV=new T(function(){return B(unAppCStr(") of ",new T(function(){return B(_hq(B(_hA(0,E(_FR),_1M)),_FM));})));},1);return B(_hq(B(_hA(0,E(_FP),_1M)),_FV));});return B(unAppCStr(": Claim payment (with id: ",_FU));},1);return B(_hq(B(_hA(0,E(_FQ),_1M)),_FT));}),_FW=__app2(E(_FN),toJSStr(B(unAppCStr("P",_FS))),toJSStr(B(_Fu(0,new T3(2,_FP,_FQ,_FR),_1M))));return new F(function(){return _F8(_);});},_FX=function(_FY,_FZ,_){while(1){var _G0=B((function(_G1,_G2,_){var _G3=E(_G2);if(!_G3._){var _G4=E(_G3.b);_FY=function(_){var _G5=B(_FO(_G4.a,_G4.b,_G3.c,_));return new F(function(){return _FX(_G1,_G3.e,_);});};_FZ=_G3.d;return __continue;}else{return new F(function(){return A1(_G1,_);});}})(_FY,_FZ,_));if(_G0!=__continue){return _G0;}}},_G6=new T(function(){return B(unCStr(")"));}),_G7=function(_G8,_G9,_Ga,_){var _Gb=new T(function(){var _Gc=new T(function(){var _Gd=new T(function(){var _Ge=new T(function(){return B(unAppCStr(" ADA from commit (with id: ",new T(function(){return B(_hq(B(_hA(0,E(_G8),_1M)),_G6));})));},1);return B(_hq(B(_hA(0,E(_Ga),_1M)),_Ge));});return B(unAppCStr(": Redeem ",_Gd));},1);return B(_hq(B(_hA(0,E(_G9),_1M)),_Gc));}),_Gf=__app2(E(_FN),toJSStr(B(unAppCStr("P",_Gb))),toJSStr(B(_Fu(0,new T3(1,_G8,_G9,_Ga),_1M))));return new F(function(){return _F8(_);});},_Gg=function(_Gh,_Gi,_){while(1){var _Gj=B((function(_Gk,_Gl,_){var _Gm=E(_Gl);if(!_Gm._){var _Gn=E(_Gm.b);_Gh=function(_){var _Go=B(_G7(_Gn.a,_Gn.b,_Gn.c,_));return new F(function(){return _Gg(_Gk,_Gm.d,_);});};_Gi=_Gm.c;return __continue;}else{return new F(function(){return A1(_Gk,_);});}})(_Gh,_Gi,_));if(_Gj!=__continue){return _Gj;}}},_Gp=function(_){return _h9;},_Gq=function(_Gr,_Gs,_Gt,_Gu,_){var _Gv=new T(function(){var _Gw=new T(function(){var _Gx=new T(function(){var _Gy=new T(function(){var _Gz=new T(function(){var _GA=new T(function(){return B(unAppCStr(" ADA expiring on: ",new T(function(){return B(_hA(0,E(_Gu),_1M));})));},1);return B(_hq(B(_hA(0,E(_Gt),_1M)),_GA));});return B(unAppCStr(") of ",_Gz));},1);return B(_hq(B(_hA(0,E(_Gr),_1M)),_Gy));});return B(unAppCStr(": Make commit (with id: ",_Gx));},1);return B(_hq(B(_hA(0,E(_Gs),_1M)),_Gw));}),_GB=__app2(E(_FN),toJSStr(B(unAppCStr("P",_Gv))),toJSStr(B(_Fu(0,new T4(0,_Gr,_Gs,_Gt,_Gu),_1M))));return new F(function(){return _F8(_);});},_GC=function(_GD,_GE,_){while(1){var _GF=B((function(_GG,_GH,_){var _GI=E(_GH);if(!_GI._){var _GJ=E(_GI.b);_GD=function(_){var _GK=B(_Gq(_GJ.a,_GJ.b,_GJ.c,_GJ.d,_));return new F(function(){return _GC(_GG,_GI.d,_);});};_GE=_GI.c;return __continue;}else{return new F(function(){return A1(_GG,_);});}})(_GD,_GE,_));if(_GF!=__continue){return _GF;}}},_GL=function(_GM,_GN,_GO,_GP,_){var _GQ=B(_GC(_Gp,_GM,_)),_GR=B(_Gg(_Gp,_GN,_)),_GS=B(_FX(_Gp,_GO,_));return new F(function(){return _Fi(_Gp,_GP,_);});},_GT=function(_GU,_GV){return E(_GU)==E(_GV);},_GW=function(_GX,_GY){var _GZ=E(_GX);switch(_GZ._){case 0:var _H0=E(_GY);if(!_H0._){if(E(_GZ.a)!=E(_H0.a)){return false;}else{if(E(_GZ.b)!=E(_H0.b)){return false;}else{if(E(_GZ.c)!=E(_H0.c)){return false;}else{return new F(function(){return _GT(_GZ.d,_H0.d);});}}}}else{return false;}break;case 1:var _H1=E(_GY);if(_H1._==1){if(E(_GZ.a)!=E(_H1.a)){return false;}else{if(E(_GZ.b)!=E(_H1.b)){return false;}else{if(E(_GZ.c)!=E(_H1.c)){return false;}else{return new F(function(){return _GT(_GZ.d,_H1.d);});}}}}else{return false;}break;case 2:var _H2=E(_GY);if(_H2._==2){if(E(_GZ.a)!=E(_H2.a)){return false;}else{if(E(_GZ.b)!=E(_H2.b)){return false;}else{if(E(_GZ.c)!=E(_H2.c)){return false;}else{return new F(function(){return _GT(_GZ.d,_H2.d);});}}}}else{return false;}break;case 3:var _H3=E(_GY);if(_H3._==3){if(E(_GZ.a)!=E(_H3.a)){return false;}else{if(E(_GZ.b)!=E(_H3.b)){return false;}else{return new F(function(){return _GT(_GZ.c,_H3.c);});}}}else{return false;}break;case 4:var _H4=E(_GY);if(_H4._==4){if(E(_GZ.a)!=E(_H4.a)){return false;}else{if(E(_GZ.b)!=E(_H4.b)){return false;}else{return new F(function(){return _GT(_GZ.c,_H4.c);});}}}else{return false;}break;case 5:var _H5=E(_GY);if(_H5._==5){if(E(_GZ.a)!=E(_H5.a)){return false;}else{if(E(_GZ.b)!=E(_H5.b)){return false;}else{return new F(function(){return _GT(_GZ.c,_H5.c);});}}}else{return false;}break;case 6:var _H6=E(_GY);if(_H6._==6){if(E(_GZ.a)!=E(_H6.a)){return false;}else{return new F(function(){return _GT(_GZ.b,_H6.b);});}}else{return false;}break;default:var _H7=E(_GY);if(_H7._==7){if(E(_GZ.a)!=E(_H7.a)){return false;}else{if(E(_GZ.b)!=E(_H7.b)){return false;}else{return new F(function(){return _GT(_GZ.c,_H7.c);});}}}else{return false;}}},_H8=function(_H9,_Ha){return (!B(_GW(_H9,_Ha)))?true:false;},_Hb=new T2(0,_GW,_H8),_Hc=function(_Hd,_He){while(1){var _Hf=E(_Hd);switch(_Hf._){case 0:var _Hg=E(_He);if(!_Hg._){return new F(function(){return _GT(_Hf.a,_Hg.a);});}else{return false;}break;case 1:var _Hh=E(_He);if(_Hh._==1){if(!B(_Hc(_Hf.a,_Hh.a))){return false;}else{_Hd=_Hf.b;_He=_Hh.b;continue;}}else{return false;}break;default:var _Hi=E(_He);if(_Hi._==2){return new F(function(){return _GT(_Hf.a,_Hi.a);});}else{return false;}}}},_Hj=function(_Hk,_Hl){while(1){var _Hm=E(_Hk);switch(_Hm._){case 0:var _Hn=E(_Hl);if(!_Hn._){return new F(function(){return _GT(_Hm.a,_Hn.a);});}else{return false;}break;case 1:var _Ho=E(_Hl);if(_Ho._==1){if(!B(_Hj(_Hm.a,_Ho.a))){return false;}else{_Hk=_Hm.b;_Hl=_Ho.b;continue;}}else{return false;}break;case 2:var _Hp=E(_Hl);if(_Hp._==2){if(!B(_Hj(_Hm.a,_Hp.a))){return false;}else{_Hk=_Hm.b;_Hl=_Hp.b;continue;}}else{return false;}break;case 3:var _Hq=E(_Hl);if(_Hq._==3){_Hk=_Hm.a;_Hl=_Hq.a;continue;}else{return false;}break;case 4:var _Hr=E(_Hl);if(_Hr._==4){if(E(_Hm.a)!=E(_Hr.a)){return false;}else{if(E(_Hm.b)!=E(_Hr.b)){return false;}else{return new F(function(){return _GT(_Hm.c,_Hr.c);});}}}else{return false;}break;case 5:var _Hs=E(_Hl);if(_Hs._==5){if(E(_Hm.a)!=E(_Hs.a)){return false;}else{return new F(function(){return _GT(_Hm.b,_Hs.b);});}}else{return false;}break;case 6:var _Ht=E(_Hl);if(_Ht._==6){if(!B(_Hc(_Hm.a,_Ht.a))){return false;}else{return new F(function(){return _Hc(_Hm.b,_Ht.b);});}}else{return false;}break;case 7:return (E(_Hl)._==7)?true:false;default:return (E(_Hl)._==8)?true:false;}}},_Hu=function(_Hv,_Hw){while(1){var _Hx=E(_Hv);switch(_Hx._){case 0:return (E(_Hw)._==0)?true:false;case 1:var _Hy=E(_Hw);if(_Hy._==1){if(E(_Hx.a)!=E(_Hy.a)){return false;}else{if(E(_Hx.b)!=E(_Hy.b)){return false;}else{if(E(_Hx.c)!=E(_Hy.c)){return false;}else{if(E(_Hx.d)!=E(_Hy.d)){return false;}else{if(E(_Hx.e)!=E(_Hy.e)){return false;}else{if(!B(_Hu(_Hx.f,_Hy.f))){return false;}else{_Hv=_Hx.g;_Hw=_Hy.g;continue;}}}}}}}else{return false;}break;case 2:var _Hz=E(_Hw);if(_Hz._==2){if(E(_Hx.a)!=E(_Hz.a)){return false;}else{_Hv=_Hx.b;_Hw=_Hz.b;continue;}}else{return false;}break;case 3:var _HA=E(_Hw);if(_HA._==3){if(E(_Hx.a)!=E(_HA.a)){return false;}else{if(E(_Hx.b)!=E(_HA.b)){return false;}else{if(E(_Hx.c)!=E(_HA.c)){return false;}else{if(E(_Hx.d)!=E(_HA.d)){return false;}else{if(E(_Hx.e)!=E(_HA.e)){return false;}else{_Hv=_Hx.f;_Hw=_HA.f;continue;}}}}}}else{return false;}break;case 4:var _HB=E(_Hw);if(_HB._==4){if(!B(_Hu(_Hx.a,_HB.a))){return false;}else{_Hv=_Hx.b;_Hw=_HB.b;continue;}}else{return false;}break;case 5:var _HC=E(_Hw);if(_HC._==5){if(!B(_Hj(_Hx.a,_HC.a))){return false;}else{if(!B(_Hu(_Hx.b,_HC.b))){return false;}else{_Hv=_Hx.c;_Hw=_HC.c;continue;}}}else{return false;}break;default:var _HD=E(_Hw);if(_HD._==6){if(!B(_Hj(_Hx.a,_HD.a))){return false;}else{if(E(_Hx.b)!=E(_HD.b)){return false;}else{if(!B(_Hu(_Hx.c,_HD.c))){return false;}else{_Hv=_Hx.d;_Hw=_HD.d;continue;}}}}else{return false;}}}},_HE=function(_HF,_HG,_HH,_HI){if(_HF!=_HH){return false;}else{return new F(function(){return _GT(_HG,_HI);});}},_HJ=function(_HK,_HL){var _HM=E(_HK),_HN=E(_HL);return new F(function(){return _HE(E(_HM.a),_HM.b,E(_HN.a),_HN.b);});},_HO=function(_HP,_HQ,_HR,_HS){return (_HP!=_HR)?true:(E(_HQ)!=E(_HS))?true:false;},_HT=function(_HU,_HV){var _HW=E(_HU),_HX=E(_HV);return new F(function(){return _HO(E(_HW.a),_HW.b,E(_HX.a),_HX.b);});},_HY=new T2(0,_HJ,_HT),_HZ=function(_I0,_I1){return E(_I0)!=E(_I1);},_I2=new T2(0,_GT,_HZ),_I3=function(_I4,_I5,_I6,_I7,_I8,_I9){return (!B(A3(_pR,_I4,_I6,_I8)))?true:(!B(A3(_pR,_I5,_I7,_I9)))?true:false;},_Ia=function(_Ib,_Ic,_Id,_Ie){var _If=E(_Id),_Ig=E(_Ie);return new F(function(){return _I3(_Ib,_Ic,_If.a,_If.b,_Ig.a,_Ig.b);});},_Ih=function(_Ii,_Ij,_Ik,_Il,_Im,_In){if(!B(A3(_pR,_Ii,_Ik,_Im))){return false;}else{return new F(function(){return A3(_pR,_Ij,_Il,_In);});}},_Io=function(_Ip,_Iq,_Ir,_Is){var _It=E(_Ir),_Iu=E(_Is);return new F(function(){return _Ih(_Ip,_Iq,_It.a,_It.b,_Iu.a,_Iu.b);});},_Iv=function(_Iw,_Ix){return new T2(0,function(_Iy,_Iz){return new F(function(){return _Io(_Iw,_Ix,_Iy,_Iz);});},function(_Iy,_Iz){return new F(function(){return _Ia(_Iw,_Ix,_Iy,_Iz);});});},_IA=function(_IB,_IC,_ID){while(1){var _IE=E(_IC);if(!_IE._){return (E(_ID)._==0)?true:false;}else{var _IF=E(_ID);if(!_IF._){return false;}else{if(!B(A3(_pR,_IB,_IE.a,_IF.a))){return false;}else{_IC=_IE.b;_ID=_IF.b;continue;}}}}},_IG=function(_IH,_II){var _IJ=new T(function(){return B(_Iv(_IH,_II));}),_IK=function(_IL,_IM){var _IN=function(_IO){var _IP=function(_IQ){if(_IO!=_IQ){return false;}else{return new F(function(){return _IA(_IJ,B(_hc(_1M,_IL)),B(_hc(_1M,_IM)));});}},_IR=E(_IM);if(!_IR._){return new F(function(){return _IP(_IR.a);});}else{return new F(function(){return _IP(0);});}},_IS=E(_IL);if(!_IS._){return new F(function(){return _IN(_IS.a);});}else{return new F(function(){return _IN(0);});}};return E(_IK);},_IT=new T(function(){return B(_IG(_HY,_I2));}),_IU=new T2(0,_GT,_HZ),_IV=function(_IW,_IX){var _IY=E(_IW);if(!_IY._){var _IZ=E(_IX);if(!_IZ._){if(E(_IY.a)!=E(_IZ.a)){return false;}else{return new F(function(){return _GT(_IY.b,_IZ.b);});}}else{return false;}}else{return (E(_IX)._==0)?false:true;}},_J0=function(_J1,_J2,_J3,_J4){if(_J1!=_J3){return false;}else{return new F(function(){return _IV(_J2,_J4);});}},_J5=function(_J6,_J7){var _J8=E(_J6),_J9=E(_J7);return new F(function(){return _J0(E(_J8.a),_J8.b,E(_J9.a),_J9.b);});},_Ja=function(_Jb,_Jc,_Jd,_Je){if(_Jb!=_Jd){return true;}else{var _Jf=E(_Jc);if(!_Jf._){var _Jg=E(_Je);return (_Jg._==0)?(E(_Jf.a)!=E(_Jg.a))?true:(E(_Jf.b)!=E(_Jg.b))?true:false:true;}else{return (E(_Je)._==0)?true:false;}}},_Jh=function(_Ji,_Jj){var _Jk=E(_Ji),_Jl=E(_Jj);return new F(function(){return _Ja(E(_Jk.a),_Jk.b,E(_Jl.a),_Jl.b);});},_Jm=new T2(0,_J5,_Jh),_Jn=new T(function(){return B(_IG(_IU,_Jm));}),_Jo=function(_Jp,_Jq){var _Jr=E(_Jp),_Js=E(_Jq);return (_Jr>_Js)?E(_Jr):E(_Js);},_Jt=function(_Ju,_Jv){var _Jw=E(_Ju),_Jx=E(_Jv);return (_Jw>_Jx)?E(_Jx):E(_Jw);},_Jy=function(_Jz,_JA){return (_Jz>=_JA)?(_Jz!=_JA)?2:1:0;},_JB=function(_JC,_JD){return new F(function(){return _Jy(E(_JC),E(_JD));});},_JE=function(_JF,_JG){return E(_JF)>=E(_JG);},_JH=function(_JI,_JJ){return E(_JI)>E(_JJ);},_JK=function(_JL,_JM){return E(_JL)<=E(_JM);},_JN=function(_JO,_JP){return E(_JO)<E(_JP);},_JQ={_:0,a:_IU,b:_JB,c:_JN,d:_JK,e:_JH,f:_JE,g:_Jo,h:_Jt},_JR=function(_JS,_JT,_JU,_JV,_JW){while(1){var _JX=E(_JW);if(!_JX._){var _JY=_JX.c,_JZ=_JX.d,_K0=E(_JX.b),_K1=E(_K0.a);if(_JS>=_K1){if(_JS!=_K1){_JT=_;_JW=_JZ;continue;}else{var _K2=E(_K0.b);if(_JU>=_K2){if(_JU!=_K2){_JT=_;_JW=_JZ;continue;}else{var _K3=E(_K0.c);if(_JV>=_K3){if(_JV!=_K3){_JT=_;_JW=_JZ;continue;}else{return true;}}else{_JT=_;_JW=_JY;continue;}}}else{_JT=_;_JW=_JY;continue;}}}else{_JT=_;_JW=_JY;continue;}}else{return false;}}},_K4=function(_K5,_K6,_K7,_K8,_K9){while(1){var _Ka=E(_K9);if(!_Ka._){var _Kb=_Ka.c,_Kc=_Ka.d,_Kd=E(_Ka.b),_Ke=E(_Kd.a);if(_K5>=_Ke){if(_K5!=_Ke){_K6=_;_K9=_Kc;continue;}else{var _Kf=E(_Kd.b);if(_K7>=_Kf){if(_K7!=_Kf){_K6=_;_K9=_Kc;continue;}else{var _Kg=E(_K8),_Kh=E(_Kd.c);if(_Kg>=_Kh){if(_Kg!=_Kh){return new F(function(){return _JR(_K5,_,_K7,_Kg,_Kc);});}else{return true;}}else{return new F(function(){return _JR(_K5,_,_K7,_Kg,_Kb);});}}}else{_K6=_;_K9=_Kb;continue;}}}else{_K6=_;_K9=_Kb;continue;}}else{return false;}}},_Ki=function(_Kj,_Kk,_Kl,_Km,_Kn){while(1){var _Ko=E(_Kn);if(!_Ko._){var _Kp=_Ko.c,_Kq=_Ko.d,_Kr=E(_Ko.b),_Ks=E(_Kr.a);if(_Kj>=_Ks){if(_Kj!=_Ks){_Kk=_;_Kn=_Kq;continue;}else{var _Kt=E(_Kl),_Ku=E(_Kr.b);if(_Kt>=_Ku){if(_Kt!=_Ku){return new F(function(){return _K4(_Kj,_,_Kt,_Km,_Kq);});}else{var _Kv=E(_Km),_Kw=E(_Kr.c);if(_Kv>=_Kw){if(_Kv!=_Kw){return new F(function(){return _JR(_Kj,_,_Kt,_Kv,_Kq);});}else{return true;}}else{return new F(function(){return _JR(_Kj,_,_Kt,_Kv,_Kp);});}}}else{return new F(function(){return _K4(_Kj,_,_Kt,_Km,_Kp);});}}}else{_Kk=_;_Kn=_Kp;continue;}}else{return false;}}},_Kx=function(_Ky,_Kz,_KA,_KB){var _KC=E(_KB);if(!_KC._){var _KD=_KC.c,_KE=_KC.d,_KF=E(_KC.b),_KG=E(_Ky),_KH=E(_KF.a);if(_KG>=_KH){if(_KG!=_KH){return new F(function(){return _Ki(_KG,_,_Kz,_KA,_KE);});}else{var _KI=E(_Kz),_KJ=E(_KF.b);if(_KI>=_KJ){if(_KI!=_KJ){return new F(function(){return _K4(_KG,_,_KI,_KA,_KE);});}else{var _KK=E(_KA),_KL=E(_KF.c);if(_KK>=_KL){if(_KK!=_KL){return new F(function(){return _JR(_KG,_,_KI,_KK,_KE);});}else{return true;}}else{return new F(function(){return _JR(_KG,_,_KI,_KK,_KD);});}}}else{return new F(function(){return _K4(_KG,_,_KI,_KA,_KD);});}}}else{return new F(function(){return _Ki(_KG,_,_Kz,_KA,_KD);});}}else{return false;}},_KM=function(_KN,_KO,_KP,_KQ,_KR){var _KS=E(_KR);if(!_KS._){if(E(_KS.b)>E(_KO)){return false;}else{return new F(function(){return _Kx(_KP,_KQ,_KS.a,E(_KN).b);});}}else{return false;}},_KT=function(_KU,_KV,_KW,_KX,_KY){var _KZ=E(_KY);if(!_KZ._){var _L0=new T(function(){var _L1=B(_KT(_KZ.a,_KZ.b,_KZ.c,_KZ.d,_KZ.e));return new T2(0,_L1.a,_L1.b);});return new T2(0,new T(function(){return E(E(_L0).a);}),new T(function(){return B(_9e(_KV,_KW,_KX,E(_L0).b));}));}else{return new T2(0,new T2(0,_KV,_KW),_KX);}},_L2=function(_L3,_L4,_L5,_L6,_L7){var _L8=E(_L6);if(!_L8._){var _L9=new T(function(){var _La=B(_L2(_L8.a,_L8.b,_L8.c,_L8.d,_L8.e));return new T2(0,_La.a,_La.b);});return new T2(0,new T(function(){return E(E(_L9).a);}),new T(function(){return B(_8n(_L4,_L5,E(_L9).b,_L7));}));}else{return new T2(0,new T2(0,_L4,_L5),_L7);}},_Lb=function(_Lc,_Ld){var _Le=E(_Lc);if(!_Le._){var _Lf=_Le.a,_Lg=E(_Ld);if(!_Lg._){var _Lh=_Lg.a;if(_Lf<=_Lh){var _Li=B(_L2(_Lh,_Lg.b,_Lg.c,_Lg.d,_Lg.e)),_Lj=E(_Li.a);return new F(function(){return _9e(_Lj.a,_Lj.b,_Le,_Li.b);});}else{var _Lk=B(_KT(_Lf,_Le.b,_Le.c,_Le.d,_Le.e)),_Ll=E(_Lk.a);return new F(function(){return _8n(_Ll.a,_Ll.b,_Lk.b,_Lg);});}}else{return E(_Le);}}else{return E(_Ld);}},_Lm=function(_Ln,_Lo,_Lp,_Lq,_Lr,_Ls){var _Lt=E(_Ln);if(!_Lt._){var _Lu=_Lt.a,_Lv=_Lt.b,_Lw=_Lt.c,_Lx=_Lt.d,_Ly=_Lt.e;if((imul(3,_Lu)|0)>=_Lo){if((imul(3,_Lo)|0)>=_Lu){return new F(function(){return _Lb(_Lt,new T5(0,_Lo,E(_Lp),_Lq,E(_Lr),E(_Ls)));});}else{return new F(function(){return _8n(_Lv,_Lw,_Lx,B(_Lm(_Ly,_Lo,_Lp,_Lq,_Lr,_Ls)));});}}else{return new F(function(){return _9e(_Lp,_Lq,B(_Lz(_Lu,_Lv,_Lw,_Lx,_Ly,_Lr)),_Ls);});}}else{return new T5(0,_Lo,E(_Lp),_Lq,E(_Lr),E(_Ls));}},_Lz=function(_LA,_LB,_LC,_LD,_LE,_LF){var _LG=E(_LF);if(!_LG._){var _LH=_LG.a,_LI=_LG.b,_LJ=_LG.c,_LK=_LG.d,_LL=_LG.e;if((imul(3,_LA)|0)>=_LH){if((imul(3,_LH)|0)>=_LA){return new F(function(){return _Lb(new T5(0,_LA,E(_LB),_LC,E(_LD),E(_LE)),_LG);});}else{return new F(function(){return _8n(_LB,_LC,_LD,B(_Lm(_LE,_LH,_LI,_LJ,_LK,_LL)));});}}else{return new F(function(){return _9e(_LI,_LJ,B(_Lz(_LA,_LB,_LC,_LD,_LE,_LK)),_LL);});}}else{return new T5(0,_LA,E(_LB),_LC,E(_LD),E(_LE));}},_LM=function(_LN,_LO){var _LP=E(_LN);if(!_LP._){var _LQ=_LP.a,_LR=_LP.b,_LS=_LP.c,_LT=_LP.d,_LU=_LP.e,_LV=E(_LO);if(!_LV._){var _LW=_LV.a,_LX=_LV.b,_LY=_LV.c,_LZ=_LV.d,_M0=_LV.e;if((imul(3,_LQ)|0)>=_LW){if((imul(3,_LW)|0)>=_LQ){return new F(function(){return _Lb(_LP,_LV);});}else{return new F(function(){return _8n(_LR,_LS,_LT,B(_Lm(_LU,_LW,_LX,_LY,_LZ,_M0)));});}}else{return new F(function(){return _9e(_LX,_LY,B(_Lz(_LQ,_LR,_LS,_LT,_LU,_LZ)),_M0);});}}else{return E(_LP);}}else{return E(_LO);}},_M1=function(_M2,_M3){var _M4=E(_M3);if(!_M4._){var _M5=_M4.b,_M6=_M4.c,_M7=B(_M1(_M2,_M4.d)),_M8=_M7.a,_M9=_M7.b,_Ma=B(_M1(_M2,_M4.e)),_Mb=_Ma.a,_Mc=_Ma.b;return (!B(A2(_M2,_M5,_M6)))?new T2(0,B(_LM(_M8,_Mb)),B(_ay(_M5,_M6,_M9,_Mc))):new T2(0,B(_ay(_M5,_M6,_M8,_Mb)),B(_LM(_M9,_Mc)));}else{return new T2(0,_8i,_8i);}},_Md=__Z,_Me=function(_Mf,_Mg){while(1){var _Mh=B((function(_Mi,_Mj){var _Mk=E(_Mj);if(!_Mk._){var _Ml=_Mk.e,_Mm=new T(function(){var _Mn=E(_Mk.c),_Mo=E(_Mn.b);if(!_Mo._){return new T2(1,new T3(5,_Mk.b,_Mn.a,_Mo.a),new T(function(){return B(_Me(_Mi,_Ml));}));}else{return B(_Me(_Mi,_Ml));}},1);_Mf=_Mm;_Mg=_Mk.d;return __continue;}else{return E(_Mi);}})(_Mf,_Mg));if(_Mh!=__continue){return _Mh;}}},_Mp=function(_Mq,_Mr){var _Ms=E(_Mr);return (_Ms._==0)?new T5(0,_Ms.a,E(_Ms.b),new T(function(){return B(A1(_Mq,_Ms.c));}),E(B(_Mp(_Mq,_Ms.d))),E(B(_Mp(_Mq,_Ms.e)))):new T0(1);},_Mt=new T0(1),_Mu=function(_Mv){var _Mw=E(_Mv),_Mx=E(_Mw.b);return new T2(0,_Mw.a,_Mt);},_My=function(_Mz){return E(E(_Mz).b);},_MA=function(_MB,_MC,_MD){var _ME=E(_MC);if(!_ME._){return E(_MD);}else{var _MF=function(_MG,_MH){while(1){var _MI=E(_MH);if(!_MI._){var _MJ=_MI.b,_MK=_MI.e;switch(B(A3(_My,_MB,_MG,_MJ))){case 0:return new F(function(){return _ay(_MJ,_MI.c,B(_MF(_MG,_MI.d)),_MK);});break;case 1:return E(_MK);default:_MH=_MK;continue;}}else{return new T0(1);}}};return new F(function(){return _MF(_ME.a,_MD);});}},_ML=function(_MM,_MN,_MO){var _MP=E(_MN);if(!_MP._){return E(_MO);}else{var _MQ=function(_MR,_MS){while(1){var _MT=E(_MS);if(!_MT._){var _MU=_MT.b,_MV=_MT.d;switch(B(A3(_My,_MM,_MU,_MR))){case 0:return new F(function(){return _ay(_MU,_MT.c,_MV,B(_MQ(_MR,_MT.e)));});break;case 1:return E(_MV);default:_MS=_MV;continue;}}else{return new T0(1);}}};return new F(function(){return _MQ(_MP.a,_MO);});}},_MW=function(_MX,_MY,_MZ,_N0){var _N1=E(_MY),_N2=E(_N0);if(!_N2._){var _N3=_N2.b,_N4=_N2.c,_N5=_N2.d,_N6=_N2.e;switch(B(A3(_My,_MX,_N1,_N3))){case 0:return new F(function(){return _9e(_N3,_N4,B(_MW(_MX,_N1,_MZ,_N5)),_N6);});break;case 1:return E(_N2);default:return new F(function(){return _8n(_N3,_N4,_N5,B(_MW(_MX,_N1,_MZ,_N6)));});}}else{return new T5(0,1,E(_N1),_MZ,E(_8i),E(_8i));}},_N7=function(_N8,_N9,_Na,_Nb){return new F(function(){return _MW(_N8,_N9,_Na,_Nb);});},_Nc=function(_Nd){return E(E(_Nd).d);},_Ne=function(_Nf){return E(E(_Nf).f);},_Ng=function(_Nh,_Ni,_Nj,_Nk){var _Nl=E(_Ni);if(!_Nl._){var _Nm=E(_Nj);if(!_Nm._){return E(_Nk);}else{var _Nn=function(_No,_Np){while(1){var _Nq=E(_Np);if(!_Nq._){if(!B(A3(_Ne,_Nh,_Nq.b,_No))){return E(_Nq);}else{_Np=_Nq.d;continue;}}else{return new T0(1);}}};return new F(function(){return _Nn(_Nm.a,_Nk);});}}else{var _Nr=_Nl.a,_Ns=E(_Nj);if(!_Ns._){var _Nt=function(_Nu,_Nv){while(1){var _Nw=E(_Nv);if(!_Nw._){if(!B(A3(_Nc,_Nh,_Nw.b,_Nu))){return E(_Nw);}else{_Nv=_Nw.e;continue;}}else{return new T0(1);}}};return new F(function(){return _Nt(_Nr,_Nk);});}else{var _Nx=function(_Ny,_Nz,_NA){while(1){var _NB=E(_NA);if(!_NB._){var _NC=_NB.b;if(!B(A3(_Nc,_Nh,_NC,_Ny))){if(!B(A3(_Ne,_Nh,_NC,_Nz))){return E(_NB);}else{_NA=_NB.d;continue;}}else{_NA=_NB.e;continue;}}else{return new T0(1);}}};return new F(function(){return _Nx(_Nr,_Ns.a,_Nk);});}}},_ND=function(_NE,_NF,_NG,_NH,_NI){var _NJ=E(_NI);if(!_NJ._){var _NK=_NJ.b,_NL=_NJ.c,_NM=_NJ.d,_NN=_NJ.e,_NO=E(_NH);if(!_NO._){var _NP=_NO.b,_NQ=function(_NR){var _NS=new T1(1,E(_NP));return new F(function(){return _ay(_NP,_NO.c,B(_ND(_NE,_NF,_NS,_NO.d,B(_Ng(_NE,_NF,_NS,_NJ)))),B(_ND(_NE,_NS,_NG,_NO.e,B(_Ng(_NE,_NS,_NG,_NJ)))));});};if(!E(_NM)._){return new F(function(){return _NQ(_);});}else{if(!E(_NN)._){return new F(function(){return _NQ(_);});}else{return new F(function(){return _N7(_NE,_NK,_NL,_NO);});}}}else{return new F(function(){return _ay(_NK,_NL,B(_MA(_NE,_NF,_NM)),B(_ML(_NE,_NG,_NN)));});}}else{return E(_NH);}},_NT=function(_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1,_O2,_O3,_O4,_O5,_O6){var _O7=function(_O8){var _O9=new T1(1,E(_NY));return new F(function(){return _ay(_NY,_NZ,B(_ND(_NU,_NV,_O9,_O0,B(_Ng(_NU,_NV,_O9,new T5(0,_O2,E(_O3),_O4,E(_O5),E(_O6)))))),B(_ND(_NU,_O9,_NW,_O1,B(_Ng(_NU,_O9,_NW,new T5(0,_O2,E(_O3),_O4,E(_O5),E(_O6)))))));});};if(!E(_O5)._){return new F(function(){return _O7(_);});}else{if(!E(_O6)._){return new F(function(){return _O7(_);});}else{return new F(function(){return _N7(_NU,_O3,_O4,new T5(0,_NX,E(_NY),_NZ,E(_O0),E(_O1)));});}}},_Oa=function(_Ob,_Oc,_Od){var _Oe=new T(function(){var _Of=new T(function(){return E(E(_Od).b);}),_Og=B(_M1(function(_Oh,_Oi){var _Oj=E(_Oi);return new F(function(){return _KM(_Ob,_Of,_Oh,_Oj.a,_Oj.b);});},_Oc));return new T2(0,_Og.a,_Og.b);}),_Ok=new T(function(){return E(E(_Oe).a);});return new T2(0,new T(function(){var _Ol=B(_Mp(_Mu,_Ok));if(!_Ol._){var _Om=E(E(_Oe).b);if(!_Om._){return B(_NT(_JQ,_Md,_Md,_Ol.a,_Ol.b,_Ol.c,_Ol.d,_Ol.e,_Om.a,_Om.b,_Om.c,_Om.d,_Om.e));}else{return E(_Ol);}}else{return E(E(_Oe).b);}}),new T(function(){return B(_Me(_1M,_Ok));}));},_On=function(_Oo,_Op,_Oq,_Or){while(1){var _Os=E(_Or);if(!_Os._){var _Ot=_Os.d,_Ou=_Os.e,_Ov=E(_Os.b),_Ow=E(_Ov.a);if(_Oo>=_Ow){if(_Oo!=_Ow){_Op=_;_Or=_Ou;continue;}else{var _Ox=E(_Ov.b);if(_Oq>=_Ox){if(_Oq!=_Ox){_Op=_;_Or=_Ou;continue;}else{return true;}}else{_Op=_;_Or=_Ot;continue;}}}else{_Op=_;_Or=_Ot;continue;}}else{return false;}}},_Oy=function(_Oz,_OA,_OB,_OC){while(1){var _OD=E(_OC);if(!_OD._){var _OE=_OD.d,_OF=_OD.e,_OG=E(_OD.b),_OH=E(_OG.a);if(_Oz>=_OH){if(_Oz!=_OH){_OA=_;_OC=_OF;continue;}else{var _OI=E(_OB),_OJ=E(_OG.b);if(_OI>=_OJ){if(_OI!=_OJ){return new F(function(){return _On(_Oz,_,_OI,_OF);});}else{return true;}}else{return new F(function(){return _On(_Oz,_,_OI,_OE);});}}}else{_OA=_;_OC=_OE;continue;}}else{return false;}}},_OK=function(_OL,_OM,_ON,_OO,_OP){var _OQ=E(_OP);if(!_OQ._){var _OR=_OQ.c,_OS=_OQ.d,_OT=_OQ.e,_OU=E(_OQ.b),_OV=E(_OU.a);if(_OL>=_OV){if(_OL!=_OV){return new F(function(){return _8n(_OU,_OR,_OS,B(_OK(_OL,_,_ON,_OO,_OT)));});}else{var _OW=E(_OU.b);if(_ON>=_OW){if(_ON!=_OW){return new F(function(){return _8n(_OU,_OR,_OS,B(_OK(_OL,_,_ON,_OO,_OT)));});}else{return new T5(0,_OQ.a,E(new T2(0,_OL,_ON)),_OO,E(_OS),E(_OT));}}else{return new F(function(){return _9e(_OU,_OR,B(_OK(_OL,_,_ON,_OO,_OS)),_OT);});}}}else{return new F(function(){return _9e(_OU,_OR,B(_OK(_OL,_,_ON,_OO,_OS)),_OT);});}}else{return new T5(0,1,E(new T2(0,_OL,_ON)),_OO,E(_8i),E(_8i));}},_OX=function(_OY,_OZ,_P0,_P1,_P2){var _P3=E(_P2);if(!_P3._){var _P4=_P3.c,_P5=_P3.d,_P6=_P3.e,_P7=E(_P3.b),_P8=E(_P7.a);if(_OY>=_P8){if(_OY!=_P8){return new F(function(){return _8n(_P7,_P4,_P5,B(_OX(_OY,_,_P0,_P1,_P6)));});}else{var _P9=E(_P0),_Pa=E(_P7.b);if(_P9>=_Pa){if(_P9!=_Pa){return new F(function(){return _8n(_P7,_P4,_P5,B(_OK(_OY,_,_P9,_P1,_P6)));});}else{return new T5(0,_P3.a,E(new T2(0,_OY,_P9)),_P1,E(_P5),E(_P6));}}else{return new F(function(){return _9e(_P7,_P4,B(_OK(_OY,_,_P9,_P1,_P5)),_P6);});}}}else{return new F(function(){return _9e(_P7,_P4,B(_OX(_OY,_,_P0,_P1,_P5)),_P6);});}}else{return new T5(0,1,E(new T2(0,_OY,_P0)),_P1,E(_8i),E(_8i));}},_Pb=function(_Pc,_Pd,_Pe,_Pf){var _Pg=E(_Pf);if(!_Pg._){var _Ph=_Pg.c,_Pi=_Pg.d,_Pj=_Pg.e,_Pk=E(_Pg.b),_Pl=E(_Pc),_Pm=E(_Pk.a);if(_Pl>=_Pm){if(_Pl!=_Pm){return new F(function(){return _8n(_Pk,_Ph,_Pi,B(_OX(_Pl,_,_Pd,_Pe,_Pj)));});}else{var _Pn=E(_Pd),_Po=E(_Pk.b);if(_Pn>=_Po){if(_Pn!=_Po){return new F(function(){return _8n(_Pk,_Ph,_Pi,B(_OK(_Pl,_,_Pn,_Pe,_Pj)));});}else{return new T5(0,_Pg.a,E(new T2(0,_Pl,_Pn)),_Pe,E(_Pi),E(_Pj));}}else{return new F(function(){return _9e(_Pk,_Ph,B(_OK(_Pl,_,_Pn,_Pe,_Pi)),_Pj);});}}}else{return new F(function(){return _9e(_Pk,_Ph,B(_OX(_Pl,_,_Pd,_Pe,_Pi)),_Pj);});}}else{return new T5(0,1,E(new T2(0,_Pc,_Pd)),_Pe,E(_8i),E(_8i));}},_Pp=function(_Pq,_Pr,_Ps){while(1){var _Pt=B((function(_Pu,_Pv,_Pw){var _Px=E(_Pw);if(!_Px._){var _Py=_Px.c,_Pz=_Px.e,_PA=E(_Px.b),_PB=_PA.a,_PC=_PA.b,_PD=B(_Pp(_Pu,_Pv,_Px.d)),_PE=_PD.a,_PF=_PD.b,_PG=function(_PH){return new F(function(){return _Pp(new T(function(){return B(_Pb(_PB,_PC,_Py,_PE));}),new T2(1,new T3(7,_PB,_PC,_Py),_PF),_Pz);});},_PI=E(_PE);if(!_PI._){var _PJ=_PI.d,_PK=_PI.e,_PL=E(_PI.b),_PM=E(_PB),_PN=E(_PL.a);if(_PM>=_PN){if(_PM!=_PN){if(!B(_Oy(_PM,_,_PC,_PK))){return new F(function(){return _PG(_);});}else{_Pq=_PI;_Pr=_PF;_Ps=_Pz;return __continue;}}else{var _PO=E(_PC),_PP=E(_PL.b);if(_PO>=_PP){if(_PO!=_PP){if(!B(_On(_PM,_,_PO,_PK))){return new F(function(){return _PG(_);});}else{_Pq=_PI;_Pr=_PF;_Ps=_Pz;return __continue;}}else{_Pq=_PI;_Pr=_PF;_Ps=_Pz;return __continue;}}else{if(!B(_On(_PM,_,_PO,_PJ))){return new F(function(){return _PG(_);});}else{_Pq=_PI;_Pr=_PF;_Ps=_Pz;return __continue;}}}}else{if(!B(_Oy(_PM,_,_PC,_PJ))){return new F(function(){return _PG(_);});}else{_Pq=_PI;_Pr=_PF;_Ps=_Pz;return __continue;}}}else{return new F(function(){return _PG(_);});}}else{return new T2(0,_Pu,_Pv);}})(_Pq,_Pr,_Ps));if(_Pt!=__continue){return _Pt;}}},_PQ=function(_PR,_PS,_PT,_PU){while(1){var _PV=E(_PU);if(!_PV._){var _PW=_PV.d,_PX=_PV.e,_PY=E(_PV.b),_PZ=E(_PY.a);if(_PR>=_PZ){if(_PR!=_PZ){_PS=_;_PU=_PX;continue;}else{var _Q0=E(_PY.b);if(_PT>=_Q0){if(_PT!=_Q0){_PS=_;_PU=_PX;continue;}else{return new T1(1,_PV.c);}}else{_PS=_;_PU=_PW;continue;}}}else{_PS=_;_PU=_PW;continue;}}else{return __Z;}}},_Q1=function(_Q2,_Q3,_Q4,_Q5){while(1){var _Q6=E(_Q5);if(!_Q6._){var _Q7=_Q6.d,_Q8=_Q6.e,_Q9=E(_Q6.b),_Qa=E(_Q9.a);if(_Q2>=_Qa){if(_Q2!=_Qa){_Q3=_;_Q5=_Q8;continue;}else{var _Qb=E(_Q4),_Qc=E(_Q9.b);if(_Qb>=_Qc){if(_Qb!=_Qc){return new F(function(){return _PQ(_Q2,_,_Qb,_Q8);});}else{return new T1(1,_Q6.c);}}else{return new F(function(){return _PQ(_Q2,_,_Qb,_Q7);});}}}else{_Q3=_;_Q5=_Q7;continue;}}else{return __Z;}}},_Qd=function(_Qe,_Qf,_Qg,_Qh,_Qi){while(1){var _Qj=E(_Qi);if(!_Qj._){var _Qk=_Qj.c,_Ql=_Qj.d,_Qm=E(_Qj.b),_Qn=E(_Qe),_Qo=E(_Qm.a);if(_Qn>=_Qo){if(_Qn!=_Qo){_Qe=_Qn;_Qi=_Ql;continue;}else{var _Qp=E(_Qf),_Qq=E(_Qm.b);if(_Qp>=_Qq){if(_Qp!=_Qq){_Qe=_Qn;_Qf=_Qp;_Qi=_Ql;continue;}else{var _Qr=E(_Qg),_Qs=E(_Qm.c);if(_Qr>=_Qs){if(_Qr!=_Qs){_Qe=_Qn;_Qf=_Qp;_Qg=_Qr;_Qi=_Ql;continue;}else{var _Qt=E(_Qm.d);if(_Qh>=_Qt){if(_Qh!=_Qt){_Qe=_Qn;_Qf=_Qp;_Qg=_Qr;_Qi=_Ql;continue;}else{return true;}}else{_Qe=_Qn;_Qf=_Qp;_Qg=_Qr;_Qi=_Qk;continue;}}}else{_Qe=_Qn;_Qf=_Qp;_Qg=_Qr;_Qi=_Qk;continue;}}}else{_Qe=_Qn;_Qf=_Qp;_Qi=_Qk;continue;}}}else{_Qe=_Qn;_Qi=_Qk;continue;}}else{return false;}}},_Qu=function(_Qv,_Qw){return E(_Qv)+E(_Qw)|0;},_Qx=0,_Qy=function(_Qz,_QA,_QB){var _QC=function(_QD,_QE){while(1){var _QF=B((function(_QG,_QH){var _QI=E(_QH);if(!_QI._){var _QJ=new T(function(){return B(_QC(_QG,_QI.e));}),_QK=function(_QL){var _QM=E(_QI.c),_QN=E(_QM.b);if(!_QN._){if(E(_QM.a)!=E(_QA)){return new F(function(){return A1(_QJ,_QL);});}else{if(E(_QN.b)>E(_QB)){return new F(function(){return A1(_QJ,new T(function(){return B(_Qu(_QL,_QN.a));}));});}else{return new F(function(){return A1(_QJ,_QL);});}}}else{return new F(function(){return A1(_QJ,_QL);});}};_QD=_QK;_QE=_QI.d;return __continue;}else{return E(_QG);}})(_QD,_QE));if(_QF!=__continue){return _QF;}}};return new F(function(){return A3(_QC,_na,_Qz,_Qx);});},_QO=function(_QP,_QQ){while(1){var _QR=E(_QQ);if(!_QR._){var _QS=E(_QR.b);if(_QP>=_QS){if(_QP!=_QS){_QQ=_QR.e;continue;}else{return new T1(1,_QR.c);}}else{_QQ=_QR.d;continue;}}else{return __Z;}}},_QT=__Z,_QU=new T(function(){return B(unCStr("attempt to discount when insufficient cash available"));}),_QV=new T(function(){return B(err(_QU));}),_QW=function(_QX,_QY){var _QZ=E(_QY);if(!_QZ._){return E(_QV);}else{var _R0=_QZ.b,_R1=E(_QZ.a),_R2=_R1.a,_R3=E(_R1.b),_R4=_R3.a,_R5=E(_R3.b);if(!_R5._){var _R6=_R5.b,_R7=E(_R5.a);return (_QX>_R7)?(_R7>=_QX)?E(_R0):new T2(1,new T2(0,_R2,new T2(0,_R4,new T2(0,_Qx,_R6))),new T(function(){return B(_QW(_QX-_R7|0,_R0));})):new T2(1,new T2(0,_R2,new T2(0,_R4,new T2(0,_R7-_QX|0,_R6))),_1M);}else{return E(_R0);}}},_R8=function(_R9,_Ra){var _Rb=E(_Ra);if(!_Rb._){return E(_QV);}else{var _Rc=_Rb.b,_Rd=E(_Rb.a),_Re=_Rd.a,_Rf=E(_Rd.b),_Rg=_Rf.a,_Rh=E(_Rf.b);if(!_Rh._){var _Ri=_Rh.b,_Rj=E(_R9),_Rk=E(_Rh.a);return (_Rj>_Rk)?(_Rk>=_Rj)?E(_Rc):new T2(1,new T2(0,_Re,new T2(0,_Rg,new T2(0,_Qx,_Ri))),new T(function(){return B(_QW(_Rj-_Rk|0,_Rc));})):new T2(1,new T2(0,_Re,new T2(0,_Rg,new T2(0,_Rk-_Rj|0,_Ri))),_1M);}else{return E(_Rc);}}},_Rl=function(_Rm,_Rn){var _Ro=E(_Rn);if(!_Ro._){var _Rp=_Ro.b,_Rq=_Ro.c,_Rr=_Ro.d,_Rs=_Ro.e;if(!B(A2(_Rm,_Rp,_Rq))){return new F(function(){return _LM(B(_Rl(_Rm,_Rr)),B(_Rl(_Rm,_Rs)));});}else{return new F(function(){return _ay(_Rp,_Rq,B(_Rl(_Rm,_Rr)),B(_Rl(_Rm,_Rs)));});}}else{return new T0(1);}},_Rt=function(_Ru,_Rv){var _Rw=E(_Ru);if(!_Rw._){var _Rx=E(_Rv);if(!_Rx._){return new F(function(){return _JB(_Rw.b,_Rx.b);});}else{return 0;}}else{return (E(_Rv)._==0)?2:1;}},_Ry=function(_Rz,_RA){return new F(function(){return _Rt(E(E(_Rz).b).b,E(E(_RA).b).b);});},_RB=new T2(1,_1M,_1M),_RC=function(_RD,_RE){var _RF=function(_RG,_RH){var _RI=E(_RG);if(!_RI._){return E(_RH);}else{var _RJ=_RI.a,_RK=E(_RH);if(!_RK._){return E(_RI);}else{var _RL=_RK.a;return (B(A2(_RD,_RJ,_RL))==2)?new T2(1,_RL,new T(function(){return B(_RF(_RI,_RK.b));})):new T2(1,_RJ,new T(function(){return B(_RF(_RI.b,_RK));}));}}},_RM=function(_RN){var _RO=E(_RN);if(!_RO._){return __Z;}else{var _RP=E(_RO.b);return (_RP._==0)?E(_RO):new T2(1,new T(function(){return B(_RF(_RO.a,_RP.a));}),new T(function(){return B(_RM(_RP.b));}));}},_RQ=new T(function(){return B(_RR(B(_RM(_1M))));}),_RR=function(_RS){while(1){var _RT=E(_RS);if(!_RT._){return E(_RQ);}else{if(!E(_RT.b)._){return E(_RT.a);}else{_RS=B(_RM(_RT));continue;}}}},_RU=new T(function(){return B(_RV(_1M));}),_RW=function(_RX,_RY,_RZ){while(1){var _S0=B((function(_S1,_S2,_S3){var _S4=E(_S3);if(!_S4._){return new T2(1,new T2(1,_S1,_S2),_RU);}else{var _S5=_S4.a;if(B(A2(_RD,_S1,_S5))==2){var _S6=new T2(1,_S1,_S2);_RX=_S5;_RY=_S6;_RZ=_S4.b;return __continue;}else{return new T2(1,new T2(1,_S1,_S2),new T(function(){return B(_RV(_S4));}));}}})(_RX,_RY,_RZ));if(_S0!=__continue){return _S0;}}},_S7=function(_S8,_S9,_Sa){while(1){var _Sb=B((function(_Sc,_Sd,_Se){var _Sf=E(_Se);if(!_Sf._){return new T2(1,new T(function(){return B(A1(_Sd,new T2(1,_Sc,_1M)));}),_RU);}else{var _Sg=_Sf.a,_Sh=_Sf.b;switch(B(A2(_RD,_Sc,_Sg))){case 0:_S8=_Sg;_S9=function(_Si){return new F(function(){return A1(_Sd,new T2(1,_Sc,_Si));});};_Sa=_Sh;return __continue;case 1:_S8=_Sg;_S9=function(_Sj){return new F(function(){return A1(_Sd,new T2(1,_Sc,_Sj));});};_Sa=_Sh;return __continue;default:return new T2(1,new T(function(){return B(A1(_Sd,new T2(1,_Sc,_1M)));}),new T(function(){return B(_RV(_Sf));}));}}})(_S8,_S9,_Sa));if(_Sb!=__continue){return _Sb;}}},_RV=function(_Sk){var _Sl=E(_Sk);if(!_Sl._){return E(_RB);}else{var _Sm=_Sl.a,_Sn=E(_Sl.b);if(!_Sn._){return new T2(1,_Sl,_1M);}else{var _So=_Sn.a,_Sp=_Sn.b;if(B(A2(_RD,_Sm,_So))==2){return new F(function(){return _RW(_So,new T2(1,_Sm,_1M),_Sp);});}else{return new F(function(){return _S7(_So,function(_Sq){return new T2(1,_Sm,_Sq);},_Sp);});}}}};return new F(function(){return _RR(B(_RV(_RE)));});},_Sr=function(_Ss,_St,_Su){var _Sv=B(_EV(B(_R8(_St,B(_RC(_Ry,B(_hc(_1M,B(_Rl(function(_Sw,_Sx){return new F(function(){return A1(_Ss,_Sx);});},_Su))))))))));if(!_Sv._){var _Sy=E(_Su);if(!_Sy._){return new F(function(){return _NT(_JQ,_Md,_Md,_Sv.a,_Sv.b,_Sv.c,_Sv.d,_Sv.e,_Sy.a,_Sy.b,_Sy.c,_Sy.d,_Sy.e);});}else{return E(_Sv);}}else{return E(_Su);}},_Sz=function(_SA,_SB,_SC,_SD){while(1){var _SE=E(_SD);if(!_SE._){var _SF=_SE.d,_SG=_SE.e,_SH=E(_SE.b),_SI=E(_SH.a);if(_SA>=_SI){if(_SA!=_SI){_SB=_;_SD=_SG;continue;}else{var _SJ=E(_SH.b);if(_SC>=_SJ){if(_SC!=_SJ){_SB=_;_SD=_SG;continue;}else{return new T1(1,_SE.c);}}else{_SB=_;_SD=_SF;continue;}}}else{_SB=_;_SD=_SF;continue;}}else{return __Z;}}},_SK=function(_SL,_SM,_SN,_SO){while(1){var _SP=E(_SO);if(!_SP._){var _SQ=_SP.d,_SR=_SP.e,_SS=E(_SP.b),_ST=E(_SS.a);if(_SL>=_ST){if(_SL!=_ST){_SM=_;_SO=_SR;continue;}else{var _SU=E(_SN),_SV=E(_SS.b);if(_SU>=_SV){if(_SU!=_SV){return new F(function(){return _Sz(_SL,_,_SU,_SR);});}else{return new T1(1,_SP.c);}}else{return new F(function(){return _Sz(_SL,_,_SU,_SQ);});}}}else{_SM=_;_SO=_SQ;continue;}}else{return __Z;}}},_SW=function(_SX,_SY){var _SZ=E(_SY);switch(_SZ._){case 0:var _T0=B(_QO(E(_SZ.a),_SX));if(!_T0._){return E(_Qx);}else{var _T1=E(E(_T0.a).b);return (_T1._==0)?E(_T1.a):E(_Qx);}break;case 1:return B(_SW(_SX,_SZ.a))+B(_SW(_SX,_SZ.b))|0;default:return E(_SZ.a);}},_T2=function(_T3,_T4,_T5){var _T6=E(_T5);if(!_T6._){var _T7=_T6.d,_T8=_T6.e,_T9=E(_T6.b),_Ta=E(_T3),_Tb=E(_T9.a);if(_Ta>=_Tb){if(_Ta!=_Tb){return new F(function(){return _Oy(_Ta,_,_T4,_T8);});}else{var _Tc=E(_T4),_Td=E(_T9.b);if(_Tc>=_Td){if(_Tc!=_Td){return new F(function(){return _On(_Ta,_,_Tc,_T8);});}else{return true;}}else{return new F(function(){return _On(_Ta,_,_Tc,_T7);});}}}else{return new F(function(){return _Oy(_Ta,_,_T4,_T7);});}}else{return false;}},_Te=function(_Tf,_Tg,_Th){while(1){var _Ti=E(_Tg);switch(_Ti._){case 0:return (E(_Ti.a)>E(E(_Th).b))?true:false;case 1:if(!B(_Te(_Tf,_Ti.a,_Th))){return false;}else{_Tg=_Ti.b;continue;}break;case 2:if(!B(_Te(_Tf,_Ti.a,_Th))){_Tg=_Ti.b;continue;}else{return true;}break;case 3:return (!B(_Te(_Tf,_Ti.a,_Th)))?true:false;case 4:var _Tj=_Ti.b,_Tk=_Ti.c,_Tl=E(E(_Tf).b);if(!_Tl._){var _Tm=_Tl.d,_Tn=_Tl.e,_To=E(_Tl.b),_Tp=E(_Ti.a),_Tq=E(_To.a);if(_Tp>=_Tq){if(_Tp!=_Tq){var _Tr=B(_SK(_Tp,_,_Tj,_Tn));if(!_Tr._){return false;}else{return new F(function(){return _GT(_Tr.a,_Tk);});}}else{var _Ts=E(_Tj),_Tt=E(_To.b);if(_Ts>=_Tt){if(_Ts!=_Tt){var _Tu=B(_Sz(_Tp,_,_Ts,_Tn));if(!_Tu._){return false;}else{return new F(function(){return _GT(_Tu.a,_Tk);});}}else{return new F(function(){return _GT(_Tl.c,_Tk);});}}else{var _Tv=B(_Sz(_Tp,_,_Ts,_Tm));if(!_Tv._){return false;}else{return new F(function(){return _GT(_Tv.a,_Tk);});}}}}else{var _Tw=B(_SK(_Tp,_,_Tj,_Tm));if(!_Tw._){return false;}else{return new F(function(){return _GT(_Tw.a,_Tk);});}}}else{return false;}break;case 5:return new F(function(){return _T2(_Ti.a,_Ti.b,E(_Tf).b);});break;case 6:var _Tx=E(_Tf).a;return B(_SW(_Tx,_Ti.a))>=B(_SW(_Tx,_Ti.b));case 7:return true;default:return false;}}},_Ty=function(_Tz,_TA,_TB,_TC){var _TD=E(_TB);switch(_TD._){case 0:return new T3(0,_TA,_QT,_1M);case 1:var _TE=_TD.a,_TF=_TD.b,_TG=_TD.c,_TH=_TD.g,_TI=E(_TD.e),_TJ=E(E(_TC).b),_TK=_TI<=_TJ,_TL=new T(function(){return E(_TD.d)<=_TJ;}),_TM=new T(function(){return B(_E2(E(_TE),new T2(0,_TF,new T(function(){if(!E(_TK)){if(!E(_TL)){return new T2(0,_TG,_TI);}else{return new T0(1);}}else{return new T0(1);}})),E(_TA).a));});return (!E(_TK))?(!E(_TL))?(!B(_Qd(_TE,_TF,_TG,_TI,E(_Tz).a)))?new T3(0,_TA,_TD,_1M):new T3(0,new T(function(){return new T2(0,_TM,E(_TA).b);}),_TD.f,new T2(1,new T3(3,_TE,_TF,_TG),_1M)):new T3(0,new T(function(){return new T2(0,_TM,E(_TA).b);}),_TH,_1M):new T3(0,new T(function(){return new T2(0,_TM,E(_TA).b);}),_TH,_1M);case 2:var _TN=_TD.b,_TO=E(_TA),_TP=_TO.a,_TQ=E(_TD.a),_TR=B(_QO(_TQ,_TP));if(!_TR._){return new T3(0,_TO,_TD,_1M);}else{var _TS=E(_TR.a),_TT=_TS.a,_TU=E(_TS.b);if(!_TU._){var _TV=_TU.a;return (!B(_Ki(_TQ,_,_TT,_TV,E(_Tz).b)))?new T3(0,_TO,_TD,_1M):new T3(0,new T2(0,new T(function(){return B(_E2(_TQ,new T2(0,_TT,_Mt),_TP));}),_TO.b),_TN,new T2(1,new T3(4,_TQ,_TT,_TV),_1M));}else{return new T3(0,_TO,_TN,new T2(1,new T2(6,_TQ,_TT),_1M));}}break;case 3:var _TW=_TD.a,_TX=_TD.b,_TY=_TD.c,_TZ=_TD.d,_U0=_TD.f,_U1=E(E(_TC).b);if(E(_TD.e)>_U1){var _U2=function(_U3){var _U4=E(_TZ);if(E(_U3)!=_U4){return new T3(0,_TA,_TD,_1M);}else{var _U5=E(_TA),_U6=_U5.a;if(B(_Qy(_U6,_TX,_U1))<_U4){return new T3(0,_U5,_U0,new T2(1,new T4(2,_TW,_TX,_TY,_U4),_1M));}else{var _U7=new T(function(){return B(_Sr(function(_U8){var _U9=E(_U8),_Ua=E(_U9.b);return (_Ua._==0)?(E(_U9.a)!=E(_TX))?false:(E(_Ua.b)>_U1)?true:false:false;},_U4,_U6));});return new T3(0,new T2(0,_U7,_U5.b),_U0,new T2(1,new T4(0,_TW,_TX,_TY,_U4),_1M));}}},_Ub=E(E(_Tz).c);if(!_Ub._){var _Uc=_Ub.d,_Ud=_Ub.e,_Ue=E(_Ub.b),_Uf=E(_TW),_Ug=E(_Ue.a);if(_Uf>=_Ug){if(_Uf!=_Ug){var _Uh=B(_Q1(_Uf,_,_TY,_Ud));if(!_Uh._){return new T3(0,_TA,_TD,_1M);}else{return new F(function(){return _U2(_Uh.a);});}}else{var _Ui=E(_TY),_Uj=E(_Ue.b);if(_Ui>=_Uj){if(_Ui!=_Uj){var _Uk=B(_PQ(_Uf,_,_Ui,_Ud));if(!_Uk._){return new T3(0,_TA,_TD,_1M);}else{return new F(function(){return _U2(_Uk.a);});}}else{return new F(function(){return _U2(_Ub.c);});}}else{var _Ul=B(_PQ(_Uf,_,_Ui,_Uc));if(!_Ul._){return new T3(0,_TA,_TD,_1M);}else{return new F(function(){return _U2(_Ul.a);});}}}}else{var _Um=B(_Q1(_Uf,_,_TY,_Uc));if(!_Um._){return new T3(0,_TA,_TD,_1M);}else{return new F(function(){return _U2(_Um.a);});}}}else{return new T3(0,_TA,_TD,_1M);}}else{return new T3(0,_TA,_U0,new T2(1,new T4(1,_TW,_TX,_TY,_TZ),_1M));}break;case 4:var _Un=new T(function(){var _Uo=B(_Ty(_Tz,_TA,_TD.a,_TC));return new T3(0,_Uo.a,_Uo.b,_Uo.c);}),_Up=new T(function(){var _Uq=B(_Ty(_Tz,new T(function(){return E(E(_Un).a);}),_TD.b,_TC));return new T3(0,_Uq.a,_Uq.b,_Uq.c);}),_Ur=new T(function(){return B(_hq(E(_Un).c,new T(function(){return E(E(_Up).c);},1)));}),_Us=new T(function(){var _Ut=E(_Un).b,_Uu=E(_Up).b,_Uv=function(_Uw){var _Ux=E(_Uu);switch(_Ux._){case 0:return E(_Ut);case 1:return new T2(4,_Ut,_Ux);case 2:return new T2(4,_Ut,_Ux);case 3:return new T2(4,_Ut,_Ux);case 4:return new T2(4,_Ut,_Ux);case 5:return new T2(4,_Ut,_Ux);default:return new T2(4,_Ut,_Ux);}};switch(E(_Ut)._){case 0:return E(_Uu);break;case 1:return B(_Uv(_));break;case 2:return B(_Uv(_));break;case 3:return B(_Uv(_));break;case 4:return B(_Uv(_));break;case 5:return B(_Uv(_));break;default:return B(_Uv(_));}});return new T3(0,new T(function(){return E(E(_Up).a);}),_Us,_Ur);case 5:return (!B(_Te(_TA,_TD.a,_TC)))?new T3(0,_TA,_TD.c,_1M):new T3(0,_TA,_TD.b,_1M);default:var _Uy=E(_TC);return (E(_TD.b)>E(_Uy.b))?(!B(_Te(_TA,_TD.a,_Uy)))?new T3(0,_TA,_TD,_1M):new T3(0,_TA,_TD.c,_1M):new T3(0,_TA,_TD.d,_1M);}},_Uz=function(_UA,_UB,_UC,_UD){var _UE=new T(function(){var _UF=B(_Oa(_UA,new T(function(){return E(E(_UB).a);},1),_UD));return new T2(0,_UF.a,_UF.b);}),_UG=new T(function(){var _UH=B(_Pp(new T(function(){return E(E(_UB).b);}),_1M,E(_UA).d));return new T2(0,_UH.a,_UH.b);}),_UI=new T(function(){var _UJ=new T(function(){var _UK=E(_UB);return new T2(0,new T(function(){return E(E(_UE).a);}),new T(function(){return E(E(_UG).a);}));}),_UL=B(_Ty(_UA,_UJ,_UC,_UD));return new T3(0,_UL.a,_UL.b,_UL.c);}),_UM=new T(function(){var _UN=new T(function(){return B(_hq(E(_UE).b,new T(function(){return E(E(_UI).c);},1)));},1);return B(_hq(E(_UG).b,_UN));});return new T3(0,new T(function(){return E(E(_UI).a);}),new T(function(){return E(E(_UI).b);}),_UM);},_UO=function(_UP,_UQ,_UR,_US,_UT,_UU){var _UV=new T2(0,_UQ,_UR),_UW=B(_Uz(_UP,_UV,_US,_UT)),_UX=_UW.b,_UY=_UW.c,_UZ=E(_UW.a),_V0=_UZ.a,_V1=_UZ.b,_V2=function(_V3){return new F(function(){return _UO(_UP,_V0,_V1,_UX,_UT,new T(function(){return B(_hq(_UY,_UU));}));});};if(!B(A2(_Jn,_V0,_UQ))){return new F(function(){return _V2(_);});}else{if(!B(A2(_IT,_V1,_UR))){return new F(function(){return _V2(_);});}else{if(!B(_Hu(_UX,_US))){return new F(function(){return _V2(_);});}else{if(!B(_IA(_Hb,_UY,_1M))){return new F(function(){return _V2(_);});}else{return new T3(0,_UV,_US,_UU);}}}}},_V4=function(_V5,_V6){var _V7=E(_V5),_V8=E(_V6);return (E(_V7.a)!=E(_V8.a))?true:(E(_V7.b)!=E(_V8.b))?true:(E(_V7.c)!=E(_V8.c))?true:(E(_V7.d)!=E(_V8.d))?true:false;},_V9=function(_Va,_Vb,_Vc,_Vd,_Ve,_Vf,_Vg,_Vh){if(_Va!=_Ve){return false;}else{if(E(_Vb)!=E(_Vf)){return false;}else{if(E(_Vc)!=E(_Vg)){return false;}else{return new F(function(){return _GT(_Vd,_Vh);});}}}},_Vi=function(_Vj,_Vk){var _Vl=E(_Vj),_Vm=E(_Vk);return new F(function(){return _V9(E(_Vl.a),_Vl.b,_Vl.c,_Vl.d,E(_Vm.a),_Vm.b,_Vm.c,_Vm.d);});},_Vn=new T2(0,_Vi,_V4),_Vo=function(_Vp,_Vq,_Vr,_Vs,_Vt,_Vu,_Vv,_Vw){if(_Vp>=_Vt){if(_Vp!=_Vt){return false;}else{var _Vx=E(_Vq),_Vy=E(_Vu);if(_Vx>=_Vy){if(_Vx!=_Vy){return false;}else{var _Vz=E(_Vr),_VA=E(_Vv);if(_Vz>=_VA){if(_Vz!=_VA){return false;}else{return new F(function(){return _JN(_Vs,_Vw);});}}else{return true;}}}else{return true;}}}else{return true;}},_VB=function(_VC,_VD){var _VE=E(_VC),_VF=E(_VD);return new F(function(){return _Vo(E(_VE.a),_VE.b,_VE.c,_VE.d,E(_VF.a),_VF.b,_VF.c,_VF.d);});},_VG=function(_VH,_VI,_VJ,_VK,_VL,_VM,_VN,_VO){if(_VH>=_VL){if(_VH!=_VL){return false;}else{var _VP=E(_VI),_VQ=E(_VM);if(_VP>=_VQ){if(_VP!=_VQ){return false;}else{var _VR=E(_VJ),_VS=E(_VN);if(_VR>=_VS){if(_VR!=_VS){return false;}else{return new F(function(){return _JK(_VK,_VO);});}}else{return true;}}}else{return true;}}}else{return true;}},_VT=function(_VU,_VV){var _VW=E(_VU),_VX=E(_VV);return new F(function(){return _VG(E(_VW.a),_VW.b,_VW.c,_VW.d,E(_VX.a),_VX.b,_VX.c,_VX.d);});},_VY=function(_VZ,_W0,_W1,_W2,_W3,_W4,_W5,_W6){if(_VZ>=_W3){if(_VZ!=_W3){return true;}else{var _W7=E(_W0),_W8=E(_W4);if(_W7>=_W8){if(_W7!=_W8){return true;}else{var _W9=E(_W1),_Wa=E(_W5);if(_W9>=_Wa){if(_W9!=_Wa){return true;}else{return new F(function(){return _JH(_W2,_W6);});}}else{return false;}}}else{return false;}}}else{return false;}},_Wb=function(_Wc,_Wd){var _We=E(_Wc),_Wf=E(_Wd);return new F(function(){return _VY(E(_We.a),_We.b,_We.c,_We.d,E(_Wf.a),_Wf.b,_Wf.c,_Wf.d);});},_Wg=function(_Wh,_Wi,_Wj,_Wk,_Wl,_Wm,_Wn,_Wo){if(_Wh>=_Wl){if(_Wh!=_Wl){return true;}else{var _Wp=E(_Wi),_Wq=E(_Wm);if(_Wp>=_Wq){if(_Wp!=_Wq){return true;}else{var _Wr=E(_Wj),_Ws=E(_Wn);if(_Wr>=_Ws){if(_Wr!=_Ws){return true;}else{return new F(function(){return _JE(_Wk,_Wo);});}}else{return false;}}}else{return false;}}}else{return false;}},_Wt=function(_Wu,_Wv){var _Ww=E(_Wu),_Wx=E(_Wv);return new F(function(){return _Wg(E(_Ww.a),_Ww.b,_Ww.c,_Ww.d,E(_Wx.a),_Wx.b,_Wx.c,_Wx.d);});},_Wy=function(_Wz,_WA,_WB,_WC,_WD,_WE,_WF,_WG){if(_Wz>=_WD){if(_Wz!=_WD){return 2;}else{var _WH=E(_WA),_WI=E(_WE);if(_WH>=_WI){if(_WH!=_WI){return 2;}else{var _WJ=E(_WB),_WK=E(_WF);if(_WJ>=_WK){if(_WJ!=_WK){return 2;}else{return new F(function(){return _JB(_WC,_WG);});}}else{return 0;}}}else{return 0;}}}else{return 0;}},_WL=function(_WM,_WN){var _WO=E(_WM),_WP=E(_WN);return new F(function(){return _Wy(E(_WO.a),_WO.b,_WO.c,_WO.d,E(_WP.a),_WP.b,_WP.c,_WP.d);});},_WQ=function(_WR,_WS){var _WT=E(_WR),_WU=E(_WT.a),_WV=E(_WS),_WW=E(_WV.a);if(_WU>=_WW){if(_WU!=_WW){return E(_WT);}else{var _WX=E(_WT.b),_WY=E(_WV.b);if(_WX>=_WY){if(_WX!=_WY){return E(_WT);}else{var _WZ=E(_WT.c),_X0=E(_WV.c);return (_WZ>=_X0)?(_WZ!=_X0)?E(_WT):(E(_WT.d)>E(_WV.d))?E(_WT):E(_WV):E(_WV);}}else{return E(_WV);}}}else{return E(_WV);}},_X1=function(_X2,_X3){var _X4=E(_X2),_X5=E(_X4.a),_X6=E(_X3),_X7=E(_X6.a);if(_X5>=_X7){if(_X5!=_X7){return E(_X6);}else{var _X8=E(_X4.b),_X9=E(_X6.b);if(_X8>=_X9){if(_X8!=_X9){return E(_X6);}else{var _Xa=E(_X4.c),_Xb=E(_X6.c);return (_Xa>=_Xb)?(_Xa!=_Xb)?E(_X6):(E(_X4.d)>E(_X6.d))?E(_X6):E(_X4):E(_X4);}}else{return E(_X4);}}}else{return E(_X4);}},_Xc={_:0,a:_Vn,b:_WL,c:_VB,d:_VT,e:_Wb,f:_Wt,g:_WQ,h:_X1},_Xd=function(_Xe,_Xf,_Xg,_Xh){if(_Xe>=_Xg){if(_Xe!=_Xg){return 2;}else{return new F(function(){return _JB(_Xf,_Xh);});}}else{return 0;}},_Xi=function(_Xj,_Xk){var _Xl=E(_Xj),_Xm=E(_Xk);return new F(function(){return _Xd(E(_Xl.a),_Xl.b,E(_Xm.a),_Xm.b);});},_Xn=function(_Xo,_Xp,_Xq,_Xr){if(_Xo>=_Xq){if(_Xo!=_Xq){return false;}else{return new F(function(){return _JN(_Xp,_Xr);});}}else{return true;}},_Xs=function(_Xt,_Xu){var _Xv=E(_Xt),_Xw=E(_Xu);return new F(function(){return _Xn(E(_Xv.a),_Xv.b,E(_Xw.a),_Xw.b);});},_Xx=function(_Xy,_Xz,_XA,_XB){if(_Xy>=_XA){if(_Xy!=_XA){return false;}else{return new F(function(){return _JK(_Xz,_XB);});}}else{return true;}},_XC=function(_XD,_XE){var _XF=E(_XD),_XG=E(_XE);return new F(function(){return _Xx(E(_XF.a),_XF.b,E(_XG.a),_XG.b);});},_XH=function(_XI,_XJ,_XK,_XL){if(_XI>=_XK){if(_XI!=_XK){return true;}else{return new F(function(){return _JH(_XJ,_XL);});}}else{return false;}},_XM=function(_XN,_XO){var _XP=E(_XN),_XQ=E(_XO);return new F(function(){return _XH(E(_XP.a),_XP.b,E(_XQ.a),_XQ.b);});},_XR=function(_XS,_XT,_XU,_XV){if(_XS>=_XU){if(_XS!=_XU){return true;}else{return new F(function(){return _JE(_XT,_XV);});}}else{return false;}},_XW=function(_XX,_XY){var _XZ=E(_XX),_Y0=E(_XY);return new F(function(){return _XR(E(_XZ.a),_XZ.b,E(_Y0.a),_Y0.b);});},_Y1=function(_Y2,_Y3){var _Y4=E(_Y2),_Y5=_Y4.b,_Y6=E(_Y4.a),_Y7=E(_Y3),_Y8=_Y7.b,_Y9=E(_Y7.a);if(_Y6>=_Y9){if(_Y6!=_Y9){return new T2(0,_Y6,_Y5);}else{var _Ya=E(_Y5),_Yb=E(_Y8);return (_Ya>_Yb)?new T2(0,_Y6,_Ya):new T2(0,_Y9,_Yb);}}else{return new T2(0,_Y9,_Y8);}},_Yc=function(_Yd,_Ye){var _Yf=E(_Yd),_Yg=_Yf.b,_Yh=E(_Yf.a),_Yi=E(_Ye),_Yj=_Yi.b,_Yk=E(_Yi.a);if(_Yh>=_Yk){if(_Yh!=_Yk){return new T2(0,_Yk,_Yj);}else{var _Yl=E(_Yg),_Ym=E(_Yj);return (_Yl>_Ym)?new T2(0,_Yk,_Ym):new T2(0,_Yh,_Yl);}}else{return new T2(0,_Yh,_Yg);}},_Yn={_:0,a:_HY,b:_Xi,c:_Xs,d:_XC,e:_XM,f:_XW,g:_Y1,h:_Yc},_Yo=function(_Yp,_Yq,_Yr,_Ys){if(_Yp!=_Yr){return false;}else{return new F(function(){return _GT(_Yq,_Ys);});}},_Yt=function(_Yu,_Yv){var _Yw=E(_Yu),_Yx=E(_Yv);return new F(function(){return _Yo(E(_Yw.a),_Yw.b,E(_Yx.a),_Yx.b);});},_Yy=function(_Yz,_YA,_YB,_YC){return (_Yz!=_YB)?true:(E(_YA)!=E(_YC))?true:false;},_YD=function(_YE,_YF){var _YG=E(_YE),_YH=E(_YF);return new F(function(){return _Yy(E(_YG.a),_YG.b,E(_YH.a),_YH.b);});},_YI=new T2(0,_Yt,_YD),_YJ=function(_YK,_YL,_YM,_YN){if(_YK>=_YM){if(_YK!=_YM){return 2;}else{return new F(function(){return _JB(_YL,_YN);});}}else{return 0;}},_YO=function(_YP,_YQ){var _YR=E(_YP),_YS=E(_YQ);return new F(function(){return _YJ(E(_YR.a),_YR.b,E(_YS.a),_YS.b);});},_YT=function(_YU,_YV,_YW,_YX){if(_YU>=_YW){if(_YU!=_YW){return false;}else{return new F(function(){return _JN(_YV,_YX);});}}else{return true;}},_YY=function(_YZ,_Z0){var _Z1=E(_YZ),_Z2=E(_Z0);return new F(function(){return _YT(E(_Z1.a),_Z1.b,E(_Z2.a),_Z2.b);});},_Z3=function(_Z4,_Z5,_Z6,_Z7){if(_Z4>=_Z6){if(_Z4!=_Z6){return false;}else{return new F(function(){return _JK(_Z5,_Z7);});}}else{return true;}},_Z8=function(_Z9,_Za){var _Zb=E(_Z9),_Zc=E(_Za);return new F(function(){return _Z3(E(_Zb.a),_Zb.b,E(_Zc.a),_Zc.b);});},_Zd=function(_Ze,_Zf,_Zg,_Zh){if(_Ze>=_Zg){if(_Ze!=_Zg){return true;}else{return new F(function(){return _JH(_Zf,_Zh);});}}else{return false;}},_Zi=function(_Zj,_Zk){var _Zl=E(_Zj),_Zm=E(_Zk);return new F(function(){return _Zd(E(_Zl.a),_Zl.b,E(_Zm.a),_Zm.b);});},_Zn=function(_Zo,_Zp,_Zq,_Zr){if(_Zo>=_Zq){if(_Zo!=_Zq){return true;}else{return new F(function(){return _JE(_Zp,_Zr);});}}else{return false;}},_Zs=function(_Zt,_Zu){var _Zv=E(_Zt),_Zw=E(_Zu);return new F(function(){return _Zn(E(_Zv.a),_Zv.b,E(_Zw.a),_Zw.b);});},_Zx=function(_Zy,_Zz){var _ZA=E(_Zy),_ZB=_ZA.b,_ZC=E(_ZA.a),_ZD=E(_Zz),_ZE=_ZD.b,_ZF=E(_ZD.a);if(_ZC>=_ZF){if(_ZC!=_ZF){return new T2(0,_ZC,_ZB);}else{var _ZG=E(_ZB),_ZH=E(_ZE);return (_ZG>_ZH)?new T2(0,_ZC,_ZG):new T2(0,_ZF,_ZH);}}else{return new T2(0,_ZF,_ZE);}},_ZI=function(_ZJ,_ZK){var _ZL=E(_ZJ),_ZM=_ZL.b,_ZN=E(_ZL.a),_ZO=E(_ZK),_ZP=_ZO.b,_ZQ=E(_ZO.a);if(_ZN>=_ZQ){if(_ZN!=_ZQ){return new T2(0,_ZQ,_ZP);}else{var _ZR=E(_ZM),_ZS=E(_ZP);return (_ZR>_ZS)?new T2(0,_ZQ,_ZS):new T2(0,_ZN,_ZR);}}else{return new T2(0,_ZN,_ZM);}},_ZT={_:0,a:_YI,b:_YO,c:_YY,d:_Z8,e:_Zi,f:_Zs,g:_Zx,h:_ZI},_ZU=function(_ZV,_ZW){var _ZX=E(_ZV),_ZY=E(_ZW);return (E(_ZX.a)!=E(_ZY.a))?true:(E(_ZX.b)!=E(_ZY.b))?true:(E(_ZX.c)!=E(_ZY.c))?true:false;},_ZZ=function(_100,_101,_102,_103,_104,_105){if(_100!=_103){return false;}else{if(E(_101)!=E(_104)){return false;}else{return new F(function(){return _GT(_102,_105);});}}},_106=function(_107,_108){var _109=E(_107),_10a=E(_108);return new F(function(){return _ZZ(E(_109.a),_109.b,_109.c,E(_10a.a),_10a.b,_10a.c);});},_10b=new T2(0,_106,_ZU),_10c=function(_10d,_10e,_10f,_10g,_10h,_10i){if(_10d>=_10g){if(_10d!=_10g){return false;}else{var _10j=E(_10e),_10k=E(_10h);if(_10j>=_10k){if(_10j!=_10k){return false;}else{return new F(function(){return _JN(_10f,_10i);});}}else{return true;}}}else{return true;}},_10l=function(_10m,_10n){var _10o=E(_10m),_10p=E(_10n);return new F(function(){return _10c(E(_10o.a),_10o.b,_10o.c,E(_10p.a),_10p.b,_10p.c);});},_10q=function(_10r,_10s,_10t,_10u,_10v,_10w){if(_10r>=_10u){if(_10r!=_10u){return false;}else{var _10x=E(_10s),_10y=E(_10v);if(_10x>=_10y){if(_10x!=_10y){return false;}else{return new F(function(){return _JK(_10t,_10w);});}}else{return true;}}}else{return true;}},_10z=function(_10A,_10B){var _10C=E(_10A),_10D=E(_10B);return new F(function(){return _10q(E(_10C.a),_10C.b,_10C.c,E(_10D.a),_10D.b,_10D.c);});},_10E=function(_10F,_10G,_10H,_10I,_10J,_10K){if(_10F>=_10I){if(_10F!=_10I){return true;}else{var _10L=E(_10G),_10M=E(_10J);if(_10L>=_10M){if(_10L!=_10M){return true;}else{return new F(function(){return _JH(_10H,_10K);});}}else{return false;}}}else{return false;}},_10N=function(_10O,_10P){var _10Q=E(_10O),_10R=E(_10P);return new F(function(){return _10E(E(_10Q.a),_10Q.b,_10Q.c,E(_10R.a),_10R.b,_10R.c);});},_10S=function(_10T,_10U,_10V,_10W,_10X,_10Y){if(_10T>=_10W){if(_10T!=_10W){return true;}else{var _10Z=E(_10U),_110=E(_10X);if(_10Z>=_110){if(_10Z!=_110){return true;}else{return new F(function(){return _JE(_10V,_10Y);});}}else{return false;}}}else{return false;}},_111=function(_112,_113){var _114=E(_112),_115=E(_113);return new F(function(){return _10S(E(_114.a),_114.b,_114.c,E(_115.a),_115.b,_115.c);});},_116=function(_117,_118,_119,_11a,_11b,_11c){if(_117>=_11a){if(_117!=_11a){return 2;}else{var _11d=E(_118),_11e=E(_11b);if(_11d>=_11e){if(_11d!=_11e){return 2;}else{return new F(function(){return _JB(_119,_11c);});}}else{return 0;}}}else{return 0;}},_11f=function(_11g,_11h){var _11i=E(_11g),_11j=E(_11h);return new F(function(){return _116(E(_11i.a),_11i.b,_11i.c,E(_11j.a),_11j.b,_11j.c);});},_11k=function(_11l,_11m){var _11n=E(_11l),_11o=E(_11n.a),_11p=E(_11m),_11q=E(_11p.a);if(_11o>=_11q){if(_11o!=_11q){return E(_11n);}else{var _11r=E(_11n.b),_11s=E(_11p.b);return (_11r>=_11s)?(_11r!=_11s)?E(_11n):(E(_11n.c)>E(_11p.c))?E(_11n):E(_11p):E(_11p);}}else{return E(_11p);}},_11t=function(_11u,_11v){var _11w=E(_11u),_11x=E(_11w.a),_11y=E(_11v),_11z=E(_11y.a);if(_11x>=_11z){if(_11x!=_11z){return E(_11y);}else{var _11A=E(_11w.b),_11B=E(_11y.b);return (_11A>=_11B)?(_11A!=_11B)?E(_11y):(E(_11w.c)>E(_11y.c))?E(_11y):E(_11w):E(_11w);}}else{return E(_11w);}},_11C={_:0,a:_10b,b:_11f,c:_10l,d:_10z,e:_10N,f:_111,g:_11k,h:_11t},_11D=__Z,_11E=function(_11F,_11G,_11H){var _11I=E(_11G);if(!_11I._){return E(_11H);}else{var _11J=function(_11K,_11L){while(1){var _11M=E(_11L);if(!_11M._){var _11N=_11M.b,_11O=_11M.d;switch(B(A3(_My,_11F,_11K,_11N))){case 0:return new F(function(){return _2x(_11N,B(_11J(_11K,_11M.c)),_11O);});break;case 1:return E(_11O);default:_11L=_11O;continue;}}else{return new T0(1);}}};return new F(function(){return _11J(_11I.a,_11H);});}},_11P=function(_11Q,_11R,_11S){var _11T=E(_11R);if(!_11T._){return E(_11S);}else{var _11U=function(_11V,_11W){while(1){var _11X=E(_11W);if(!_11X._){var _11Y=_11X.b,_11Z=_11X.c;switch(B(A3(_My,_11Q,_11Y,_11V))){case 0:return new F(function(){return _2x(_11Y,_11Z,B(_11U(_11V,_11X.d)));});break;case 1:return E(_11Z);default:_11W=_11Z;continue;}}else{return new T0(1);}}};return new F(function(){return _11U(_11T.a,_11S);});}},_120=function(_121,_122,_123){var _124=E(_122),_125=E(_123);if(!_125._){var _126=_125.b,_127=_125.c,_128=_125.d;switch(B(A3(_My,_121,_124,_126))){case 0:return new F(function(){return _5(_126,B(_120(_121,_124,_127)),_128);});break;case 1:return E(_125);default:return new F(function(){return _H(_126,_127,B(_120(_121,_124,_128)));});}}else{return new T4(0,1,E(_124),E(_0),E(_0));}},_129=function(_12a,_12b,_12c){return new F(function(){return _120(_12a,_12b,_12c);});},_12d=function(_12e,_12f,_12g,_12h){var _12i=E(_12f);if(!_12i._){var _12j=E(_12g);if(!_12j._){return E(_12h);}else{var _12k=function(_12l,_12m){while(1){var _12n=E(_12m);if(!_12n._){if(!B(A3(_Ne,_12e,_12n.b,_12l))){return E(_12n);}else{_12m=_12n.c;continue;}}else{return new T0(1);}}};return new F(function(){return _12k(_12j.a,_12h);});}}else{var _12o=_12i.a,_12p=E(_12g);if(!_12p._){var _12q=function(_12r,_12s){while(1){var _12t=E(_12s);if(!_12t._){if(!B(A3(_Nc,_12e,_12t.b,_12r))){return E(_12t);}else{_12s=_12t.d;continue;}}else{return new T0(1);}}};return new F(function(){return _12q(_12o,_12h);});}else{var _12u=function(_12v,_12w,_12x){while(1){var _12y=E(_12x);if(!_12y._){var _12z=_12y.b;if(!B(A3(_Nc,_12e,_12z,_12v))){if(!B(A3(_Ne,_12e,_12z,_12w))){return E(_12y);}else{_12x=_12y.c;continue;}}else{_12x=_12y.d;continue;}}else{return new T0(1);}}};return new F(function(){return _12u(_12o,_12p.a,_12h);});}}},_12A=function(_12B,_12C,_12D,_12E,_12F){var _12G=E(_12F);if(!_12G._){var _12H=_12G.b,_12I=_12G.c,_12J=_12G.d,_12K=E(_12E);if(!_12K._){var _12L=_12K.b,_12M=function(_12N){var _12O=new T1(1,E(_12L));return new F(function(){return _2x(_12L,B(_12A(_12B,_12C,_12O,_12K.c,B(_12d(_12B,_12C,_12O,_12G)))),B(_12A(_12B,_12O,_12D,_12K.d,B(_12d(_12B,_12O,_12D,_12G)))));});};if(!E(_12I)._){return new F(function(){return _12M(_);});}else{if(!E(_12J)._){return new F(function(){return _12M(_);});}else{return new F(function(){return _129(_12B,_12H,_12K);});}}}else{return new F(function(){return _2x(_12H,B(_11E(_12B,_12C,_12I)),B(_11P(_12B,_12D,_12J)));});}}else{return E(_12E);}},_12P=function(_12Q,_12R,_12S,_12T,_12U,_12V,_12W,_12X,_12Y,_12Z,_130){var _131=function(_132){var _133=new T1(1,E(_12U));return new F(function(){return _2x(_12U,B(_12A(_12Q,_12R,_133,_12V,B(_12d(_12Q,_12R,_133,new T4(0,_12X,E(_12Y),E(_12Z),E(_130)))))),B(_12A(_12Q,_133,_12S,_12W,B(_12d(_12Q,_133,_12S,new T4(0,_12X,E(_12Y),E(_12Z),E(_130)))))));});};if(!E(_12Z)._){return new F(function(){return _131(_);});}else{if(!E(_130)._){return new F(function(){return _131(_);});}else{return new F(function(){return _129(_12Q,_12Y,new T4(0,_12T,E(_12U),E(_12V),E(_12W)));});}}},_134=function(_135,_136,_137,_138,_139,_13a,_13b,_13c){return new T4(0,new T(function(){var _13d=E(_135);if(!_13d._){var _13e=E(_139);if(!_13e._){return B(_12P(_Xc,_11D,_11D,_13d.a,_13d.b,_13d.c,_13d.d,_13e.a,_13e.b,_13e.c,_13e.d));}else{return E(_13d);}}else{return E(_139);}}),new T(function(){var _13f=E(_136);if(!_13f._){var _13g=E(_13a);if(!_13g._){return B(_12P(_11C,_11D,_11D,_13f.a,_13f.b,_13f.c,_13f.d,_13g.a,_13g.b,_13g.c,_13g.d));}else{return E(_13f);}}else{return E(_13a);}}),new T(function(){var _13h=E(_137);if(!_13h._){var _13i=E(_13b);if(!_13i._){return B(_NT(_ZT,_Md,_Md,_13h.a,_13h.b,_13h.c,_13h.d,_13h.e,_13i.a,_13i.b,_13i.c,_13i.d,_13i.e));}else{return E(_13h);}}else{return E(_13b);}}),new T(function(){var _13j=E(_138);if(!_13j._){var _13k=E(_13c);if(!_13k._){return B(_NT(_Yn,_Md,_Md,_13j.a,_13j.b,_13j.c,_13j.d,_13j.e,_13k.a,_13k.b,_13k.c,_13k.d,_13k.e));}else{return E(_13j);}}else{return E(_13c);}}));},_13l=function(_13m,_13n){while(1){var _13o=E(_13n);if(!_13o._){var _13p=E(_13o.b);if(_13m>=_13p){if(_13m!=_13p){_13n=_13o.e;continue;}else{return true;}}else{_13n=_13o.d;continue;}}else{return false;}}},_13q=function(_13r,_13s){while(1){var _13t=E(_13s);if(!_13t._){var _13u=E(_13t.b);if(_13r>=_13u){if(_13r!=_13u){_13s=_13t.e;continue;}else{return new T1(1,_13t.c);}}else{_13s=_13t.d;continue;}}else{return __Z;}}},_13v=function(_13w,_13x){var _13y=E(_13w);switch(_13y._){case 1:var _13z=E(_13y.a);return (!B(_13l(_13z,E(_13x).a)))?new T4(0,new T4(0,1,E(new T4(0,_13z,_13y.b,_13y.c,_13y.e)),E(_0),E(_0)),_0,_8i,_8i):new T4(0,_0,_0,_8i,_8i);case 2:var _13A=E(_13y.a),_13B=B(_13q(_13A,E(_13x).a));if(!_13B._){return new T4(0,_0,_0,_8i,_8i);}else{var _13C=E(_13B.a),_13D=E(_13C.b);return (_13D._==0)?new T4(0,_0,new T4(0,1,E(new T3(0,_13A,_13C.a,_13D.a)),E(_0),E(_0)),_8i,_8i):new T4(0,_0,_0,_8i,_8i);}break;case 3:return new T4(0,_0,_0,new T5(0,1,E(new T2(0,_13y.a,_13y.c)),_13y.d,E(_8i),E(_8i)),_8i);case 4:var _13E=B(_13v(_13y.a,_13x)),_13F=B(_13v(_13y.b,_13x));return new F(function(){return _134(_13E.a,_13E.b,_13E.c,_13E.d,_13F.a,_13F.b,_13F.c,_13F.d);});break;default:return new T4(0,_0,_0,_8i,_8i);}},_13G=function(_13H,_13I){var _13J=new T(function(){var _13K=function(_13L,_13M){while(1){var _13N=B((function(_13O,_13P){var _13Q=E(_13P);if(!_13Q._){var _13R=_13Q.e,_13S=new T(function(){var _13T=E(_13Q.c),_13U=E(_13T.b);if(!_13U._){var _13V=E(E(_13H).b);if(E(_13U.b)>_13V){var _13W=function(_13X,_13Y){while(1){var _13Z=B((function(_140,_141){var _142=E(_141);if(!_142._){var _143=_142.e,_144=new T(function(){var _145=E(_142.c),_146=E(_145.b);if(!_146._){if(E(_146.b)>_13V){return B(_13W(_140,_143));}else{return new T2(1,new T3(0,_142.b,_145.a,_146.a),new T(function(){return B(_13W(_140,_143));}));}}else{return B(_13W(_140,_143));}},1);_13X=_144;_13Y=_142.d;return __continue;}else{return E(_140);}})(_13X,_13Y));if(_13Z!=__continue){return _13Z;}}};return B(_13W(_13O,_13R));}else{var _147=new T(function(){var _148=function(_149,_14a){while(1){var _14b=B((function(_14c,_14d){var _14e=E(_14d);if(!_14e._){var _14f=_14e.e,_14g=new T(function(){var _14h=E(_14e.c),_14i=E(_14h.b);if(!_14i._){if(E(_14i.b)>_13V){return B(_148(_14c,_14f));}else{return new T2(1,new T3(0,_14e.b,_14h.a,_14i.a),new T(function(){return B(_148(_14c,_14f));}));}}else{return B(_148(_14c,_14f));}},1);_149=_14g;_14a=_14e.d;return __continue;}else{return E(_14c);}})(_149,_14a));if(_14b!=__continue){return _14b;}}};return B(_148(_13O,_13R));});return new T2(1,new T3(0,_13Q.b,_13T.a,_13U.a),_147);}}else{return B(_13K(_13O,_13R));}},1);_13L=_13S;_13M=_13Q.d;return __continue;}else{return E(_13O);}})(_13L,_13M));if(_13N!=__continue){return _13N;}}};return B(_83(B(_13K(_1M,_13I))));});return new T4(0,_0,_13J,_8i,_8i);},_14j=function(_14k,_14l,_14m,_14n){while(1){var _14o=E(_14n);if(!_14o._){var _14p=_14o.d,_14q=_14o.e,_14r=E(_14o.b),_14s=E(_14r.a);if(_14k>=_14s){if(_14k!=_14s){_14l=_;_14n=_14q;continue;}else{var _14t=E(_14r.b);if(_14m>=_14t){if(_14m!=_14t){_14l=_;_14n=_14q;continue;}else{return true;}}else{_14l=_;_14n=_14p;continue;}}}else{_14l=_;_14n=_14p;continue;}}else{return false;}}},_14u=function(_14v,_14w,_14x,_14y){while(1){var _14z=E(_14y);if(!_14z._){var _14A=_14z.d,_14B=_14z.e,_14C=E(_14z.b),_14D=E(_14C.a);if(_14v>=_14D){if(_14v!=_14D){_14w=_;_14y=_14B;continue;}else{var _14E=E(_14x),_14F=E(_14C.b);if(_14E>=_14F){if(_14E!=_14F){return new F(function(){return _14j(_14v,_,_14E,_14B);});}else{return true;}}else{return new F(function(){return _14j(_14v,_,_14E,_14A);});}}}else{_14w=_;_14y=_14A;continue;}}else{return false;}}},_14G=function(_14H,_14I,_14J,_14K,_14L){while(1){var _14M=E(_14H);if(!_14M._){return new T4(0,_14I,_14J,_14K,_14L);}else{var _14N=E(_14M.a),_14O=B(_134(_14I,_14J,_14K,_14L,_14N.a,_14N.b,_14N.c,_14N.d));_14H=_14M.b;_14I=_14O.a;_14J=_14O.b;_14K=_14O.c;_14L=_14O.d;continue;}}},_14P=function(_14Q,_14R,_14S,_14T,_14U){while(1){var _14V=E(_14Q);if(!_14V._){return new T4(0,_14R,_14S,_14T,_14U);}else{var _14W=E(_14V.a),_14X=B(_134(_14R,_14S,_14T,_14U,_14W.a,_14W.b,_14W.c,_14W.d));_14Q=_14V.b;_14R=_14X.a;_14S=_14X.b;_14T=_14X.c;_14U=_14X.d;continue;}}},_14Y=function(_14Z,_150){var _151=B(_152(_14Z,_150));return new T4(0,_151.a,_151.b,_151.c,_151.d);},_153=0,_152=function(_154,_155){while(1){var _156=B((function(_157,_158){var _159=E(_158);switch(_159._){case 1:var _15a=B(_152(_157,_159.a));return new F(function(){return _14P(new T2(1,new T(function(){return B(_14Y(_157,_159.b));}),_1M),_15a.a,_15a.b,_15a.c,_15a.d);});break;case 2:var _15b=B(_152(_157,_159.a));return new F(function(){return _14G(new T2(1,new T(function(){return B(_14Y(_157,_159.b));}),_1M),_15b.a,_15b.b,_15b.c,_15b.d);});break;case 3:var _15c=_157;_154=_15c;_155=_159.a;return __continue;case 4:var _15d=_159.a,_15e=_159.b,_15f=E(E(_157).b);if(!_15f._){var _15g=_15f.d,_15h=_15f.e,_15i=E(_15f.b),_15j=E(_15d),_15k=E(_15i.a);if(_15j>=_15k){if(_15j!=_15k){return (!B(_14u(_15j,_,_15e,_15h)))?new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_15j,_15e)),_153,E(_8i),E(_8i))):new T4(0,_0,_0,_8i,_8i);}else{var _15l=E(_15e),_15m=E(_15i.b);return (_15l>=_15m)?(_15l!=_15m)?(!B(_14j(_15j,_,_15l,_15h)))?new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_15j,_15l)),_153,E(_8i),E(_8i))):new T4(0,_0,_0,_8i,_8i):new T4(0,_0,_0,_8i,_8i):(!B(_14j(_15j,_,_15l,_15g)))?new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_15j,_15l)),_153,E(_8i),E(_8i))):new T4(0,_0,_0,_8i,_8i);}}else{return (!B(_14u(_15j,_,_15e,_15g)))?new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_15j,_15e)),_153,E(_8i),E(_8i))):new T4(0,_0,_0,_8i,_8i);}}else{return new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_15d,_15e)),_153,E(_8i),E(_8i)));}break;case 5:var _15n=_159.a,_15o=_159.b,_15p=E(E(_157).b);if(!_15p._){var _15q=_15p.d,_15r=_15p.e,_15s=E(_15p.b),_15t=E(_15n),_15u=E(_15s.a);if(_15t>=_15u){if(_15t!=_15u){return (!B(_14u(_15t,_,_15o,_15r)))?new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_15t,_15o)),_153,E(_8i),E(_8i))):new T4(0,_0,_0,_8i,_8i);}else{var _15v=E(_15o),_15w=E(_15s.b);return (_15v>=_15w)?(_15v!=_15w)?(!B(_14j(_15t,_,_15v,_15r)))?new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_15t,_15v)),_153,E(_8i),E(_8i))):new T4(0,_0,_0,_8i,_8i):new T4(0,_0,_0,_8i,_8i):(!B(_14j(_15t,_,_15v,_15q)))?new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_15t,_15v)),_153,E(_8i),E(_8i))):new T4(0,_0,_0,_8i,_8i);}}else{return (!B(_14u(_15t,_,_15o,_15q)))?new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_15t,_15o)),_153,E(_8i),E(_8i))):new T4(0,_0,_0,_8i,_8i);}}else{return new T4(0,_0,_0,_8i,new T5(0,1,E(new T2(0,_15n,_15o)),_153,E(_8i),E(_8i)));}break;default:return new T4(0,_0,_0,_8i,_8i);}})(_154,_155));if(_156!=__continue){return _156;}}},_15x=function(_15y,_15z,_15A,_15B,_15C){while(1){var _15D=E(_15y);if(!_15D._){return new T4(0,_15z,_15A,_15B,_15C);}else{var _15E=E(_15D.a),_15F=B(_134(_15z,_15A,_15B,_15C,_15E.a,_15E.b,_15E.c,_15E.d));_15y=_15D.b;_15z=_15F.a;_15A=_15F.b;_15B=_15F.c;_15C=_15F.d;continue;}}},_15G=function(_15H,_15I,_15J,_15K,_15L){while(1){var _15M=E(_15H);if(!_15M._){return new T4(0,_15I,_15J,_15K,_15L);}else{var _15N=E(_15M.a),_15O=B(_134(_15I,_15J,_15K,_15L,_15N.a,_15N.b,_15N.c,_15N.d));_15H=_15M.b;_15I=_15O.a;_15J=_15O.b;_15K=_15O.c;_15L=_15O.d;continue;}}},_15P=function(_15Q,_15R){var _15S=B(_15T(_15Q,_15R));return new T4(0,_15S.a,_15S.b,_15S.c,_15S.d);},_15T=function(_15U,_15V){while(1){var _15W=B((function(_15X,_15Y){var _15Z=E(_15Y);switch(_15Z._){case 0:return new T4(0,_0,_0,_8i,_8i);case 1:var _160=B(_15T(_15X,_15Z.f));return new F(function(){return _15G(new T2(1,new T(function(){return B(_15P(_15X,_15Z.g));}),_1M),_160.a,_160.b,_160.c,_160.d);});break;case 2:var _161=_15X;_15U=_161;_15V=_15Z.b;return __continue;case 3:var _161=_15X;_15U=_161;_15V=_15Z.f;return __continue;case 4:var _162=B(_15T(_15X,_15Z.a));return new F(function(){return _15x(new T2(1,new T(function(){return B(_15P(_15X,_15Z.b));}),_1M),_162.a,_162.b,_162.c,_162.d);});break;case 5:var _163=B(_152(_15X,_15Z.a)),_164=B(_15T(_15X,_15Z.b)),_165=B(_134(_163.a,_163.b,_163.c,_163.d,_164.a,_164.b,_164.c,_164.d)),_166=B(_15T(_15X,_15Z.c));return new F(function(){return _134(_165.a,_165.b,_165.c,_165.d,_166.a,_166.b,_166.c,_166.d);});break;default:var _167=B(_152(_15X,_15Z.a)),_168=B(_15T(_15X,_15Z.c)),_169=B(_134(_167.a,_167.b,_167.c,_167.d,_168.a,_168.b,_168.c,_168.d)),_16a=B(_15T(_15X,_15Z.d));return new F(function(){return _134(_169.a,_169.b,_169.c,_169.d,_16a.a,_16a.b,_16a.c,_16a.d);});}})(_15U,_15V));if(_15W!=__continue){return _15W;}}},_16b=function(_16c,_16d,_16e,_16f,_16g){while(1){var _16h=E(_16c);if(!_16h._){return new T4(0,_16d,_16e,_16f,_16g);}else{var _16i=E(_16h.a),_16j=B(_134(_16d,_16e,_16f,_16g,_16i.a,_16i.b,_16i.c,_16i.d));_16c=_16h.b;_16d=_16j.a;_16e=_16j.b;_16f=_16j.c;_16g=_16j.d;continue;}}},_16k=function(_16l,_16m,_16n,_16o,_16p,_16q){var _16r=E(_16l),_16s=B(_134(_16n,_16o,_16p,_16q,_16r.a,_16r.b,_16r.c,_16r.d));return new F(function(){return _16b(_16m,_16s.a,_16s.b,_16s.c,_16s.d);});},_16t=function(_16u,_16v,_16w,_16x,_16y){var _16z=B(_UO(_16v,_16x,_16y,_16w,_16u,_1M)),_16A=_16z.a,_16B=_16z.b,_16C=B(_13v(_16B,_16A));return new F(function(){return _16k(new T(function(){var _16D=B(_13G(_16u,E(_16A).a));return new T4(0,_16D.a,_16D.b,_16D.c,_16D.d);}),new T2(1,new T(function(){var _16E=B(_15T(_16A,_16B));return new T4(0,_16E.a,_16E.b,_16E.c,_16E.d);}),_1M),_16C.a,_16C.b,_16C.c,_16C.d);});},_16F="(function (t) {return document.getElementById(t).value})",_16G=new T(function(){return eval("(function () {return Blockly.Marlowe.workspaceToCode(demoWorkspace);})");}),_16H=new T(function(){return B(unCStr("contractState"));}),_16I=new T(function(){return B(unCStr("currBlock"));}),_16J=new T(function(){return eval("(function (x) { var node = document.getElementById(x); while (node.hasChildNodes()) { node.removeChild(node.lastChild); } })");}),_16K=new T(function(){return B(err(_ha));}),_16L=new T(function(){return B(err(_jS));}),_16M=new T(function(){return B(A3(_xS,_yl,_xn,_DB));}),_16N=new T(function(){return B(err(_ha));}),_16O=new T(function(){return B(err(_jS));}),_16P=function(_zv){return new F(function(){return _xH(_BM,_zv);});},_16Q=function(_16R,_16S){return new F(function(){return _yv(_16P,_16S);});},_16T=new T(function(){return B(_yv(_16P,_jV));}),_16U=function(_zv){return new F(function(){return _l5(_16T,_zv);});},_16V=function(_16W){var _16X=new T(function(){return B(A3(_xH,_BM,_16W,_jV));});return function(_zc){return new F(function(){return _l5(_16X,_zc);});};},_16Y=new T4(0,_16V,_16U,_16P,_16Q),_16Z=new T(function(){return B(unCStr("NotRedeemed"));}),_170=new T(function(){return B(unCStr("ManuallyRedeemed"));}),_171=function(_172,_173){var _174=new T(function(){var _175=new T(function(){return B(A1(_173,_Mt));});return B(_wQ(function(_176){var _177=E(_176);return (_177._==3)?(!B(_lT(_177.a,_170)))?new T0(2):E(_175):new T0(2);}));}),_178=function(_179){return E(_174);},_17a=new T(function(){if(E(_172)>10){return new T0(2);}else{var _17b=new T(function(){var _17c=new T(function(){var _17d=function(_17e){return new F(function(){return A3(_xS,_yl,_ze,function(_17f){return new F(function(){return A1(_173,new T2(0,_17e,_17f));});});});};return B(A3(_xS,_yl,_ze,_17d));});return B(_wQ(function(_17g){var _17h=E(_17g);return (_17h._==3)?(!B(_lT(_17h.a,_16Z)))?new T0(2):E(_17c):new T0(2);}));}),_17i=function(_17j){return E(_17b);};return new T1(1,function(_17k){return new F(function(){return A2(_vx,_17k,_17i);});});}});return new F(function(){return _lf(new T1(1,function(_17l){return new F(function(){return A2(_vx,_17l,_178);});}),_17a);});},_17m=function(_zv){return new F(function(){return _xH(_171,_zv);});},_17n=function(_17o,_17p){return new F(function(){return _yv(_17m,_17p);});},_17q=new T(function(){return B(_yv(_17m,_jV));}),_17r=function(_zv){return new F(function(){return _l5(_17q,_zv);});},_17s=function(_17t){var _17u=new T(function(){return B(A3(_xH,_171,_17t,_jV));});return function(_zc){return new F(function(){return _l5(_17u,_zc);});};},_17v=new T4(0,_17s,_17r,_17m,_17n),_17w=function(_17x,_17y){return new F(function(){return _A0(_zd,_17v,_17y);});},_17z=new T(function(){return B(_yv(_17w,_jV));}),_17A=function(_zv){return new F(function(){return _l5(_17z,_zv);});},_17B=new T(function(){return B(_A0(_zd,_17v,_jV));}),_17C=function(_zv){return new F(function(){return _l5(_17B,_zv);});},_17D=function(_17E,_zv){return new F(function(){return _17C(_zv);});},_17F=function(_17G,_17H){return new F(function(){return _yv(_17w,_17H);});},_17I=new T4(0,_17D,_17A,_17w,_17F),_17J=function(_17K,_17L){return new F(function(){return _A0(_16Y,_17I,_17L);});},_17M=function(_17N,_17O){return new F(function(){return _yv(_17J,_17O);});},_17P=new T(function(){return B(_yv(_17M,_jV));}),_17Q=function(_Av){return new F(function(){return _l5(_17P,_Av);});},_17R=function(_17S){return new F(function(){return _yv(_17M,_17S);});},_17T=function(_17U,_17V){return new F(function(){return _17R(_17V);});},_17W=new T(function(){return B(_yv(_17J,_jV));}),_17X=function(_Av){return new F(function(){return _l5(_17W,_Av);});},_17Y=function(_17Z,_Av){return new F(function(){return _17X(_Av);});},_180=new T4(0,_17Y,_17Q,_17M,_17T),_181=new T(function(){return B(_A0(_180,_AF,_DB));}),_182=42,_183=new T(function(){return B(unCStr("actions"));}),_184=function(_185){while(1){var _186=B((function(_187){var _188=E(_187);if(!_188._){return __Z;}else{var _189=_188.b,_18a=E(_188.a);if(!E(_18a.b)._){return new T2(1,_18a.a,new T(function(){return B(_184(_189));}));}else{_185=_189;return __continue;}}})(_185));if(_186!=__continue){return _186;}}},_18b=new T(function(){return B(err(_ha));}),_18c=new T(function(){return B(err(_jS));}),_18d=new T(function(){return B(unCStr("ConstMoney"));}),_18e=new T(function(){return B(unCStr("AvailableMoney"));}),_18f=new T(function(){return B(unCStr("AddMoney"));}),_18g=function(_18h,_18i){var _18j=new T(function(){var _18k=new T(function(){if(_18h>10){return new T0(2);}else{var _18l=new T(function(){var _18m=new T(function(){return B(A3(_xS,_yl,_ze,function(_18n){return new F(function(){return A1(_18i,new T1(2,_18n));});}));});return B(_wQ(function(_18o){var _18p=E(_18o);return (_18p._==3)?(!B(_lT(_18p.a,_18d)))?new T0(2):E(_18m):new T0(2);}));}),_18q=function(_18r){return E(_18l);};return new T1(1,function(_18s){return new F(function(){return A2(_vx,_18s,_18q);});});}});if(_18h>10){return B(_lf(_jU,_18k));}else{var _18t=new T(function(){var _18u=new T(function(){var _18v=function(_18w){return new F(function(){return A3(_xH,_18x,_ze,function(_18y){return new F(function(){return A1(_18i,new T2(1,_18w,_18y));});});});};return B(A3(_xH,_18x,_ze,_18v));});return B(_wQ(function(_18z){var _18A=E(_18z);return (_18A._==3)?(!B(_lT(_18A.a,_18f)))?new T0(2):E(_18u):new T0(2);}));}),_18B=function(_18C){return E(_18t);};return B(_lf(new T1(1,function(_18D){return new F(function(){return A2(_vx,_18D,_18B);});}),_18k));}});if(_18h>10){return new F(function(){return _lf(_jU,_18j);});}else{var _18E=new T(function(){var _18F=new T(function(){return B(A3(_xH,_BM,_ze,function(_18G){return new F(function(){return A1(_18i,new T1(0,_18G));});}));});return B(_wQ(function(_18H){var _18I=E(_18H);return (_18I._==3)?(!B(_lT(_18I.a,_18e)))?new T0(2):E(_18F):new T0(2);}));}),_18J=function(_18K){return E(_18E);};return new F(function(){return _lf(new T1(1,function(_18L){return new F(function(){return A2(_vx,_18L,_18J);});}),_18j);});}},_18x=function(_18M,_18N){return new F(function(){return _18g(E(_18M),_18N);});},_18O=new T0(7),_18P=function(_18Q,_18R){return new F(function(){return A1(_18R,_18O);});},_18S=new T(function(){return B(unCStr("TrueObs"));}),_18T=new T2(0,_18S,_18P),_18U=new T0(8),_18V=function(_18W,_18X){return new F(function(){return A1(_18X,_18U);});},_18Y=new T(function(){return B(unCStr("FalseObs"));}),_18Z=new T2(0,_18Y,_18V),_190=new T2(1,_18Z,_1M),_191=new T2(1,_18T,_190),_192=function(_193,_194,_195){var _196=E(_193);if(!_196._){return new T0(2);}else{var _197=E(_196.a),_198=_197.a,_199=new T(function(){return B(A2(_197.b,_194,_195));}),_19a=new T(function(){return B(_wQ(function(_19b){var _19c=E(_19b);switch(_19c._){case 3:return (!B(_lT(_198,_19c.a)))?new T0(2):E(_199);case 4:return (!B(_lT(_198,_19c.a)))?new T0(2):E(_199);default:return new T0(2);}}));}),_19d=function(_19e){return E(_19a);};return new F(function(){return _lf(new T1(1,function(_19f){return new F(function(){return A2(_vx,_19f,_19d);});}),new T(function(){return B(_192(_196.b,_194,_195));}));});}},_19g=new T(function(){return B(unCStr("ValueGE"));}),_19h=new T(function(){return B(unCStr("PersonChoseSomething"));}),_19i=new T(function(){return B(unCStr("PersonChoseThis"));}),_19j=new T(function(){return B(unCStr("BelowTimeout"));}),_19k=new T(function(){return B(unCStr("AndObs"));}),_19l=new T(function(){return B(unCStr("OrObs"));}),_19m=new T(function(){return B(unCStr("NotObs"));}),_19n=function(_19o,_19p){var _19q=new T(function(){var _19r=E(_19o),_19s=new T(function(){var _19t=new T(function(){var _19u=new T(function(){var _19v=new T(function(){var _19w=new T(function(){var _19x=new T(function(){if(_19r>10){return new T0(2);}else{var _19y=new T(function(){var _19z=new T(function(){var _19A=function(_19B){return new F(function(){return A3(_xH,_18x,_ze,function(_19C){return new F(function(){return A1(_19p,new T2(6,_19B,_19C));});});});};return B(A3(_xH,_18x,_ze,_19A));});return B(_wQ(function(_19D){var _19E=E(_19D);return (_19E._==3)?(!B(_lT(_19E.a,_19g)))?new T0(2):E(_19z):new T0(2);}));}),_19F=function(_19G){return E(_19y);};return new T1(1,function(_19H){return new F(function(){return A2(_vx,_19H,_19F);});});}});if(_19r>10){return B(_lf(_jU,_19x));}else{var _19I=new T(function(){var _19J=new T(function(){var _19K=function(_19L){return new F(function(){return A3(_xS,_yl,_ze,function(_19M){return new F(function(){return A1(_19p,new T2(5,_19L,_19M));});});});};return B(A3(_xH,_zr,_ze,_19K));});return B(_wQ(function(_19N){var _19O=E(_19N);return (_19O._==3)?(!B(_lT(_19O.a,_19h)))?new T0(2):E(_19J):new T0(2);}));}),_19P=function(_19Q){return E(_19I);};return B(_lf(new T1(1,function(_19R){return new F(function(){return A2(_vx,_19R,_19P);});}),_19x));}});if(_19r>10){return B(_lf(_jU,_19w));}else{var _19S=new T(function(){var _19T=new T(function(){var _19U=function(_19V){var _19W=function(_19X){return new F(function(){return A3(_xS,_yl,_ze,function(_19Y){return new F(function(){return A1(_19p,new T3(4,_19V,_19X,_19Y));});});});};return new F(function(){return A3(_xS,_yl,_ze,_19W);});};return B(A3(_xH,_zr,_ze,_19U));});return B(_wQ(function(_19Z){var _1a0=E(_19Z);return (_1a0._==3)?(!B(_lT(_1a0.a,_19i)))?new T0(2):E(_19T):new T0(2);}));}),_1a1=function(_1a2){return E(_19S);};return B(_lf(new T1(1,function(_1a3){return new F(function(){return A2(_vx,_1a3,_1a1);});}),_19w));}});if(_19r>10){return B(_lf(_jU,_19v));}else{var _1a4=new T(function(){var _1a5=new T(function(){return B(A3(_xH,_19n,_ze,function(_1a6){return new F(function(){return A1(_19p,new T1(3,_1a6));});}));});return B(_wQ(function(_1a7){var _1a8=E(_1a7);return (_1a8._==3)?(!B(_lT(_1a8.a,_19m)))?new T0(2):E(_1a5):new T0(2);}));}),_1a9=function(_1aa){return E(_1a4);};return B(_lf(new T1(1,function(_1ab){return new F(function(){return A2(_vx,_1ab,_1a9);});}),_19v));}});if(_19r>10){return B(_lf(_jU,_19u));}else{var _1ac=new T(function(){var _1ad=new T(function(){var _1ae=function(_1af){return new F(function(){return A3(_xH,_19n,_ze,function(_1ag){return new F(function(){return A1(_19p,new T2(2,_1af,_1ag));});});});};return B(A3(_xH,_19n,_ze,_1ae));});return B(_wQ(function(_1ah){var _1ai=E(_1ah);return (_1ai._==3)?(!B(_lT(_1ai.a,_19l)))?new T0(2):E(_1ad):new T0(2);}));}),_1aj=function(_1ak){return E(_1ac);};return B(_lf(new T1(1,function(_1al){return new F(function(){return A2(_vx,_1al,_1aj);});}),_19u));}});if(_19r>10){return B(_lf(_jU,_19t));}else{var _1am=new T(function(){var _1an=new T(function(){var _1ao=function(_1ap){return new F(function(){return A3(_xH,_19n,_ze,function(_1aq){return new F(function(){return A1(_19p,new T2(1,_1ap,_1aq));});});});};return B(A3(_xH,_19n,_ze,_1ao));});return B(_wQ(function(_1ar){var _1as=E(_1ar);return (_1as._==3)?(!B(_lT(_1as.a,_19k)))?new T0(2):E(_1an):new T0(2);}));}),_1at=function(_1au){return E(_1am);};return B(_lf(new T1(1,function(_1av){return new F(function(){return A2(_vx,_1av,_1at);});}),_19t));}});if(_19r>10){return B(_lf(_jU,_19s));}else{var _1aw=new T(function(){var _1ax=new T(function(){return B(A3(_xS,_yl,_ze,function(_1ay){return new F(function(){return A1(_19p,new T1(0,_1ay));});}));});return B(_wQ(function(_1az){var _1aA=E(_1az);return (_1aA._==3)?(!B(_lT(_1aA.a,_19j)))?new T0(2):E(_1ax):new T0(2);}));}),_1aB=function(_1aC){return E(_1aw);};return B(_lf(new T1(1,function(_1aD){return new F(function(){return A2(_vx,_1aD,_1aB);});}),_19s));}});return new F(function(){return _lf(B(_192(_191,_19o,_19p)),_19q);});},_1aE=new T(function(){return B(unCStr("Null"));}),_1aF=new T(function(){return B(unCStr("CommitCash"));}),_1aG=new T(function(){return B(unCStr("RedeemCC"));}),_1aH=new T(function(){return B(unCStr("Pay"));}),_1aI=new T(function(){return B(unCStr("Both"));}),_1aJ=new T(function(){return B(unCStr("Choice"));}),_1aK=new T(function(){return B(unCStr("When"));}),_1aL=function(_1aM,_1aN){var _1aO=new T(function(){var _1aP=new T(function(){return B(A1(_1aN,_QT));});return B(_wQ(function(_1aQ){var _1aR=E(_1aQ);return (_1aR._==3)?(!B(_lT(_1aR.a,_1aE)))?new T0(2):E(_1aP):new T0(2);}));}),_1aS=function(_1aT){return E(_1aO);},_1aU=new T(function(){var _1aV=E(_1aM),_1aW=new T(function(){var _1aX=new T(function(){var _1aY=new T(function(){var _1aZ=new T(function(){var _1b0=new T(function(){if(_1aV>10){return new T0(2);}else{var _1b1=new T(function(){var _1b2=new T(function(){var _1b3=function(_1b4){var _1b5=function(_1b6){var _1b7=function(_1b8){return new F(function(){return A3(_xH,_1aL,_ze,function(_1b9){return new F(function(){return A1(_1aN,new T4(6,_1b4,_1b6,_1b8,_1b9));});});});};return new F(function(){return A3(_xH,_1aL,_ze,_1b7);});};return new F(function(){return A3(_xS,_yl,_ze,_1b5);});};return B(A3(_xH,_19n,_ze,_1b3));});return B(_wQ(function(_1ba){var _1bb=E(_1ba);return (_1bb._==3)?(!B(_lT(_1bb.a,_1aK)))?new T0(2):E(_1b2):new T0(2);}));}),_1bc=function(_1bd){return E(_1b1);};return new T1(1,function(_1be){return new F(function(){return A2(_vx,_1be,_1bc);});});}});if(_1aV>10){return B(_lf(_jU,_1b0));}else{var _1bf=new T(function(){var _1bg=new T(function(){var _1bh=function(_1bi){var _1bj=function(_1bk){return new F(function(){return A3(_xH,_1aL,_ze,function(_1bl){return new F(function(){return A1(_1aN,new T3(5,_1bi,_1bk,_1bl));});});});};return new F(function(){return A3(_xH,_1aL,_ze,_1bj);});};return B(A3(_xH,_19n,_ze,_1bh));});return B(_wQ(function(_1bm){var _1bn=E(_1bm);return (_1bn._==3)?(!B(_lT(_1bn.a,_1aJ)))?new T0(2):E(_1bg):new T0(2);}));}),_1bo=function(_1bp){return E(_1bf);};return B(_lf(new T1(1,function(_1bq){return new F(function(){return A2(_vx,_1bq,_1bo);});}),_1b0));}});if(_1aV>10){return B(_lf(_jU,_1aZ));}else{var _1br=new T(function(){var _1bs=new T(function(){var _1bt=function(_1bu){return new F(function(){return A3(_xH,_1aL,_ze,function(_1bv){return new F(function(){return A1(_1aN,new T2(4,_1bu,_1bv));});});});};return B(A3(_xH,_1aL,_ze,_1bt));});return B(_wQ(function(_1bw){var _1bx=E(_1bw);return (_1bx._==3)?(!B(_lT(_1bx.a,_1aI)))?new T0(2):E(_1bs):new T0(2);}));}),_1by=function(_1bz){return E(_1br);};return B(_lf(new T1(1,function(_1bA){return new F(function(){return A2(_vx,_1bA,_1by);});}),_1aZ));}});if(_1aV>10){return B(_lf(_jU,_1aY));}else{var _1bB=new T(function(){var _1bC=new T(function(){var _1bD=function(_1bE){var _1bF=function(_1bG){var _1bH=function(_1bI){var _1bJ=function(_1bK){var _1bL=function(_1bM){return new F(function(){return A3(_xH,_1aL,_ze,function(_1bN){return new F(function(){return A1(_1aN,new T6(3,_1bE,_1bG,_1bI,_1bK,_1bM,_1bN));});});});};return new F(function(){return A3(_xS,_yl,_ze,_1bL);});};return new F(function(){return A3(_xS,_yl,_ze,_1bJ);});};return new F(function(){return A3(_xS,_yl,_ze,_1bH);});};return new F(function(){return A3(_xS,_yl,_ze,_1bF);});};return B(A3(_xH,_AS,_ze,_1bD));});return B(_wQ(function(_1bO){var _1bP=E(_1bO);return (_1bP._==3)?(!B(_lT(_1bP.a,_1aH)))?new T0(2):E(_1bC):new T0(2);}));}),_1bQ=function(_1bR){return E(_1bB);};return B(_lf(new T1(1,function(_1bS){return new F(function(){return A2(_vx,_1bS,_1bQ);});}),_1aY));}});if(_1aV>10){return B(_lf(_jU,_1aX));}else{var _1bT=new T(function(){var _1bU=new T(function(){var _1bV=function(_1bW){return new F(function(){return A3(_xH,_1aL,_ze,function(_1bX){return new F(function(){return A1(_1aN,new T2(2,_1bW,_1bX));});});});};return B(A3(_xH,_BM,_ze,_1bV));});return B(_wQ(function(_1bY){var _1bZ=E(_1bY);return (_1bZ._==3)?(!B(_lT(_1bZ.a,_1aG)))?new T0(2):E(_1bU):new T0(2);}));}),_1c0=function(_1c1){return E(_1bT);};return B(_lf(new T1(1,function(_1c2){return new F(function(){return A2(_vx,_1c2,_1c0);});}),_1aX));}});if(_1aV>10){return B(_lf(_jU,_1aW));}else{var _1c3=new T(function(){var _1c4=new T(function(){var _1c5=function(_1c6){var _1c7=function(_1c8){var _1c9=function(_1ca){var _1cb=function(_1cc){var _1cd=function(_1ce){var _1cf=function(_1cg){return new F(function(){return A3(_xH,_1aL,_ze,function(_1ch){return new F(function(){return A1(_1aN,{_:1,a:_1c6,b:_1c8,c:_1ca,d:_1cc,e:_1ce,f:_1cg,g:_1ch});});});});};return new F(function(){return A3(_xH,_1aL,_ze,_1cf);});};return new F(function(){return A3(_xS,_yl,_ze,_1cd);});};return new F(function(){return A3(_xS,_yl,_ze,_1cb);});};return new F(function(){return A3(_xS,_yl,_ze,_1c9);});};return new F(function(){return A3(_xS,_yl,_ze,_1c7);});};return B(A3(_xH,_BM,_ze,_1c5));});return B(_wQ(function(_1ci){var _1cj=E(_1ci);return (_1cj._==3)?(!B(_lT(_1cj.a,_1aF)))?new T0(2):E(_1c4):new T0(2);}));}),_1ck=function(_1cl){return E(_1c3);};return B(_lf(new T1(1,function(_1cm){return new F(function(){return A2(_vx,_1cm,_1ck);});}),_1aW));}});return new F(function(){return _lf(new T1(1,function(_1cn){return new F(function(){return A2(_vx,_1cn,_1aS);});}),_1aU);});},_1co=new T(function(){return B(A3(_xH,_1aL,_xn,_DB));}),_1cp=function(_1cq,_){var _1cr=__app0(E(_16G)),_1cs=eval(E(_16F)),_1ct=__app1(E(_1cs),toJSStr(E(_16I))),_1cu=__app1(E(_1cs),toJSStr(E(_16H))),_1cv=__app1(E(_16J),toJSStr(_183)),_1cw=B(_184(B(_l5(_181,new T(function(){var _1cx=String(_1cu);return fromJSStr(_1cx);})))));if(!_1cw._){return E(_16O);}else{if(!E(_1cw.b)._){var _1cy=E(_1cw.a),_1cz=new T(function(){var _1cA=B(_184(B(_l5(_1co,new T(function(){var _1cB=String(_1cr);return fromJSStr(_1cB);})))));if(!_1cA._){return E(_18c);}else{if(!E(_1cA.b)._){return E(_1cA.a);}else{return E(_18b);}}}),_1cC=new T(function(){var _1cD=B(_184(B(_l5(_16M,new T(function(){var _1cE=String(_1ct);return fromJSStr(_1cE);})))));if(!_1cD._){return E(_16L);}else{if(!E(_1cD.b)._){return E(_1cD.a);}else{return E(_16K);}}}),_1cF=B(_16t(new T2(0,_182,_1cC),_1cq,_1cz,new T(function(){return B(_EV(_1cy.a));}),new T(function(){return B(_dJ(_1cy.b));})));return new F(function(){return _GL(_1cF.a,_1cF.b,_1cF.c,_1cF.d,_);});}else{return E(_16N);}}},_1cG=new T(function(){return B(unCStr("contractInput"));}),_1cH="(function (t, s) {document.getElementById(t).value = s})",_1cI=function(_1cJ,_1cK,_){var _1cL=eval(E(_1cH)),_1cM=__app2(E(_1cL),toJSStr(E(_1cJ)),toJSStr(E(_1cK)));return new F(function(){return _F8(_);});},_1cN=function(_1cO,_1cP,_1cQ,_){var _1cR=E(_1cG),_1cS=toJSStr(_1cR),_1cT=eval(E(_16F)),_1cU=__app1(E(_1cT),_1cS),_1cV=B(_184(B(_l5(_DG,new T(function(){var _1cW=String(_1cU);return fromJSStr(_1cW);})))));if(!_1cV._){return E(_jT);}else{if(!E(_1cV.b)._){var _1cX=E(_1cV.a),_1cY=B(_jD(new T(function(){return B(_3G(_1cX.a));},1),new T(function(){return B(_83(_1cX.b));},1),new T(function(){return B(_fp(_1cQ,_1cO,_1cP,B(_gT(_1cX.c))));},1),new T(function(){return B(_dJ(_1cX.d));},1))),_1cZ=B(_1cI(_1cR,new T2(1,_1cY.a,_1cY.b),_)),_1d0=__app1(E(_1cT),_1cS),_1d1=new T(function(){var _1d2=B(_184(B(_l5(_DG,new T(function(){var _1d3=String(_1d0);return fromJSStr(_1d3);})))));if(!_1d2._){return E(_jT);}else{if(!E(_1d2.b)._){var _1d4=E(_1d2.a);return new T4(0,new T(function(){return B(_3G(_1d4.a));}),new T(function(){return B(_83(_1d4.b));}),new T(function(){return B(_gT(_1d4.c));}),new T(function(){return B(_dJ(_1d4.d));}));}else{return E(_jR);}}});return new F(function(){return _1cp(_1d1,_);});}else{return E(_jR);}}},_1d5=function(_1d6,_1d7,_1d8,_1d9,_1da){var _1db=E(_1da);if(!_1db._){var _1dc=_1db.c,_1dd=_1db.d,_1de=E(_1db.b),_1df=E(_1de.a);if(_1d6>=_1df){if(_1d6!=_1df){return new F(function(){return _H(_1de,_1dc,B(_1d5(_1d6,_,_1d8,_1d9,_1dd)));});}else{var _1dg=E(_1de.b);if(_1d8>=_1dg){if(_1d8!=_1dg){return new F(function(){return _H(_1de,_1dc,B(_1d5(_1d6,_,_1d8,_1d9,_1dd)));});}else{var _1dh=E(_1de.c);if(_1d9>=_1dh){if(_1d9!=_1dh){return new F(function(){return _H(_1de,_1dc,B(_1d5(_1d6,_,_1d8,_1d9,_1dd)));});}else{return new T4(0,_1db.a,E(new T3(0,_1d6,_1d8,_1d9)),E(_1dc),E(_1dd));}}else{return new F(function(){return _5(_1de,B(_1d5(_1d6,_,_1d8,_1d9,_1dc)),_1dd);});}}}else{return new F(function(){return _5(_1de,B(_1d5(_1d6,_,_1d8,_1d9,_1dc)),_1dd);});}}}else{return new F(function(){return _5(_1de,B(_1d5(_1d6,_,_1d8,_1d9,_1dc)),_1dd);});}}else{return new T4(0,1,E(new T3(0,_1d6,_1d8,_1d9)),E(_0),E(_0));}},_1di=function(_1dj,_1dk,_1dl,_1dm,_1dn){var _1do=E(_1dn);if(!_1do._){var _1dp=_1do.c,_1dq=_1do.d,_1dr=E(_1do.b),_1ds=E(_1dr.a);if(_1dj>=_1ds){if(_1dj!=_1ds){return new F(function(){return _H(_1dr,_1dp,B(_1di(_1dj,_,_1dl,_1dm,_1dq)));});}else{var _1dt=E(_1dr.b);if(_1dl>=_1dt){if(_1dl!=_1dt){return new F(function(){return _H(_1dr,_1dp,B(_1di(_1dj,_,_1dl,_1dm,_1dq)));});}else{var _1du=E(_1dm),_1dv=E(_1dr.c);if(_1du>=_1dv){if(_1du!=_1dv){return new F(function(){return _H(_1dr,_1dp,B(_1d5(_1dj,_,_1dl,_1du,_1dq)));});}else{return new T4(0,_1do.a,E(new T3(0,_1dj,_1dl,_1du)),E(_1dp),E(_1dq));}}else{return new F(function(){return _5(_1dr,B(_1d5(_1dj,_,_1dl,_1du,_1dp)),_1dq);});}}}else{return new F(function(){return _5(_1dr,B(_1di(_1dj,_,_1dl,_1dm,_1dp)),_1dq);});}}}else{return new F(function(){return _5(_1dr,B(_1di(_1dj,_,_1dl,_1dm,_1dp)),_1dq);});}}else{return new T4(0,1,E(new T3(0,_1dj,_1dl,_1dm)),E(_0),E(_0));}},_1dw=function(_1dx,_1dy,_1dz,_1dA,_1dB){var _1dC=E(_1dB);if(!_1dC._){var _1dD=_1dC.c,_1dE=_1dC.d,_1dF=E(_1dC.b),_1dG=E(_1dF.a);if(_1dx>=_1dG){if(_1dx!=_1dG){return new F(function(){return _H(_1dF,_1dD,B(_1dw(_1dx,_,_1dz,_1dA,_1dE)));});}else{var _1dH=E(_1dz),_1dI=E(_1dF.b);if(_1dH>=_1dI){if(_1dH!=_1dI){return new F(function(){return _H(_1dF,_1dD,B(_1di(_1dx,_,_1dH,_1dA,_1dE)));});}else{var _1dJ=E(_1dA),_1dK=E(_1dF.c);if(_1dJ>=_1dK){if(_1dJ!=_1dK){return new F(function(){return _H(_1dF,_1dD,B(_1d5(_1dx,_,_1dH,_1dJ,_1dE)));});}else{return new T4(0,_1dC.a,E(new T3(0,_1dx,_1dH,_1dJ)),E(_1dD),E(_1dE));}}else{return new F(function(){return _5(_1dF,B(_1d5(_1dx,_,_1dH,_1dJ,_1dD)),_1dE);});}}}else{return new F(function(){return _5(_1dF,B(_1di(_1dx,_,_1dH,_1dA,_1dD)),_1dE);});}}}else{return new F(function(){return _5(_1dF,B(_1dw(_1dx,_,_1dz,_1dA,_1dD)),_1dE);});}}else{return new T4(0,1,E(new T3(0,_1dx,_1dz,_1dA)),E(_0),E(_0));}},_1dL=function(_1dM,_1dN,_1dO,_1dP){var _1dQ=E(_1dP);if(!_1dQ._){var _1dR=_1dQ.c,_1dS=_1dQ.d,_1dT=E(_1dQ.b),_1dU=E(_1dM),_1dV=E(_1dT.a);if(_1dU>=_1dV){if(_1dU!=_1dV){return new F(function(){return _H(_1dT,_1dR,B(_1dw(_1dU,_,_1dN,_1dO,_1dS)));});}else{var _1dW=E(_1dN),_1dX=E(_1dT.b);if(_1dW>=_1dX){if(_1dW!=_1dX){return new F(function(){return _H(_1dT,_1dR,B(_1di(_1dU,_,_1dW,_1dO,_1dS)));});}else{var _1dY=E(_1dO),_1dZ=E(_1dT.c);if(_1dY>=_1dZ){if(_1dY!=_1dZ){return new F(function(){return _H(_1dT,_1dR,B(_1d5(_1dU,_,_1dW,_1dY,_1dS)));});}else{return new T4(0,_1dQ.a,E(new T3(0,_1dU,_1dW,_1dY)),E(_1dR),E(_1dS));}}else{return new F(function(){return _5(_1dT,B(_1d5(_1dU,_,_1dW,_1dY,_1dR)),_1dS);});}}}else{return new F(function(){return _5(_1dT,B(_1di(_1dU,_,_1dW,_1dO,_1dR)),_1dS);});}}}else{return new F(function(){return _5(_1dT,B(_1dw(_1dU,_,_1dN,_1dO,_1dR)),_1dS);});}}else{return new T4(0,1,E(new T3(0,_1dM,_1dN,_1dO)),E(_0),E(_0));}},_1e0=function(_1e1,_1e2,_1e3,_){var _1e4=E(_1cG),_1e5=toJSStr(_1e4),_1e6=eval(E(_16F)),_1e7=__app1(E(_1e6),_1e5),_1e8=B(_184(B(_l5(_DG,new T(function(){var _1e9=String(_1e7);return fromJSStr(_1e9);})))));if(!_1e8._){return E(_jT);}else{if(!E(_1e8.b)._){var _1ea=E(_1e8.a),_1eb=B(_jD(new T(function(){return B(_3G(_1ea.a));},1),new T(function(){return B(_1dL(_1e3,_1e1,_1e2,B(_83(_1ea.b))));},1),new T(function(){return B(_gT(_1ea.c));},1),new T(function(){return B(_dJ(_1ea.d));},1))),_1ec=B(_1cI(_1e4,new T2(1,_1eb.a,_1eb.b),_)),_1ed=__app1(E(_1e6),_1e5),_1ee=new T(function(){var _1ef=B(_184(B(_l5(_DG,new T(function(){var _1eg=String(_1ed);return fromJSStr(_1eg);})))));if(!_1ef._){return E(_jT);}else{if(!E(_1ef.b)._){var _1eh=E(_1ef.a);return new T4(0,new T(function(){return B(_3G(_1eh.a));}),new T(function(){return B(_83(_1eh.b));}),new T(function(){return B(_gT(_1eh.c));}),new T(function(){return B(_dJ(_1eh.d));}));}else{return E(_jR);}}});return new F(function(){return _1cp(_1ee,_);});}else{return E(_jR);}}},_1ei=function(_1ej,_1ek,_1el,_1em,_){var _1en=E(_1cG),_1eo=toJSStr(_1en),_1ep=eval(E(_16F)),_1eq=__app1(E(_1ep),_1eo),_1er=B(_184(B(_l5(_DG,new T(function(){var _1es=String(_1eq);return fromJSStr(_1es);})))));if(!_1er._){return E(_jT);}else{if(!E(_1er.b)._){var _1et=E(_1er.a),_1eu=B(_jD(new T(function(){return B(_1h(_1el,_1ej,_1ek,_1em,B(_3G(_1et.a))));},1),new T(function(){return B(_83(_1et.b));},1),new T(function(){return B(_gT(_1et.c));},1),new T(function(){return B(_dJ(_1et.d));},1))),_1ev=B(_1cI(_1en,new T2(1,_1eu.a,_1eu.b),_)),_1ew=__app1(E(_1ep),_1eo),_1ex=new T(function(){var _1ey=B(_184(B(_l5(_DG,new T(function(){var _1ez=String(_1ew);return fromJSStr(_1ez);})))));if(!_1ey._){return E(_jT);}else{if(!E(_1ey.b)._){var _1eA=E(_1ey.a);return new T4(0,new T(function(){return B(_3G(_1eA.a));}),new T(function(){return B(_83(_1eA.b));}),new T(function(){return B(_gT(_1eA.c));}),new T(function(){return B(_dJ(_1eA.d));}));}else{return E(_jR);}}});return new F(function(){return _1cp(_1ex,_);});}else{return E(_jR);}}},_1eB=new T(function(){return B(err(_jS));}),_1eC=new T(function(){return B(unCStr("SICC"));}),_1eD=new T(function(){return B(unCStr("SIRC"));}),_1eE=new T(function(){return B(unCStr("SIP"));}),_1eF=11,_1eG=function(_1eH,_1eI){var _1eJ=new T(function(){var _1eK=new T(function(){if(_1eH>10){return new T0(2);}else{var _1eL=new T(function(){var _1eM=new T(function(){var _1eN=function(_1eO){var _1eP=function(_1eQ){return new F(function(){return A3(_xS,_yl,_1eF,function(_1eR){return new F(function(){return A1(_1eI,new T3(2,_1eO,_1eQ,_1eR));});});});};return new F(function(){return A3(_xS,_yl,_1eF,_1eP);});};return B(A3(_xH,_AS,_1eF,_1eN));});return B(_wQ(function(_1eS){var _1eT=E(_1eS);return (_1eT._==3)?(!B(_lT(_1eT.a,_1eE)))?new T0(2):E(_1eM):new T0(2);}));}),_1eU=function(_1eV){return E(_1eL);};return new T1(1,function(_1eW){return new F(function(){return A2(_vx,_1eW,_1eU);});});}});if(_1eH>10){return B(_lf(_jU,_1eK));}else{var _1eX=new T(function(){var _1eY=new T(function(){var _1eZ=function(_1f0){var _1f1=function(_1f2){return new F(function(){return A3(_xS,_yl,_1eF,function(_1f3){return new F(function(){return A1(_1eI,new T3(1,_1f0,_1f2,_1f3));});});});};return new F(function(){return A3(_xS,_yl,_1eF,_1f1);});};return B(A3(_xH,_BM,_1eF,_1eZ));});return B(_wQ(function(_1f4){var _1f5=E(_1f4);return (_1f5._==3)?(!B(_lT(_1f5.a,_1eD)))?new T0(2):E(_1eY):new T0(2);}));}),_1f6=function(_1f7){return E(_1eX);};return B(_lf(new T1(1,function(_1f8){return new F(function(){return A2(_vx,_1f8,_1f6);});}),_1eK));}});if(_1eH>10){return new F(function(){return _lf(_jU,_1eJ);});}else{var _1f9=new T(function(){var _1fa=new T(function(){var _1fb=function(_1fc){var _1fd=function(_1fe){var _1ff=function(_1fg){return new F(function(){return A3(_xS,_yl,_1eF,function(_1fh){return new F(function(){return A1(_1eI,new T4(0,_1fc,_1fe,_1fg,_1fh));});});});};return new F(function(){return A3(_xS,_yl,_1eF,_1ff);});};return new F(function(){return A3(_xS,_yl,_1eF,_1fd);});};return B(A3(_xH,_BM,_1eF,_1fb));});return B(_wQ(function(_1fi){var _1fj=E(_1fi);return (_1fj._==3)?(!B(_lT(_1fj.a,_1eC)))?new T0(2):E(_1fa):new T0(2);}));}),_1fk=function(_1fl){return E(_1f9);};return new F(function(){return _lf(new T1(1,function(_1fm){return new F(function(){return A2(_vx,_1fm,_1fk);});}),_1eJ);});}},_1fn=function(_1fo,_1fp){return new F(function(){return _1eG(E(_1fo),_1fp);});},_1fq=new T(function(){return B(A3(_xH,_1fn,_xn,_DB));}),_1fr=function(_1fs,_){var _1ft=B(_184(B(_l5(_1fq,_1fs))));if(!_1ft._){return E(_1eB);}else{if(!E(_1ft.b)._){var _1fu=E(_1ft.a);switch(_1fu._){case 0:return new F(function(){return _1ei(_1fu.b,_1fu.c,_1fu.a,_1fu.d,_);});break;case 1:return new F(function(){return _1e0(_1fu.b,_1fu.c,_1fu.a,_);});break;default:return new F(function(){return _1cN(_1fu.b,_1fu.c,_1fu.a,_);});}}else{return E(_hb);}}},_1fv=function(_1fw,_1fx,_1fy,_){var _1fz=E(_1cG),_1fA=toJSStr(_1fz),_1fB=eval(E(_16F)),_1fC=__app1(E(_1fB),_1fA),_1fD=B(_184(B(_l5(_DG,new T(function(){var _1fE=String(_1fC);return fromJSStr(_1fE);})))));if(!_1fD._){return E(_jT);}else{if(!E(_1fD.b)._){var _1fF=E(_1fD.a),_1fG=B(_jD(new T(function(){return B(_3G(_1fF.a));},1),new T(function(){return B(_83(_1fF.b));},1),new T(function(){return B(_gT(_1fF.c));},1),new T(function(){return B(_cf(_1fy,_1fw,_1fx,B(_dJ(_1fF.d))));},1))),_1fH=B(_1cI(_1fz,new T2(1,_1fG.a,_1fG.b),_)),_1fI=__app1(E(_1fB),_1fA),_1fJ=new T(function(){var _1fK=B(_184(B(_l5(_DG,new T(function(){var _1fL=String(_1fI);return fromJSStr(_1fL);})))));if(!_1fK._){return E(_jT);}else{if(!E(_1fK.b)._){var _1fM=E(_1fK.a);return new T4(0,new T(function(){return B(_3G(_1fM.a));}),new T(function(){return B(_83(_1fM.b));}),new T(function(){return B(_gT(_1fM.c));}),new T(function(){return B(_dJ(_1fM.d));}));}else{return E(_jR);}}});return new F(function(){return _1cp(_1fJ,_);});}else{return E(_jR);}}},_1fN=new T(function(){return B(err(_ha));}),_1fO=new T(function(){return B(err(_jS));}),_1fP=new T(function(){return B(_A0(_zE,_zd,_DB));}),_1fQ=function(_1fR,_1fS,_){var _1fT=new T(function(){var _1fU=B(_184(B(_l5(_1fP,_1fR))));if(!_1fU._){return E(_1fO);}else{if(!E(_1fU.b)._){var _1fV=E(_1fU.a);return new T2(0,_1fV.a,_1fV.b);}else{return E(_1fN);}}});return new F(function(){return _1fv(new T(function(){return E(E(_1fT).b);}),_1fS,new T(function(){return E(E(_1fT).a);}),_);});},_1fW=new T(function(){return B(unCStr("When"));}),_1fX=new T(function(){return B(unCStr("Choice"));}),_1fY=new T(function(){return B(unCStr("Both"));}),_1fZ=new T(function(){return B(unCStr("Pay"));}),_1g0=new T(function(){return B(unCStr("RedeemCC"));}),_1g1=new T(function(){return B(unCStr("CommitCash"));}),_1g2=new T(function(){return B(unCStr("Null"));}),_1g3=32,_1g4=new T2(1,_1g3,_1M),_1g5=function(_1g6){var _1g7=E(_1g6);return (_1g7==1)?E(_1g4):new T2(1,_1g3,new T(function(){return B(_1g5(_1g7-1|0));}));},_1g8=new T(function(){return B(unCStr("head"));}),_1g9=new T(function(){return B(_io(_1g8));}),_1ga=function(_1gb){return new F(function(){return _hA(0,E(_1gb),_1M);});},_1gc=new T(function(){return B(unCStr("IdentPay"));}),_1gd=new T(function(){return B(unCStr("PersonChoseSomething"));}),_1ge=new T(function(){return B(unCStr("PersonChoseThis"));}),_1gf=new T(function(){return B(unCStr("NotObs"));}),_1gg=new T(function(){return B(unCStr("OrObs"));}),_1gh=new T(function(){return B(unCStr("AndObs"));}),_1gi=new T(function(){return B(unCStr("BelowTimeout"));}),_1gj=new T(function(){return B(unCStr("IdentChoice"));}),_1gk=new T(function(){return B(unCStr("IdentCC"));}),_1gl=new T(function(){return B(unCStr("ConstMoney"));}),_1gm=new T(function(){return B(unCStr("AddMoney"));}),_1gn=new T(function(){return B(unCStr("AvailableMoney"));}),_1go=new T(function(){return B(unCStr("FalseObs"));}),_1gp=new T(function(){return B(unCStr("TrueObs"));}),_1gq=new T(function(){return B(unCStr("ValueGE"));}),_1gr=function(_1gs){var _1gt=E(_1gs);switch(_1gt._){case 0:var _1gu=E(_1gt.a);switch(_1gu._){case 0:return new T2(0,_1g2,_1M);case 1:return new T2(0,_1g1,new T2(1,new T1(3,_1gu.a),new T2(1,new T1(6,_1gu.b),new T2(1,new T1(6,_1gu.c),new T2(1,new T1(6,_1gu.d),new T2(1,new T1(6,_1gu.e),new T2(1,new T1(0,_1gu.f),new T2(1,new T1(0,_1gu.g),_1M))))))));case 2:return new T2(0,_1g0,new T2(1,new T1(3,_1gu.a),new T2(1,new T1(0,_1gu.b),_1M)));case 3:return new T2(0,_1fZ,new T2(1,new T1(5,_1gu.a),new T2(1,new T1(6,_1gu.b),new T2(1,new T1(6,_1gu.c),new T2(1,new T1(6,_1gu.d),new T2(1,new T1(6,_1gu.e),new T2(1,new T1(0,_1gu.f),_1M)))))));case 4:return new T2(0,_1fY,new T2(1,new T1(0,_1gu.a),new T2(1,new T1(0,_1gu.b),_1M)));case 5:return new T2(0,_1fX,new T2(1,new T1(1,_1gu.a),new T2(1,new T1(0,_1gu.b),new T2(1,new T1(0,_1gu.c),_1M))));default:return new T2(0,_1fW,new T2(1,new T1(1,_1gu.a),new T2(1,new T1(6,_1gu.b),new T2(1,new T1(0,_1gu.c),new T2(1,new T1(0,_1gu.d),_1M)))));}break;case 1:var _1gv=E(_1gt.a);switch(_1gv._){case 0:return new T2(0,_1gi,new T2(1,new T1(6,_1gv.a),_1M));case 1:return new T2(0,_1gh,new T2(1,new T1(1,_1gv.a),new T2(1,new T1(1,_1gv.b),_1M)));case 2:return new T2(0,_1gg,new T2(1,new T1(1,_1gv.a),new T2(1,new T1(1,_1gv.b),_1M)));case 3:return new T2(0,_1gf,new T2(1,new T1(1,_1gv.a),_1M));case 4:return new T2(0,_1ge,new T2(1,new T1(4,_1gv.a),new T2(1,new T1(6,_1gv.b),new T2(1,new T1(6,_1gv.c),_1M))));case 5:return new T2(0,_1gd,new T2(1,new T1(4,_1gv.a),new T2(1,new T1(6,_1gv.b),_1M)));case 6:return new T2(0,_1gq,new T2(1,new T1(2,_1gv.a),new T2(1,new T1(2,_1gv.b),_1M)));case 7:return new T2(0,_1gp,_1M);default:return new T2(0,_1go,_1M);}break;case 2:var _1gw=E(_1gt.a);switch(_1gw._){case 0:return new T2(0,_1gn,new T2(1,new T1(3,_1gw.a),_1M));case 1:return new T2(0,_1gm,new T2(1,new T1(2,_1gw.a),new T2(1,new T1(2,_1gw.b),_1M)));default:return new T2(0,_1gl,new T2(1,new T1(6,_1gw.a),_1M));}break;case 3:return new T2(0,_1gk,new T2(1,new T1(6,_1gt.a),_1M));case 4:return new T2(0,_1gj,new T2(1,new T1(6,_1gt.a),_1M));case 5:return new T2(0,_1gc,new T2(1,new T1(6,_1gt.a),_1M));default:return new T2(0,new T(function(){return B(_1ga(_1gt.a));}),_1M);}},_1gx=function(_1gy){var _1gz=B(_1gr(_1gy)),_1gA=_1gz.a,_1gB=E(_1gz.b);if(!_1gB._){return new T1(0,new T2(0,_1gA,_1M));}else{switch(E(_1gy)._){case 0:return new T1(2,new T2(0,_1gA,_1gB));case 1:return new T1(2,new T2(0,_1gA,_1gB));case 2:return new T1(2,new T2(0,_1gA,_1gB));default:return new T1(1,new T2(0,_1gA,_1gB));}}},_1gC=function(_1gD,_1gE){var _1gF=E(_1gE);if(!_1gF._){return __Z;}else{var _1gG=_1gF.a,_1gH=new T(function(){var _1gI=B(_kG(new T(function(){return B(A1(_1gD,_1gG));}),_1gF.b));return new T2(0,_1gI.a,_1gI.b);});return new T2(1,new T2(1,_1gG,new T(function(){return E(E(_1gH).a);})),new T(function(){return B(_1gC(_1gD,E(_1gH).b));}));}},_1gJ=new T(function(){return B(unCStr(" "));}),_1gK=function(_1gL,_1gM){return (E(_1gL)._==2)?false:(E(_1gM)._==2)?false:true;},_1gN=function(_1gO,_1gP){var _1gQ=E(_1gP);return (_1gQ._==0)?__Z:new T2(1,_1gO,new T2(1,_1gQ.a,new T(function(){return B(_1gN(_1gO,_1gQ.b));})));},_1gR=new T(function(){return B(unCStr("\n"));}),_1gS=function(_1gT){var _1gU=E(_1gT);if(!_1gU._){return __Z;}else{return new F(function(){return _hq(_1gU.a,new T(function(){return B(_1gS(_1gU.b));},1));});}},_1gV=function(_1gW,_1gX){return new F(function(){return _hq(_1gW,new T(function(){return B(_1gS(_1gX));},1));});},_1gY=function(_1gZ){var _1h0=E(_1gZ);if(!_1h0._){return __Z;}else{return new F(function(){return _hq(_1h0.a,new T(function(){return B(_1gY(_1h0.b));},1));});}},_1h1=function(_1h2,_1h3){return new F(function(){return _hq(_1h2,new T(function(){return B(_1gY(_1h3));},1));});},_1h4=function(_1h5){var _1h6=E(_1h5);if(!_1h6._){return __Z;}else{return new F(function(){return _hq(_1h6.a,new T(function(){return B(_1h4(_1h6.b));},1));});}},_1h7=function(_1h8,_1h9){return new F(function(){return _hq(_1h8,new T(function(){return B(_1h4(_1h9));},1));});},_1ha=new T(function(){return B(unCStr("tail"));}),_1hb=new T(function(){return B(_io(_1ha));}),_1hc=function(_1hd,_1he,_1hf){var _1hg=E(_1hf);if(!_1hg._){return E(_1he);}else{var _1hh=new T(function(){return (E(_1hd)+B(_oy(_1he,0))|0)+1|0;}),_1hi=new T(function(){return B(_1gC(_1gK,B(_oD(_1gx,_1hg))));}),_1hj=new T(function(){var _1hk=E(_1hi);if(!_1hk._){return E(_1hb);}else{var _1hl=new T(function(){var _1hm=E(_1hh);if(0>=_1hm){return __Z;}else{return B(_1g5(_1hm));}}),_1hn=function(_1ho){return new F(function(){return _1hp(_1hh,_1ho);});},_1hq=function(_1hr){var _1hs=new T(function(){var _1ht=B(_oD(_1hn,_1hr));if(!_1ht._){return __Z;}else{return B(_1gV(_1ht.a,new T(function(){return B(_1gN(_1gJ,_1ht.b));})));}},1);return new F(function(){return _hq(_1hl,_1hs);});};return B(_1gN(_1gR,B(_oD(_1hq,_1hk.b))));}}),_1hu=new T(function(){var _1hv=new T(function(){var _1hw=E(_1hi);if(!_1hw._){return E(_1g9);}else{return B(_1gN(_1gJ,B(_oD(function(_1ho){return new F(function(){return _1hp(_1hh,_1ho);});},_1hw.a))));}});return B(_1h1(_1he,_1hv));});return new F(function(){return _1h7(_1hu,_1hj);});}},_1hx=new T(function(){return B(unCStr(")"));}),_1hp=function(_1hy,_1hz){var _1hA=E(_1hz);switch(_1hA._){case 0:var _1hB=E(_1hA.a);return new F(function(){return _1hC(0,_1hB.a,_1hB.b);});break;case 1:return new F(function(){return unAppCStr("(",new T(function(){var _1hD=E(_1hA.a);return B(_hq(B(_1hC(0,_1hD.a,_1hD.b)),_1hx));}));});break;default:var _1hE=new T(function(){var _1hF=E(_1hA.a);return B(_hq(B(_1hc(new T(function(){return E(_1hy)+1|0;},1),_1hF.a,_1hF.b)),_1hx));});return new F(function(){return unAppCStr("(",_1hE);});}},_1hC=function(_1hG,_1hH,_1hI){var _1hJ=E(_1hI);if(!_1hJ._){return E(_1hH);}else{var _1hK=new T(function(){return (_1hG+B(_oy(_1hH,0))|0)+1|0;}),_1hL=new T(function(){return B(_1gC(_1gK,B(_oD(_1gx,_1hJ))));}),_1hM=new T(function(){var _1hN=E(_1hL);if(!_1hN._){return E(_1hb);}else{var _1hO=new T(function(){var _1hP=E(_1hK);if(0>=_1hP){return __Z;}else{return B(_1g5(_1hP));}}),_1hQ=function(_1ho){return new F(function(){return _1hp(_1hK,_1ho);});},_1hR=function(_1hS){var _1hT=new T(function(){var _1hU=B(_oD(_1hQ,_1hS));if(!_1hU._){return __Z;}else{return B(_1gV(_1hU.a,new T(function(){return B(_1gN(_1gJ,_1hU.b));})));}},1);return new F(function(){return _hq(_1hO,_1hT);});};return B(_1gN(_1gR,B(_oD(_1hR,_1hN.b))));}}),_1hV=new T(function(){var _1hW=new T(function(){var _1hX=E(_1hL);if(!_1hX._){return E(_1g9);}else{return B(_1gN(_1gJ,B(_oD(function(_1ho){return new F(function(){return _1hp(_1hK,_1ho);});},_1hX.a))));}});return B(_1h1(_1hH,_1hW));});return new F(function(){return _1h7(_1hV,_1hM);});}},_1hY=new T(function(){return B(_1hC(0,_1g2,_1M));}),_1hZ=function(_1i0,_){return new T(function(){var _1i1=B(_184(B(_l5(_1co,_1i0))));if(!_1i1._){return E(_18c);}else{if(!E(_1i1.b)._){var _1i2=E(_1i1.a);switch(_1i2._){case 0:return E(_1hY);break;case 1:return B(_1hC(0,_1g1,new T2(1,new T1(3,_1i2.a),new T2(1,new T1(6,_1i2.b),new T2(1,new T1(6,_1i2.c),new T2(1,new T1(6,_1i2.d),new T2(1,new T1(6,_1i2.e),new T2(1,new T1(0,_1i2.f),new T2(1,new T1(0,_1i2.g),_1M)))))))));break;case 2:return B(_1hC(0,_1g0,new T2(1,new T1(3,_1i2.a),new T2(1,new T1(0,_1i2.b),_1M))));break;case 3:return B(_1hC(0,_1fZ,new T2(1,new T1(5,_1i2.a),new T2(1,new T1(6,_1i2.b),new T2(1,new T1(6,_1i2.c),new T2(1,new T1(6,_1i2.d),new T2(1,new T1(6,_1i2.e),new T2(1,new T1(0,_1i2.f),_1M))))))));break;case 4:return B(_1hC(0,_1fY,new T2(1,new T1(0,_1i2.a),new T2(1,new T1(0,_1i2.b),_1M))));break;case 5:return B(_1hC(0,_1fX,new T2(1,new T1(1,_1i2.a),new T2(1,new T1(0,_1i2.b),new T2(1,new T1(0,_1i2.c),_1M)))));break;default:return B(_1hC(0,_1fW,new T2(1,new T1(1,_1i2.a),new T2(1,new T1(6,_1i2.b),new T2(1,new T1(0,_1i2.c),new T2(1,new T1(0,_1i2.d),_1M))))));}}else{return E(_18b);}}});},_1i3=new T(function(){return B(unCStr("codeArea"));}),_1i4=function(_){var _1i5=__app0(E(_16G)),_1i6=B(_1hZ(new T(function(){var _1i7=String(_1i5);return fromJSStr(_1i7);}),_)),_1i8=B(_1cI(_1i3,_1i6,_)),_1i9=eval(E(_16F)),_1ia=__app1(E(_1i9),toJSStr(E(_1cG))),_1ib=new T(function(){var _1ic=B(_184(B(_l5(_DG,new T(function(){var _1id=String(_1ia);return fromJSStr(_1id);})))));if(!_1ic._){return E(_jT);}else{if(!E(_1ic.b)._){var _1ie=E(_1ic.a);return new T4(0,new T(function(){return B(_3G(_1ie.a));}),new T(function(){return B(_83(_1ie.b));}),new T(function(){return B(_gT(_1ie.c));}),new T(function(){return B(_dJ(_1ie.d));}));}else{return E(_jR);}}});return new F(function(){return _1cp(_1ib,_);});},_1if="(function (b) { return (b.inputList.length); })",_1ig="(function (b, x) { return (b.inputList[x]); })",_1ih=function(_1ii,_1ij,_){var _1ik=eval(E(_1ig)),_1il=__app2(E(_1ik),_1ii,_1ij);return new T1(0,_1il);},_1im=function(_1in,_1io,_1ip,_){var _1iq=E(_1ip);if(!_1iq._){return _1M;}else{var _1ir=B(_1ih(_1in,E(_1iq.a),_)),_1is=B(_1im(_1in,_,_1iq.b,_));return new T2(1,_1ir,_1is);}},_1it=function(_1iu,_1iv){if(_1iu<=_1iv){var _1iw=function(_1ix){return new T2(1,_1ix,new T(function(){if(_1ix!=_1iv){return B(_1iw(_1ix+1|0));}else{return __Z;}}));};return new F(function(){return _1iw(_1iu);});}else{return __Z;}},_1iy=function(_1iz,_){var _1iA=eval(E(_1if)),_1iB=__app1(E(_1iA),_1iz),_1iC=Number(_1iB),_1iD=jsTrunc(_1iC);return new F(function(){return _1im(_1iz,_,new T(function(){return B(_1it(0,_1iD-1|0));}),_);});},_1iE="(function (y, ip) {y.previousConnection.connect(ip.connection);})",_1iF="(function (x) { return x.name; })",_1iG=new T(function(){return B(unCStr("\""));}),_1iH=function(_1iI){return new F(function(){return err(B(unAppCStr("No input matches \"",new T(function(){return B(_hq(_1iI,_1iG));}))));});},_1iJ=function(_1iK,_1iL,_){var _1iM=E(_1iL);if(!_1iM._){return new F(function(){return _1iH(_1iK);});}else{var _1iN=E(_1iM.a),_1iO=E(_1iF),_1iP=eval(_1iO),_1iQ=__app1(E(_1iP),E(_1iN.a)),_1iR=String(_1iQ);if(!B(_lT(fromJSStr(_1iR),_1iK))){var _1iS=function(_1iT,_1iU,_){while(1){var _1iV=E(_1iU);if(!_1iV._){return new F(function(){return _1iH(_1iT);});}else{var _1iW=E(_1iV.a),_1iX=eval(_1iO),_1iY=__app1(E(_1iX),E(_1iW.a)),_1iZ=String(_1iY);if(!B(_lT(fromJSStr(_1iZ),_1iT))){_1iU=_1iV.b;continue;}else{return _1iW;}}}};return new F(function(){return _1iS(_1iK,_1iM.b,_);});}else{return _1iN;}}},_1j0=function(_1j1,_1j2,_1j3,_){var _1j4=B(_1iy(_1j2,_)),_1j5=B(_1iJ(_1j1,_1j4,_)),_1j6=eval(E(_1iE)),_1j7=__app2(E(_1j6),E(E(_1j3).a),E(E(_1j5).a));return new F(function(){return _F8(_);});},_1j8=function(_1j9){return new F(function(){return err(B(unAppCStr("No fieldrow matches \"",new T(function(){return B(_hq(_1j9,_1iG));}))));});},_1ja=function(_1jb,_1jc,_){var _1jd=E(_1jc);if(!_1jd._){return new F(function(){return _1j8(_1jb);});}else{var _1je=E(_1jd.a),_1jf=E(_1iF),_1jg=eval(_1jf),_1jh=__app1(E(_1jg),E(_1je.a)),_1ji=String(_1jh);if(!B(_lT(fromJSStr(_1ji),_1jb))){var _1jj=function(_1jk,_1jl,_){while(1){var _1jm=E(_1jl);if(!_1jm._){return new F(function(){return _1j8(_1jk);});}else{var _1jn=E(_1jm.a),_1jo=eval(_1jf),_1jp=__app1(E(_1jo),E(_1jn.a)),_1jq=String(_1jp);if(!B(_lT(fromJSStr(_1jq),_1jk))){_1jl=_1jm.b;continue;}else{return _1jn;}}}};return new F(function(){return _1jj(_1jb,_1jd.b,_);});}else{return _1je;}}},_1jr="(function (b) { return (b.fieldRow.length); })",_1js="(function (b, x) { return (b.fieldRow[x]); })",_1jt=function(_1ju,_1jv,_){var _1jw=eval(E(_1js)),_1jx=__app2(E(_1jw),_1ju,_1jv);return new T1(0,_1jx);},_1jy=function(_1jz,_1jA,_1jB,_){var _1jC=E(_1jB);if(!_1jC._){return _1M;}else{var _1jD=B(_1jt(_1jz,E(_1jC.a),_)),_1jE=B(_1jy(_1jz,_,_1jC.b,_));return new T2(1,_1jD,_1jE);}},_1jF=function(_1jG,_){var _1jH=eval(E(_1jr)),_1jI=__app1(E(_1jH),_1jG),_1jJ=Number(_1jI),_1jK=jsTrunc(_1jJ);return new F(function(){return _1jy(_1jG,_,new T(function(){return B(_1it(0,_1jK-1|0));}),_);});},_1jL=function(_1jM,_){var _1jN=E(_1jM);if(!_1jN._){return _1M;}else{var _1jO=B(_1jF(E(E(_1jN.a).a),_)),_1jP=B(_1jL(_1jN.b,_));return new T2(1,_1jO,_1jP);}},_1jQ=function(_1jR){var _1jS=E(_1jR);if(!_1jS._){return __Z;}else{return new F(function(){return _hq(_1jS.a,new T(function(){return B(_1jQ(_1jS.b));},1));});}},_1jT=function(_1jU,_1jV,_){var _1jW=B(_1iy(_1jV,_)),_1jX=B(_1jL(_1jW,_));return new F(function(){return _1ja(_1jU,B(_1jQ(_1jX)),_);});},_1jY="(function (y, ip) {y.outputConnection.connect(ip.connection);})",_1jZ=function(_1k0,_1k1,_1k2,_){var _1k3=B(_1iy(_1k1,_)),_1k4=B(_1iJ(_1k0,_1k3,_)),_1k5=eval(E(_1jY)),_1k6=__app2(E(_1k5),E(E(_1k2).a),E(E(_1k4).a));return new F(function(){return _F8(_);});},_1k7=new T(function(){return B(unCStr("contract_commitcash"));}),_1k8=new T(function(){return B(unCStr("contract_redeemcc"));}),_1k9=new T(function(){return B(unCStr("contract_pay"));}),_1ka=new T(function(){return B(unCStr("contract_both"));}),_1kb=new T(function(){return B(unCStr("contract_choice"));}),_1kc=new T(function(){return B(unCStr("contract_when"));}),_1kd="(function (x) {var c = demoWorkspace.newBlock(x); c.initSvg(); return c;})",_1ke=function(_1kf,_){var _1kg=eval(E(_1kd)),_1kh=__app1(E(_1kg),toJSStr(E(_1kf)));return new T1(0,_1kh);},_1ki=new T(function(){return B(unCStr("payer_id"));}),_1kj=new T(function(){return B(unCStr("pay_id"));}),_1kk=new T(function(){return B(unCStr("ccommit_id"));}),_1kl=new T(function(){return B(unCStr("end_expiration"));}),_1km=new T(function(){return B(unCStr("start_expiration"));}),_1kn=new T(function(){return B(unCStr("person_id"));}),_1ko=new T(function(){return B(unCStr("contract_null"));}),_1kp=new T(function(){return B(unCStr("contract2"));}),_1kq=new T(function(){return B(unCStr("contract1"));}),_1kr=new T(function(){return B(unCStr("observation"));}),_1ks=new T(function(){return B(unCStr("timeout"));}),_1kt=new T(function(){return B(unCStr("contract"));}),_1ku=new T(function(){return B(unCStr("expiration"));}),_1kv=new T(function(){return B(unCStr("ammount"));}),_1kw=new T(function(){return B(unCStr("payee_id"));}),_1kx=function(_1ky,_1kz,_1kA,_){var _1kB=B(_1iy(_1kz,_)),_1kC=B(_1iJ(_1ky,_1kB,_)),_1kD=eval(E(_1jY)),_1kE=__app2(E(_1kD),E(E(_1kA).a),E(E(_1kC).a));return new F(function(){return _F8(_);});},_1kF=new T(function(){return B(unCStr("observation_personchosethis"));}),_1kG=new T(function(){return B(unCStr("observation_personchosesomething"));}),_1kH=new T(function(){return B(unCStr("observation_value_ge"));}),_1kI=new T(function(){return B(unCStr("observation_trueobs"));}),_1kJ=new T(function(){return B(unCStr("observation_falseobs"));}),_1kK=new T(function(){return B(unCStr("observation_belowtimeout"));}),_1kL=new T(function(){return B(unCStr("observation_andobs"));}),_1kM=new T(function(){return B(unCStr("observation_orobs"));}),_1kN=new T(function(){return B(unCStr("observation_notobs"));}),_1kO=new T(function(){return B(unCStr("value2"));}),_1kP=new T(function(){return B(unCStr("value1"));}),_1kQ=new T(function(){return B(unCStr("person"));}),_1kR=new T(function(){return B(unCStr("choice_id"));}),_1kS=new T(function(){return B(unCStr("choice_value"));}),_1kT=new T(function(){return B(unCStr("observation2"));}),_1kU=new T(function(){return B(unCStr("observation1"));}),_1kV=new T(function(){return B(unCStr("block_number"));}),_1kW=new T(function(){return B(unCStr("value_available_money"));}),_1kX=new T(function(){return B(unCStr("value_add_money"));}),_1kY=new T(function(){return B(unCStr("value_const_money"));}),_1kZ=new T(function(){return B(unCStr("money"));}),_1l0=new T(function(){return B(unCStr("commit_id"));}),_1l1="(function (b, s) { return (b.setText(s)); })",_1l2=function(_1l3,_){var _1l4=E(_1l3);switch(_1l4._){case 0:var _1l5=B(_1ke(_1kW,_)),_1l6=E(_1l5),_1l7=B(_1jT(_1l0,E(_1l6.a),_)),_1l8=eval(E(_1l1)),_1l9=__app2(E(_1l8),E(E(_1l7).a),toJSStr(B(_hA(0,E(_1l4.a),_1M))));return _1l6;case 1:var _1la=B(_1l2(_1l4.a,_)),_1lb=B(_1l2(_1l4.b,_)),_1lc=B(_1ke(_1kX,_)),_1ld=E(_1lc),_1le=E(_1ld.a),_1lf=B(_1kx(_1kP,_1le,_1la,_)),_1lg=B(_1kx(_1kO,_1le,_1lb,_));return _1ld;default:var _1lh=B(_1ke(_1kY,_)),_1li=E(_1lh),_1lj=B(_1jT(_1kZ,E(_1li.a),_)),_1lk=eval(E(_1l1)),_1ll=__app2(E(_1lk),E(E(_1lj).a),toJSStr(B(_hA(0,E(_1l4.a),_1M))));return _1li;}},_1lm=function(_1ln,_){var _1lo=E(_1ln);switch(_1lo._){case 0:var _1lp=B(_1ke(_1kK,_)),_1lq=E(_1lp),_1lr=B(_1jT(_1kV,E(_1lq.a),_)),_1ls=eval(E(_1l1)),_1lt=__app2(E(_1ls),E(E(_1lr).a),toJSStr(B(_hA(0,E(_1lo.a),_1M))));return _1lq;case 1:var _1lu=B(_1lm(_1lo.a,_)),_1lv=B(_1lm(_1lo.b,_)),_1lw=B(_1ke(_1kL,_)),_1lx=E(_1lw),_1ly=E(_1lx.a),_1lz=B(_1jZ(_1kU,_1ly,_1lu,_)),_1lA=B(_1jZ(_1kT,_1ly,_1lv,_));return _1lx;case 2:var _1lB=B(_1lm(_1lo.a,_)),_1lC=B(_1lm(_1lo.b,_)),_1lD=B(_1ke(_1kM,_)),_1lE=E(_1lD),_1lF=E(_1lE.a),_1lG=B(_1jZ(_1kU,_1lF,_1lB,_)),_1lH=B(_1jZ(_1kT,_1lF,_1lC,_));return _1lE;case 3:var _1lI=B(_1lm(_1lo.a,_)),_1lJ=B(_1ke(_1kN,_)),_1lK=E(_1lJ),_1lL=B(_1jZ(_1kr,E(_1lK.a),_1lI,_));return _1lK;case 4:var _1lM=B(_1ke(_1kF,_)),_1lN=E(_1lM),_1lO=E(_1lN.a),_1lP=B(_1jT(_1kR,_1lO,_)),_1lQ=eval(E(_1l1)),_1lR=__app2(E(_1lQ),E(E(_1lP).a),toJSStr(B(_hA(0,E(_1lo.a),_1M)))),_1lS=B(_1jT(_1kQ,_1lO,_)),_1lT=__app2(E(_1lQ),E(E(_1lS).a),toJSStr(B(_hA(0,E(_1lo.b),_1M)))),_1lU=B(_1jT(_1kS,_1lO,_)),_1lV=__app2(E(_1lQ),E(E(_1lU).a),toJSStr(B(_hA(0,E(_1lo.c),_1M))));return _1lN;case 5:var _1lW=B(_1ke(_1kG,_)),_1lX=E(_1lW),_1lY=E(_1lX.a),_1lZ=B(_1jT(_1kR,_1lY,_)),_1m0=eval(E(_1l1)),_1m1=__app2(E(_1m0),E(E(_1lZ).a),toJSStr(B(_hA(0,E(_1lo.a),_1M)))),_1m2=B(_1jT(_1kQ,_1lY,_)),_1m3=__app2(E(_1m0),E(E(_1m2).a),toJSStr(B(_hA(0,E(_1lo.b),_1M))));return _1lX;case 6:var _1m4=B(_1l2(_1lo.a,_)),_1m5=B(_1l2(_1lo.b,_)),_1m6=B(_1ke(_1kH,_)),_1m7=E(_1m6),_1m8=E(_1m7.a),_1m9=B(_1kx(_1kP,_1m8,_1m4,_)),_1ma=B(_1kx(_1kO,_1m8,_1m5,_));return _1m7;case 7:return new F(function(){return _1ke(_1kI,_);});break;default:return new F(function(){return _1ke(_1kJ,_);});}},_1mb=function(_1mc,_){var _1md=E(_1mc);switch(_1md._){case 0:return new F(function(){return _1ke(_1ko,_);});break;case 1:var _1me=B(_1mb(_1md.f,_)),_1mf=B(_1mb(_1md.g,_)),_1mg=B(_1ke(_1k7,_)),_1mh=E(_1mg),_1mi=E(_1mh.a),_1mj=B(_1jT(_1kk,_1mi,_)),_1mk=eval(E(_1l1)),_1ml=__app2(E(_1mk),E(E(_1mj).a),toJSStr(B(_hA(0,E(_1md.a),_1M)))),_1mm=B(_1jT(_1kn,_1mi,_)),_1mn=__app2(E(_1mk),E(E(_1mm).a),toJSStr(B(_hA(0,E(_1md.b),_1M)))),_1mo=B(_1jT(_1kv,_1mi,_)),_1mp=__app2(E(_1mk),E(E(_1mo).a),toJSStr(B(_hA(0,E(_1md.c),_1M)))),_1mq=B(_1jT(_1km,_1mi,_)),_1mr=__app2(E(_1mk),E(E(_1mq).a),toJSStr(B(_hA(0,E(_1md.d),_1M)))),_1ms=B(_1jT(_1kl,_1mi,_)),_1mt=__app2(E(_1mk),E(E(_1ms).a),toJSStr(B(_hA(0,E(_1md.e),_1M)))),_1mu=B(_1j0(_1kq,_1mi,_1me,_)),_1mv=B(_1j0(_1kp,_1mi,_1mf,_));return _1mh;case 2:var _1mw=B(_1mb(_1md.b,_)),_1mx=B(_1ke(_1k8,_)),_1my=E(_1mx),_1mz=E(_1my.a),_1mA=B(_1jT(_1kk,_1mz,_)),_1mB=eval(E(_1l1)),_1mC=__app2(E(_1mB),E(E(_1mA).a),toJSStr(B(_hA(0,E(_1md.a),_1M)))),_1mD=B(_1j0(_1kt,_1mz,_1mw,_));return _1my;case 3:var _1mE=B(_1mb(_1md.f,_)),_1mF=B(_1ke(_1k9,_)),_1mG=E(_1mF),_1mH=E(_1mG.a),_1mI=B(_1jT(_1kj,_1mH,_)),_1mJ=eval(E(_1l1)),_1mK=__app2(E(_1mJ),E(E(_1mI).a),toJSStr(B(_hA(0,E(_1md.a),_1M)))),_1mL=B(_1jT(_1ki,_1mH,_)),_1mM=__app2(E(_1mJ),E(E(_1mL).a),toJSStr(B(_hA(0,E(_1md.b),_1M)))),_1mN=B(_1jT(_1kw,_1mH,_)),_1mO=__app2(E(_1mJ),E(E(_1mN).a),toJSStr(B(_hA(0,E(_1md.c),_1M)))),_1mP=B(_1jT(_1kv,_1mH,_)),_1mQ=__app2(E(_1mJ),E(E(_1mP).a),toJSStr(B(_hA(0,E(_1md.d),_1M)))),_1mR=B(_1jT(_1ku,_1mH,_)),_1mS=__app2(E(_1mJ),E(E(_1mR).a),toJSStr(B(_hA(0,E(_1md.e),_1M)))),_1mT=B(_1j0(_1kt,_1mH,_1mE,_));return _1mG;case 4:var _1mU=B(_1mb(_1md.a,_)),_1mV=B(_1mb(_1md.b,_)),_1mW=B(_1ke(_1ka,_)),_1mX=E(_1mW),_1mY=E(_1mX.a),_1mZ=B(_1j0(_1kq,_1mY,_1mU,_)),_1n0=B(_1j0(_1kp,_1mY,_1mV,_));return _1mX;case 5:var _1n1=B(_1lm(_1md.a,_)),_1n2=B(_1mb(_1md.b,_)),_1n3=B(_1mb(_1md.c,_)),_1n4=B(_1ke(_1kb,_)),_1n5=E(_1n4),_1n6=E(_1n5.a),_1n7=B(_1jZ(_1kr,_1n6,_1n1,_)),_1n8=B(_1j0(_1kq,_1n6,_1n2,_)),_1n9=B(_1j0(_1kp,_1n6,_1n3,_));return _1n5;default:var _1na=B(_1lm(_1md.a,_)),_1nb=B(_1mb(_1md.c,_)),_1nc=B(_1mb(_1md.d,_)),_1nd=B(_1ke(_1kc,_)),_1ne=E(_1nd),_1nf=E(_1ne.a),_1ng=B(_1jT(_1ks,_1nf,_)),_1nh=eval(E(_1l1)),_1ni=__app2(E(_1nh),E(E(_1ng).a),toJSStr(B(_hA(0,E(_1md.b),_1M)))),_1nj=B(_1jZ(_1kr,_1nf,_1na,_)),_1nk=B(_1j0(_1kq,_1nf,_1nb,_)),_1nl=B(_1j0(_1kp,_1nf,_1nc,_));return _1ne;}},_1nm=new T(function(){return eval("(function () {var i; var b = demoWorkspace.getAllBlocks(); for (i = b.length - 1; i > 0; --i) { if (b[i] !== undefined) { b[i].dispose() } };})");}),_1nn=new T(function(){return eval("(function() {return (demoWorkspace.getAllBlocks()[0]);})");}),_1no=new T(function(){return B(unCStr("base_contract"));}),_1np=new T(function(){return eval("(function() { demoWorkspace.render(); onresize(); })");}),_1nq=function(_1nr,_){var _1ns=__app0(E(_1nm)),_1nt=__app0(E(_1nn)),_1nu=B(_184(B(_l5(_1co,_1nr))));if(!_1nu._){return E(_18c);}else{if(!E(_1nu.b)._){var _1nv=B(_1mb(_1nu.a,_)),_1nw=B(_1j0(_1no,_1nt,_1nv,_)),_1nx=__app0(E(_1np)),_1ny=eval(E(_16F)),_1nz=__app1(E(_1ny),toJSStr(E(_1cG))),_1nA=new T(function(){var _1nB=B(_184(B(_l5(_DG,new T(function(){var _1nC=String(_1nz);return fromJSStr(_1nC);})))));if(!_1nB._){return E(_jT);}else{if(!E(_1nB.b)._){var _1nD=E(_1nB.a);return new T4(0,new T(function(){return B(_3G(_1nD.a));}),new T(function(){return B(_83(_1nD.b));}),new T(function(){return B(_gT(_1nD.c));}),new T(function(){return B(_dJ(_1nD.d));}));}else{return E(_jR);}}});return new F(function(){return _1cp(_1nA,_);});}else{return E(_18b);}}},_1nE=function(_){var _1nF=eval(E(_16F)),_1nG=__app1(E(_1nF),toJSStr(E(_1i3)));return new F(function(){return _1nq(new T(function(){var _1nH=String(_1nG);return fromJSStr(_1nH);}),_);});},_1nI=new T(function(){return B(unCStr("contractOutput"));}),_1nJ=new T(function(){return B(unCStr("([], [], [], [])"));}),_1nK=new T(function(){return B(unCStr("([], [])"));}),_1nL=new T(function(){return B(_hA(0,0,_1M));}),_1nM=function(_){var _1nN=__app0(E(_1nm)),_1nO=B(_1cI(_1i3,_1M,_)),_1nP=B(_1cI(_16I,_1nL,_)),_1nQ=B(_1cI(_16H,_1nK,_)),_1nR=B(_1cI(_1cG,_1nJ,_));return new F(function(){return _1cI(_1nI,_1M,_);});},_1nS=new T(function(){return B(unCStr("NotRedeemed "));}),_1nT=function(_1nU,_1nV,_1nW){var _1nX=E(_1nV);if(!_1nX._){var _1nY=function(_1nZ){return new F(function(){return _hA(11,E(_1nX.a),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1nX.b),_1nZ));})));});};if(E(_1nU)<11){return new F(function(){return _hq(_1nS,new T(function(){return B(_1nY(_1nW));},1));});}else{var _1o0=new T(function(){return B(_hq(_1nS,new T(function(){return B(_1nY(new T2(1,_hy,_1nW)));},1)));});return new T2(1,_hz,_1o0);}}else{return new F(function(){return _hq(_170,_1nW);});}},_1o1=0,_1o2=function(_1o3,_1o4,_1o5){var _1o6=new T(function(){var _1o7=function(_1o8){var _1o9=E(_1o4),_1oa=new T(function(){return B(A3(_is,_hk,new T2(1,function(_1ob){return new F(function(){return _hA(0,E(_1o9.a),_1ob);});},new T2(1,function(_Av){return new F(function(){return _1nT(_1o1,_1o9.b,_Av);});},_1M)),new T2(1,_hy,_1o8)));});return new T2(1,_hz,_1oa);};return B(A3(_is,_hk,new T2(1,function(_1oc){return new F(function(){return _hF(0,_1o3,_1oc);});},new T2(1,_1o7,_1M)),new T2(1,_hy,_1o5)));});return new T2(0,_hz,_1o6);},_1od=function(_1oe,_1of){var _1og=E(_1oe),_1oh=B(_1o2(_1og.a,_1og.b,_1of));return new T2(1,_1oh.a,_1oh.b);},_1oi=function(_1oj,_1ok){return new F(function(){return _iR(_1od,_1oj,_1ok);});},_1ol=new T(function(){return B(unCStr("ChoiceMade "));}),_1om=new T(function(){return B(unCStr("DuplicateRedeem "));}),_1on=new T(function(){return B(unCStr("ExpiredCommitRedeemed "));}),_1oo=new T(function(){return B(unCStr("CommitRedeemed "));}),_1op=new T(function(){return B(unCStr("SuccessfulCommit "));}),_1oq=new T(function(){return B(unCStr("FailedPay "));}),_1or=new T(function(){return B(unCStr("ExpiredPay "));}),_1os=new T(function(){return B(unCStr("SuccessfulPay "));}),_1ot=function(_1ou,_1ov,_1ow){var _1ox=E(_1ov);switch(_1ox._){case 0:var _1oy=function(_1oz){var _1oA=new T(function(){var _1oB=new T(function(){return B(_hA(11,E(_1ox.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1ox.d),_1oz));}))));});return B(_hA(11,E(_1ox.b),new T2(1,_hK,_1oB)));});return new F(function(){return _ih(11,_1ox.a,new T2(1,_hK,_1oA));});};if(_1ou<11){return new F(function(){return _hq(_1os,new T(function(){return B(_1oy(_1ow));},1));});}else{var _1oC=new T(function(){return B(_hq(_1os,new T(function(){return B(_1oy(new T2(1,_hy,_1ow)));},1)));});return new T2(1,_hz,_1oC);}break;case 1:var _1oD=function(_1oE){var _1oF=new T(function(){var _1oG=new T(function(){return B(_hA(11,E(_1ox.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1ox.d),_1oE));}))));});return B(_hA(11,E(_1ox.b),new T2(1,_hK,_1oG)));});return new F(function(){return _ih(11,_1ox.a,new T2(1,_hK,_1oF));});};if(_1ou<11){return new F(function(){return _hq(_1or,new T(function(){return B(_1oD(_1ow));},1));});}else{var _1oH=new T(function(){return B(_hq(_1or,new T(function(){return B(_1oD(new T2(1,_hy,_1ow)));},1)));});return new T2(1,_hz,_1oH);}break;case 2:var _1oI=function(_1oJ){var _1oK=new T(function(){var _1oL=new T(function(){return B(_hA(11,E(_1ox.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1ox.d),_1oJ));}))));});return B(_hA(11,E(_1ox.b),new T2(1,_hK,_1oL)));});return new F(function(){return _ih(11,_1ox.a,new T2(1,_hK,_1oK));});};if(_1ou<11){return new F(function(){return _hq(_1oq,new T(function(){return B(_1oI(_1ow));},1));});}else{var _1oM=new T(function(){return B(_hq(_1oq,new T(function(){return B(_1oI(new T2(1,_hy,_1ow)));},1)));});return new T2(1,_hz,_1oM);}break;case 3:var _1oN=function(_1oO){var _1oP=new T(function(){var _1oQ=new T(function(){return B(_hA(11,E(_1ox.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1ox.c),_1oO));}))));});return B(_hF(11,_1ox.a,new T2(1,_hK,_1oQ)));},1);return new F(function(){return _hq(_1op,_1oP);});};if(_1ou<11){return new F(function(){return _1oN(_1ow);});}else{return new T2(1,_hz,new T(function(){return B(_1oN(new T2(1,_hy,_1ow)));}));}break;case 4:var _1oR=function(_1oS){var _1oT=new T(function(){var _1oU=new T(function(){return B(_hA(11,E(_1ox.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1ox.c),_1oS));}))));});return B(_hF(11,_1ox.a,new T2(1,_hK,_1oU)));},1);return new F(function(){return _hq(_1oo,_1oT);});};if(_1ou<11){return new F(function(){return _1oR(_1ow);});}else{return new T2(1,_hz,new T(function(){return B(_1oR(new T2(1,_hy,_1ow)));}));}break;case 5:var _1oV=function(_1oW){var _1oX=new T(function(){var _1oY=new T(function(){return B(_hA(11,E(_1ox.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1ox.c),_1oW));}))));});return B(_hF(11,_1ox.a,new T2(1,_hK,_1oY)));},1);return new F(function(){return _hq(_1on,_1oX);});};if(_1ou<11){return new F(function(){return _1oV(_1ow);});}else{return new T2(1,_hz,new T(function(){return B(_1oV(new T2(1,_hy,_1ow)));}));}break;case 6:var _1oZ=function(_1p0){return new F(function(){return _hF(11,_1ox.a,new T2(1,_hK,new T(function(){return B(_hA(11,E(_1ox.b),_1p0));})));});};if(_1ou<11){return new F(function(){return _hq(_1om,new T(function(){return B(_1oZ(_1ow));},1));});}else{var _1p1=new T(function(){return B(_hq(_1om,new T(function(){return B(_1oZ(new T2(1,_hy,_1ow)));},1)));});return new T2(1,_hz,_1p1);}break;default:var _1p2=function(_1p3){var _1p4=new T(function(){var _1p5=new T(function(){return B(_hA(11,E(_1ox.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1ox.c),_1p3));}))));});return B(_j6(11,_1ox.a,new T2(1,_hK,_1p5)));},1);return new F(function(){return _hq(_1ol,_1p4);});};if(_1ou<11){return new F(function(){return _1p2(_1ow);});}else{return new T2(1,_hz,new T(function(){return B(_1p2(new T2(1,_hy,_1ow)));}));}}},_1p6=new T(function(){return B(unAppCStr("[]",_1M));}),_1p7=new T2(1,_iP,_1M),_1p8=function(_1p9){var _1pa=E(_1p9);if(!_1pa._){return E(_1p7);}else{var _1pb=new T(function(){return B(_1ot(0,_1pa.a,new T(function(){return B(_1p8(_1pa.b));})));});return new T2(1,_hj,_1pb);}},_1pc=function(_){var _1pd=E(_1cG),_1pe=toJSStr(_1pd),_1pf=eval(E(_16F)),_1pg=_1pf,_1ph=__app1(E(_1pg),_1pe),_1pi=E(_16H),_1pj=__app1(E(_1pg),toJSStr(_1pi)),_1pk=__app0(E(_16G)),_1pl=E(_16I),_1pm=__app1(E(_1pg),toJSStr(_1pl)),_1pn=new T(function(){var _1po=B(_184(B(_l5(_16M,new T(function(){var _1pp=String(_1pm);return fromJSStr(_1pp);})))));if(!_1po._){return E(_16L);}else{if(!E(_1po.b)._){return E(_1po.a);}else{return E(_16K);}}}),_1pq=B(_184(B(_l5(_181,new T(function(){var _1pr=String(_1pj);return fromJSStr(_1pr);})))));if(!_1pq._){return E(_16O);}else{if(!E(_1pq.b)._){var _1ps=E(_1pq.a),_1pt=new T(function(){var _1pu=B(_184(B(_l5(_1co,new T(function(){var _1pv=String(_1pk);return fromJSStr(_1pv);})))));if(!_1pu._){return E(_18c);}else{if(!E(_1pu.b)._){return E(_1pu.a);}else{return E(_18b);}}}),_1pw=new T(function(){var _1px=B(_184(B(_l5(_DG,new T(function(){var _1py=String(_1ph);return fromJSStr(_1py);})))));if(!_1px._){return E(_jT);}else{if(!E(_1px.b)._){var _1pz=E(_1px.a);return new T4(0,new T(function(){return B(_3G(_1pz.a));}),new T(function(){return B(_83(_1pz.b));}),new T(function(){return B(_gT(_1pz.c));}),new T(function(){return B(_dJ(_1pz.d));}));}else{return E(_jR);}}}),_1pA=B(_UO(_1pw,new T(function(){return B(_EV(_1ps.a));}),new T(function(){return B(_dJ(_1ps.b));}),_1pt,new T2(0,_182,_1pn),_1M)),_1pB=function(_,_1pC){var _1pD=function(_,_1pE){var _1pF=E(_1pA.a),_1pG=new T(function(){var _1pH=new T(function(){return B(_hc(_1M,_1pF.b));}),_1pI=new T(function(){return B(_hc(_1M,_1pF.a));});return B(A3(_is,_hk,new T2(1,function(_1pJ){return new F(function(){return _1oi(_1pI,_1pJ);});},new T2(1,function(_1pK){return new F(function(){return _js(_1pH,_1pK);});},_1M)),_jv));}),_1pL=B(_1cI(_1pi,new T2(1,_hz,_1pG),_)),_1pM=B(_1cI(_1pd,_1nJ,_)),_1pN=B(_1cI(_1pl,B(_hA(0,E(_1pn)+1|0,_1M)),_)),_1pO=__app1(E(_1pg),toJSStr(E(_1i3))),_1pP=B(_1nq(new T(function(){var _1pQ=String(_1pO);return fromJSStr(_1pQ);}),_)),_1pR=__app1(E(_1pg),_1pe),_1pS=new T(function(){var _1pT=B(_184(B(_l5(_DG,new T(function(){var _1pU=String(_1pR);return fromJSStr(_1pU);})))));if(!_1pT._){return E(_jT);}else{if(!E(_1pT.b)._){var _1pV=E(_1pT.a);return new T4(0,new T(function(){return B(_3G(_1pV.a));}),new T(function(){return B(_83(_1pV.b));}),new T(function(){return B(_gT(_1pV.c));}),new T(function(){return B(_dJ(_1pV.d));}));}else{return E(_jR);}}});return new F(function(){return _1cp(_1pS,_);});},_1pW=E(_1pA.b);switch(_1pW._){case 0:var _1pX=B(_1cI(_1i3,_1hY,_));return new F(function(){return _1pD(_,_1pX);});break;case 1:var _1pY=B(_1cI(_1i3,B(_1hC(0,_1g1,new T2(1,new T1(3,_1pW.a),new T2(1,new T1(6,_1pW.b),new T2(1,new T1(6,_1pW.c),new T2(1,new T1(6,_1pW.d),new T2(1,new T1(6,_1pW.e),new T2(1,new T1(0,_1pW.f),new T2(1,new T1(0,_1pW.g),_1M))))))))),_));return new F(function(){return _1pD(_,_1pY);});break;case 2:var _1pZ=B(_1cI(_1i3,B(_1hC(0,_1g0,new T2(1,new T1(3,_1pW.a),new T2(1,new T1(0,_1pW.b),_1M)))),_));return new F(function(){return _1pD(_,_1pZ);});break;case 3:var _1q0=B(_1cI(_1i3,B(_1hC(0,_1fZ,new T2(1,new T1(5,_1pW.a),new T2(1,new T1(6,_1pW.b),new T2(1,new T1(6,_1pW.c),new T2(1,new T1(6,_1pW.d),new T2(1,new T1(6,_1pW.e),new T2(1,new T1(0,_1pW.f),_1M)))))))),_));return new F(function(){return _1pD(_,_1q0);});break;case 4:var _1q1=B(_1cI(_1i3,B(_1hC(0,_1fY,new T2(1,new T1(0,_1pW.a),new T2(1,new T1(0,_1pW.b),_1M)))),_));return new F(function(){return _1pD(_,_1q1);});break;case 5:var _1q2=B(_1cI(_1i3,B(_1hC(0,_1fX,new T2(1,new T1(1,_1pW.a),new T2(1,new T1(0,_1pW.b),new T2(1,new T1(0,_1pW.c),_1M))))),_));return new F(function(){return _1pD(_,_1q2);});break;default:var _1q3=B(_1cI(_1i3,B(_1hC(0,_1fW,new T2(1,new T1(1,_1pW.a),new T2(1,new T1(6,_1pW.b),new T2(1,new T1(0,_1pW.c),new T2(1,new T1(0,_1pW.d),_1M)))))),_));return new F(function(){return _1pD(_,_1q3);});}},_1q4=E(_1pA.c);if(!_1q4._){var _1q5=B(_1cI(_1nI,_1p6,_));return new F(function(){return _1pB(_,_1q5);});}else{var _1q6=new T(function(){return B(_1ot(0,_1q4.a,new T(function(){return B(_1p8(_1q4.b));})));}),_1q7=B(_1cI(_1nI,new T2(1,_iQ,_1q6),_));return new F(function(){return _1pB(_,_1q7);});}}else{return E(_16N);}}},_1q8=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1q9=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qa=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qb=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qc=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qd=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qe=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qf=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qg=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qh=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qi=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1qj=function(_){return new F(function(){return __jsNull();});},_1qk=function(_1ql){var _1qm=B(A1(_1ql,_));return E(_1qm);},_1qn=new T(function(){return B(_1qk(_1qj));}),_1qo=new T(function(){return E(_1qn);}),_1qp=function(_){var _1qq=eval(E(_16F)),_1qr=__app1(E(_1qq),toJSStr(E(_1cG))),_1qs=new T(function(){var _1qt=B(_184(B(_l5(_DG,new T(function(){var _1qu=String(_1qr);return fromJSStr(_1qu);})))));if(!_1qt._){return E(_jT);}else{if(!E(_1qt.b)._){var _1qv=E(_1qt.a);return new T4(0,new T(function(){return B(_3G(_1qv.a));}),new T(function(){return B(_83(_1qv.b));}),new T(function(){return B(_gT(_1qv.c));}),new T(function(){return B(_dJ(_1qv.d));}));}else{return E(_jR);}}});return new F(function(){return _1cp(_1qs,_);});},_1qw=function(_){var _1qx=eval(E(_16F)),_1qy=__app1(E(_1qx),toJSStr(E(_1i3))),_1qz=B(_1nq(new T(function(){var _1qA=String(_1qy);return fromJSStr(_1qA);}),_)),_1qB=__createJSFunc(0,function(_){var _1qC=B(_1nM(_));return _1qo;}),_1qD=__app2(E(_1qf),"clear_workspace",_1qB),_1qE=__createJSFunc(0,function(_){var _1qF=B(_1i4(_));return _1qo;}),_1qG=__app2(E(_1qe),"b2c",_1qE),_1qH=__createJSFunc(0,function(_){var _1qI=B(_1nE(_));return _1qo;}),_1qJ=__app2(E(_1qd),"c2b",_1qH),_1qK=function(_1qL){var _1qM=new T(function(){var _1qN=Number(E(_1qL));return jsTrunc(_1qN);}),_1qO=function(_1qP){var _1qQ=new T(function(){var _1qR=Number(E(_1qP));return jsTrunc(_1qR);}),_1qS=function(_1qT){var _1qU=new T(function(){var _1qV=Number(E(_1qT));return jsTrunc(_1qV);}),_1qW=function(_1qX,_){var _1qY=B(_1ei(_1qM,_1qQ,_1qU,new T(function(){var _1qZ=Number(E(_1qX));return jsTrunc(_1qZ);}),_));return _1qo;};return E(_1qW);};return E(_1qS);};return E(_1qO);},_1r0=__createJSFunc(5,E(_1qK)),_1r1=__app2(E(_1qc),"commit",_1r0),_1r2=function(_1r3){var _1r4=new T(function(){var _1r5=Number(E(_1r3));return jsTrunc(_1r5);}),_1r6=function(_1r7){var _1r8=new T(function(){var _1r9=Number(E(_1r7));return jsTrunc(_1r9);}),_1ra=function(_1rb,_){var _1rc=B(_1e0(_1r4,_1r8,new T(function(){var _1rd=Number(E(_1rb));return jsTrunc(_1rd);}),_));return _1qo;};return E(_1ra);};return E(_1r6);},_1re=__createJSFunc(4,E(_1r2)),_1rf=__app2(E(_1qb),"redeem",_1re),_1rg=function(_1rh){var _1ri=new T(function(){var _1rj=Number(E(_1rh));return jsTrunc(_1rj);}),_1rk=function(_1rl){var _1rm=new T(function(){var _1rn=Number(E(_1rl));return jsTrunc(_1rn);}),_1ro=function(_1rp,_){var _1rq=B(_1cN(_1ri,_1rm,new T(function(){var _1rr=Number(E(_1rp));return jsTrunc(_1rr);}),_));return _1qo;};return E(_1ro);};return E(_1rk);},_1rs=__createJSFunc(4,E(_1rg)),_1rt=__app2(E(_1qa),"claim",_1rs),_1ru=function(_1rv){var _1rw=new T(function(){var _1rx=Number(E(_1rv));return jsTrunc(_1rx);}),_1ry=function(_1rz){var _1rA=new T(function(){var _1rB=Number(E(_1rz));return jsTrunc(_1rB);}),_1rC=function(_1rD,_){var _1rE=B(_1fv(_1rw,_1rA,new T(function(){var _1rF=Number(E(_1rD));return jsTrunc(_1rF);}),_));return _1qo;};return E(_1rC);};return E(_1ry);},_1rG=__createJSFunc(4,E(_1ru)),_1rH=__app2(E(_1q9),"choose",_1rG),_1rI=__createJSFunc(0,function(_){var _1rJ=B(_1pc(_));return _1qo;}),_1rK=__app2(E(_1q8),"execute",_1rI),_1rL=__createJSFunc(0,function(_){var _1rM=B(_1qp(_));return _1qo;}),_1rN=__app2(E(_1qi),"refreshActions",_1rL),_1rO=function(_1rP,_){var _1rQ=B(_1fr(new T(function(){var _1rR=String(E(_1rP));return fromJSStr(_1rR);}),_));return _1qo;},_1rS=__createJSFunc(2,E(_1rO)),_1rT=__app2(E(_1qh),"addAction",_1rS),_1rU=function(_1rV){var _1rW=new T(function(){var _1rX=String(E(_1rV));return fromJSStr(_1rX);}),_1rY=function(_1rZ,_){var _1s0=B(_1fQ(_1rW,new T(function(){var _1s1=Number(E(_1rZ));return jsTrunc(_1s1);}),_));return _1qo;};return E(_1rY);},_1s2=__createJSFunc(3,E(_1rU)),_1s3=__app2(E(_1qg),"addActionWithNum",_1s2),_1s4=__app1(E(_1qx),toJSStr(E(_1cG))),_1s5=new T(function(){var _1s6=B(_184(B(_l5(_DG,new T(function(){var _1s7=String(_1s4);return fromJSStr(_1s7);})))));if(!_1s6._){return E(_jT);}else{if(!E(_1s6.b)._){var _1s8=E(_1s6.a);return new T4(0,new T(function(){return B(_3G(_1s8.a));}),new T(function(){return B(_83(_1s8.b));}),new T(function(){return B(_gT(_1s8.c));}),new T(function(){return B(_dJ(_1s8.d));}));}else{return E(_jR);}}}),_1s9=B(_1cp(_1s5,_));return _h9;},_1sa=function(_){return new F(function(){return _1qw(_);});};
var hasteMain = function() {B(A(_1sa, [0]));};window.onload = hasteMain;
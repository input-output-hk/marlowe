"use strict";
var __haste_prog_id = '02b3409559bdac26fffb31f6d53816f8e16621ff7ce216879f2b4fc70c04df9d';
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

var _0=new T0(1),_1=__Z,_2=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_3=function(_4){return new F(function(){return err(_2);});},_5=new T(function(){return B(_3(_));}),_6=function(_7,_8,_9,_a){var _b=E(_9);if(!_b._){var _c=_b.a,_d=E(_a);if(!_d._){var _e=_d.a,_f=_d.b,_g=_d.c;if(_e<=(imul(3,_c)|0)){return new T5(0,(1+_c|0)+_e|0,E(_7),_8,E(_b),E(_d));}else{var _h=E(_d.d);if(!_h._){var _i=_h.a,_j=_h.b,_k=_h.c,_l=_h.d,_m=E(_d.e);if(!_m._){var _n=_m.a;if(_i>=(imul(2,_n)|0)){var _o=function(_p){var _q=E(_7),_r=E(_h.e);return (_r._==0)?new T5(0,(1+_c|0)+_e|0,E(_j),_k,E(new T5(0,(1+_c|0)+_p|0,E(_q),_8,E(_b),E(_l))),E(new T5(0,(1+_n|0)+_r.a|0,E(_f),_g,E(_r),E(_m)))):new T5(0,(1+_c|0)+_e|0,E(_j),_k,E(new T5(0,(1+_c|0)+_p|0,E(_q),_8,E(_b),E(_l))),E(new T5(0,1+_n|0,E(_f),_g,E(_0),E(_m))));},_s=E(_l);if(!_s._){return new F(function(){return _o(_s.a);});}else{return new F(function(){return _o(0);});}}else{return new T5(0,(1+_c|0)+_e|0,E(_f),_g,E(new T5(0,(1+_c|0)+_i|0,E(_7),_8,E(_b),E(_h))),E(_m));}}else{return E(_5);}}else{return E(_5);}}}else{return new T5(0,1+_c|0,E(_7),_8,E(_b),E(_0));}}else{var _t=E(_a);if(!_t._){var _u=_t.a,_v=_t.b,_w=_t.c,_x=_t.e,_y=E(_t.d);if(!_y._){var _z=_y.a,_A=_y.b,_B=_y.c,_C=_y.d,_D=E(_x);if(!_D._){var _E=_D.a;if(_z>=(imul(2,_E)|0)){var _F=function(_G){var _H=E(_7),_I=E(_y.e);return (_I._==0)?new T5(0,1+_u|0,E(_A),_B,E(new T5(0,1+_G|0,E(_H),_8,E(_0),E(_C))),E(new T5(0,(1+_E|0)+_I.a|0,E(_v),_w,E(_I),E(_D)))):new T5(0,1+_u|0,E(_A),_B,E(new T5(0,1+_G|0,E(_H),_8,E(_0),E(_C))),E(new T5(0,1+_E|0,E(_v),_w,E(_0),E(_D))));},_J=E(_C);if(!_J._){return new F(function(){return _F(_J.a);});}else{return new F(function(){return _F(0);});}}else{return new T5(0,1+_u|0,E(_v),_w,E(new T5(0,1+_z|0,E(_7),_8,E(_0),E(_y))),E(_D));}}else{return new T5(0,3,E(_A),_B,E(new T5(0,1,E(_7),_8,E(_0),E(_0))),E(new T5(0,1,E(_v),_w,E(_0),E(_0))));}}else{var _K=E(_x);return (_K._==0)?new T5(0,3,E(_v),_w,E(new T5(0,1,E(_7),_8,E(_0),E(_0))),E(_K)):new T5(0,2,E(_7),_8,E(_0),E(_t));}}else{return new T5(0,1,E(_7),_8,E(_0),E(_0));}}},_L=function(_M,_N){return new T5(0,1,E(_M),_N,E(_0),E(_0));},_O=function(_P,_Q,_R){var _S=E(_R);if(!_S._){return new F(function(){return _6(_S.b,_S.c,_S.d,B(_O(_P,_Q,_S.e)));});}else{return new F(function(){return _L(_P,_Q);});}},_T=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_U=function(_V){return new F(function(){return err(_T);});},_W=new T(function(){return B(_U(_));}),_X=function(_Y,_Z,_10,_11){var _12=E(_11);if(!_12._){var _13=_12.a,_14=E(_10);if(!_14._){var _15=_14.a,_16=_14.b,_17=_14.c;if(_15<=(imul(3,_13)|0)){return new T5(0,(1+_15|0)+_13|0,E(_Y),_Z,E(_14),E(_12));}else{var _18=E(_14.d);if(!_18._){var _19=_18.a,_1a=E(_14.e);if(!_1a._){var _1b=_1a.a,_1c=_1a.b,_1d=_1a.c,_1e=_1a.d;if(_1b>=(imul(2,_19)|0)){var _1f=function(_1g){var _1h=E(_1a.e);return (_1h._==0)?new T5(0,(1+_15|0)+_13|0,E(_1c),_1d,E(new T5(0,(1+_19|0)+_1g|0,E(_16),_17,E(_18),E(_1e))),E(new T5(0,(1+_13|0)+_1h.a|0,E(_Y),_Z,E(_1h),E(_12)))):new T5(0,(1+_15|0)+_13|0,E(_1c),_1d,E(new T5(0,(1+_19|0)+_1g|0,E(_16),_17,E(_18),E(_1e))),E(new T5(0,1+_13|0,E(_Y),_Z,E(_0),E(_12))));},_1i=E(_1e);if(!_1i._){return new F(function(){return _1f(_1i.a);});}else{return new F(function(){return _1f(0);});}}else{return new T5(0,(1+_15|0)+_13|0,E(_16),_17,E(_18),E(new T5(0,(1+_13|0)+_1b|0,E(_Y),_Z,E(_1a),E(_12))));}}else{return E(_W);}}else{return E(_W);}}}else{return new T5(0,1+_13|0,E(_Y),_Z,E(_0),E(_12));}}else{var _1j=E(_10);if(!_1j._){var _1k=_1j.a,_1l=_1j.b,_1m=_1j.c,_1n=_1j.e,_1o=E(_1j.d);if(!_1o._){var _1p=_1o.a,_1q=E(_1n);if(!_1q._){var _1r=_1q.a,_1s=_1q.b,_1t=_1q.c,_1u=_1q.d;if(_1r>=(imul(2,_1p)|0)){var _1v=function(_1w){var _1x=E(_1q.e);return (_1x._==0)?new T5(0,1+_1k|0,E(_1s),_1t,E(new T5(0,(1+_1p|0)+_1w|0,E(_1l),_1m,E(_1o),E(_1u))),E(new T5(0,1+_1x.a|0,E(_Y),_Z,E(_1x),E(_0)))):new T5(0,1+_1k|0,E(_1s),_1t,E(new T5(0,(1+_1p|0)+_1w|0,E(_1l),_1m,E(_1o),E(_1u))),E(new T5(0,1,E(_Y),_Z,E(_0),E(_0))));},_1y=E(_1u);if(!_1y._){return new F(function(){return _1v(_1y.a);});}else{return new F(function(){return _1v(0);});}}else{return new T5(0,1+_1k|0,E(_1l),_1m,E(_1o),E(new T5(0,1+_1r|0,E(_Y),_Z,E(_1q),E(_0))));}}else{return new T5(0,3,E(_1l),_1m,E(_1o),E(new T5(0,1,E(_Y),_Z,E(_0),E(_0))));}}else{var _1z=E(_1n);return (_1z._==0)?new T5(0,3,E(_1z.b),_1z.c,E(new T5(0,1,E(_1l),_1m,E(_0),E(_0))),E(new T5(0,1,E(_Y),_Z,E(_0),E(_0)))):new T5(0,2,E(_Y),_Z,E(_1j),E(_0));}}else{return new T5(0,1,E(_Y),_Z,E(_0),E(_0));}}},_1A=function(_1B,_1C,_1D){var _1E=E(_1D);if(!_1E._){return new F(function(){return _X(_1E.b,_1E.c,B(_1A(_1B,_1C,_1E.d)),_1E.e);});}else{return new F(function(){return _L(_1B,_1C);});}},_1F=function(_1G,_1H,_1I,_1J,_1K,_1L,_1M){return new F(function(){return _X(_1J,_1K,B(_1A(_1G,_1H,_1L)),_1M);});},_1N=function(_1O,_1P,_1Q,_1R,_1S,_1T,_1U,_1V){var _1W=E(_1Q);if(!_1W._){var _1X=_1W.a,_1Y=_1W.b,_1Z=_1W.c,_20=_1W.d,_21=_1W.e;if((imul(3,_1X)|0)>=_1R){if((imul(3,_1R)|0)>=_1X){return new T5(0,(_1X+_1R|0)+1|0,E(_1O),_1P,E(_1W),E(new T5(0,_1R,E(_1S),_1T,E(_1U),E(_1V))));}else{return new F(function(){return _6(_1Y,_1Z,_20,B(_1N(_1O,_1P,_21,_1R,_1S,_1T,_1U,_1V)));});}}else{return new F(function(){return _X(_1S,_1T,B(_22(_1O,_1P,_1X,_1Y,_1Z,_20,_21,_1U)),_1V);});}}else{return new F(function(){return _1F(_1O,_1P,_1R,_1S,_1T,_1U,_1V);});}},_22=function(_23,_24,_25,_26,_27,_28,_29,_2a){var _2b=E(_2a);if(!_2b._){var _2c=_2b.a,_2d=_2b.b,_2e=_2b.c,_2f=_2b.d,_2g=_2b.e;if((imul(3,_25)|0)>=_2c){if((imul(3,_2c)|0)>=_25){return new T5(0,(_25+_2c|0)+1|0,E(_23),_24,E(new T5(0,_25,E(_26),_27,E(_28),E(_29))),E(_2b));}else{return new F(function(){return _6(_26,_27,_28,B(_1N(_23,_24,_29,_2c,_2d,_2e,_2f,_2g)));});}}else{return new F(function(){return _X(_2d,_2e,B(_22(_23,_24,_25,_26,_27,_28,_29,_2f)),_2g);});}}else{return new F(function(){return _O(_23,_24,new T5(0,_25,E(_26),_27,E(_28),E(_29)));});}},_2h=function(_2i,_2j,_2k,_2l){var _2m=E(_2k);if(!_2m._){var _2n=_2m.a,_2o=_2m.b,_2p=_2m.c,_2q=_2m.d,_2r=_2m.e,_2s=E(_2l);if(!_2s._){var _2t=_2s.a,_2u=_2s.b,_2v=_2s.c,_2w=_2s.d,_2x=_2s.e;if((imul(3,_2n)|0)>=_2t){if((imul(3,_2t)|0)>=_2n){return new T5(0,(_2n+_2t|0)+1|0,E(_2i),_2j,E(_2m),E(_2s));}else{return new F(function(){return _6(_2o,_2p,_2q,B(_1N(_2i,_2j,_2r,_2t,_2u,_2v,_2w,_2x)));});}}else{return new F(function(){return _X(_2u,_2v,B(_22(_2i,_2j,_2n,_2o,_2p,_2q,_2r,_2w)),_2x);});}}else{return new F(function(){return _O(_2i,_2j,_2m);});}}else{return new F(function(){return _1A(_2i,_2j,_2l);});}},_2y=function(_2z,_2A,_2B,_2C,_2D){var _2E=E(_2z);if(_2E==1){var _2F=E(_2D);if(!_2F._){return new T3(0,new T5(0,1,E(new T2(0,_2A,_2B)),_2C,E(_0),E(_0)),_1,_1);}else{var _2G=E(E(_2F.a).a),_2H=E(_2A),_2I=E(_2G.a);return (_2H>=_2I)?(_2H!=_2I)?new T3(0,new T5(0,1,E(new T2(0,_2H,_2B)),_2C,E(_0),E(_0)),_1,_2F):(_2B<E(_2G.b))?new T3(0,new T5(0,1,E(new T2(0,_2H,_2B)),_2C,E(_0),E(_0)),_2F,_1):new T3(0,new T5(0,1,E(new T2(0,_2H,_2B)),_2C,E(_0),E(_0)),_1,_2F):new T3(0,new T5(0,1,E(new T2(0,_2H,_2B)),_2C,E(_0),E(_0)),_2F,_1);}}else{var _2J=B(_2y(_2E>>1,_2A,_2B,_2C,_2D)),_2K=_2J.a,_2L=_2J.c,_2M=E(_2J.b);if(!_2M._){return new T3(0,_2K,_1,_2L);}else{var _2N=E(_2M.a),_2O=_2N.a,_2P=_2N.b,_2Q=E(_2M.b);if(!_2Q._){return new T3(0,new T(function(){return B(_O(_2O,_2P,_2K));}),_1,_2L);}else{var _2R=_2Q.b,_2S=E(_2Q.a),_2T=_2S.b,_2U=E(_2O),_2V=E(_2S.a),_2W=_2V.b,_2X=E(_2U.a),_2Y=E(_2V.a);if(_2X>=_2Y){if(_2X!=_2Y){return new T3(0,_2K,_1,_2M);}else{var _2Z=E(_2W);if(E(_2U.b)<_2Z){var _30=B(_2y(_2E>>1,_2Y,_2Z,_2T,_2R));return new T3(0,new T(function(){return B(_2h(_2U,_2P,_2K,_30.a));}),_30.b,_30.c);}else{return new T3(0,_2K,_1,_2M);}}}else{var _31=B(_32(_2E>>1,_2Y,_2W,_2T,_2R));return new T3(0,new T(function(){return B(_2h(_2U,_2P,_2K,_31.a));}),_31.b,_31.c);}}}}},_32=function(_33,_34,_35,_36,_37){var _38=E(_33);if(_38==1){var _39=E(_37);if(!_39._){return new T3(0,new T5(0,1,E(new T2(0,_34,_35)),_36,E(_0),E(_0)),_1,_1);}else{var _3a=E(E(_39.a).a),_3b=E(_34),_3c=E(_3a.a);if(_3b>=_3c){if(_3b!=_3c){return new T3(0,new T5(0,1,E(new T2(0,_3b,_35)),_36,E(_0),E(_0)),_1,_39);}else{var _3d=E(_35);return (_3d<E(_3a.b))?new T3(0,new T5(0,1,E(new T2(0,_3b,_3d)),_36,E(_0),E(_0)),_39,_1):new T3(0,new T5(0,1,E(new T2(0,_3b,_3d)),_36,E(_0),E(_0)),_1,_39);}}else{return new T3(0,new T5(0,1,E(new T2(0,_3b,_35)),_36,E(_0),E(_0)),_39,_1);}}}else{var _3e=B(_32(_38>>1,_34,_35,_36,_37)),_3f=_3e.a,_3g=_3e.c,_3h=E(_3e.b);if(!_3h._){return new T3(0,_3f,_1,_3g);}else{var _3i=E(_3h.a),_3j=_3i.a,_3k=_3i.b,_3l=E(_3h.b);if(!_3l._){return new T3(0,new T(function(){return B(_O(_3j,_3k,_3f));}),_1,_3g);}else{var _3m=_3l.b,_3n=E(_3l.a),_3o=_3n.b,_3p=E(_3j),_3q=E(_3n.a),_3r=_3q.b,_3s=E(_3p.a),_3t=E(_3q.a);if(_3s>=_3t){if(_3s!=_3t){return new T3(0,_3f,_1,_3h);}else{var _3u=E(_3r);if(E(_3p.b)<_3u){var _3v=B(_2y(_38>>1,_3t,_3u,_3o,_3m));return new T3(0,new T(function(){return B(_2h(_3p,_3k,_3f,_3v.a));}),_3v.b,_3v.c);}else{return new T3(0,_3f,_1,_3h);}}}else{var _3w=B(_32(_38>>1,_3t,_3r,_3o,_3m));return new T3(0,new T(function(){return B(_2h(_3p,_3k,_3f,_3w.a));}),_3w.b,_3w.c);}}}}},_3x=function(_3y,_3z,_3A,_3B,_3C){var _3D=E(_3C);if(!_3D._){var _3E=_3D.c,_3F=_3D.d,_3G=_3D.e,_3H=E(_3D.b),_3I=E(_3H.a);if(_3y>=_3I){if(_3y!=_3I){return new F(function(){return _6(_3H,_3E,_3F,B(_3x(_3y,_,_3A,_3B,_3G)));});}else{var _3J=E(_3H.b);if(_3A>=_3J){if(_3A!=_3J){return new F(function(){return _6(_3H,_3E,_3F,B(_3x(_3y,_,_3A,_3B,_3G)));});}else{return new T5(0,_3D.a,E(new T2(0,_3y,_3A)),_3B,E(_3F),E(_3G));}}else{return new F(function(){return _X(_3H,_3E,B(_3x(_3y,_,_3A,_3B,_3F)),_3G);});}}}else{return new F(function(){return _X(_3H,_3E,B(_3x(_3y,_,_3A,_3B,_3F)),_3G);});}}else{return new T5(0,1,E(new T2(0,_3y,_3A)),_3B,E(_0),E(_0));}},_3K=function(_3L,_3M,_3N,_3O,_3P){var _3Q=E(_3P);if(!_3Q._){var _3R=_3Q.c,_3S=_3Q.d,_3T=_3Q.e,_3U=E(_3Q.b),_3V=E(_3U.a);if(_3L>=_3V){if(_3L!=_3V){return new F(function(){return _6(_3U,_3R,_3S,B(_3K(_3L,_,_3N,_3O,_3T)));});}else{var _3W=E(_3N),_3X=E(_3U.b);if(_3W>=_3X){if(_3W!=_3X){return new F(function(){return _6(_3U,_3R,_3S,B(_3x(_3L,_,_3W,_3O,_3T)));});}else{return new T5(0,_3Q.a,E(new T2(0,_3L,_3W)),_3O,E(_3S),E(_3T));}}else{return new F(function(){return _X(_3U,_3R,B(_3x(_3L,_,_3W,_3O,_3S)),_3T);});}}}else{return new F(function(){return _X(_3U,_3R,B(_3K(_3L,_,_3N,_3O,_3S)),_3T);});}}else{return new T5(0,1,E(new T2(0,_3L,_3N)),_3O,E(_0),E(_0));}},_3Y=function(_3Z,_40,_41,_42){var _43=E(_42);if(!_43._){var _44=_43.c,_45=_43.d,_46=_43.e,_47=E(_43.b),_48=E(_3Z),_49=E(_47.a);if(_48>=_49){if(_48!=_49){return new F(function(){return _6(_47,_44,_45,B(_3K(_48,_,_40,_41,_46)));});}else{var _4a=E(_40),_4b=E(_47.b);if(_4a>=_4b){if(_4a!=_4b){return new F(function(){return _6(_47,_44,_45,B(_3x(_48,_,_4a,_41,_46)));});}else{return new T5(0,_43.a,E(new T2(0,_48,_4a)),_41,E(_45),E(_46));}}else{return new F(function(){return _X(_47,_44,B(_3x(_48,_,_4a,_41,_45)),_46);});}}}else{return new F(function(){return _X(_47,_44,B(_3K(_48,_,_40,_41,_45)),_46);});}}else{return new T5(0,1,E(new T2(0,_3Z,_40)),_41,E(_0),E(_0));}},_4c=function(_4d,_4e){while(1){var _4f=E(_4e);if(!_4f._){return E(_4d);}else{var _4g=E(_4f.a),_4h=E(_4g.a),_4i=B(_3Y(_4h.a,_4h.b,_4g.b,_4d));_4d=_4i;_4e=_4f.b;continue;}}},_4j=function(_4k,_4l,_4m,_4n,_4o){return new F(function(){return _4c(B(_3Y(_4l,_4m,_4n,_4k)),_4o);});},_4p=function(_4q,_4r,_4s){var _4t=E(_4r),_4u=E(_4t.a);return new F(function(){return _4c(B(_3Y(_4u.a,_4u.b,_4t.b,_4q)),_4s);});},_4v=function(_4w,_4x,_4y){var _4z=E(_4y);if(!_4z._){return E(_4x);}else{var _4A=E(_4z.a),_4B=_4A.a,_4C=_4A.b,_4D=E(_4z.b);if(!_4D._){return new F(function(){return _O(_4B,_4C,_4x);});}else{var _4E=E(_4D.a),_4F=E(_4B),_4G=_4F.b,_4H=E(_4E.a),_4I=_4H.b,_4J=E(_4F.a),_4K=E(_4H.a),_4L=function(_4M){var _4N=B(_32(_4w,_4K,_4I,_4E.b,_4D.b)),_4O=_4N.a,_4P=E(_4N.c);if(!_4P._){return new F(function(){return _4v(_4w<<1,B(_2h(_4F,_4C,_4x,_4O)),_4N.b);});}else{return new F(function(){return _4p(B(_2h(_4F,_4C,_4x,_4O)),_4P.a,_4P.b);});}};if(_4J>=_4K){if(_4J!=_4K){return new F(function(){return _4j(_4x,_4J,_4G,_4C,_4D);});}else{var _4Q=E(_4G);if(_4Q<E(_4I)){return new F(function(){return _4L(_);});}else{return new F(function(){return _4j(_4x,_4J,_4Q,_4C,_4D);});}}}else{return new F(function(){return _4L(_);});}}}},_4R=function(_4S,_4T,_4U,_4V,_4W,_4X){var _4Y=E(_4X);if(!_4Y._){return new F(function(){return _O(new T2(0,_4U,_4V),_4W,_4T);});}else{var _4Z=E(_4Y.a),_50=E(_4Z.a),_51=_50.b,_52=E(_4U),_53=E(_50.a),_54=function(_55){var _56=B(_32(_4S,_53,_51,_4Z.b,_4Y.b)),_57=_56.a,_58=E(_56.c);if(!_58._){return new F(function(){return _4v(_4S<<1,B(_2h(new T2(0,_52,_4V),_4W,_4T,_57)),_56.b);});}else{return new F(function(){return _4p(B(_2h(new T2(0,_52,_4V),_4W,_4T,_57)),_58.a,_58.b);});}};if(_52>=_53){if(_52!=_53){return new F(function(){return _4j(_4T,_52,_4V,_4W,_4Y);});}else{if(_4V<E(_51)){return new F(function(){return _54(_);});}else{return new F(function(){return _4j(_4T,_52,_4V,_4W,_4Y);});}}}else{return new F(function(){return _54(_);});}}},_59=function(_5a,_5b,_5c,_5d,_5e,_5f){var _5g=E(_5f);if(!_5g._){return new F(function(){return _O(new T2(0,_5c,_5d),_5e,_5b);});}else{var _5h=E(_5g.a),_5i=E(_5h.a),_5j=_5i.b,_5k=E(_5c),_5l=E(_5i.a),_5m=function(_5n){var _5o=B(_32(_5a,_5l,_5j,_5h.b,_5g.b)),_5p=_5o.a,_5q=E(_5o.c);if(!_5q._){return new F(function(){return _4v(_5a<<1,B(_2h(new T2(0,_5k,_5d),_5e,_5b,_5p)),_5o.b);});}else{return new F(function(){return _4p(B(_2h(new T2(0,_5k,_5d),_5e,_5b,_5p)),_5q.a,_5q.b);});}};if(_5k>=_5l){if(_5k!=_5l){return new F(function(){return _4j(_5b,_5k,_5d,_5e,_5g);});}else{var _5r=E(_5d);if(_5r<E(_5j)){return new F(function(){return _5m(_);});}else{return new F(function(){return _4j(_5b,_5k,_5r,_5e,_5g);});}}}else{return new F(function(){return _5m(_);});}}},_5s=function(_5t){var _5u=E(_5t);if(!_5u._){return new T0(1);}else{var _5v=E(_5u.a),_5w=_5v.a,_5x=_5v.b,_5y=E(_5u.b);if(!_5y._){return new T5(0,1,E(_5w),_5x,E(_0),E(_0));}else{var _5z=_5y.b,_5A=E(_5y.a),_5B=_5A.b,_5C=E(_5w),_5D=E(_5A.a),_5E=_5D.b,_5F=E(_5C.a),_5G=E(_5D.a);if(_5F>=_5G){if(_5F!=_5G){return new F(function(){return _4j(new T5(0,1,E(_5C),_5x,E(_0),E(_0)),_5G,_5E,_5B,_5z);});}else{var _5H=E(_5E);if(E(_5C.b)<_5H){return new F(function(){return _4R(1,new T5(0,1,E(_5C),_5x,E(_0),E(_0)),_5G,_5H,_5B,_5z);});}else{return new F(function(){return _4j(new T5(0,1,E(_5C),_5x,E(_0),E(_0)),_5G,_5H,_5B,_5z);});}}}else{return new F(function(){return _59(1,new T5(0,1,E(_5C),_5x,E(_0),E(_0)),_5G,_5E,_5B,_5z);});}}}},_5I=new T0(1),_5J=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_5K=function(_5L){return new F(function(){return err(_5J);});},_5M=new T(function(){return B(_5K(_));}),_5N=function(_5O,_5P,_5Q){var _5R=E(_5P);if(!_5R._){var _5S=_5R.a,_5T=E(_5Q);if(!_5T._){var _5U=_5T.a,_5V=_5T.b;if(_5U<=(imul(3,_5S)|0)){return new T4(0,(1+_5S|0)+_5U|0,E(_5O),E(_5R),E(_5T));}else{var _5W=E(_5T.c);if(!_5W._){var _5X=_5W.a,_5Y=_5W.b,_5Z=_5W.c,_60=E(_5T.d);if(!_60._){var _61=_60.a;if(_5X>=(imul(2,_61)|0)){var _62=function(_63){var _64=E(_5O),_65=E(_5W.d);return (_65._==0)?new T4(0,(1+_5S|0)+_5U|0,E(_5Y),E(new T4(0,(1+_5S|0)+_63|0,E(_64),E(_5R),E(_5Z))),E(new T4(0,(1+_61|0)+_65.a|0,E(_5V),E(_65),E(_60)))):new T4(0,(1+_5S|0)+_5U|0,E(_5Y),E(new T4(0,(1+_5S|0)+_63|0,E(_64),E(_5R),E(_5Z))),E(new T4(0,1+_61|0,E(_5V),E(_5I),E(_60))));},_66=E(_5Z);if(!_66._){return new F(function(){return _62(_66.a);});}else{return new F(function(){return _62(0);});}}else{return new T4(0,(1+_5S|0)+_5U|0,E(_5V),E(new T4(0,(1+_5S|0)+_5X|0,E(_5O),E(_5R),E(_5W))),E(_60));}}else{return E(_5M);}}else{return E(_5M);}}}else{return new T4(0,1+_5S|0,E(_5O),E(_5R),E(_5I));}}else{var _67=E(_5Q);if(!_67._){var _68=_67.a,_69=_67.b,_6a=_67.d,_6b=E(_67.c);if(!_6b._){var _6c=_6b.a,_6d=_6b.b,_6e=_6b.c,_6f=E(_6a);if(!_6f._){var _6g=_6f.a;if(_6c>=(imul(2,_6g)|0)){var _6h=function(_6i){var _6j=E(_5O),_6k=E(_6b.d);return (_6k._==0)?new T4(0,1+_68|0,E(_6d),E(new T4(0,1+_6i|0,E(_6j),E(_5I),E(_6e))),E(new T4(0,(1+_6g|0)+_6k.a|0,E(_69),E(_6k),E(_6f)))):new T4(0,1+_68|0,E(_6d),E(new T4(0,1+_6i|0,E(_6j),E(_5I),E(_6e))),E(new T4(0,1+_6g|0,E(_69),E(_5I),E(_6f))));},_6l=E(_6e);if(!_6l._){return new F(function(){return _6h(_6l.a);});}else{return new F(function(){return _6h(0);});}}else{return new T4(0,1+_68|0,E(_69),E(new T4(0,1+_6c|0,E(_5O),E(_5I),E(_6b))),E(_6f));}}else{return new T4(0,3,E(_6d),E(new T4(0,1,E(_5O),E(_5I),E(_5I))),E(new T4(0,1,E(_69),E(_5I),E(_5I))));}}else{var _6m=E(_6a);return (_6m._==0)?new T4(0,3,E(_69),E(new T4(0,1,E(_5O),E(_5I),E(_5I))),E(_6m)):new T4(0,2,E(_5O),E(_5I),E(_67));}}else{return new T4(0,1,E(_5O),E(_5I),E(_5I));}}},_6n=function(_6o){return new T4(0,1,E(_6o),E(_5I),E(_5I));},_6p=function(_6q,_6r){var _6s=E(_6r);if(!_6s._){return new F(function(){return _5N(_6s.b,_6s.c,B(_6p(_6q,_6s.d)));});}else{return new F(function(){return _6n(_6q);});}},_6t=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_6u=function(_6v){return new F(function(){return err(_6t);});},_6w=new T(function(){return B(_6u(_));}),_6x=function(_6y,_6z,_6A){var _6B=E(_6A);if(!_6B._){var _6C=_6B.a,_6D=E(_6z);if(!_6D._){var _6E=_6D.a,_6F=_6D.b;if(_6E<=(imul(3,_6C)|0)){return new T4(0,(1+_6E|0)+_6C|0,E(_6y),E(_6D),E(_6B));}else{var _6G=E(_6D.c);if(!_6G._){var _6H=_6G.a,_6I=E(_6D.d);if(!_6I._){var _6J=_6I.a,_6K=_6I.b,_6L=_6I.c;if(_6J>=(imul(2,_6H)|0)){var _6M=function(_6N){var _6O=E(_6I.d);return (_6O._==0)?new T4(0,(1+_6E|0)+_6C|0,E(_6K),E(new T4(0,(1+_6H|0)+_6N|0,E(_6F),E(_6G),E(_6L))),E(new T4(0,(1+_6C|0)+_6O.a|0,E(_6y),E(_6O),E(_6B)))):new T4(0,(1+_6E|0)+_6C|0,E(_6K),E(new T4(0,(1+_6H|0)+_6N|0,E(_6F),E(_6G),E(_6L))),E(new T4(0,1+_6C|0,E(_6y),E(_5I),E(_6B))));},_6P=E(_6L);if(!_6P._){return new F(function(){return _6M(_6P.a);});}else{return new F(function(){return _6M(0);});}}else{return new T4(0,(1+_6E|0)+_6C|0,E(_6F),E(_6G),E(new T4(0,(1+_6C|0)+_6J|0,E(_6y),E(_6I),E(_6B))));}}else{return E(_6w);}}else{return E(_6w);}}}else{return new T4(0,1+_6C|0,E(_6y),E(_5I),E(_6B));}}else{var _6Q=E(_6z);if(!_6Q._){var _6R=_6Q.a,_6S=_6Q.b,_6T=_6Q.d,_6U=E(_6Q.c);if(!_6U._){var _6V=_6U.a,_6W=E(_6T);if(!_6W._){var _6X=_6W.a,_6Y=_6W.b,_6Z=_6W.c;if(_6X>=(imul(2,_6V)|0)){var _70=function(_71){var _72=E(_6W.d);return (_72._==0)?new T4(0,1+_6R|0,E(_6Y),E(new T4(0,(1+_6V|0)+_71|0,E(_6S),E(_6U),E(_6Z))),E(new T4(0,1+_72.a|0,E(_6y),E(_72),E(_5I)))):new T4(0,1+_6R|0,E(_6Y),E(new T4(0,(1+_6V|0)+_71|0,E(_6S),E(_6U),E(_6Z))),E(new T4(0,1,E(_6y),E(_5I),E(_5I))));},_73=E(_6Z);if(!_73._){return new F(function(){return _70(_73.a);});}else{return new F(function(){return _70(0);});}}else{return new T4(0,1+_6R|0,E(_6S),E(_6U),E(new T4(0,1+_6X|0,E(_6y),E(_6W),E(_5I))));}}else{return new T4(0,3,E(_6S),E(_6U),E(new T4(0,1,E(_6y),E(_5I),E(_5I))));}}else{var _74=E(_6T);return (_74._==0)?new T4(0,3,E(_74.b),E(new T4(0,1,E(_6S),E(_5I),E(_5I))),E(new T4(0,1,E(_6y),E(_5I),E(_5I)))):new T4(0,2,E(_6y),E(_6Q),E(_5I));}}else{return new T4(0,1,E(_6y),E(_5I),E(_5I));}}},_75=function(_76,_77){var _78=E(_77);if(!_78._){return new F(function(){return _6x(_78.b,B(_75(_76,_78.c)),_78.d);});}else{return new F(function(){return _6n(_76);});}},_79=function(_7a,_7b,_7c,_7d,_7e){return new F(function(){return _5N(_7c,_7d,B(_6p(_7a,_7e)));});},_7f=function(_7g,_7h,_7i,_7j,_7k){return new F(function(){return _6x(_7i,B(_75(_7g,_7j)),_7k);});},_7l=function(_7m,_7n,_7o,_7p,_7q,_7r){var _7s=E(_7n);if(!_7s._){var _7t=_7s.a,_7u=_7s.b,_7v=_7s.c,_7w=_7s.d;if((imul(3,_7t)|0)>=_7o){if((imul(3,_7o)|0)>=_7t){return new T4(0,(_7t+_7o|0)+1|0,E(_7m),E(_7s),E(new T4(0,_7o,E(_7p),E(_7q),E(_7r))));}else{return new F(function(){return _5N(_7u,_7v,B(_7l(_7m,_7w,_7o,_7p,_7q,_7r)));});}}else{return new F(function(){return _6x(_7p,B(_7x(_7m,_7t,_7u,_7v,_7w,_7q)),_7r);});}}else{return new F(function(){return _7f(_7m,_7o,_7p,_7q,_7r);});}},_7x=function(_7y,_7z,_7A,_7B,_7C,_7D){var _7E=E(_7D);if(!_7E._){var _7F=_7E.a,_7G=_7E.b,_7H=_7E.c,_7I=_7E.d;if((imul(3,_7z)|0)>=_7F){if((imul(3,_7F)|0)>=_7z){return new T4(0,(_7z+_7F|0)+1|0,E(_7y),E(new T4(0,_7z,E(_7A),E(_7B),E(_7C))),E(_7E));}else{return new F(function(){return _5N(_7A,_7B,B(_7l(_7y,_7C,_7F,_7G,_7H,_7I)));});}}else{return new F(function(){return _6x(_7G,B(_7x(_7y,_7z,_7A,_7B,_7C,_7H)),_7I);});}}else{return new F(function(){return _79(_7y,_7z,_7A,_7B,_7C);});}},_7J=function(_7K,_7L,_7M){var _7N=E(_7L);if(!_7N._){var _7O=_7N.a,_7P=_7N.b,_7Q=_7N.c,_7R=_7N.d,_7S=E(_7M);if(!_7S._){var _7T=_7S.a,_7U=_7S.b,_7V=_7S.c,_7W=_7S.d;if((imul(3,_7O)|0)>=_7T){if((imul(3,_7T)|0)>=_7O){return new T4(0,(_7O+_7T|0)+1|0,E(_7K),E(_7N),E(_7S));}else{return new F(function(){return _5N(_7P,_7Q,B(_7l(_7K,_7R,_7T,_7U,_7V,_7W)));});}}else{return new F(function(){return _6x(_7U,B(_7x(_7K,_7O,_7P,_7Q,_7R,_7V)),_7W);});}}else{return new F(function(){return _79(_7K,_7O,_7P,_7Q,_7R);});}}else{return new F(function(){return _75(_7K,_7M);});}},_7X=function(_7Y,_7Z,_80,_81,_82){var _83=E(_7Y);if(_83==1){var _84=E(_82);if(!_84._){return new T3(0,new T4(0,1,E(new T3(0,_7Z,_80,_81)),E(_5I),E(_5I)),_1,_1);}else{var _85=E(_7Z),_86=E(_84.a),_87=E(_86.a);if(_85>=_87){if(_85!=_87){return new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_1,_84);}else{var _88=E(_86.b);return (_80>=_88)?(_80!=_88)?new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_1,_84):(_81<E(_86.c))?new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_84,_1):new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_1,_84):new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_84,_1);}}else{return new T3(0,new T4(0,1,E(new T3(0,_85,_80,_81)),E(_5I),E(_5I)),_84,_1);}}}else{var _89=B(_7X(_83>>1,_7Z,_80,_81,_82)),_8a=_89.a,_8b=_89.c,_8c=E(_89.b);if(!_8c._){return new T3(0,_8a,_1,_8b);}else{var _8d=_8c.a,_8e=E(_8c.b);if(!_8e._){return new T3(0,new T(function(){return B(_6p(_8d,_8a));}),_1,_8b);}else{var _8f=_8e.b,_8g=E(_8d),_8h=E(_8g.a),_8i=E(_8e.a),_8j=_8i.b,_8k=_8i.c,_8l=E(_8i.a);if(_8h>=_8l){if(_8h!=_8l){return new T3(0,_8a,_1,_8c);}else{var _8m=E(_8g.b),_8n=E(_8j);if(_8m>=_8n){if(_8m!=_8n){return new T3(0,_8a,_1,_8c);}else{var _8o=E(_8k);if(E(_8g.c)<_8o){var _8p=B(_7X(_83>>1,_8l,_8n,_8o,_8f));return new T3(0,new T(function(){return B(_7J(_8g,_8a,_8p.a));}),_8p.b,_8p.c);}else{return new T3(0,_8a,_1,_8c);}}}else{var _8q=B(_8r(_83>>1,_8l,_8n,_8k,_8f));return new T3(0,new T(function(){return B(_7J(_8g,_8a,_8q.a));}),_8q.b,_8q.c);}}}else{var _8s=B(_8t(_83>>1,_8l,_8j,_8k,_8f));return new T3(0,new T(function(){return B(_7J(_8g,_8a,_8s.a));}),_8s.b,_8s.c);}}}}},_8r=function(_8u,_8v,_8w,_8x,_8y){var _8z=E(_8u);if(_8z==1){var _8A=E(_8y);if(!_8A._){return new T3(0,new T4(0,1,E(new T3(0,_8v,_8w,_8x)),E(_5I),E(_5I)),_1,_1);}else{var _8B=E(_8v),_8C=E(_8A.a),_8D=E(_8C.a);if(_8B>=_8D){if(_8B!=_8D){return new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8x)),E(_5I),E(_5I)),_1,_8A);}else{var _8E=E(_8C.b);if(_8w>=_8E){if(_8w!=_8E){return new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8x)),E(_5I),E(_5I)),_1,_8A);}else{var _8F=E(_8x);return (_8F<E(_8C.c))?new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8F)),E(_5I),E(_5I)),_8A,_1):new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8F)),E(_5I),E(_5I)),_1,_8A);}}else{return new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8x)),E(_5I),E(_5I)),_8A,_1);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_8B,_8w,_8x)),E(_5I),E(_5I)),_8A,_1);}}}else{var _8G=B(_8r(_8z>>1,_8v,_8w,_8x,_8y)),_8H=_8G.a,_8I=_8G.c,_8J=E(_8G.b);if(!_8J._){return new T3(0,_8H,_1,_8I);}else{var _8K=_8J.a,_8L=E(_8J.b);if(!_8L._){return new T3(0,new T(function(){return B(_6p(_8K,_8H));}),_1,_8I);}else{var _8M=_8L.b,_8N=E(_8K),_8O=E(_8N.a),_8P=E(_8L.a),_8Q=_8P.b,_8R=_8P.c,_8S=E(_8P.a);if(_8O>=_8S){if(_8O!=_8S){return new T3(0,_8H,_1,_8J);}else{var _8T=E(_8N.b),_8U=E(_8Q);if(_8T>=_8U){if(_8T!=_8U){return new T3(0,_8H,_1,_8J);}else{var _8V=E(_8R);if(E(_8N.c)<_8V){var _8W=B(_7X(_8z>>1,_8S,_8U,_8V,_8M));return new T3(0,new T(function(){return B(_7J(_8N,_8H,_8W.a));}),_8W.b,_8W.c);}else{return new T3(0,_8H,_1,_8J);}}}else{var _8X=B(_8r(_8z>>1,_8S,_8U,_8R,_8M));return new T3(0,new T(function(){return B(_7J(_8N,_8H,_8X.a));}),_8X.b,_8X.c);}}}else{var _8Y=B(_8t(_8z>>1,_8S,_8Q,_8R,_8M));return new T3(0,new T(function(){return B(_7J(_8N,_8H,_8Y.a));}),_8Y.b,_8Y.c);}}}}},_8t=function(_8Z,_90,_91,_92,_93){var _94=E(_8Z);if(_94==1){var _95=E(_93);if(!_95._){return new T3(0,new T4(0,1,E(new T3(0,_90,_91,_92)),E(_5I),E(_5I)),_1,_1);}else{var _96=E(_90),_97=E(_95.a),_98=E(_97.a);if(_96>=_98){if(_96!=_98){return new T3(0,new T4(0,1,E(new T3(0,_96,_91,_92)),E(_5I),E(_5I)),_1,_95);}else{var _99=E(_91),_9a=E(_97.b);if(_99>=_9a){if(_99!=_9a){return new T3(0,new T4(0,1,E(new T3(0,_96,_99,_92)),E(_5I),E(_5I)),_1,_95);}else{var _9b=E(_92);return (_9b<E(_97.c))?new T3(0,new T4(0,1,E(new T3(0,_96,_99,_9b)),E(_5I),E(_5I)),_95,_1):new T3(0,new T4(0,1,E(new T3(0,_96,_99,_9b)),E(_5I),E(_5I)),_1,_95);}}else{return new T3(0,new T4(0,1,E(new T3(0,_96,_99,_92)),E(_5I),E(_5I)),_95,_1);}}}else{return new T3(0,new T4(0,1,E(new T3(0,_96,_91,_92)),E(_5I),E(_5I)),_95,_1);}}}else{var _9c=B(_8t(_94>>1,_90,_91,_92,_93)),_9d=_9c.a,_9e=_9c.c,_9f=E(_9c.b);if(!_9f._){return new T3(0,_9d,_1,_9e);}else{var _9g=_9f.a,_9h=E(_9f.b);if(!_9h._){return new T3(0,new T(function(){return B(_6p(_9g,_9d));}),_1,_9e);}else{var _9i=_9h.b,_9j=E(_9g),_9k=E(_9j.a),_9l=E(_9h.a),_9m=_9l.b,_9n=_9l.c,_9o=E(_9l.a);if(_9k>=_9o){if(_9k!=_9o){return new T3(0,_9d,_1,_9f);}else{var _9p=E(_9j.b),_9q=E(_9m);if(_9p>=_9q){if(_9p!=_9q){return new T3(0,_9d,_1,_9f);}else{var _9r=E(_9n);if(E(_9j.c)<_9r){var _9s=B(_7X(_94>>1,_9o,_9q,_9r,_9i));return new T3(0,new T(function(){return B(_7J(_9j,_9d,_9s.a));}),_9s.b,_9s.c);}else{return new T3(0,_9d,_1,_9f);}}}else{var _9t=B(_8r(_94>>1,_9o,_9q,_9n,_9i));return new T3(0,new T(function(){return B(_7J(_9j,_9d,_9t.a));}),_9t.b,_9t.c);}}}else{var _9u=B(_8t(_94>>1,_9o,_9m,_9n,_9i));return new T3(0,new T(function(){return B(_7J(_9j,_9d,_9u.a));}),_9u.b,_9u.c);}}}}},_9v=function(_9w,_9x,_9y,_9z,_9A){var _9B=E(_9A);if(!_9B._){var _9C=_9B.c,_9D=_9B.d,_9E=E(_9B.b),_9F=E(_9E.a);if(_9w>=_9F){if(_9w!=_9F){return new F(function(){return _5N(_9E,_9C,B(_9v(_9w,_,_9y,_9z,_9D)));});}else{var _9G=E(_9E.b);if(_9y>=_9G){if(_9y!=_9G){return new F(function(){return _5N(_9E,_9C,B(_9v(_9w,_,_9y,_9z,_9D)));});}else{var _9H=E(_9E.c);if(_9z>=_9H){if(_9z!=_9H){return new F(function(){return _5N(_9E,_9C,B(_9v(_9w,_,_9y,_9z,_9D)));});}else{return new T4(0,_9B.a,E(new T3(0,_9w,_9y,_9z)),E(_9C),E(_9D));}}else{return new F(function(){return _6x(_9E,B(_9v(_9w,_,_9y,_9z,_9C)),_9D);});}}}else{return new F(function(){return _6x(_9E,B(_9v(_9w,_,_9y,_9z,_9C)),_9D);});}}}else{return new F(function(){return _6x(_9E,B(_9v(_9w,_,_9y,_9z,_9C)),_9D);});}}else{return new T4(0,1,E(new T3(0,_9w,_9y,_9z)),E(_5I),E(_5I));}},_9I=function(_9J,_9K,_9L,_9M,_9N){var _9O=E(_9N);if(!_9O._){var _9P=_9O.c,_9Q=_9O.d,_9R=E(_9O.b),_9S=E(_9R.a);if(_9J>=_9S){if(_9J!=_9S){return new F(function(){return _5N(_9R,_9P,B(_9I(_9J,_,_9L,_9M,_9Q)));});}else{var _9T=E(_9R.b);if(_9L>=_9T){if(_9L!=_9T){return new F(function(){return _5N(_9R,_9P,B(_9I(_9J,_,_9L,_9M,_9Q)));});}else{var _9U=E(_9M),_9V=E(_9R.c);if(_9U>=_9V){if(_9U!=_9V){return new F(function(){return _5N(_9R,_9P,B(_9v(_9J,_,_9L,_9U,_9Q)));});}else{return new T4(0,_9O.a,E(new T3(0,_9J,_9L,_9U)),E(_9P),E(_9Q));}}else{return new F(function(){return _6x(_9R,B(_9v(_9J,_,_9L,_9U,_9P)),_9Q);});}}}else{return new F(function(){return _6x(_9R,B(_9I(_9J,_,_9L,_9M,_9P)),_9Q);});}}}else{return new F(function(){return _6x(_9R,B(_9I(_9J,_,_9L,_9M,_9P)),_9Q);});}}else{return new T4(0,1,E(new T3(0,_9J,_9L,_9M)),E(_5I),E(_5I));}},_9W=function(_9X,_9Y,_9Z,_a0,_a1){var _a2=E(_a1);if(!_a2._){var _a3=_a2.c,_a4=_a2.d,_a5=E(_a2.b),_a6=E(_a5.a);if(_9X>=_a6){if(_9X!=_a6){return new F(function(){return _5N(_a5,_a3,B(_9W(_9X,_,_9Z,_a0,_a4)));});}else{var _a7=E(_9Z),_a8=E(_a5.b);if(_a7>=_a8){if(_a7!=_a8){return new F(function(){return _5N(_a5,_a3,B(_9I(_9X,_,_a7,_a0,_a4)));});}else{var _a9=E(_a0),_aa=E(_a5.c);if(_a9>=_aa){if(_a9!=_aa){return new F(function(){return _5N(_a5,_a3,B(_9v(_9X,_,_a7,_a9,_a4)));});}else{return new T4(0,_a2.a,E(new T3(0,_9X,_a7,_a9)),E(_a3),E(_a4));}}else{return new F(function(){return _6x(_a5,B(_9v(_9X,_,_a7,_a9,_a3)),_a4);});}}}else{return new F(function(){return _6x(_a5,B(_9I(_9X,_,_a7,_a0,_a3)),_a4);});}}}else{return new F(function(){return _6x(_a5,B(_9W(_9X,_,_9Z,_a0,_a3)),_a4);});}}else{return new T4(0,1,E(new T3(0,_9X,_9Z,_a0)),E(_5I),E(_5I));}},_ab=function(_ac,_ad,_ae,_af){var _ag=E(_af);if(!_ag._){var _ah=_ag.c,_ai=_ag.d,_aj=E(_ag.b),_ak=E(_ac),_al=E(_aj.a);if(_ak>=_al){if(_ak!=_al){return new F(function(){return _5N(_aj,_ah,B(_9W(_ak,_,_ad,_ae,_ai)));});}else{var _am=E(_ad),_an=E(_aj.b);if(_am>=_an){if(_am!=_an){return new F(function(){return _5N(_aj,_ah,B(_9I(_ak,_,_am,_ae,_ai)));});}else{var _ao=E(_ae),_ap=E(_aj.c);if(_ao>=_ap){if(_ao!=_ap){return new F(function(){return _5N(_aj,_ah,B(_9v(_ak,_,_am,_ao,_ai)));});}else{return new T4(0,_ag.a,E(new T3(0,_ak,_am,_ao)),E(_ah),E(_ai));}}else{return new F(function(){return _6x(_aj,B(_9v(_ak,_,_am,_ao,_ah)),_ai);});}}}else{return new F(function(){return _6x(_aj,B(_9I(_ak,_,_am,_ae,_ah)),_ai);});}}}else{return new F(function(){return _6x(_aj,B(_9W(_ak,_,_ad,_ae,_ah)),_ai);});}}else{return new T4(0,1,E(new T3(0,_ac,_ad,_ae)),E(_5I),E(_5I));}},_aq=function(_ar,_as){while(1){var _at=E(_as);if(!_at._){return E(_ar);}else{var _au=E(_at.a),_av=B(_ab(_au.a,_au.b,_au.c,_ar));_ar=_av;_as=_at.b;continue;}}},_aw=function(_ax,_ay,_az,_aA,_aB){return new F(function(){return _aq(B(_ab(_ay,_az,_aA,_ax)),_aB);});},_aC=function(_aD,_aE,_aF){var _aG=E(_aE);return new F(function(){return _aq(B(_ab(_aG.a,_aG.b,_aG.c,_aD)),_aF);});},_aH=function(_aI,_aJ,_aK){var _aL=E(_aK);if(!_aL._){return E(_aJ);}else{var _aM=_aL.a,_aN=E(_aL.b);if(!_aN._){return new F(function(){return _6p(_aM,_aJ);});}else{var _aO=E(_aM),_aP=_aO.b,_aQ=_aO.c,_aR=E(_aO.a),_aS=E(_aN.a),_aT=_aS.b,_aU=_aS.c,_aV=E(_aS.a),_aW=function(_aX){var _aY=B(_8t(_aI,_aV,_aT,_aU,_aN.b)),_aZ=_aY.a,_b0=E(_aY.c);if(!_b0._){return new F(function(){return _aH(_aI<<1,B(_7J(_aO,_aJ,_aZ)),_aY.b);});}else{return new F(function(){return _aC(B(_7J(_aO,_aJ,_aZ)),_b0.a,_b0.b);});}};if(_aR>=_aV){if(_aR!=_aV){return new F(function(){return _aw(_aJ,_aR,_aP,_aQ,_aN);});}else{var _b1=E(_aP),_b2=E(_aT);if(_b1>=_b2){if(_b1!=_b2){return new F(function(){return _aw(_aJ,_aR,_b1,_aQ,_aN);});}else{var _b3=E(_aQ);if(_b3<E(_aU)){return new F(function(){return _aW(_);});}else{return new F(function(){return _aw(_aJ,_aR,_b1,_b3,_aN);});}}}else{return new F(function(){return _aW(_);});}}}else{return new F(function(){return _aW(_);});}}}},_b4=function(_b5,_b6,_b7,_b8,_b9,_ba){var _bb=E(_ba);if(!_bb._){return new F(function(){return _6p(new T3(0,_b7,_b8,_b9),_b6);});}else{var _bc=E(_b7),_bd=E(_bb.a),_be=_bd.b,_bf=_bd.c,_bg=E(_bd.a),_bh=function(_bi){var _bj=B(_8t(_b5,_bg,_be,_bf,_bb.b)),_bk=_bj.a,_bl=E(_bj.c);if(!_bl._){return new F(function(){return _aH(_b5<<1,B(_7J(new T3(0,_bc,_b8,_b9),_b6,_bk)),_bj.b);});}else{return new F(function(){return _aC(B(_7J(new T3(0,_bc,_b8,_b9),_b6,_bk)),_bl.a,_bl.b);});}};if(_bc>=_bg){if(_bc!=_bg){return new F(function(){return _aw(_b6,_bc,_b8,_b9,_bb);});}else{var _bm=E(_be);if(_b8>=_bm){if(_b8!=_bm){return new F(function(){return _aw(_b6,_bc,_b8,_b9,_bb);});}else{var _bn=E(_b9);if(_bn<E(_bf)){return new F(function(){return _bh(_);});}else{return new F(function(){return _aw(_b6,_bc,_b8,_bn,_bb);});}}}else{return new F(function(){return _bh(_);});}}}else{return new F(function(){return _bh(_);});}}},_bo=function(_bp,_bq,_br,_bs,_bt,_bu){var _bv=E(_bu);if(!_bv._){return new F(function(){return _6p(new T3(0,_br,_bs,_bt),_bq);});}else{var _bw=E(_br),_bx=E(_bv.a),_by=_bx.b,_bz=_bx.c,_bA=E(_bx.a),_bB=function(_bC){var _bD=B(_8t(_bp,_bA,_by,_bz,_bv.b)),_bE=_bD.a,_bF=E(_bD.c);if(!_bF._){return new F(function(){return _aH(_bp<<1,B(_7J(new T3(0,_bw,_bs,_bt),_bq,_bE)),_bD.b);});}else{return new F(function(){return _aC(B(_7J(new T3(0,_bw,_bs,_bt),_bq,_bE)),_bF.a,_bF.b);});}};if(_bw>=_bA){if(_bw!=_bA){return new F(function(){return _aw(_bq,_bw,_bs,_bt,_bv);});}else{var _bG=E(_by);if(_bs>=_bG){if(_bs!=_bG){return new F(function(){return _aw(_bq,_bw,_bs,_bt,_bv);});}else{if(_bt<E(_bz)){return new F(function(){return _bB(_);});}else{return new F(function(){return _aw(_bq,_bw,_bs,_bt,_bv);});}}}else{return new F(function(){return _bB(_);});}}}else{return new F(function(){return _bB(_);});}}},_bH=function(_bI,_bJ,_bK,_bL,_bM,_bN){var _bO=E(_bN);if(!_bO._){return new F(function(){return _6p(new T3(0,_bK,_bL,_bM),_bJ);});}else{var _bP=E(_bK),_bQ=E(_bO.a),_bR=_bQ.b,_bS=_bQ.c,_bT=E(_bQ.a),_bU=function(_bV){var _bW=B(_8t(_bI,_bT,_bR,_bS,_bO.b)),_bX=_bW.a,_bY=E(_bW.c);if(!_bY._){return new F(function(){return _aH(_bI<<1,B(_7J(new T3(0,_bP,_bL,_bM),_bJ,_bX)),_bW.b);});}else{return new F(function(){return _aC(B(_7J(new T3(0,_bP,_bL,_bM),_bJ,_bX)),_bY.a,_bY.b);});}};if(_bP>=_bT){if(_bP!=_bT){return new F(function(){return _aw(_bJ,_bP,_bL,_bM,_bO);});}else{var _bZ=E(_bL),_c0=E(_bR);if(_bZ>=_c0){if(_bZ!=_c0){return new F(function(){return _aw(_bJ,_bP,_bZ,_bM,_bO);});}else{var _c1=E(_bM);if(_c1<E(_bS)){return new F(function(){return _bU(_);});}else{return new F(function(){return _aw(_bJ,_bP,_bZ,_c1,_bO);});}}}else{return new F(function(){return _bU(_);});}}}else{return new F(function(){return _bU(_);});}}},_c2=function(_c3){var _c4=E(_c3);if(!_c4._){return new T0(1);}else{var _c5=_c4.a,_c6=E(_c4.b);if(!_c6._){return new T4(0,1,E(_c5),E(_5I),E(_5I));}else{var _c7=_c6.b,_c8=E(_c5),_c9=E(_c8.a),_ca=E(_c6.a),_cb=_ca.b,_cc=_ca.c,_cd=E(_ca.a);if(_c9>=_cd){if(_c9!=_cd){return new F(function(){return _aw(new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cb,_cc,_c7);});}else{var _ce=E(_c8.b),_cf=E(_cb);if(_ce>=_cf){if(_ce!=_cf){return new F(function(){return _aw(new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cf,_cc,_c7);});}else{var _cg=E(_cc);if(E(_c8.c)<_cg){return new F(function(){return _bo(1,new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cf,_cg,_c7);});}else{return new F(function(){return _aw(new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cf,_cg,_c7);});}}}else{return new F(function(){return _b4(1,new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cf,_cc,_c7);});}}}else{return new F(function(){return _bH(1,new T4(0,1,E(_c8),E(_5I),E(_5I)),_cd,_cb,_cc,_c7);});}}}},_ch=function(_ci,_cj,_ck,_cl,_cm){var _cn=E(_ci);if(_cn==1){var _co=E(_cm);if(!_co._){return new T3(0,new T5(0,1,E(new T2(0,_cj,_ck)),_cl,E(_0),E(_0)),_1,_1);}else{var _cp=E(E(_co.a).a),_cq=E(_cj),_cr=E(_cp.a);return (_cq>=_cr)?(_cq!=_cr)?new T3(0,new T5(0,1,E(new T2(0,_cq,_ck)),_cl,E(_0),E(_0)),_1,_co):(_ck<E(_cp.b))?new T3(0,new T5(0,1,E(new T2(0,_cq,_ck)),_cl,E(_0),E(_0)),_co,_1):new T3(0,new T5(0,1,E(new T2(0,_cq,_ck)),_cl,E(_0),E(_0)),_1,_co):new T3(0,new T5(0,1,E(new T2(0,_cq,_ck)),_cl,E(_0),E(_0)),_co,_1);}}else{var _cs=B(_ch(_cn>>1,_cj,_ck,_cl,_cm)),_ct=_cs.a,_cu=_cs.c,_cv=E(_cs.b);if(!_cv._){return new T3(0,_ct,_1,_cu);}else{var _cw=E(_cv.a),_cx=_cw.a,_cy=_cw.b,_cz=E(_cv.b);if(!_cz._){return new T3(0,new T(function(){return B(_O(_cx,_cy,_ct));}),_1,_cu);}else{var _cA=_cz.b,_cB=E(_cz.a),_cC=_cB.b,_cD=E(_cx),_cE=E(_cB.a),_cF=_cE.b,_cG=E(_cD.a),_cH=E(_cE.a);if(_cG>=_cH){if(_cG!=_cH){return new T3(0,_ct,_1,_cv);}else{var _cI=E(_cF);if(E(_cD.b)<_cI){var _cJ=B(_ch(_cn>>1,_cH,_cI,_cC,_cA));return new T3(0,new T(function(){return B(_2h(_cD,_cy,_ct,_cJ.a));}),_cJ.b,_cJ.c);}else{return new T3(0,_ct,_1,_cv);}}}else{var _cK=B(_cL(_cn>>1,_cH,_cF,_cC,_cA));return new T3(0,new T(function(){return B(_2h(_cD,_cy,_ct,_cK.a));}),_cK.b,_cK.c);}}}}},_cL=function(_cM,_cN,_cO,_cP,_cQ){var _cR=E(_cM);if(_cR==1){var _cS=E(_cQ);if(!_cS._){return new T3(0,new T5(0,1,E(new T2(0,_cN,_cO)),_cP,E(_0),E(_0)),_1,_1);}else{var _cT=E(E(_cS.a).a),_cU=E(_cN),_cV=E(_cT.a);if(_cU>=_cV){if(_cU!=_cV){return new T3(0,new T5(0,1,E(new T2(0,_cU,_cO)),_cP,E(_0),E(_0)),_1,_cS);}else{var _cW=E(_cO);return (_cW<E(_cT.b))?new T3(0,new T5(0,1,E(new T2(0,_cU,_cW)),_cP,E(_0),E(_0)),_cS,_1):new T3(0,new T5(0,1,E(new T2(0,_cU,_cW)),_cP,E(_0),E(_0)),_1,_cS);}}else{return new T3(0,new T5(0,1,E(new T2(0,_cU,_cO)),_cP,E(_0),E(_0)),_cS,_1);}}}else{var _cX=B(_cL(_cR>>1,_cN,_cO,_cP,_cQ)),_cY=_cX.a,_cZ=_cX.c,_d0=E(_cX.b);if(!_d0._){return new T3(0,_cY,_1,_cZ);}else{var _d1=E(_d0.a),_d2=_d1.a,_d3=_d1.b,_d4=E(_d0.b);if(!_d4._){return new T3(0,new T(function(){return B(_O(_d2,_d3,_cY));}),_1,_cZ);}else{var _d5=_d4.b,_d6=E(_d4.a),_d7=_d6.b,_d8=E(_d2),_d9=E(_d6.a),_da=_d9.b,_db=E(_d8.a),_dc=E(_d9.a);if(_db>=_dc){if(_db!=_dc){return new T3(0,_cY,_1,_d0);}else{var _dd=E(_da);if(E(_d8.b)<_dd){var _de=B(_ch(_cR>>1,_dc,_dd,_d7,_d5));return new T3(0,new T(function(){return B(_2h(_d8,_d3,_cY,_de.a));}),_de.b,_de.c);}else{return new T3(0,_cY,_1,_d0);}}}else{var _df=B(_cL(_cR>>1,_dc,_da,_d7,_d5));return new T3(0,new T(function(){return B(_2h(_d8,_d3,_cY,_df.a));}),_df.b,_df.c);}}}}},_dg=function(_dh,_di,_dj,_dk,_dl){var _dm=E(_dl);if(!_dm._){var _dn=_dm.c,_do=_dm.d,_dp=_dm.e,_dq=E(_dm.b),_dr=E(_dq.a);if(_dh>=_dr){if(_dh!=_dr){return new F(function(){return _6(_dq,_dn,_do,B(_dg(_dh,_,_dj,_dk,_dp)));});}else{var _ds=E(_dq.b);if(_dj>=_ds){if(_dj!=_ds){return new F(function(){return _6(_dq,_dn,_do,B(_dg(_dh,_,_dj,_dk,_dp)));});}else{return new T5(0,_dm.a,E(new T2(0,_dh,_dj)),_dk,E(_do),E(_dp));}}else{return new F(function(){return _X(_dq,_dn,B(_dg(_dh,_,_dj,_dk,_do)),_dp);});}}}else{return new F(function(){return _X(_dq,_dn,B(_dg(_dh,_,_dj,_dk,_do)),_dp);});}}else{return new T5(0,1,E(new T2(0,_dh,_dj)),_dk,E(_0),E(_0));}},_dt=function(_du,_dv,_dw,_dx,_dy){var _dz=E(_dy);if(!_dz._){var _dA=_dz.c,_dB=_dz.d,_dC=_dz.e,_dD=E(_dz.b),_dE=E(_dD.a);if(_du>=_dE){if(_du!=_dE){return new F(function(){return _6(_dD,_dA,_dB,B(_dt(_du,_,_dw,_dx,_dC)));});}else{var _dF=E(_dw),_dG=E(_dD.b);if(_dF>=_dG){if(_dF!=_dG){return new F(function(){return _6(_dD,_dA,_dB,B(_dg(_du,_,_dF,_dx,_dC)));});}else{return new T5(0,_dz.a,E(new T2(0,_du,_dF)),_dx,E(_dB),E(_dC));}}else{return new F(function(){return _X(_dD,_dA,B(_dg(_du,_,_dF,_dx,_dB)),_dC);});}}}else{return new F(function(){return _X(_dD,_dA,B(_dt(_du,_,_dw,_dx,_dB)),_dC);});}}else{return new T5(0,1,E(new T2(0,_du,_dw)),_dx,E(_0),E(_0));}},_dH=function(_dI,_dJ,_dK,_dL){var _dM=E(_dL);if(!_dM._){var _dN=_dM.c,_dO=_dM.d,_dP=_dM.e,_dQ=E(_dM.b),_dR=E(_dI),_dS=E(_dQ.a);if(_dR>=_dS){if(_dR!=_dS){return new F(function(){return _6(_dQ,_dN,_dO,B(_dt(_dR,_,_dJ,_dK,_dP)));});}else{var _dT=E(_dJ),_dU=E(_dQ.b);if(_dT>=_dU){if(_dT!=_dU){return new F(function(){return _6(_dQ,_dN,_dO,B(_dg(_dR,_,_dT,_dK,_dP)));});}else{return new T5(0,_dM.a,E(new T2(0,_dR,_dT)),_dK,E(_dO),E(_dP));}}else{return new F(function(){return _X(_dQ,_dN,B(_dg(_dR,_,_dT,_dK,_dO)),_dP);});}}}else{return new F(function(){return _X(_dQ,_dN,B(_dt(_dR,_,_dJ,_dK,_dO)),_dP);});}}else{return new T5(0,1,E(new T2(0,_dI,_dJ)),_dK,E(_0),E(_0));}},_dV=function(_dW,_dX){while(1){var _dY=E(_dX);if(!_dY._){return E(_dW);}else{var _dZ=E(_dY.a),_e0=E(_dZ.a),_e1=B(_dH(_e0.a,_e0.b,_dZ.b,_dW));_dW=_e1;_dX=_dY.b;continue;}}},_e2=function(_e3,_e4,_e5,_e6,_e7){return new F(function(){return _dV(B(_dH(_e4,_e5,_e6,_e3)),_e7);});},_e8=function(_e9,_ea,_eb){var _ec=E(_ea),_ed=E(_ec.a);return new F(function(){return _dV(B(_dH(_ed.a,_ed.b,_ec.b,_e9)),_eb);});},_ee=function(_ef,_eg,_eh){var _ei=E(_eh);if(!_ei._){return E(_eg);}else{var _ej=E(_ei.a),_ek=_ej.a,_el=_ej.b,_em=E(_ei.b);if(!_em._){return new F(function(){return _O(_ek,_el,_eg);});}else{var _en=E(_em.a),_eo=E(_ek),_ep=_eo.b,_eq=E(_en.a),_er=_eq.b,_es=E(_eo.a),_et=E(_eq.a),_eu=function(_ev){var _ew=B(_cL(_ef,_et,_er,_en.b,_em.b)),_ex=_ew.a,_ey=E(_ew.c);if(!_ey._){return new F(function(){return _ee(_ef<<1,B(_2h(_eo,_el,_eg,_ex)),_ew.b);});}else{return new F(function(){return _e8(B(_2h(_eo,_el,_eg,_ex)),_ey.a,_ey.b);});}};if(_es>=_et){if(_es!=_et){return new F(function(){return _e2(_eg,_es,_ep,_el,_em);});}else{var _ez=E(_ep);if(_ez<E(_er)){return new F(function(){return _eu(_);});}else{return new F(function(){return _e2(_eg,_es,_ez,_el,_em);});}}}else{return new F(function(){return _eu(_);});}}}},_eA=function(_eB,_eC,_eD,_eE,_eF,_eG){var _eH=E(_eG);if(!_eH._){return new F(function(){return _O(new T2(0,_eD,_eE),_eF,_eC);});}else{var _eI=E(_eH.a),_eJ=E(_eI.a),_eK=_eJ.b,_eL=E(_eD),_eM=E(_eJ.a),_eN=function(_eO){var _eP=B(_cL(_eB,_eM,_eK,_eI.b,_eH.b)),_eQ=_eP.a,_eR=E(_eP.c);if(!_eR._){return new F(function(){return _ee(_eB<<1,B(_2h(new T2(0,_eL,_eE),_eF,_eC,_eQ)),_eP.b);});}else{return new F(function(){return _e8(B(_2h(new T2(0,_eL,_eE),_eF,_eC,_eQ)),_eR.a,_eR.b);});}};if(_eL>=_eM){if(_eL!=_eM){return new F(function(){return _e2(_eC,_eL,_eE,_eF,_eH);});}else{var _eS=E(_eE);if(_eS<E(_eK)){return new F(function(){return _eN(_);});}else{return new F(function(){return _e2(_eC,_eL,_eS,_eF,_eH);});}}}else{return new F(function(){return _eN(_);});}}},_eT=function(_eU,_eV,_eW,_eX,_eY,_eZ){var _f0=E(_eZ);if(!_f0._){return new F(function(){return _O(new T2(0,_eW,_eX),_eY,_eV);});}else{var _f1=E(_f0.a),_f2=E(_f1.a),_f3=_f2.b,_f4=E(_eW),_f5=E(_f2.a),_f6=function(_f7){var _f8=B(_cL(_eU,_f5,_f3,_f1.b,_f0.b)),_f9=_f8.a,_fa=E(_f8.c);if(!_fa._){return new F(function(){return _ee(_eU<<1,B(_2h(new T2(0,_f4,_eX),_eY,_eV,_f9)),_f8.b);});}else{return new F(function(){return _e8(B(_2h(new T2(0,_f4,_eX),_eY,_eV,_f9)),_fa.a,_fa.b);});}};if(_f4>=_f5){if(_f4!=_f5){return new F(function(){return _e2(_eV,_f4,_eX,_eY,_f0);});}else{if(_eX<E(_f3)){return new F(function(){return _f6(_);});}else{return new F(function(){return _e2(_eV,_f4,_eX,_eY,_f0);});}}}else{return new F(function(){return _f6(_);});}}},_fb=function(_fc){var _fd=E(_fc);if(!_fd._){return new T0(1);}else{var _fe=E(_fd.a),_ff=_fe.a,_fg=_fe.b,_fh=E(_fd.b);if(!_fh._){return new T5(0,1,E(_ff),_fg,E(_0),E(_0));}else{var _fi=_fh.b,_fj=E(_fh.a),_fk=_fj.b,_fl=E(_ff),_fm=E(_fj.a),_fn=_fm.b,_fo=E(_fl.a),_fp=E(_fm.a);if(_fo>=_fp){if(_fo!=_fp){return new F(function(){return _e2(new T5(0,1,E(_fl),_fg,E(_0),E(_0)),_fp,_fn,_fk,_fi);});}else{var _fq=E(_fn);if(E(_fl.b)<_fq){return new F(function(){return _eT(1,new T5(0,1,E(_fl),_fg,E(_0),E(_0)),_fp,_fq,_fk,_fi);});}else{return new F(function(){return _e2(new T5(0,1,E(_fl),_fg,E(_0),E(_0)),_fp,_fq,_fk,_fi);});}}}else{return new F(function(){return _eA(1,new T5(0,1,E(_fl),_fg,E(_0),E(_0)),_fp,_fn,_fk,_fi);});}}}},_fr=function(_fs,_ft,_fu,_fv,_fw){var _fx=E(_fw);if(!_fx._){var _fy=_fx.c,_fz=_fx.d,_fA=E(_fx.b),_fB=E(_fs),_fC=E(_fA.a);if(_fB>=_fC){if(_fB!=_fC){return new F(function(){return _5N(_fA,_fy,B(_fr(_fB,_ft,_fu,_fv,_fz)));});}else{var _fD=E(_ft),_fE=E(_fA.b);if(_fD>=_fE){if(_fD!=_fE){return new F(function(){return _5N(_fA,_fy,B(_fr(_fB,_fD,_fu,_fv,_fz)));});}else{var _fF=E(_fu),_fG=E(_fA.c);if(_fF>=_fG){if(_fF!=_fG){return new F(function(){return _5N(_fA,_fy,B(_fr(_fB,_fD,_fF,_fv,_fz)));});}else{var _fH=E(_fv),_fI=E(_fA.d);if(_fH>=_fI){if(_fH!=_fI){return new F(function(){return _5N(_fA,_fy,B(_fr(_fB,_fD,_fF,_fH,_fz)));});}else{return new T4(0,_fx.a,E(new T4(0,_fB,_fD,_fF,_fH)),E(_fy),E(_fz));}}else{return new F(function(){return _6x(_fA,B(_fr(_fB,_fD,_fF,_fH,_fy)),_fz);});}}}else{return new F(function(){return _6x(_fA,B(_fr(_fB,_fD,_fF,_fv,_fy)),_fz);});}}}else{return new F(function(){return _6x(_fA,B(_fr(_fB,_fD,_fu,_fv,_fy)),_fz);});}}}else{return new F(function(){return _6x(_fA,B(_fr(_fB,_ft,_fu,_fv,_fy)),_fz);});}}else{return new T4(0,1,E(new T4(0,_fs,_ft,_fu,_fv)),E(_5I),E(_5I));}},_fJ=function(_fK,_fL){while(1){var _fM=E(_fL);if(!_fM._){return E(_fK);}else{var _fN=E(_fM.a),_fO=B(_fr(_fN.a,_fN.b,_fN.c,_fN.d,_fK));_fK=_fO;_fL=_fM.b;continue;}}},_fP=function(_fQ,_fR,_fS,_fT,_fU,_fV){return new F(function(){return _fJ(B(_fr(_fR,_fS,_fT,_fU,_fQ)),_fV);});},_fW=function(_fX,_fY){var _fZ=E(_fY);if(!_fZ._){return new T3(0,_5I,_1,_1);}else{var _g0=_fZ.a,_g1=E(_fX);if(_g1==1){var _g2=E(_fZ.b);if(!_g2._){return new T3(0,new T(function(){return new T4(0,1,E(_g0),E(_5I),E(_5I));}),_1,_1);}else{var _g3=E(_g0),_g4=E(_g3.a),_g5=E(_g2.a),_g6=E(_g5.a);if(_g4>=_g6){if(_g4!=_g6){return new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_1,_g2);}else{var _g7=E(_g3.b),_g8=E(_g5.b);if(_g7>=_g8){if(_g7!=_g8){return new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_1,_g2);}else{var _g9=E(_g3.c),_ga=E(_g5.c);return (_g9>=_ga)?(_g9!=_ga)?new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_1,_g2):(E(_g3.d)<E(_g5.d))?new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_g2,_1):new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_1,_g2):new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_g2,_1);}}else{return new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_g2,_1);}}}else{return new T3(0,new T4(0,1,E(_g3),E(_5I),E(_5I)),_g2,_1);}}}else{var _gb=B(_fW(_g1>>1,_fZ)),_gc=_gb.a,_gd=_gb.c,_ge=E(_gb.b);if(!_ge._){return new T3(0,_gc,_1,_gd);}else{var _gf=_ge.a,_gg=E(_ge.b);if(!_gg._){return new T3(0,new T(function(){return B(_6p(_gf,_gc));}),_1,_gd);}else{var _gh=E(_gf),_gi=E(_gh.a),_gj=E(_gg.a),_gk=E(_gj.a);if(_gi>=_gk){if(_gi!=_gk){return new T3(0,_gc,_1,_ge);}else{var _gl=E(_gh.b),_gm=E(_gj.b);if(_gl>=_gm){if(_gl!=_gm){return new T3(0,_gc,_1,_ge);}else{var _gn=E(_gh.c),_go=E(_gj.c);if(_gn>=_go){if(_gn!=_go){return new T3(0,_gc,_1,_ge);}else{if(E(_gh.d)<E(_gj.d)){var _gp=B(_fW(_g1>>1,_gg));return new T3(0,new T(function(){return B(_7J(_gh,_gc,_gp.a));}),_gp.b,_gp.c);}else{return new T3(0,_gc,_1,_ge);}}}else{var _gq=B(_fW(_g1>>1,_gg));return new T3(0,new T(function(){return B(_7J(_gh,_gc,_gq.a));}),_gq.b,_gq.c);}}}else{var _gr=B(_fW(_g1>>1,_gg));return new T3(0,new T(function(){return B(_7J(_gh,_gc,_gr.a));}),_gr.b,_gr.c);}}}else{var _gs=B(_fW(_g1>>1,_gg));return new T3(0,new T(function(){return B(_7J(_gh,_gc,_gs.a));}),_gs.b,_gs.c);}}}}}},_gt=function(_gu,_gv,_gw){var _gx=E(_gw);if(!_gx._){return E(_gv);}else{var _gy=_gx.a,_gz=E(_gx.b);if(!_gz._){return new F(function(){return _6p(_gy,_gv);});}else{var _gA=E(_gy),_gB=_gA.b,_gC=_gA.c,_gD=_gA.d,_gE=E(_gA.a),_gF=E(_gz.a),_gG=E(_gF.a),_gH=function(_gI){var _gJ=B(_fW(_gu,_gz)),_gK=_gJ.a,_gL=E(_gJ.c);if(!_gL._){return new F(function(){return _gt(_gu<<1,B(_7J(_gA,_gv,_gK)),_gJ.b);});}else{return new F(function(){return _fJ(B(_7J(_gA,_gv,_gK)),_gL);});}};if(_gE>=_gG){if(_gE!=_gG){return new F(function(){return _fP(_gv,_gE,_gB,_gC,_gD,_gz);});}else{var _gM=E(_gB),_gN=E(_gF.b);if(_gM>=_gN){if(_gM!=_gN){return new F(function(){return _fP(_gv,_gE,_gM,_gC,_gD,_gz);});}else{var _gO=E(_gC),_gP=E(_gF.c);if(_gO>=_gP){if(_gO!=_gP){return new F(function(){return _fP(_gv,_gE,_gM,_gO,_gD,_gz);});}else{var _gQ=E(_gD);if(_gQ<E(_gF.d)){return new F(function(){return _gH(_);});}else{return new F(function(){return _fP(_gv,_gE,_gM,_gO,_gQ,_gz);});}}}else{return new F(function(){return _gH(_);});}}}else{return new F(function(){return _gH(_);});}}}else{return new F(function(){return _gH(_);});}}}},_gR=function(_gS){var _gT=E(_gS);if(!_gT._){return new T0(1);}else{var _gU=_gT.a,_gV=E(_gT.b);if(!_gV._){return new T4(0,1,E(_gU),E(_5I),E(_5I));}else{var _gW=_gV.b,_gX=E(_gU),_gY=E(_gX.a),_gZ=E(_gV.a),_h0=_gZ.b,_h1=_gZ.c,_h2=_gZ.d,_h3=E(_gZ.a);if(_gY>=_h3){if(_gY!=_h3){return new F(function(){return _fP(new T4(0,1,E(_gX),E(_5I),E(_5I)),_h3,_h0,_h1,_h2,_gW);});}else{var _h4=E(_gX.b),_h5=E(_h0);if(_h4>=_h5){if(_h4!=_h5){return new F(function(){return _fP(new T4(0,1,E(_gX),E(_5I),E(_5I)),_h3,_h5,_h1,_h2,_gW);});}else{var _h6=E(_gX.c),_h7=E(_h1);if(_h6>=_h7){if(_h6!=_h7){return new F(function(){return _fP(new T4(0,1,E(_gX),E(_5I),E(_5I)),_h3,_h5,_h7,_h2,_gW);});}else{var _h8=E(_h2);if(E(_gX.d)<_h8){return new F(function(){return _gt(1,new T4(0,1,E(_gX),E(_5I),E(_5I)),_gV);});}else{return new F(function(){return _fP(new T4(0,1,E(_gX),E(_5I),E(_5I)),_h3,_h5,_h7,_h8,_gW);});}}}else{return new F(function(){return _gt(1,new T4(0,1,E(_gX),E(_5I),E(_5I)),_gV);});}}}else{return new F(function(){return _gt(1,new T4(0,1,E(_gX),E(_5I),E(_5I)),_gV);});}}}else{return new F(function(){return _gt(1,new T4(0,1,E(_gX),E(_5I),E(_5I)),_gV);});}}}},_h9=0,_ha=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_hb=new T(function(){return B(err(_ha));}),_hc=function(_hd,_he){while(1){var _hf=B((function(_hg,_hh){var _hi=E(_hh);if(!_hi._){_hd=new T2(1,new T2(0,_hi.b,_hi.c),new T(function(){return B(_hc(_hg,_hi.e));}));_he=_hi.d;return __continue;}else{return E(_hg);}})(_hd,_he));if(_hf!=__continue){return _hf;}}},_hj=44,_hk=function(_hl,_hm,_hn){return new F(function(){return A1(_hl,new T2(1,_hj,new T(function(){return B(A1(_hm,_hn));})));});},_ho=new T(function(){return B(unCStr("CC "));}),_hp=new T(function(){return B(unCStr("IdentCC "));}),_hq=function(_hr,_hs){var _ht=E(_hr);return (_ht._==0)?E(_hs):new T2(1,_ht.a,new T(function(){return B(_hq(_ht.b,_hs));}));},_hu=function(_hv,_hw){var _hx=jsShowI(_hv);return new F(function(){return _hq(fromJSStr(_hx),_hw);});},_hy=41,_hz=40,_hA=function(_hB,_hC,_hD){if(_hC>=0){return new F(function(){return _hu(_hC,_hD);});}else{if(_hB<=6){return new F(function(){return _hu(_hC,_hD);});}else{return new T2(1,_hz,new T(function(){var _hE=jsShowI(_hC);return B(_hq(fromJSStr(_hE),new T2(1,_hy,_hD)));}));}}},_hF=function(_hG,_hH,_hI){if(_hG<11){return new F(function(){return _hq(_hp,new T(function(){return B(_hA(11,E(_hH),_hI));},1));});}else{var _hJ=new T(function(){return B(_hq(_hp,new T(function(){return B(_hA(11,E(_hH),new T2(1,_hy,_hI)));},1)));});return new T2(1,_hz,_hJ);}},_hK=32,_hL=function(_hM,_hN,_hO,_hP,_hQ,_hR){var _hS=function(_hT){var _hU=new T(function(){var _hV=new T(function(){return B(_hA(11,E(_hP),new T2(1,_hK,new T(function(){return B(_hA(11,E(_hQ),_hT));}))));});return B(_hA(11,E(_hO),new T2(1,_hK,_hV)));});return new F(function(){return _hF(11,_hN,new T2(1,_hK,_hU));});};if(_hM<11){return new F(function(){return _hq(_ho,new T(function(){return B(_hS(_hR));},1));});}else{var _hW=new T(function(){return B(_hq(_ho,new T(function(){return B(_hS(new T2(1,_hy,_hR)));},1)));});return new T2(1,_hz,_hW);}},_hX=function(_hY,_hZ){var _i0=E(_hY);return new F(function(){return _hL(0,_i0.a,_i0.b,_i0.c,_i0.d,_hZ);});},_i1=new T(function(){return B(unCStr("RC "));}),_i2=function(_i3,_i4,_i5,_i6,_i7){var _i8=function(_i9){var _ia=new T(function(){var _ib=new T(function(){return B(_hA(11,E(_i5),new T2(1,_hK,new T(function(){return B(_hA(11,E(_i6),_i9));}))));});return B(_hF(11,_i4,new T2(1,_hK,_ib)));},1);return new F(function(){return _hq(_i1,_ia);});};if(_i3<11){return new F(function(){return _i8(_i7);});}else{return new T2(1,_hz,new T(function(){return B(_i8(new T2(1,_hy,_i7)));}));}},_ic=function(_id,_ie){var _if=E(_id);return new F(function(){return _i2(0,_if.a,_if.b,_if.c,_ie);});},_ig=new T(function(){return B(unCStr("IdentPay "));}),_ih=function(_ii,_ij,_ik){if(_ii<11){return new F(function(){return _hq(_ig,new T(function(){return B(_hA(11,E(_ij),_ik));},1));});}else{var _il=new T(function(){return B(_hq(_ig,new T(function(){return B(_hA(11,E(_ij),new T2(1,_hy,_ik)));},1)));});return new T2(1,_hz,_il);}},_im=new T(function(){return B(unCStr(": empty list"));}),_in=new T(function(){return B(unCStr("Prelude."));}),_io=function(_ip){return new F(function(){return err(B(_hq(_in,new T(function(){return B(_hq(_ip,_im));},1))));});},_iq=new T(function(){return B(unCStr("foldr1"));}),_ir=new T(function(){return B(_io(_iq));}),_is=function(_it,_iu){var _iv=E(_iu);if(!_iv._){return E(_ir);}else{var _iw=_iv.a,_ix=E(_iv.b);if(!_ix._){return E(_iw);}else{return new F(function(){return A2(_it,_iw,new T(function(){return B(_is(_it,_ix));}));});}}},_iy=function(_iz,_iA,_iB){var _iC=new T(function(){var _iD=function(_iE){var _iF=E(_iz),_iG=new T(function(){return B(A3(_is,_hk,new T2(1,function(_iH){return new F(function(){return _ih(0,_iF.a,_iH);});},new T2(1,function(_iI){return new F(function(){return _hA(0,E(_iF.b),_iI);});},_1)),new T2(1,_hy,_iE)));});return new T2(1,_hz,_iG);};return B(A3(_is,_hk,new T2(1,_iD,new T2(1,function(_iJ){return new F(function(){return _hA(0,E(_iA),_iJ);});},_1)),new T2(1,_hy,_iB)));});return new T2(0,_hz,_iC);},_iK=function(_iL,_iM){var _iN=E(_iL),_iO=B(_iy(_iN.a,_iN.b,_iM));return new T2(1,_iO.a,_iO.b);},_iP=93,_iQ=91,_iR=function(_iS,_iT,_iU){var _iV=E(_iT);if(!_iV._){return new F(function(){return unAppCStr("[]",_iU);});}else{var _iW=new T(function(){var _iX=new T(function(){var _iY=function(_iZ){var _j0=E(_iZ);if(!_j0._){return E(new T2(1,_iP,_iU));}else{var _j1=new T(function(){return B(A2(_iS,_j0.a,new T(function(){return B(_iY(_j0.b));})));});return new T2(1,_hj,_j1);}};return B(_iY(_iV.b));});return B(A2(_iS,_iV.a,_iX));});return new T2(1,_iQ,_iW);}},_j2=function(_j3,_j4){return new F(function(){return _iR(_iK,_j3,_j4);});},_j5=new T(function(){return B(unCStr("IdentChoice "));}),_j6=function(_j7,_j8,_j9){if(_j7<11){return new F(function(){return _hq(_j5,new T(function(){return B(_hA(11,E(_j8),_j9));},1));});}else{var _ja=new T(function(){return B(_hq(_j5,new T(function(){return B(_hA(11,E(_j8),new T2(1,_hy,_j9)));},1)));});return new T2(1,_hz,_ja);}},_jb=function(_jc,_jd,_je){var _jf=new T(function(){var _jg=function(_jh){var _ji=E(_jc),_jj=new T(function(){return B(A3(_is,_hk,new T2(1,function(_jk){return new F(function(){return _j6(0,_ji.a,_jk);});},new T2(1,function(_jl){return new F(function(){return _hA(0,E(_ji.b),_jl);});},_1)),new T2(1,_hy,_jh)));});return new T2(1,_hz,_jj);};return B(A3(_is,_hk,new T2(1,_jg,new T2(1,function(_jm){return new F(function(){return _hA(0,E(_jd),_jm);});},_1)),new T2(1,_hy,_je)));});return new T2(0,_hz,_jf);},_jn=function(_jo,_jp){var _jq=E(_jo),_jr=B(_jb(_jq.a,_jq.b,_jp));return new T2(1,_jr.a,_jr.b);},_js=function(_jt,_ju){return new F(function(){return _iR(_jn,_jt,_ju);});},_jv=new T2(1,_hy,_1),_jw=function(_jx,_jy){while(1){var _jz=B((function(_jA,_jB){var _jC=E(_jB);if(!_jC._){_jx=new T2(1,_jC.b,new T(function(){return B(_jw(_jA,_jC.d));}));_jy=_jC.c;return __continue;}else{return E(_jA);}})(_jx,_jy));if(_jz!=__continue){return _jz;}}},_jD=function(_jE,_jF,_jG,_jH){var _jI=new T(function(){var _jJ=new T(function(){return B(_hc(_1,_jH));}),_jK=new T(function(){return B(_hc(_1,_jG));}),_jL=new T(function(){return B(_jw(_1,_jF));}),_jM=new T(function(){return B(_jw(_1,_jE));});return B(A3(_is,_hk,new T2(1,function(_jN){return new F(function(){return _iR(_hX,_jM,_jN);});},new T2(1,function(_jO){return new F(function(){return _iR(_ic,_jL,_jO);});},new T2(1,function(_jP){return new F(function(){return _j2(_jK,_jP);});},new T2(1,function(_jQ){return new F(function(){return _js(_jJ,_jQ);});},_1)))),_jv));});return new T2(0,_hz,_jI);},_jR=new T(function(){return B(err(_ha));}),_jS=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_jT=new T(function(){return B(err(_jS));}),_jU=new T0(2),_jV=function(_jW){return new T2(3,_jW,_jU);},_jX=new T(function(){return B(unCStr("base"));}),_jY=new T(function(){return B(unCStr("Control.Exception.Base"));}),_jZ=new T(function(){return B(unCStr("PatternMatchFail"));}),_k0=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_jX,_jY,_jZ),_k1=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_k0,_1,_1),_k2=function(_k3){return E(_k1);},_k4=function(_k5){return E(E(_k5).a);},_k6=function(_k7,_k8,_k9){var _ka=B(A1(_k7,_)),_kb=B(A1(_k8,_)),_kc=hs_eqWord64(_ka.a,_kb.a);if(!_kc){return __Z;}else{var _kd=hs_eqWord64(_ka.b,_kb.b);return (!_kd)?__Z:new T1(1,_k9);}},_ke=function(_kf){var _kg=E(_kf);return new F(function(){return _k6(B(_k4(_kg.a)),_k2,_kg.b);});},_kh=function(_ki){return E(E(_ki).a);},_kj=function(_kk){return new T2(0,_kl,_kk);},_km=function(_kn,_ko){return new F(function(){return _hq(E(_kn).a,_ko);});},_kp=function(_kq,_kr){return new F(function(){return _iR(_km,_kq,_kr);});},_ks=function(_kt,_ku,_kv){return new F(function(){return _hq(E(_ku).a,_kv);});},_kw=new T3(0,_ks,_kh,_kp),_kl=new T(function(){return new T5(0,_k2,_kw,_kj,_ke,_kh);}),_kx=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_ky=function(_kz){return E(E(_kz).c);},_kA=function(_kB,_kC){return new F(function(){return die(new T(function(){return B(A2(_ky,_kC,_kB));}));});},_kD=function(_kE,_kF){return new F(function(){return _kA(_kE,_kF);});},_kG=function(_kH,_kI){var _kJ=E(_kI);if(!_kJ._){return new T2(0,_1,_1);}else{var _kK=_kJ.a;if(!B(A1(_kH,_kK))){return new T2(0,_1,_kJ);}else{var _kL=new T(function(){var _kM=B(_kG(_kH,_kJ.b));return new T2(0,_kM.a,_kM.b);});return new T2(0,new T2(1,_kK,new T(function(){return E(E(_kL).a);})),new T(function(){return E(E(_kL).b);}));}}},_kN=32,_kO=new T(function(){return B(unCStr("\n"));}),_kP=function(_kQ){return (E(_kQ)==124)?false:true;},_kR=function(_kS,_kT){var _kU=B(_kG(_kP,B(unCStr(_kS)))),_kV=_kU.a,_kW=function(_kX,_kY){var _kZ=new T(function(){var _l0=new T(function(){return B(_hq(_kT,new T(function(){return B(_hq(_kY,_kO));},1)));});return B(unAppCStr(": ",_l0));},1);return new F(function(){return _hq(_kX,_kZ);});},_l1=E(_kU.b);if(!_l1._){return new F(function(){return _kW(_kV,_1);});}else{if(E(_l1.a)==124){return new F(function(){return _kW(_kV,new T2(1,_kN,_l1.b));});}else{return new F(function(){return _kW(_kV,_1);});}}},_l2=function(_l3){return new F(function(){return _kD(new T1(0,new T(function(){return B(_kR(_l3,_kx));})),_kl);});},_l4=new T(function(){return B(_l2("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_l5=function(_l6,_l7){while(1){var _l8=B((function(_l9,_la){var _lb=E(_l9);switch(_lb._){case 0:var _lc=E(_la);if(!_lc._){return __Z;}else{_l6=B(A1(_lb.a,_lc.a));_l7=_lc.b;return __continue;}break;case 1:var _ld=B(A1(_lb.a,_la)),_le=_la;_l6=_ld;_l7=_le;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_lb.a,_la),new T(function(){return B(_l5(_lb.b,_la));}));default:return E(_lb.a);}})(_l6,_l7));if(_l8!=__continue){return _l8;}}},_lf=function(_lg,_lh){var _li=function(_lj){var _lk=E(_lh);if(_lk._==3){return new T2(3,_lk.a,new T(function(){return B(_lf(_lg,_lk.b));}));}else{var _ll=E(_lg);if(_ll._==2){return E(_lk);}else{var _lm=E(_lk);if(_lm._==2){return E(_ll);}else{var _ln=function(_lo){var _lp=E(_lm);if(_lp._==4){var _lq=function(_lr){return new T1(4,new T(function(){return B(_hq(B(_l5(_ll,_lr)),_lp.a));}));};return new T1(1,_lq);}else{var _ls=E(_ll);if(_ls._==1){var _lt=_ls.a,_lu=E(_lp);if(!_lu._){return new T1(1,function(_lv){return new F(function(){return _lf(B(A1(_lt,_lv)),_lu);});});}else{var _lw=function(_lx){return new F(function(){return _lf(B(A1(_lt,_lx)),new T(function(){return B(A1(_lu.a,_lx));}));});};return new T1(1,_lw);}}else{var _ly=E(_lp);if(!_ly._){return E(_l4);}else{var _lz=function(_lA){return new F(function(){return _lf(_ls,new T(function(){return B(A1(_ly.a,_lA));}));});};return new T1(1,_lz);}}}},_lB=E(_ll);switch(_lB._){case 1:var _lC=E(_lm);if(_lC._==4){var _lD=function(_lE){return new T1(4,new T(function(){return B(_hq(B(_l5(B(A1(_lB.a,_lE)),_lE)),_lC.a));}));};return new T1(1,_lD);}else{return new F(function(){return _ln(_);});}break;case 4:var _lF=_lB.a,_lG=E(_lm);switch(_lG._){case 0:var _lH=function(_lI){var _lJ=new T(function(){return B(_hq(_lF,new T(function(){return B(_l5(_lG,_lI));},1)));});return new T1(4,_lJ);};return new T1(1,_lH);case 1:var _lK=function(_lL){var _lM=new T(function(){return B(_hq(_lF,new T(function(){return B(_l5(B(A1(_lG.a,_lL)),_lL));},1)));});return new T1(4,_lM);};return new T1(1,_lK);default:return new T1(4,new T(function(){return B(_hq(_lF,_lG.a));}));}break;default:return new F(function(){return _ln(_);});}}}}},_lN=E(_lg);switch(_lN._){case 0:var _lO=E(_lh);if(!_lO._){var _lP=function(_lQ){return new F(function(){return _lf(B(A1(_lN.a,_lQ)),new T(function(){return B(A1(_lO.a,_lQ));}));});};return new T1(0,_lP);}else{return new F(function(){return _li(_);});}break;case 3:return new T2(3,_lN.a,new T(function(){return B(_lf(_lN.b,_lh));}));default:return new F(function(){return _li(_);});}},_lR=new T(function(){return B(unCStr("("));}),_lS=new T(function(){return B(unCStr(")"));}),_lT=function(_lU,_lV){while(1){var _lW=E(_lU);if(!_lW._){return (E(_lV)._==0)?true:false;}else{var _lX=E(_lV);if(!_lX._){return false;}else{if(E(_lW.a)!=E(_lX.a)){return false;}else{_lU=_lW.b;_lV=_lX.b;continue;}}}}},_lY=function(_lZ,_m0){return E(_lZ)!=E(_m0);},_m1=function(_m2,_m3){return E(_m2)==E(_m3);},_m4=new T2(0,_m1,_lY),_m5=function(_m6,_m7){while(1){var _m8=E(_m6);if(!_m8._){return (E(_m7)._==0)?true:false;}else{var _m9=E(_m7);if(!_m9._){return false;}else{if(E(_m8.a)!=E(_m9.a)){return false;}else{_m6=_m8.b;_m7=_m9.b;continue;}}}}},_ma=function(_mb,_mc){return (!B(_m5(_mb,_mc)))?true:false;},_md=new T2(0,_m5,_ma),_me=function(_mf,_mg){var _mh=E(_mf);switch(_mh._){case 0:return new T1(0,function(_mi){return new F(function(){return _me(B(A1(_mh.a,_mi)),_mg);});});case 1:return new T1(1,function(_mj){return new F(function(){return _me(B(A1(_mh.a,_mj)),_mg);});});case 2:return new T0(2);case 3:return new F(function(){return _lf(B(A1(_mg,_mh.a)),new T(function(){return B(_me(_mh.b,_mg));}));});break;default:var _mk=function(_ml){var _mm=E(_ml);if(!_mm._){return __Z;}else{var _mn=E(_mm.a);return new F(function(){return _hq(B(_l5(B(A1(_mg,_mn.a)),_mn.b)),new T(function(){return B(_mk(_mm.b));},1));});}},_mo=B(_mk(_mh.a));return (_mo._==0)?new T0(2):new T1(4,_mo);}},_mp=function(_mq,_mr){var _ms=E(_mq);if(!_ms){return new F(function(){return A1(_mr,_h9);});}else{var _mt=new T(function(){return B(_mp(_ms-1|0,_mr));});return new T1(0,function(_mu){return E(_mt);});}},_mv=function(_mw,_mx,_my){var _mz=new T(function(){return B(A1(_mw,_jV));}),_mA=function(_mB,_mC,_mD,_mE){while(1){var _mF=B((function(_mG,_mH,_mI,_mJ){var _mK=E(_mG);switch(_mK._){case 0:var _mL=E(_mH);if(!_mL._){return new F(function(){return A1(_mx,_mJ);});}else{var _mM=_mI+1|0,_mN=_mJ;_mB=B(A1(_mK.a,_mL.a));_mC=_mL.b;_mD=_mM;_mE=_mN;return __continue;}break;case 1:var _mO=B(A1(_mK.a,_mH)),_mP=_mH,_mM=_mI,_mN=_mJ;_mB=_mO;_mC=_mP;_mD=_mM;_mE=_mN;return __continue;case 2:return new F(function(){return A1(_mx,_mJ);});break;case 3:var _mQ=new T(function(){return B(_me(_mK,_mJ));});return new F(function(){return _mp(_mI,function(_mR){return E(_mQ);});});break;default:return new F(function(){return _me(_mK,_mJ);});}})(_mB,_mC,_mD,_mE));if(_mF!=__continue){return _mF;}}};return function(_mS){return new F(function(){return _mA(_mz,_mS,0,_my);});};},_mT=function(_mU){return new F(function(){return A1(_mU,_1);});},_mV=function(_mW,_mX){var _mY=function(_mZ){var _n0=E(_mZ);if(!_n0._){return E(_mT);}else{var _n1=_n0.a;if(!B(A1(_mW,_n1))){return E(_mT);}else{var _n2=new T(function(){return B(_mY(_n0.b));}),_n3=function(_n4){var _n5=new T(function(){return B(A1(_n2,function(_n6){return new F(function(){return A1(_n4,new T2(1,_n1,_n6));});}));});return new T1(0,function(_n7){return E(_n5);});};return E(_n3);}}};return function(_n8){return new F(function(){return A2(_mY,_n8,_mX);});};},_n9=new T0(6),_na=function(_nb){return E(_nb);},_nc=new T(function(){return B(unCStr("valDig: Bad base"));}),_nd=new T(function(){return B(err(_nc));}),_ne=function(_nf,_ng){var _nh=function(_ni,_nj){var _nk=E(_ni);if(!_nk._){var _nl=new T(function(){return B(A1(_nj,_1));});return function(_nm){return new F(function(){return A1(_nm,_nl);});};}else{var _nn=E(_nk.a),_no=function(_np){var _nq=new T(function(){return B(_nh(_nk.b,function(_nr){return new F(function(){return A1(_nj,new T2(1,_np,_nr));});}));}),_ns=function(_nt){var _nu=new T(function(){return B(A1(_nq,_nt));});return new T1(0,function(_nv){return E(_nu);});};return E(_ns);};switch(E(_nf)){case 8:if(48>_nn){var _nw=new T(function(){return B(A1(_nj,_1));});return function(_nx){return new F(function(){return A1(_nx,_nw);});};}else{if(_nn>55){var _ny=new T(function(){return B(A1(_nj,_1));});return function(_nz){return new F(function(){return A1(_nz,_ny);});};}else{return new F(function(){return _no(_nn-48|0);});}}break;case 10:if(48>_nn){var _nA=new T(function(){return B(A1(_nj,_1));});return function(_nB){return new F(function(){return A1(_nB,_nA);});};}else{if(_nn>57){var _nC=new T(function(){return B(A1(_nj,_1));});return function(_nD){return new F(function(){return A1(_nD,_nC);});};}else{return new F(function(){return _no(_nn-48|0);});}}break;case 16:if(48>_nn){if(97>_nn){if(65>_nn){var _nE=new T(function(){return B(A1(_nj,_1));});return function(_nF){return new F(function(){return A1(_nF,_nE);});};}else{if(_nn>70){var _nG=new T(function(){return B(A1(_nj,_1));});return function(_nH){return new F(function(){return A1(_nH,_nG);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{if(_nn>102){if(65>_nn){var _nI=new T(function(){return B(A1(_nj,_1));});return function(_nJ){return new F(function(){return A1(_nJ,_nI);});};}else{if(_nn>70){var _nK=new T(function(){return B(A1(_nj,_1));});return function(_nL){return new F(function(){return A1(_nL,_nK);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{return new F(function(){return _no((_nn-97|0)+10|0);});}}}else{if(_nn>57){if(97>_nn){if(65>_nn){var _nM=new T(function(){return B(A1(_nj,_1));});return function(_nN){return new F(function(){return A1(_nN,_nM);});};}else{if(_nn>70){var _nO=new T(function(){return B(A1(_nj,_1));});return function(_nP){return new F(function(){return A1(_nP,_nO);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{if(_nn>102){if(65>_nn){var _nQ=new T(function(){return B(A1(_nj,_1));});return function(_nR){return new F(function(){return A1(_nR,_nQ);});};}else{if(_nn>70){var _nS=new T(function(){return B(A1(_nj,_1));});return function(_nT){return new F(function(){return A1(_nT,_nS);});};}else{return new F(function(){return _no((_nn-65|0)+10|0);});}}}else{return new F(function(){return _no((_nn-97|0)+10|0);});}}}else{return new F(function(){return _no(_nn-48|0);});}}break;default:return E(_nd);}}},_nU=function(_nV){var _nW=E(_nV);if(!_nW._){return new T0(2);}else{return new F(function(){return A1(_ng,_nW);});}};return function(_nX){return new F(function(){return A3(_nh,_nX,_na,_nU);});};},_nY=16,_nZ=8,_o0=function(_o1){var _o2=function(_o3){return new F(function(){return A1(_o1,new T1(5,new T2(0,_nZ,_o3)));});},_o4=function(_o5){return new F(function(){return A1(_o1,new T1(5,new T2(0,_nY,_o5)));});},_o6=function(_o7){switch(E(_o7)){case 79:return new T1(1,B(_ne(_nZ,_o2)));case 88:return new T1(1,B(_ne(_nY,_o4)));case 111:return new T1(1,B(_ne(_nZ,_o2)));case 120:return new T1(1,B(_ne(_nY,_o4)));default:return new T0(2);}};return function(_o8){return (E(_o8)==48)?E(new T1(0,_o6)):new T0(2);};},_o9=function(_oa){return new T1(0,B(_o0(_oa)));},_ob=__Z,_oc=function(_od){return new F(function(){return A1(_od,_ob);});},_oe=function(_of){return new F(function(){return A1(_of,_ob);});},_og=10,_oh=new T1(0,1),_oi=new T1(0,2147483647),_oj=function(_ok,_ol){while(1){var _om=E(_ok);if(!_om._){var _on=_om.a,_oo=E(_ol);if(!_oo._){var _op=_oo.a,_oq=addC(_on,_op);if(!E(_oq.b)){return new T1(0,_oq.a);}else{_ok=new T1(1,I_fromInt(_on));_ol=new T1(1,I_fromInt(_op));continue;}}else{_ok=new T1(1,I_fromInt(_on));_ol=_oo;continue;}}else{var _or=E(_ol);if(!_or._){_ok=_om;_ol=new T1(1,I_fromInt(_or.a));continue;}else{return new T1(1,I_add(_om.a,_or.a));}}}},_os=new T(function(){return B(_oj(_oi,_oh));}),_ot=function(_ou){var _ov=E(_ou);if(!_ov._){var _ow=E(_ov.a);return (_ow==( -2147483648))?E(_os):new T1(0, -_ow);}else{return new T1(1,I_negate(_ov.a));}},_ox=new T1(0,10),_oy=function(_oz,_oA){while(1){var _oB=E(_oz);if(!_oB._){return E(_oA);}else{var _oC=_oA+1|0;_oz=_oB.b;_oA=_oC;continue;}}},_oD=function(_oE,_oF){var _oG=E(_oF);return (_oG._==0)?__Z:new T2(1,new T(function(){return B(A1(_oE,_oG.a));}),new T(function(){return B(_oD(_oE,_oG.b));}));},_oH=function(_oI){return new T1(0,_oI);},_oJ=function(_oK){return new F(function(){return _oH(E(_oK));});},_oL=new T(function(){return B(unCStr("this should not happen"));}),_oM=new T(function(){return B(err(_oL));}),_oN=function(_oO,_oP){while(1){var _oQ=E(_oO);if(!_oQ._){var _oR=_oQ.a,_oS=E(_oP);if(!_oS._){var _oT=_oS.a;if(!(imul(_oR,_oT)|0)){return new T1(0,imul(_oR,_oT)|0);}else{_oO=new T1(1,I_fromInt(_oR));_oP=new T1(1,I_fromInt(_oT));continue;}}else{_oO=new T1(1,I_fromInt(_oR));_oP=_oS;continue;}}else{var _oU=E(_oP);if(!_oU._){_oO=_oQ;_oP=new T1(1,I_fromInt(_oU.a));continue;}else{return new T1(1,I_mul(_oQ.a,_oU.a));}}}},_oV=function(_oW,_oX){var _oY=E(_oX);if(!_oY._){return __Z;}else{var _oZ=E(_oY.b);return (_oZ._==0)?E(_oM):new T2(1,B(_oj(B(_oN(_oY.a,_oW)),_oZ.a)),new T(function(){return B(_oV(_oW,_oZ.b));}));}},_p0=new T1(0,0),_p1=function(_p2,_p3,_p4){while(1){var _p5=B((function(_p6,_p7,_p8){var _p9=E(_p8);if(!_p9._){return E(_p0);}else{if(!E(_p9.b)._){return E(_p9.a);}else{var _pa=E(_p7);if(_pa<=40){var _pb=function(_pc,_pd){while(1){var _pe=E(_pd);if(!_pe._){return E(_pc);}else{var _pf=B(_oj(B(_oN(_pc,_p6)),_pe.a));_pc=_pf;_pd=_pe.b;continue;}}};return new F(function(){return _pb(_p0,_p9);});}else{var _pg=B(_oN(_p6,_p6));if(!(_pa%2)){var _ph=B(_oV(_p6,_p9));_p2=_pg;_p3=quot(_pa+1|0,2);_p4=_ph;return __continue;}else{var _ph=B(_oV(_p6,new T2(1,_p0,_p9)));_p2=_pg;_p3=quot(_pa+1|0,2);_p4=_ph;return __continue;}}}}})(_p2,_p3,_p4));if(_p5!=__continue){return _p5;}}},_pi=function(_pj,_pk){return new F(function(){return _p1(_pj,new T(function(){return B(_oy(_pk,0));},1),B(_oD(_oJ,_pk)));});},_pl=function(_pm){var _pn=new T(function(){var _po=new T(function(){var _pp=function(_pq){return new F(function(){return A1(_pm,new T1(1,new T(function(){return B(_pi(_ox,_pq));})));});};return new T1(1,B(_ne(_og,_pp)));}),_pr=function(_ps){if(E(_ps)==43){var _pt=function(_pu){return new F(function(){return A1(_pm,new T1(1,new T(function(){return B(_pi(_ox,_pu));})));});};return new T1(1,B(_ne(_og,_pt)));}else{return new T0(2);}},_pv=function(_pw){if(E(_pw)==45){var _px=function(_py){return new F(function(){return A1(_pm,new T1(1,new T(function(){return B(_ot(B(_pi(_ox,_py))));})));});};return new T1(1,B(_ne(_og,_px)));}else{return new T0(2);}};return B(_lf(B(_lf(new T1(0,_pv),new T1(0,_pr))),_po));});return new F(function(){return _lf(new T1(0,function(_pz){return (E(_pz)==101)?E(_pn):new T0(2);}),new T1(0,function(_pA){return (E(_pA)==69)?E(_pn):new T0(2);}));});},_pB=function(_pC){var _pD=function(_pE){return new F(function(){return A1(_pC,new T1(1,_pE));});};return function(_pF){return (E(_pF)==46)?new T1(1,B(_ne(_og,_pD))):new T0(2);};},_pG=function(_pH){return new T1(0,B(_pB(_pH)));},_pI=function(_pJ){var _pK=function(_pL){var _pM=function(_pN){return new T1(1,B(_mv(_pl,_oc,function(_pO){return new F(function(){return A1(_pJ,new T1(5,new T3(1,_pL,_pN,_pO)));});})));};return new T1(1,B(_mv(_pG,_oe,_pM)));};return new F(function(){return _ne(_og,_pK);});},_pP=function(_pQ){return new T1(1,B(_pI(_pQ)));},_pR=function(_pS){return E(E(_pS).a);},_pT=function(_pU,_pV,_pW){while(1){var _pX=E(_pW);if(!_pX._){return false;}else{if(!B(A3(_pR,_pU,_pV,_pX.a))){_pW=_pX.b;continue;}else{return true;}}}},_pY=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_pZ=function(_q0){return new F(function(){return _pT(_m4,_q0,_pY);});},_q1=false,_q2=true,_q3=function(_q4){var _q5=new T(function(){return B(A1(_q4,_nZ));}),_q6=new T(function(){return B(A1(_q4,_nY));});return function(_q7){switch(E(_q7)){case 79:return E(_q5);case 88:return E(_q6);case 111:return E(_q5);case 120:return E(_q6);default:return new T0(2);}};},_q8=function(_q9){return new T1(0,B(_q3(_q9)));},_qa=function(_qb){return new F(function(){return A1(_qb,_og);});},_qc=function(_qd){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_hA(9,_qd,_1));}))));});},_qe=function(_qf){var _qg=E(_qf);if(!_qg._){return E(_qg.a);}else{return new F(function(){return I_toInt(_qg.a);});}},_qh=function(_qi,_qj){var _qk=E(_qi);if(!_qk._){var _ql=_qk.a,_qm=E(_qj);return (_qm._==0)?_ql<=_qm.a:I_compareInt(_qm.a,_ql)>=0;}else{var _qn=_qk.a,_qo=E(_qj);return (_qo._==0)?I_compareInt(_qn,_qo.a)<=0:I_compare(_qn,_qo.a)<=0;}},_qp=function(_qq){return new T0(2);},_qr=function(_qs){var _qt=E(_qs);if(!_qt._){return E(_qp);}else{var _qu=_qt.a,_qv=E(_qt.b);if(!_qv._){return E(_qu);}else{var _qw=new T(function(){return B(_qr(_qv));}),_qx=function(_qy){return new F(function(){return _lf(B(A1(_qu,_qy)),new T(function(){return B(A1(_qw,_qy));}));});};return E(_qx);}}},_qz=function(_qA,_qB){var _qC=function(_qD,_qE,_qF){var _qG=E(_qD);if(!_qG._){return new F(function(){return A1(_qF,_qA);});}else{var _qH=E(_qE);if(!_qH._){return new T0(2);}else{if(E(_qG.a)!=E(_qH.a)){return new T0(2);}else{var _qI=new T(function(){return B(_qC(_qG.b,_qH.b,_qF));});return new T1(0,function(_qJ){return E(_qI);});}}}};return function(_qK){return new F(function(){return _qC(_qA,_qK,_qB);});};},_qL=new T(function(){return B(unCStr("SO"));}),_qM=14,_qN=function(_qO){var _qP=new T(function(){return B(A1(_qO,_qM));});return new T1(1,B(_qz(_qL,function(_qQ){return E(_qP);})));},_qR=new T(function(){return B(unCStr("SOH"));}),_qS=1,_qT=function(_qU){var _qV=new T(function(){return B(A1(_qU,_qS));});return new T1(1,B(_qz(_qR,function(_qW){return E(_qV);})));},_qX=function(_qY){return new T1(1,B(_mv(_qT,_qN,_qY)));},_qZ=new T(function(){return B(unCStr("NUL"));}),_r0=0,_r1=function(_r2){var _r3=new T(function(){return B(A1(_r2,_r0));});return new T1(1,B(_qz(_qZ,function(_r4){return E(_r3);})));},_r5=new T(function(){return B(unCStr("STX"));}),_r6=2,_r7=function(_r8){var _r9=new T(function(){return B(A1(_r8,_r6));});return new T1(1,B(_qz(_r5,function(_ra){return E(_r9);})));},_rb=new T(function(){return B(unCStr("ETX"));}),_rc=3,_rd=function(_re){var _rf=new T(function(){return B(A1(_re,_rc));});return new T1(1,B(_qz(_rb,function(_rg){return E(_rf);})));},_rh=new T(function(){return B(unCStr("EOT"));}),_ri=4,_rj=function(_rk){var _rl=new T(function(){return B(A1(_rk,_ri));});return new T1(1,B(_qz(_rh,function(_rm){return E(_rl);})));},_rn=new T(function(){return B(unCStr("ENQ"));}),_ro=5,_rp=function(_rq){var _rr=new T(function(){return B(A1(_rq,_ro));});return new T1(1,B(_qz(_rn,function(_rs){return E(_rr);})));},_rt=new T(function(){return B(unCStr("ACK"));}),_ru=6,_rv=function(_rw){var _rx=new T(function(){return B(A1(_rw,_ru));});return new T1(1,B(_qz(_rt,function(_ry){return E(_rx);})));},_rz=new T(function(){return B(unCStr("BEL"));}),_rA=7,_rB=function(_rC){var _rD=new T(function(){return B(A1(_rC,_rA));});return new T1(1,B(_qz(_rz,function(_rE){return E(_rD);})));},_rF=new T(function(){return B(unCStr("BS"));}),_rG=8,_rH=function(_rI){var _rJ=new T(function(){return B(A1(_rI,_rG));});return new T1(1,B(_qz(_rF,function(_rK){return E(_rJ);})));},_rL=new T(function(){return B(unCStr("HT"));}),_rM=9,_rN=function(_rO){var _rP=new T(function(){return B(A1(_rO,_rM));});return new T1(1,B(_qz(_rL,function(_rQ){return E(_rP);})));},_rR=new T(function(){return B(unCStr("LF"));}),_rS=10,_rT=function(_rU){var _rV=new T(function(){return B(A1(_rU,_rS));});return new T1(1,B(_qz(_rR,function(_rW){return E(_rV);})));},_rX=new T(function(){return B(unCStr("VT"));}),_rY=11,_rZ=function(_s0){var _s1=new T(function(){return B(A1(_s0,_rY));});return new T1(1,B(_qz(_rX,function(_s2){return E(_s1);})));},_s3=new T(function(){return B(unCStr("FF"));}),_s4=12,_s5=function(_s6){var _s7=new T(function(){return B(A1(_s6,_s4));});return new T1(1,B(_qz(_s3,function(_s8){return E(_s7);})));},_s9=new T(function(){return B(unCStr("CR"));}),_sa=13,_sb=function(_sc){var _sd=new T(function(){return B(A1(_sc,_sa));});return new T1(1,B(_qz(_s9,function(_se){return E(_sd);})));},_sf=new T(function(){return B(unCStr("SI"));}),_sg=15,_sh=function(_si){var _sj=new T(function(){return B(A1(_si,_sg));});return new T1(1,B(_qz(_sf,function(_sk){return E(_sj);})));},_sl=new T(function(){return B(unCStr("DLE"));}),_sm=16,_sn=function(_so){var _sp=new T(function(){return B(A1(_so,_sm));});return new T1(1,B(_qz(_sl,function(_sq){return E(_sp);})));},_sr=new T(function(){return B(unCStr("DC1"));}),_ss=17,_st=function(_su){var _sv=new T(function(){return B(A1(_su,_ss));});return new T1(1,B(_qz(_sr,function(_sw){return E(_sv);})));},_sx=new T(function(){return B(unCStr("DC2"));}),_sy=18,_sz=function(_sA){var _sB=new T(function(){return B(A1(_sA,_sy));});return new T1(1,B(_qz(_sx,function(_sC){return E(_sB);})));},_sD=new T(function(){return B(unCStr("DC3"));}),_sE=19,_sF=function(_sG){var _sH=new T(function(){return B(A1(_sG,_sE));});return new T1(1,B(_qz(_sD,function(_sI){return E(_sH);})));},_sJ=new T(function(){return B(unCStr("DC4"));}),_sK=20,_sL=function(_sM){var _sN=new T(function(){return B(A1(_sM,_sK));});return new T1(1,B(_qz(_sJ,function(_sO){return E(_sN);})));},_sP=new T(function(){return B(unCStr("NAK"));}),_sQ=21,_sR=function(_sS){var _sT=new T(function(){return B(A1(_sS,_sQ));});return new T1(1,B(_qz(_sP,function(_sU){return E(_sT);})));},_sV=new T(function(){return B(unCStr("SYN"));}),_sW=22,_sX=function(_sY){var _sZ=new T(function(){return B(A1(_sY,_sW));});return new T1(1,B(_qz(_sV,function(_t0){return E(_sZ);})));},_t1=new T(function(){return B(unCStr("ETB"));}),_t2=23,_t3=function(_t4){var _t5=new T(function(){return B(A1(_t4,_t2));});return new T1(1,B(_qz(_t1,function(_t6){return E(_t5);})));},_t7=new T(function(){return B(unCStr("CAN"));}),_t8=24,_t9=function(_ta){var _tb=new T(function(){return B(A1(_ta,_t8));});return new T1(1,B(_qz(_t7,function(_tc){return E(_tb);})));},_td=new T(function(){return B(unCStr("EM"));}),_te=25,_tf=function(_tg){var _th=new T(function(){return B(A1(_tg,_te));});return new T1(1,B(_qz(_td,function(_ti){return E(_th);})));},_tj=new T(function(){return B(unCStr("SUB"));}),_tk=26,_tl=function(_tm){var _tn=new T(function(){return B(A1(_tm,_tk));});return new T1(1,B(_qz(_tj,function(_to){return E(_tn);})));},_tp=new T(function(){return B(unCStr("ESC"));}),_tq=27,_tr=function(_ts){var _tt=new T(function(){return B(A1(_ts,_tq));});return new T1(1,B(_qz(_tp,function(_tu){return E(_tt);})));},_tv=new T(function(){return B(unCStr("FS"));}),_tw=28,_tx=function(_ty){var _tz=new T(function(){return B(A1(_ty,_tw));});return new T1(1,B(_qz(_tv,function(_tA){return E(_tz);})));},_tB=new T(function(){return B(unCStr("GS"));}),_tC=29,_tD=function(_tE){var _tF=new T(function(){return B(A1(_tE,_tC));});return new T1(1,B(_qz(_tB,function(_tG){return E(_tF);})));},_tH=new T(function(){return B(unCStr("RS"));}),_tI=30,_tJ=function(_tK){var _tL=new T(function(){return B(A1(_tK,_tI));});return new T1(1,B(_qz(_tH,function(_tM){return E(_tL);})));},_tN=new T(function(){return B(unCStr("US"));}),_tO=31,_tP=function(_tQ){var _tR=new T(function(){return B(A1(_tQ,_tO));});return new T1(1,B(_qz(_tN,function(_tS){return E(_tR);})));},_tT=new T(function(){return B(unCStr("SP"));}),_tU=32,_tV=function(_tW){var _tX=new T(function(){return B(A1(_tW,_tU));});return new T1(1,B(_qz(_tT,function(_tY){return E(_tX);})));},_tZ=new T(function(){return B(unCStr("DEL"));}),_u0=127,_u1=function(_u2){var _u3=new T(function(){return B(A1(_u2,_u0));});return new T1(1,B(_qz(_tZ,function(_u4){return E(_u3);})));},_u5=new T2(1,_u1,_1),_u6=new T2(1,_tV,_u5),_u7=new T2(1,_tP,_u6),_u8=new T2(1,_tJ,_u7),_u9=new T2(1,_tD,_u8),_ua=new T2(1,_tx,_u9),_ub=new T2(1,_tr,_ua),_uc=new T2(1,_tl,_ub),_ud=new T2(1,_tf,_uc),_ue=new T2(1,_t9,_ud),_uf=new T2(1,_t3,_ue),_ug=new T2(1,_sX,_uf),_uh=new T2(1,_sR,_ug),_ui=new T2(1,_sL,_uh),_uj=new T2(1,_sF,_ui),_uk=new T2(1,_sz,_uj),_ul=new T2(1,_st,_uk),_um=new T2(1,_sn,_ul),_un=new T2(1,_sh,_um),_uo=new T2(1,_sb,_un),_up=new T2(1,_s5,_uo),_uq=new T2(1,_rZ,_up),_ur=new T2(1,_rT,_uq),_us=new T2(1,_rN,_ur),_ut=new T2(1,_rH,_us),_uu=new T2(1,_rB,_ut),_uv=new T2(1,_rv,_uu),_uw=new T2(1,_rp,_uv),_ux=new T2(1,_rj,_uw),_uy=new T2(1,_rd,_ux),_uz=new T2(1,_r7,_uy),_uA=new T2(1,_r1,_uz),_uB=new T2(1,_qX,_uA),_uC=new T(function(){return B(_qr(_uB));}),_uD=34,_uE=new T1(0,1114111),_uF=92,_uG=39,_uH=function(_uI){var _uJ=new T(function(){return B(A1(_uI,_rA));}),_uK=new T(function(){return B(A1(_uI,_rG));}),_uL=new T(function(){return B(A1(_uI,_rM));}),_uM=new T(function(){return B(A1(_uI,_rS));}),_uN=new T(function(){return B(A1(_uI,_rY));}),_uO=new T(function(){return B(A1(_uI,_s4));}),_uP=new T(function(){return B(A1(_uI,_sa));}),_uQ=new T(function(){return B(A1(_uI,_uF));}),_uR=new T(function(){return B(A1(_uI,_uG));}),_uS=new T(function(){return B(A1(_uI,_uD));}),_uT=new T(function(){var _uU=function(_uV){var _uW=new T(function(){return B(_oH(E(_uV)));}),_uX=function(_uY){var _uZ=B(_pi(_uW,_uY));if(!B(_qh(_uZ,_uE))){return new T0(2);}else{return new F(function(){return A1(_uI,new T(function(){var _v0=B(_qe(_uZ));if(_v0>>>0>1114111){return B(_qc(_v0));}else{return _v0;}}));});}};return new T1(1,B(_ne(_uV,_uX)));},_v1=new T(function(){var _v2=new T(function(){return B(A1(_uI,_tO));}),_v3=new T(function(){return B(A1(_uI,_tI));}),_v4=new T(function(){return B(A1(_uI,_tC));}),_v5=new T(function(){return B(A1(_uI,_tw));}),_v6=new T(function(){return B(A1(_uI,_tq));}),_v7=new T(function(){return B(A1(_uI,_tk));}),_v8=new T(function(){return B(A1(_uI,_te));}),_v9=new T(function(){return B(A1(_uI,_t8));}),_va=new T(function(){return B(A1(_uI,_t2));}),_vb=new T(function(){return B(A1(_uI,_sW));}),_vc=new T(function(){return B(A1(_uI,_sQ));}),_vd=new T(function(){return B(A1(_uI,_sK));}),_ve=new T(function(){return B(A1(_uI,_sE));}),_vf=new T(function(){return B(A1(_uI,_sy));}),_vg=new T(function(){return B(A1(_uI,_ss));}),_vh=new T(function(){return B(A1(_uI,_sm));}),_vi=new T(function(){return B(A1(_uI,_sg));}),_vj=new T(function(){return B(A1(_uI,_qM));}),_vk=new T(function(){return B(A1(_uI,_ru));}),_vl=new T(function(){return B(A1(_uI,_ro));}),_vm=new T(function(){return B(A1(_uI,_ri));}),_vn=new T(function(){return B(A1(_uI,_rc));}),_vo=new T(function(){return B(A1(_uI,_r6));}),_vp=new T(function(){return B(A1(_uI,_qS));}),_vq=new T(function(){return B(A1(_uI,_r0));}),_vr=function(_vs){switch(E(_vs)){case 64:return E(_vq);case 65:return E(_vp);case 66:return E(_vo);case 67:return E(_vn);case 68:return E(_vm);case 69:return E(_vl);case 70:return E(_vk);case 71:return E(_uJ);case 72:return E(_uK);case 73:return E(_uL);case 74:return E(_uM);case 75:return E(_uN);case 76:return E(_uO);case 77:return E(_uP);case 78:return E(_vj);case 79:return E(_vi);case 80:return E(_vh);case 81:return E(_vg);case 82:return E(_vf);case 83:return E(_ve);case 84:return E(_vd);case 85:return E(_vc);case 86:return E(_vb);case 87:return E(_va);case 88:return E(_v9);case 89:return E(_v8);case 90:return E(_v7);case 91:return E(_v6);case 92:return E(_v5);case 93:return E(_v4);case 94:return E(_v3);case 95:return E(_v2);default:return new T0(2);}};return B(_lf(new T1(0,function(_vt){return (E(_vt)==94)?E(new T1(0,_vr)):new T0(2);}),new T(function(){return B(A1(_uC,_uI));})));});return B(_lf(new T1(1,B(_mv(_q8,_qa,_uU))),_v1));});return new F(function(){return _lf(new T1(0,function(_vu){switch(E(_vu)){case 34:return E(_uS);case 39:return E(_uR);case 92:return E(_uQ);case 97:return E(_uJ);case 98:return E(_uK);case 102:return E(_uO);case 110:return E(_uM);case 114:return E(_uP);case 116:return E(_uL);case 118:return E(_uN);default:return new T0(2);}}),_uT);});},_vv=function(_vw){return new F(function(){return A1(_vw,_h9);});},_vx=function(_vy){var _vz=E(_vy);if(!_vz._){return E(_vv);}else{var _vA=E(_vz.a),_vB=_vA>>>0,_vC=new T(function(){return B(_vx(_vz.b));});if(_vB>887){var _vD=u_iswspace(_vA);if(!E(_vD)){return E(_vv);}else{var _vE=function(_vF){var _vG=new T(function(){return B(A1(_vC,_vF));});return new T1(0,function(_vH){return E(_vG);});};return E(_vE);}}else{var _vI=E(_vB);if(_vI==32){var _vJ=function(_vK){var _vL=new T(function(){return B(A1(_vC,_vK));});return new T1(0,function(_vM){return E(_vL);});};return E(_vJ);}else{if(_vI-9>>>0>4){if(E(_vI)==160){var _vN=function(_vO){var _vP=new T(function(){return B(A1(_vC,_vO));});return new T1(0,function(_vQ){return E(_vP);});};return E(_vN);}else{return E(_vv);}}else{var _vR=function(_vS){var _vT=new T(function(){return B(A1(_vC,_vS));});return new T1(0,function(_vU){return E(_vT);});};return E(_vR);}}}}},_vV=function(_vW){var _vX=new T(function(){return B(_vV(_vW));}),_vY=function(_vZ){return (E(_vZ)==92)?E(_vX):new T0(2);},_w0=function(_w1){return E(new T1(0,_vY));},_w2=new T1(1,function(_w3){return new F(function(){return A2(_vx,_w3,_w0);});}),_w4=new T(function(){return B(_uH(function(_w5){return new F(function(){return A1(_vW,new T2(0,_w5,_q2));});}));}),_w6=function(_w7){var _w8=E(_w7);if(_w8==38){return E(_vX);}else{var _w9=_w8>>>0;if(_w9>887){var _wa=u_iswspace(_w8);return (E(_wa)==0)?new T0(2):E(_w2);}else{var _wb=E(_w9);return (_wb==32)?E(_w2):(_wb-9>>>0>4)?(E(_wb)==160)?E(_w2):new T0(2):E(_w2);}}};return new F(function(){return _lf(new T1(0,function(_wc){return (E(_wc)==92)?E(new T1(0,_w6)):new T0(2);}),new T1(0,function(_wd){var _we=E(_wd);if(E(_we)==92){return E(_w4);}else{return new F(function(){return A1(_vW,new T2(0,_we,_q1));});}}));});},_wf=function(_wg,_wh){var _wi=new T(function(){return B(A1(_wh,new T1(1,new T(function(){return B(A1(_wg,_1));}))));}),_wj=function(_wk){var _wl=E(_wk),_wm=E(_wl.a);if(E(_wm)==34){if(!E(_wl.b)){return E(_wi);}else{return new F(function(){return _wf(function(_wn){return new F(function(){return A1(_wg,new T2(1,_wm,_wn));});},_wh);});}}else{return new F(function(){return _wf(function(_wo){return new F(function(){return A1(_wg,new T2(1,_wm,_wo));});},_wh);});}};return new F(function(){return _vV(_wj);});},_wp=new T(function(){return B(unCStr("_\'"));}),_wq=function(_wr){var _ws=u_iswalnum(_wr);if(!E(_ws)){return new F(function(){return _pT(_m4,_wr,_wp);});}else{return true;}},_wt=function(_wu){return new F(function(){return _wq(E(_wu));});},_wv=new T(function(){return B(unCStr(",;()[]{}`"));}),_ww=new T(function(){return B(unCStr("=>"));}),_wx=new T2(1,_ww,_1),_wy=new T(function(){return B(unCStr("~"));}),_wz=new T2(1,_wy,_wx),_wA=new T(function(){return B(unCStr("@"));}),_wB=new T2(1,_wA,_wz),_wC=new T(function(){return B(unCStr("->"));}),_wD=new T2(1,_wC,_wB),_wE=new T(function(){return B(unCStr("<-"));}),_wF=new T2(1,_wE,_wD),_wG=new T(function(){return B(unCStr("|"));}),_wH=new T2(1,_wG,_wF),_wI=new T(function(){return B(unCStr("\\"));}),_wJ=new T2(1,_wI,_wH),_wK=new T(function(){return B(unCStr("="));}),_wL=new T2(1,_wK,_wJ),_wM=new T(function(){return B(unCStr("::"));}),_wN=new T2(1,_wM,_wL),_wO=new T(function(){return B(unCStr(".."));}),_wP=new T2(1,_wO,_wN),_wQ=function(_wR){var _wS=new T(function(){return B(A1(_wR,_n9));}),_wT=new T(function(){var _wU=new T(function(){var _wV=function(_wW){var _wX=new T(function(){return B(A1(_wR,new T1(0,_wW)));});return new T1(0,function(_wY){return (E(_wY)==39)?E(_wX):new T0(2);});};return B(_uH(_wV));}),_wZ=function(_x0){var _x1=E(_x0);switch(E(_x1)){case 39:return new T0(2);case 92:return E(_wU);default:var _x2=new T(function(){return B(A1(_wR,new T1(0,_x1)));});return new T1(0,function(_x3){return (E(_x3)==39)?E(_x2):new T0(2);});}},_x4=new T(function(){var _x5=new T(function(){return B(_wf(_na,_wR));}),_x6=new T(function(){var _x7=new T(function(){var _x8=new T(function(){var _x9=function(_xa){var _xb=E(_xa),_xc=u_iswalpha(_xb);return (E(_xc)==0)?(E(_xb)==95)?new T1(1,B(_mV(_wt,function(_xd){return new F(function(){return A1(_wR,new T1(3,new T2(1,_xb,_xd)));});}))):new T0(2):new T1(1,B(_mV(_wt,function(_xe){return new F(function(){return A1(_wR,new T1(3,new T2(1,_xb,_xe)));});})));};return B(_lf(new T1(0,_x9),new T(function(){return new T1(1,B(_mv(_o9,_pP,_wR)));})));}),_xf=function(_xg){return (!B(_pT(_m4,_xg,_pY)))?new T0(2):new T1(1,B(_mV(_pZ,function(_xh){var _xi=new T2(1,_xg,_xh);if(!B(_pT(_md,_xi,_wP))){return new F(function(){return A1(_wR,new T1(4,_xi));});}else{return new F(function(){return A1(_wR,new T1(2,_xi));});}})));};return B(_lf(new T1(0,_xf),_x8));});return B(_lf(new T1(0,function(_xj){if(!B(_pT(_m4,_xj,_wv))){return new T0(2);}else{return new F(function(){return A1(_wR,new T1(2,new T2(1,_xj,_1)));});}}),_x7));});return B(_lf(new T1(0,function(_xk){return (E(_xk)==34)?E(_x5):new T0(2);}),_x6));});return B(_lf(new T1(0,function(_xl){return (E(_xl)==39)?E(new T1(0,_wZ)):new T0(2);}),_x4));});return new F(function(){return _lf(new T1(1,function(_xm){return (E(_xm)._==0)?E(_wS):new T0(2);}),_wT);});},_xn=0,_xo=function(_xp,_xq){var _xr=new T(function(){var _xs=new T(function(){var _xt=function(_xu){var _xv=new T(function(){var _xw=new T(function(){return B(A1(_xq,_xu));});return B(_wQ(function(_xx){var _xy=E(_xx);return (_xy._==2)?(!B(_lT(_xy.a,_lS)))?new T0(2):E(_xw):new T0(2);}));}),_xz=function(_xA){return E(_xv);};return new T1(1,function(_xB){return new F(function(){return A2(_vx,_xB,_xz);});});};return B(A2(_xp,_xn,_xt));});return B(_wQ(function(_xC){var _xD=E(_xC);return (_xD._==2)?(!B(_lT(_xD.a,_lR)))?new T0(2):E(_xs):new T0(2);}));}),_xE=function(_xF){return E(_xr);};return function(_xG){return new F(function(){return A2(_vx,_xG,_xE);});};},_xH=function(_xI,_xJ){var _xK=function(_xL){var _xM=new T(function(){return B(A1(_xI,_xL));}),_xN=function(_xO){return new F(function(){return _lf(B(A1(_xM,_xO)),new T(function(){return new T1(1,B(_xo(_xK,_xO)));}));});};return E(_xN);},_xP=new T(function(){return B(A1(_xI,_xJ));}),_xQ=function(_xR){return new F(function(){return _lf(B(A1(_xP,_xR)),new T(function(){return new T1(1,B(_xo(_xK,_xR)));}));});};return E(_xQ);},_xS=function(_xT,_xU){var _xV=function(_xW,_xX){var _xY=function(_xZ){return new F(function(){return A1(_xX,new T(function(){return  -E(_xZ);}));});},_y0=new T(function(){return B(_wQ(function(_y1){return new F(function(){return A3(_xT,_y1,_xW,_xY);});}));}),_y2=function(_y3){return E(_y0);},_y4=function(_y5){return new F(function(){return A2(_vx,_y5,_y2);});},_y6=new T(function(){return B(_wQ(function(_y7){var _y8=E(_y7);if(_y8._==4){var _y9=E(_y8.a);if(!_y9._){return new F(function(){return A3(_xT,_y8,_xW,_xX);});}else{if(E(_y9.a)==45){if(!E(_y9.b)._){return E(new T1(1,_y4));}else{return new F(function(){return A3(_xT,_y8,_xW,_xX);});}}else{return new F(function(){return A3(_xT,_y8,_xW,_xX);});}}}else{return new F(function(){return A3(_xT,_y8,_xW,_xX);});}}));}),_ya=function(_yb){return E(_y6);};return new T1(1,function(_yc){return new F(function(){return A2(_vx,_yc,_ya);});});};return new F(function(){return _xH(_xV,_xU);});},_yd=function(_ye){var _yf=E(_ye);if(!_yf._){var _yg=_yf.b,_yh=new T(function(){return B(_p1(new T(function(){return B(_oH(E(_yf.a)));}),new T(function(){return B(_oy(_yg,0));},1),B(_oD(_oJ,_yg))));});return new T1(1,_yh);}else{return (E(_yf.b)._==0)?(E(_yf.c)._==0)?new T1(1,new T(function(){return B(_pi(_ox,_yf.a));})):__Z:__Z;}},_yi=function(_yj,_yk){return new T0(2);},_yl=function(_ym){var _yn=E(_ym);if(_yn._==5){var _yo=B(_yd(_yn.a));if(!_yo._){return E(_yi);}else{var _yp=new T(function(){return B(_qe(_yo.a));});return function(_yq,_yr){return new F(function(){return A1(_yr,_yp);});};}}else{return E(_yi);}},_ys=function(_yt){return new F(function(){return _xS(_yl,_yt);});},_yu=new T(function(){return B(unCStr("["));}),_yv=function(_yw,_yx){var _yy=function(_yz,_yA){var _yB=new T(function(){return B(A1(_yA,_1));}),_yC=new T(function(){var _yD=function(_yE){return new F(function(){return _yy(_q2,function(_yF){return new F(function(){return A1(_yA,new T2(1,_yE,_yF));});});});};return B(A2(_yw,_xn,_yD));}),_yG=new T(function(){return B(_wQ(function(_yH){var _yI=E(_yH);if(_yI._==2){var _yJ=E(_yI.a);if(!_yJ._){return new T0(2);}else{var _yK=_yJ.b;switch(E(_yJ.a)){case 44:return (E(_yK)._==0)?(!E(_yz))?new T0(2):E(_yC):new T0(2);case 93:return (E(_yK)._==0)?E(_yB):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_yL=function(_yM){return E(_yG);};return new T1(1,function(_yN){return new F(function(){return A2(_vx,_yN,_yL);});});},_yO=function(_yP,_yQ){return new F(function(){return _yR(_yQ);});},_yR=function(_yS){var _yT=new T(function(){var _yU=new T(function(){var _yV=new T(function(){var _yW=function(_yX){return new F(function(){return _yy(_q2,function(_yY){return new F(function(){return A1(_yS,new T2(1,_yX,_yY));});});});};return B(A2(_yw,_xn,_yW));});return B(_lf(B(_yy(_q1,_yS)),_yV));});return B(_wQ(function(_yZ){var _z0=E(_yZ);return (_z0._==2)?(!B(_lT(_z0.a,_yu)))?new T0(2):E(_yU):new T0(2);}));}),_z1=function(_z2){return E(_yT);};return new F(function(){return _lf(new T1(1,function(_z3){return new F(function(){return A2(_vx,_z3,_z1);});}),new T(function(){return new T1(1,B(_xo(_yO,_yS)));}));});};return new F(function(){return _yR(_yx);});},_z4=function(_z5,_z6){return new F(function(){return _yv(_ys,_z6);});},_z7=new T(function(){return B(_yv(_ys,_jV));}),_z8=function(_yt){return new F(function(){return _l5(_z7,_yt);});},_z9=function(_za){var _zb=new T(function(){return B(A3(_xS,_yl,_za,_jV));});return function(_zc){return new F(function(){return _l5(_zb,_zc);});};},_zd=new T4(0,_z9,_z8,_ys,_z4),_ze=11,_zf=new T(function(){return B(unCStr("IdentChoice"));}),_zg=function(_zh,_zi){if(_zh>10){return new T0(2);}else{var _zj=new T(function(){var _zk=new T(function(){return B(A3(_xS,_yl,_ze,function(_zl){return new F(function(){return A1(_zi,_zl);});}));});return B(_wQ(function(_zm){var _zn=E(_zm);return (_zn._==3)?(!B(_lT(_zn.a,_zf)))?new T0(2):E(_zk):new T0(2);}));}),_zo=function(_zp){return E(_zj);};return new T1(1,function(_zq){return new F(function(){return A2(_vx,_zq,_zo);});});}},_zr=function(_zs,_zt){return new F(function(){return _zg(E(_zs),_zt);});},_zu=function(_zv){return new F(function(){return _xH(_zr,_zv);});},_zw=function(_zx,_zy){return new F(function(){return _yv(_zu,_zy);});},_zz=new T(function(){return B(_yv(_zu,_jV));}),_zA=function(_zv){return new F(function(){return _l5(_zz,_zv);});},_zB=function(_zC){var _zD=new T(function(){return B(A3(_xH,_zr,_zC,_jV));});return function(_zc){return new F(function(){return _l5(_zD,_zc);});};},_zE=new T4(0,_zB,_zA,_zu,_zw),_zF=new T(function(){return B(unCStr(","));}),_zG=function(_zH){return E(E(_zH).c);},_zI=function(_zJ,_zK,_zL){var _zM=new T(function(){return B(_zG(_zK));}),_zN=new T(function(){return B(A2(_zG,_zJ,_zL));}),_zO=function(_zP){var _zQ=function(_zR){var _zS=new T(function(){var _zT=new T(function(){return B(A2(_zM,_zL,function(_zU){return new F(function(){return A1(_zP,new T2(0,_zR,_zU));});}));});return B(_wQ(function(_zV){var _zW=E(_zV);return (_zW._==2)?(!B(_lT(_zW.a,_zF)))?new T0(2):E(_zT):new T0(2);}));}),_zX=function(_zY){return E(_zS);};return new T1(1,function(_zZ){return new F(function(){return A2(_vx,_zZ,_zX);});});};return new F(function(){return A1(_zN,_zQ);});};return E(_zO);},_A0=function(_A1,_A2,_A3){var _A4=function(_yt){return new F(function(){return _zI(_A1,_A2,_yt);});},_A5=function(_A6,_A7){return new F(function(){return _A8(_A7);});},_A8=function(_A9){return new F(function(){return _lf(new T1(1,B(_xo(_A4,_A9))),new T(function(){return new T1(1,B(_xo(_A5,_A9)));}));});};return new F(function(){return _A8(_A3);});},_Aa=function(_Ab,_Ac){return new F(function(){return _A0(_zE,_zd,_Ac);});},_Ad=new T(function(){return B(_yv(_Aa,_jV));}),_Ae=function(_zv){return new F(function(){return _l5(_Ad,_zv);});},_Af=new T(function(){return B(_A0(_zE,_zd,_jV));}),_Ag=function(_zv){return new F(function(){return _l5(_Af,_zv);});},_Ah=function(_Ai,_zv){return new F(function(){return _Ag(_zv);});},_Aj=function(_Ak,_Al){return new F(function(){return _yv(_Aa,_Al);});},_Am=new T4(0,_Ah,_Ae,_Aa,_Aj),_An=function(_Ao,_Ap){return new F(function(){return _A0(_Am,_zd,_Ap);});},_Aq=function(_Ar,_As){return new F(function(){return _yv(_An,_As);});},_At=new T(function(){return B(_yv(_Aq,_jV));}),_Au=function(_Av){return new F(function(){return _l5(_At,_Av);});},_Aw=function(_Ax){return new F(function(){return _yv(_Aq,_Ax);});},_Ay=function(_Az,_AA){return new F(function(){return _Aw(_AA);});},_AB=new T(function(){return B(_yv(_An,_jV));}),_AC=function(_Av){return new F(function(){return _l5(_AB,_Av);});},_AD=function(_AE,_Av){return new F(function(){return _AC(_Av);});},_AF=new T4(0,_AD,_Au,_Aq,_Ay),_AG=new T(function(){return B(unCStr("IdentPay"));}),_AH=function(_AI,_AJ){if(_AI>10){return new T0(2);}else{var _AK=new T(function(){var _AL=new T(function(){return B(A3(_xS,_yl,_ze,function(_AM){return new F(function(){return A1(_AJ,_AM);});}));});return B(_wQ(function(_AN){var _AO=E(_AN);return (_AO._==3)?(!B(_lT(_AO.a,_AG)))?new T0(2):E(_AL):new T0(2);}));}),_AP=function(_AQ){return E(_AK);};return new T1(1,function(_AR){return new F(function(){return A2(_vx,_AR,_AP);});});}},_AS=function(_AT,_AU){return new F(function(){return _AH(E(_AT),_AU);});},_AV=function(_zv){return new F(function(){return _xH(_AS,_zv);});},_AW=function(_AX,_AY){return new F(function(){return _yv(_AV,_AY);});},_AZ=new T(function(){return B(_yv(_AV,_jV));}),_B0=function(_zv){return new F(function(){return _l5(_AZ,_zv);});},_B1=function(_B2){var _B3=new T(function(){return B(A3(_xH,_AS,_B2,_jV));});return function(_zc){return new F(function(){return _l5(_B3,_zc);});};},_B4=new T4(0,_B1,_B0,_AV,_AW),_B5=function(_B6,_B7){return new F(function(){return _A0(_B4,_zd,_B7);});},_B8=new T(function(){return B(_yv(_B5,_jV));}),_B9=function(_zv){return new F(function(){return _l5(_B8,_zv);});},_Ba=new T(function(){return B(_A0(_B4,_zd,_jV));}),_Bb=function(_zv){return new F(function(){return _l5(_Ba,_zv);});},_Bc=function(_Bd,_zv){return new F(function(){return _Bb(_zv);});},_Be=function(_Bf,_Bg){return new F(function(){return _yv(_B5,_Bg);});},_Bh=new T4(0,_Bc,_B9,_B5,_Be),_Bi=function(_Bj,_Bk){return new F(function(){return _A0(_Bh,_zd,_Bk);});},_Bl=function(_Bm,_Bn){return new F(function(){return _yv(_Bi,_Bn);});},_Bo=new T(function(){return B(_yv(_Bl,_jV));}),_Bp=function(_Av){return new F(function(){return _l5(_Bo,_Av);});},_Bq=function(_Br){return new F(function(){return _yv(_Bl,_Br);});},_Bs=function(_Bt,_Bu){return new F(function(){return _Bq(_Bu);});},_Bv=new T(function(){return B(_yv(_Bi,_jV));}),_Bw=function(_Av){return new F(function(){return _l5(_Bv,_Av);});},_Bx=function(_By,_Av){return new F(function(){return _Bw(_Av);});},_Bz=new T4(0,_Bx,_Bp,_Bl,_Bs),_BA=new T(function(){return B(unCStr("IdentCC"));}),_BB=function(_BC,_BD){if(_BC>10){return new T0(2);}else{var _BE=new T(function(){var _BF=new T(function(){return B(A3(_xS,_yl,_ze,function(_BG){return new F(function(){return A1(_BD,_BG);});}));});return B(_wQ(function(_BH){var _BI=E(_BH);return (_BI._==3)?(!B(_lT(_BI.a,_BA)))?new T0(2):E(_BF):new T0(2);}));}),_BJ=function(_BK){return E(_BE);};return new T1(1,function(_BL){return new F(function(){return A2(_vx,_BL,_BJ);});});}},_BM=function(_BN,_BO){return new F(function(){return _BB(E(_BN),_BO);});},_BP=new T(function(){return B(unCStr("RC"));}),_BQ=function(_BR,_BS){if(_BR>10){return new T0(2);}else{var _BT=new T(function(){var _BU=new T(function(){var _BV=function(_BW){var _BX=function(_BY){return new F(function(){return A3(_xS,_yl,_ze,function(_BZ){return new F(function(){return A1(_BS,new T3(0,_BW,_BY,_BZ));});});});};return new F(function(){return A3(_xS,_yl,_ze,_BX);});};return B(A3(_xH,_BM,_ze,_BV));});return B(_wQ(function(_C0){var _C1=E(_C0);return (_C1._==3)?(!B(_lT(_C1.a,_BP)))?new T0(2):E(_BU):new T0(2);}));}),_C2=function(_C3){return E(_BT);};return new T1(1,function(_C4){return new F(function(){return A2(_vx,_C4,_C2);});});}},_C5=function(_C6,_C7){return new F(function(){return _BQ(E(_C6),_C7);});},_C8=function(_zv){return new F(function(){return _xH(_C5,_zv);});},_C9=function(_Ca,_Cb){return new F(function(){return _yv(_C8,_Cb);});},_Cc=new T(function(){return B(_yv(_C9,_jV));}),_Cd=function(_Av){return new F(function(){return _l5(_Cc,_Av);});},_Ce=new T(function(){return B(_yv(_C8,_jV));}),_Cf=function(_Av){return new F(function(){return _l5(_Ce,_Av);});},_Cg=function(_Ch,_Av){return new F(function(){return _Cf(_Av);});},_Ci=function(_Cj,_Ck){return new F(function(){return _yv(_C9,_Ck);});},_Cl=new T4(0,_Cg,_Cd,_C9,_Ci),_Cm=new T(function(){return B(unCStr("CC"));}),_Cn=function(_Co,_Cp){if(_Co>10){return new T0(2);}else{var _Cq=new T(function(){var _Cr=new T(function(){var _Cs=function(_Ct){var _Cu=function(_Cv){var _Cw=function(_Cx){return new F(function(){return A3(_xS,_yl,_ze,function(_Cy){return new F(function(){return A1(_Cp,new T4(0,_Ct,_Cv,_Cx,_Cy));});});});};return new F(function(){return A3(_xS,_yl,_ze,_Cw);});};return new F(function(){return A3(_xS,_yl,_ze,_Cu);});};return B(A3(_xH,_BM,_ze,_Cs));});return B(_wQ(function(_Cz){var _CA=E(_Cz);return (_CA._==3)?(!B(_lT(_CA.a,_Cm)))?new T0(2):E(_Cr):new T0(2);}));}),_CB=function(_CC){return E(_Cq);};return new T1(1,function(_CD){return new F(function(){return A2(_vx,_CD,_CB);});});}},_CE=function(_CF,_CG){return new F(function(){return _Cn(E(_CF),_CG);});},_CH=function(_zv){return new F(function(){return _xH(_CE,_zv);});},_CI=function(_CJ,_CK){return new F(function(){return _yv(_CH,_CK);});},_CL=new T(function(){return B(_yv(_CI,_jV));}),_CM=function(_Av){return new F(function(){return _l5(_CL,_Av);});},_CN=new T(function(){return B(_yv(_CH,_jV));}),_CO=function(_Av){return new F(function(){return _l5(_CN,_Av);});},_CP=function(_CQ,_Av){return new F(function(){return _CO(_Av);});},_CR=function(_CS,_CT){return new F(function(){return _yv(_CI,_CT);});},_CU=new T4(0,_CP,_CM,_CI,_CR),_CV=function(_CW,_CX,_CY,_CZ,_D0){var _D1=new T(function(){return B(_zI(_CW,_CX,_D0));}),_D2=new T(function(){return B(_zG(_CZ));}),_D3=function(_D4){var _D5=function(_D6){var _D7=E(_D6),_D8=new T(function(){var _D9=new T(function(){var _Da=function(_Db){var _Dc=new T(function(){var _Dd=new T(function(){return B(A2(_D2,_D0,function(_De){return new F(function(){return A1(_D4,new T4(0,_D7.a,_D7.b,_Db,_De));});}));});return B(_wQ(function(_Df){var _Dg=E(_Df);return (_Dg._==2)?(!B(_lT(_Dg.a,_zF)))?new T0(2):E(_Dd):new T0(2);}));}),_Dh=function(_Di){return E(_Dc);};return new T1(1,function(_Dj){return new F(function(){return A2(_vx,_Dj,_Dh);});});};return B(A3(_zG,_CY,_D0,_Da));});return B(_wQ(function(_Dk){var _Dl=E(_Dk);return (_Dl._==2)?(!B(_lT(_Dl.a,_zF)))?new T0(2):E(_D9):new T0(2);}));}),_Dm=function(_Dn){return E(_D8);};return new T1(1,function(_Do){return new F(function(){return A2(_vx,_Do,_Dm);});});};return new F(function(){return A1(_D1,_D5);});};return E(_D3);},_Dp=function(_Dq,_Dr,_Ds,_Dt,_Du){var _Dv=function(_yt){return new F(function(){return _CV(_Dq,_Dr,_Ds,_Dt,_yt);});},_Dw=function(_Dx,_Dy){return new F(function(){return _Dz(_Dy);});},_Dz=function(_DA){return new F(function(){return _lf(new T1(1,B(_xo(_Dv,_DA))),new T(function(){return new T1(1,B(_xo(_Dw,_DA)));}));});};return new F(function(){return _Dz(_Du);});},_DB=function(_DC){var _DD=function(_DE){return E(new T2(3,_DC,_jU));};return new T1(1,function(_DF){return new F(function(){return A2(_vx,_DF,_DD);});});},_DG=new T(function(){return B(_Dp(_CU,_Cl,_Bz,_AF,_DB));}),_DH=function(_DI,_DJ,_DK,_DL){var _DM=E(_DI);if(_DM==1){var _DN=E(_DL);if(!_DN._){return new T3(0,new T(function(){var _DO=E(_DJ);return new T5(0,1,E(_DO),_DK,E(_0),E(_0));}),_1,_1);}else{var _DP=E(_DJ);return (_DP<E(E(_DN.a).a))?new T3(0,new T5(0,1,E(_DP),_DK,E(_0),E(_0)),_DN,_1):new T3(0,new T5(0,1,E(_DP),_DK,E(_0),E(_0)),_1,_DN);}}else{var _DQ=B(_DH(_DM>>1,_DJ,_DK,_DL)),_DR=_DQ.a,_DS=_DQ.c,_DT=E(_DQ.b);if(!_DT._){return new T3(0,_DR,_1,_DS);}else{var _DU=E(_DT.a),_DV=_DU.a,_DW=_DU.b,_DX=E(_DT.b);if(!_DX._){return new T3(0,new T(function(){return B(_O(_DV,_DW,_DR));}),_1,_DS);}else{var _DY=E(_DX.a),_DZ=E(_DV),_E0=E(_DY.a);if(_DZ<_E0){var _E1=B(_DH(_DM>>1,_E0,_DY.b,_DX.b));return new T3(0,new T(function(){return B(_2h(_DZ,_DW,_DR,_E1.a));}),_E1.b,_E1.c);}else{return new T3(0,_DR,_1,_DT);}}}}},_E2=function(_E3,_E4,_E5){var _E6=E(_E5);if(!_E6._){var _E7=_E6.c,_E8=_E6.d,_E9=_E6.e,_Ea=E(_E6.b);if(_E3>=_Ea){if(_E3!=_Ea){return new F(function(){return _6(_Ea,_E7,_E8,B(_E2(_E3,_E4,_E9)));});}else{return new T5(0,_E6.a,E(_E3),_E4,E(_E8),E(_E9));}}else{return new F(function(){return _X(_Ea,_E7,B(_E2(_E3,_E4,_E8)),_E9);});}}else{return new T5(0,1,E(_E3),_E4,E(_0),E(_0));}},_Eb=function(_Ec,_Ed){while(1){var _Ee=E(_Ed);if(!_Ee._){return E(_Ec);}else{var _Ef=E(_Ee.a),_Eg=B(_E2(E(_Ef.a),_Ef.b,_Ec));_Ec=_Eg;_Ed=_Ee.b;continue;}}},_Eh=function(_Ei,_Ej,_Ek,_El){return new F(function(){return _Eb(B(_E2(E(_Ej),_Ek,_Ei)),_El);});},_Em=function(_En,_Eo,_Ep){var _Eq=E(_Eo);return new F(function(){return _Eb(B(_E2(E(_Eq.a),_Eq.b,_En)),_Ep);});},_Er=function(_Es,_Et,_Eu){while(1){var _Ev=E(_Eu);if(!_Ev._){return E(_Et);}else{var _Ew=E(_Ev.a),_Ex=_Ew.a,_Ey=_Ew.b,_Ez=E(_Ev.b);if(!_Ez._){return new F(function(){return _O(_Ex,_Ey,_Et);});}else{var _EA=E(_Ez.a),_EB=E(_Ex),_EC=E(_EA.a);if(_EB<_EC){var _ED=B(_DH(_Es,_EC,_EA.b,_Ez.b)),_EE=_ED.a,_EF=E(_ED.c);if(!_EF._){var _EG=_Es<<1,_EH=B(_2h(_EB,_Ey,_Et,_EE));_Es=_EG;_Et=_EH;_Eu=_ED.b;continue;}else{return new F(function(){return _Em(B(_2h(_EB,_Ey,_Et,_EE)),_EF.a,_EF.b);});}}else{return new F(function(){return _Eh(_Et,_EB,_Ey,_Ez);});}}}}},_EI=function(_EJ,_EK,_EL,_EM,_EN){var _EO=E(_EN);if(!_EO._){return new F(function(){return _O(_EL,_EM,_EK);});}else{var _EP=E(_EO.a),_EQ=E(_EL),_ER=E(_EP.a);if(_EQ<_ER){var _ES=B(_DH(_EJ,_ER,_EP.b,_EO.b)),_ET=_ES.a,_EU=E(_ES.c);if(!_EU._){return new F(function(){return _Er(_EJ<<1,B(_2h(_EQ,_EM,_EK,_ET)),_ES.b);});}else{return new F(function(){return _Em(B(_2h(_EQ,_EM,_EK,_ET)),_EU.a,_EU.b);});}}else{return new F(function(){return _Eh(_EK,_EQ,_EM,_EO);});}}},_EV=function(_EW){var _EX=E(_EW);if(!_EX._){return new T0(1);}else{var _EY=E(_EX.a),_EZ=_EY.a,_F0=_EY.b,_F1=E(_EX.b);if(!_F1._){var _F2=E(_EZ);return new T5(0,1,E(_F2),_F0,E(_0),E(_0));}else{var _F3=_F1.b,_F4=E(_F1.a),_F5=_F4.b,_F6=E(_EZ),_F7=E(_F4.a);if(_F6<_F7){return new F(function(){return _EI(1,new T5(0,1,E(_F6),_F0,E(_0),E(_0)),_F7,_F5,_F3);});}else{return new F(function(){return _Eh(new T5(0,1,E(_F6),_F0,E(_0),E(_0)),_F7,_F5,_F3);});}}}},_F8=function(_){return _h9;},_F9=new T(function(){return B(unCStr(": Choose"));}),_Fa=new T(function(){return eval("(function (x, y, z) {var a = document.getElementById(\'actions\'); var r = a.insertRow(); var c1 = r.insertCell(); c1.appendChild(document.createTextNode(x + \' \')); var input = document.createElement(\'input\'); input.type = \'number\'; var ch = \'ibox\' + a.childNodes.length; input.id = ch; input.value = 0; input.style.setProperty(\'width\', \'5em\'); c1.appendChild(input); c1.appendChild(document.createTextNode(\' \' + y)); var c2 = r.insertCell(); var btn = document.createElement(\'button\'); c2.appendChild(btn); btn.appendChild(document.createTextNode(\'Add action\')); btn.style.setProperty(\'width\', \'100%\'); btn.onclick = function () {Haste.addActionWithNum(z, document.getElementById(ch).value);};})");}),_Fb=function(_Fc,_Fd,_){var _Fe=new T(function(){return B(A3(_is,_hk,new T2(1,function(_Ff){return new F(function(){return _j6(0,_Fc,_Ff);});},new T2(1,function(_Fg){return new F(function(){return _hA(0,E(_Fd),_Fg);});},_1)),_jv));}),_Fh=__app3(E(_Fa),toJSStr(B(unAppCStr("P",new T(function(){return B(_hq(B(_hA(0,E(_Fd),_1)),_F9));})))),toJSStr(B(unAppCStr("for choice with id ",new T(function(){return B(_hA(0,E(_Fc),_1));})))),toJSStr(new T2(1,_hz,_Fe)));return new F(function(){return _F8(_);});},_Fi=function(_Fj,_Fk,_){while(1){var _Fl=B((function(_Fm,_Fn,_){var _Fo=E(_Fn);if(!_Fo._){var _Fp=E(_Fo.b);_Fj=function(_){var _Fq=B(_Fb(_Fp.a,_Fp.b,_));return new F(function(){return _Fi(_Fm,_Fo.e,_);});};_Fk=_Fo.d;return __continue;}else{return new F(function(){return A1(_Fm,_);});}})(_Fj,_Fk,_));if(_Fl!=__continue){return _Fl;}}},_Fr=new T(function(){return B(unCStr("SIP "));}),_Fs=new T(function(){return B(unCStr("SIRC "));}),_Ft=new T(function(){return B(unCStr("SICC "));}),_Fu=function(_Fv,_Fw,_Fx){var _Fy=E(_Fw);switch(_Fy._){case 0:var _Fz=function(_FA){var _FB=new T(function(){var _FC=new T(function(){return B(_hA(11,E(_Fy.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_Fy.d),_FA));}))));});return B(_hA(11,E(_Fy.b),new T2(1,_hK,_FC)));});return new F(function(){return _hF(11,_Fy.a,new T2(1,_hK,_FB));});};if(_Fv<11){return new F(function(){return _hq(_Ft,new T(function(){return B(_Fz(_Fx));},1));});}else{var _FD=new T(function(){return B(_hq(_Ft,new T(function(){return B(_Fz(new T2(1,_hy,_Fx)));},1)));});return new T2(1,_hz,_FD);}break;case 1:var _FE=function(_FF){var _FG=new T(function(){var _FH=new T(function(){return B(_hA(11,E(_Fy.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_Fy.c),_FF));}))));});return B(_hF(11,_Fy.a,new T2(1,_hK,_FH)));},1);return new F(function(){return _hq(_Fs,_FG);});};if(_Fv<11){return new F(function(){return _FE(_Fx);});}else{return new T2(1,_hz,new T(function(){return B(_FE(new T2(1,_hy,_Fx)));}));}break;default:var _FI=function(_FJ){var _FK=new T(function(){var _FL=new T(function(){return B(_hA(11,E(_Fy.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_Fy.c),_FJ));}))));});return B(_ih(11,_Fy.a,new T2(1,_hK,_FL)));},1);return new F(function(){return _hq(_Fr,_FK);});};if(_Fv<11){return new F(function(){return _FI(_Fx);});}else{return new T2(1,_hz,new T(function(){return B(_FI(new T2(1,_hy,_Fx)));}));}}},_FM=new T(function(){return B(unCStr(" ADA"));}),_FN=new T(function(){return eval("(function (x, y) {var r = document.getElementById(\'actions\').insertRow(); var c1 = r.insertCell(); c1.appendChild(document.createTextNode(x)); var c2 = r.insertCell(); var btn = document.createElement(\'button\'); c2.appendChild(btn); btn.appendChild(document.createTextNode(\'Add action\')); btn.style.setProperty(\'width\', \'100%\'); btn.onclick = function () {Haste.addAction(y);};})");}),_FO=function(_FP,_FQ,_FR,_){var _FS=new T(function(){var _FT=new T(function(){var _FU=new T(function(){var _FV=new T(function(){return B(unAppCStr(") of ",new T(function(){return B(_hq(B(_hA(0,E(_FR),_1)),_FM));})));},1);return B(_hq(B(_hA(0,E(_FP),_1)),_FV));});return B(unAppCStr(": Claim payment (with id: ",_FU));},1);return B(_hq(B(_hA(0,E(_FQ),_1)),_FT));}),_FW=__app2(E(_FN),toJSStr(B(unAppCStr("P",_FS))),toJSStr(B(_Fu(0,new T3(2,_FP,_FQ,_FR),_1))));return new F(function(){return _F8(_);});},_FX=function(_FY,_FZ,_){while(1){var _G0=B((function(_G1,_G2,_){var _G3=E(_G2);if(!_G3._){var _G4=E(_G3.b);_FY=function(_){var _G5=B(_FO(_G4.a,_G4.b,_G3.c,_));return new F(function(){return _FX(_G1,_G3.e,_);});};_FZ=_G3.d;return __continue;}else{return new F(function(){return A1(_G1,_);});}})(_FY,_FZ,_));if(_G0!=__continue){return _G0;}}},_G6=new T(function(){return B(unCStr(")"));}),_G7=function(_G8,_G9,_Ga,_){var _Gb=new T(function(){var _Gc=new T(function(){var _Gd=new T(function(){var _Ge=new T(function(){return B(unAppCStr(" ADA from commit (with id: ",new T(function(){return B(_hq(B(_hA(0,E(_G8),_1)),_G6));})));},1);return B(_hq(B(_hA(0,E(_Ga),_1)),_Ge));});return B(unAppCStr(": Redeem ",_Gd));},1);return B(_hq(B(_hA(0,E(_G9),_1)),_Gc));}),_Gf=__app2(E(_FN),toJSStr(B(unAppCStr("P",_Gb))),toJSStr(B(_Fu(0,new T3(1,_G8,_G9,_Ga),_1))));return new F(function(){return _F8(_);});},_Gg=function(_Gh,_Gi,_){while(1){var _Gj=B((function(_Gk,_Gl,_){var _Gm=E(_Gl);if(!_Gm._){var _Gn=E(_Gm.b);_Gh=function(_){var _Go=B(_G7(_Gn.a,_Gn.b,_Gn.c,_));return new F(function(){return _Gg(_Gk,_Gm.d,_);});};_Gi=_Gm.c;return __continue;}else{return new F(function(){return A1(_Gk,_);});}})(_Gh,_Gi,_));if(_Gj!=__continue){return _Gj;}}},_Gp=function(_){return _h9;},_Gq=function(_Gr,_Gs,_Gt,_Gu,_){var _Gv=new T(function(){var _Gw=new T(function(){var _Gx=new T(function(){var _Gy=new T(function(){var _Gz=new T(function(){var _GA=new T(function(){return B(unAppCStr(" ADA expiring on: ",new T(function(){return B(_hA(0,E(_Gu),_1));})));},1);return B(_hq(B(_hA(0,E(_Gt),_1)),_GA));});return B(unAppCStr(") of ",_Gz));},1);return B(_hq(B(_hA(0,E(_Gr),_1)),_Gy));});return B(unAppCStr(": Make commit (with id: ",_Gx));},1);return B(_hq(B(_hA(0,E(_Gs),_1)),_Gw));}),_GB=__app2(E(_FN),toJSStr(B(unAppCStr("P",_Gv))),toJSStr(B(_Fu(0,new T4(0,_Gr,_Gs,_Gt,_Gu),_1))));return new F(function(){return _F8(_);});},_GC=function(_GD,_GE,_){while(1){var _GF=B((function(_GG,_GH,_){var _GI=E(_GH);if(!_GI._){var _GJ=E(_GI.b);_GD=function(_){var _GK=B(_Gq(_GJ.a,_GJ.b,_GJ.c,_GJ.d,_));return new F(function(){return _GC(_GG,_GI.d,_);});};_GE=_GI.c;return __continue;}else{return new F(function(){return A1(_GG,_);});}})(_GD,_GE,_));if(_GF!=__continue){return _GF;}}},_GL=function(_GM,_GN,_GO,_GP,_){var _GQ=B(_GC(_Gp,_GM,_)),_GR=B(_Gg(_Gp,_GN,_)),_GS=B(_FX(_Gp,_GO,_));return new F(function(){return _Fi(_Gp,_GP,_);});},_GT=function(_GU,_GV){return E(_GU)==E(_GV);},_GW=function(_GX,_GY){return E(_GX)!=E(_GY);},_GZ=new T2(0,_GT,_GW),_H0=function(_H1,_H2){var _H3=E(_H1),_H4=E(_H2);return (_H3>_H4)?E(_H3):E(_H4);},_H5=function(_H6,_H7){var _H8=E(_H6),_H9=E(_H7);return (_H8>_H9)?E(_H9):E(_H8);},_Ha=function(_Hb,_Hc){return (_Hb>=_Hc)?(_Hb!=_Hc)?2:1:0;},_Hd=function(_He,_Hf){return new F(function(){return _Ha(E(_He),E(_Hf));});},_Hg=function(_Hh,_Hi){return E(_Hh)>=E(_Hi);},_Hj=function(_Hk,_Hl){return E(_Hk)>E(_Hl);},_Hm=function(_Hn,_Ho){return E(_Hn)<=E(_Ho);},_Hp=function(_Hq,_Hr){return E(_Hq)<E(_Hr);},_Hs={_:0,a:_GZ,b:_Hd,c:_Hp,d:_Hm,e:_Hj,f:_Hg,g:_H0,h:_H5},_Ht=function(_Hu,_Hv,_Hw,_Hx,_Hy){while(1){var _Hz=E(_Hy);if(!_Hz._){var _HA=_Hz.c,_HB=_Hz.d,_HC=E(_Hz.b),_HD=E(_HC.a);if(_Hu>=_HD){if(_Hu!=_HD){_Hv=_;_Hy=_HB;continue;}else{var _HE=E(_HC.b);if(_Hw>=_HE){if(_Hw!=_HE){_Hv=_;_Hy=_HB;continue;}else{var _HF=E(_HC.c);if(_Hx>=_HF){if(_Hx!=_HF){_Hv=_;_Hy=_HB;continue;}else{return true;}}else{_Hv=_;_Hy=_HA;continue;}}}else{_Hv=_;_Hy=_HA;continue;}}}else{_Hv=_;_Hy=_HA;continue;}}else{return false;}}},_HG=function(_HH,_HI,_HJ,_HK,_HL){while(1){var _HM=E(_HL);if(!_HM._){var _HN=_HM.c,_HO=_HM.d,_HP=E(_HM.b),_HQ=E(_HP.a);if(_HH>=_HQ){if(_HH!=_HQ){_HI=_;_HL=_HO;continue;}else{var _HR=E(_HP.b);if(_HJ>=_HR){if(_HJ!=_HR){_HI=_;_HL=_HO;continue;}else{var _HS=E(_HK),_HT=E(_HP.c);if(_HS>=_HT){if(_HS!=_HT){return new F(function(){return _Ht(_HH,_,_HJ,_HS,_HO);});}else{return true;}}else{return new F(function(){return _Ht(_HH,_,_HJ,_HS,_HN);});}}}else{_HI=_;_HL=_HN;continue;}}}else{_HI=_;_HL=_HN;continue;}}else{return false;}}},_HU=function(_HV,_HW,_HX,_HY,_HZ){while(1){var _I0=E(_HZ);if(!_I0._){var _I1=_I0.c,_I2=_I0.d,_I3=E(_I0.b),_I4=E(_I3.a);if(_HV>=_I4){if(_HV!=_I4){_HW=_;_HZ=_I2;continue;}else{var _I5=E(_HX),_I6=E(_I3.b);if(_I5>=_I6){if(_I5!=_I6){return new F(function(){return _HG(_HV,_,_I5,_HY,_I2);});}else{var _I7=E(_HY),_I8=E(_I3.c);if(_I7>=_I8){if(_I7!=_I8){return new F(function(){return _Ht(_HV,_,_I5,_I7,_I2);});}else{return true;}}else{return new F(function(){return _Ht(_HV,_,_I5,_I7,_I1);});}}}else{return new F(function(){return _HG(_HV,_,_I5,_HY,_I1);});}}}else{_HW=_;_HZ=_I1;continue;}}else{return false;}}},_I9=function(_Ia,_Ib,_Ic,_Id){var _Ie=E(_Id);if(!_Ie._){var _If=_Ie.c,_Ig=_Ie.d,_Ih=E(_Ie.b),_Ii=E(_Ia),_Ij=E(_Ih.a);if(_Ii>=_Ij){if(_Ii!=_Ij){return new F(function(){return _HU(_Ii,_,_Ib,_Ic,_Ig);});}else{var _Ik=E(_Ib),_Il=E(_Ih.b);if(_Ik>=_Il){if(_Ik!=_Il){return new F(function(){return _HG(_Ii,_,_Ik,_Ic,_Ig);});}else{var _Im=E(_Ic),_In=E(_Ih.c);if(_Im>=_In){if(_Im!=_In){return new F(function(){return _Ht(_Ii,_,_Ik,_Im,_Ig);});}else{return true;}}else{return new F(function(){return _Ht(_Ii,_,_Ik,_Im,_If);});}}}else{return new F(function(){return _HG(_Ii,_,_Ik,_Ic,_If);});}}}else{return new F(function(){return _HU(_Ii,_,_Ib,_Ic,_If);});}}else{return false;}},_Io=function(_Ip,_Iq,_Ir,_Is,_It){var _Iu=E(_It);if(!_Iu._){if(E(_Iu.b)>E(_Iq)){return false;}else{return new F(function(){return _I9(_Ir,_Is,_Iu.a,E(_Ip).b);});}}else{return false;}},_Iv=function(_Iw,_Ix,_Iy,_Iz,_IA){var _IB=E(_IA);if(!_IB._){var _IC=new T(function(){var _ID=B(_Iv(_IB.a,_IB.b,_IB.c,_IB.d,_IB.e));return new T2(0,_ID.a,_ID.b);});return new T2(0,new T(function(){return E(E(_IC).a);}),new T(function(){return B(_X(_Ix,_Iy,_Iz,E(_IC).b));}));}else{return new T2(0,new T2(0,_Ix,_Iy),_Iz);}},_IE=function(_IF,_IG,_IH,_II,_IJ){var _IK=E(_II);if(!_IK._){var _IL=new T(function(){var _IM=B(_IE(_IK.a,_IK.b,_IK.c,_IK.d,_IK.e));return new T2(0,_IM.a,_IM.b);});return new T2(0,new T(function(){return E(E(_IL).a);}),new T(function(){return B(_6(_IG,_IH,E(_IL).b,_IJ));}));}else{return new T2(0,new T2(0,_IG,_IH),_IJ);}},_IN=function(_IO,_IP){var _IQ=E(_IO);if(!_IQ._){var _IR=_IQ.a,_IS=E(_IP);if(!_IS._){var _IT=_IS.a;if(_IR<=_IT){var _IU=B(_IE(_IT,_IS.b,_IS.c,_IS.d,_IS.e)),_IV=E(_IU.a);return new F(function(){return _X(_IV.a,_IV.b,_IQ,_IU.b);});}else{var _IW=B(_Iv(_IR,_IQ.b,_IQ.c,_IQ.d,_IQ.e)),_IX=E(_IW.a);return new F(function(){return _6(_IX.a,_IX.b,_IW.b,_IS);});}}else{return E(_IQ);}}else{return E(_IP);}},_IY=function(_IZ,_J0,_J1,_J2,_J3,_J4){var _J5=E(_IZ);if(!_J5._){var _J6=_J5.a,_J7=_J5.b,_J8=_J5.c,_J9=_J5.d,_Ja=_J5.e;if((imul(3,_J6)|0)>=_J0){if((imul(3,_J0)|0)>=_J6){return new F(function(){return _IN(_J5,new T5(0,_J0,E(_J1),_J2,E(_J3),E(_J4)));});}else{return new F(function(){return _6(_J7,_J8,_J9,B(_IY(_Ja,_J0,_J1,_J2,_J3,_J4)));});}}else{return new F(function(){return _X(_J1,_J2,B(_Jb(_J6,_J7,_J8,_J9,_Ja,_J3)),_J4);});}}else{return new T5(0,_J0,E(_J1),_J2,E(_J3),E(_J4));}},_Jb=function(_Jc,_Jd,_Je,_Jf,_Jg,_Jh){var _Ji=E(_Jh);if(!_Ji._){var _Jj=_Ji.a,_Jk=_Ji.b,_Jl=_Ji.c,_Jm=_Ji.d,_Jn=_Ji.e;if((imul(3,_Jc)|0)>=_Jj){if((imul(3,_Jj)|0)>=_Jc){return new F(function(){return _IN(new T5(0,_Jc,E(_Jd),_Je,E(_Jf),E(_Jg)),_Ji);});}else{return new F(function(){return _6(_Jd,_Je,_Jf,B(_IY(_Jg,_Jj,_Jk,_Jl,_Jm,_Jn)));});}}else{return new F(function(){return _X(_Jk,_Jl,B(_Jb(_Jc,_Jd,_Je,_Jf,_Jg,_Jm)),_Jn);});}}else{return new T5(0,_Jc,E(_Jd),_Je,E(_Jf),E(_Jg));}},_Jo=function(_Jp,_Jq){var _Jr=E(_Jp);if(!_Jr._){var _Js=_Jr.a,_Jt=_Jr.b,_Ju=_Jr.c,_Jv=_Jr.d,_Jw=_Jr.e,_Jx=E(_Jq);if(!_Jx._){var _Jy=_Jx.a,_Jz=_Jx.b,_JA=_Jx.c,_JB=_Jx.d,_JC=_Jx.e;if((imul(3,_Js)|0)>=_Jy){if((imul(3,_Jy)|0)>=_Js){return new F(function(){return _IN(_Jr,_Jx);});}else{return new F(function(){return _6(_Jt,_Ju,_Jv,B(_IY(_Jw,_Jy,_Jz,_JA,_JB,_JC)));});}}else{return new F(function(){return _X(_Jz,_JA,B(_Jb(_Js,_Jt,_Ju,_Jv,_Jw,_JB)),_JC);});}}else{return E(_Jr);}}else{return E(_Jq);}},_JD=function(_JE,_JF){var _JG=E(_JF);if(!_JG._){var _JH=_JG.b,_JI=_JG.c,_JJ=B(_JD(_JE,_JG.d)),_JK=_JJ.a,_JL=_JJ.b,_JM=B(_JD(_JE,_JG.e)),_JN=_JM.a,_JO=_JM.b;return (!B(A2(_JE,_JH,_JI)))?new T2(0,B(_Jo(_JK,_JN)),B(_2h(_JH,_JI,_JL,_JO))):new T2(0,B(_2h(_JH,_JI,_JK,_JN)),B(_Jo(_JL,_JO)));}else{return new T2(0,_0,_0);}},_JP=__Z,_JQ=function(_JR,_JS){while(1){var _JT=B((function(_JU,_JV){var _JW=E(_JV);if(!_JW._){var _JX=_JW.e,_JY=new T(function(){var _JZ=E(_JW.c),_K0=E(_JZ.b);if(!_K0._){return new T2(1,new T3(5,_JW.b,_JZ.a,_K0.a),new T(function(){return B(_JQ(_JU,_JX));}));}else{return B(_JQ(_JU,_JX));}},1);_JR=_JY;_JS=_JW.d;return __continue;}else{return E(_JU);}})(_JR,_JS));if(_JT!=__continue){return _JT;}}},_K1=function(_K2,_K3){var _K4=E(_K3);return (_K4._==0)?new T5(0,_K4.a,E(_K4.b),new T(function(){return B(A1(_K2,_K4.c));}),E(B(_K1(_K2,_K4.d))),E(B(_K1(_K2,_K4.e)))):new T0(1);},_K5=new T0(1),_K6=function(_K7){var _K8=E(_K7),_K9=E(_K8.b);return new T2(0,_K8.a,_K5);},_Ka=function(_Kb){return E(E(_Kb).b);},_Kc=function(_Kd,_Ke,_Kf){var _Kg=E(_Ke);if(!_Kg._){return E(_Kf);}else{var _Kh=function(_Ki,_Kj){while(1){var _Kk=E(_Kj);if(!_Kk._){var _Kl=_Kk.b,_Km=_Kk.e;switch(B(A3(_Ka,_Kd,_Ki,_Kl))){case 0:return new F(function(){return _2h(_Kl,_Kk.c,B(_Kh(_Ki,_Kk.d)),_Km);});break;case 1:return E(_Km);default:_Kj=_Km;continue;}}else{return new T0(1);}}};return new F(function(){return _Kh(_Kg.a,_Kf);});}},_Kn=function(_Ko,_Kp,_Kq){var _Kr=E(_Kp);if(!_Kr._){return E(_Kq);}else{var _Ks=function(_Kt,_Ku){while(1){var _Kv=E(_Ku);if(!_Kv._){var _Kw=_Kv.b,_Kx=_Kv.d;switch(B(A3(_Ka,_Ko,_Kw,_Kt))){case 0:return new F(function(){return _2h(_Kw,_Kv.c,_Kx,B(_Ks(_Kt,_Kv.e)));});break;case 1:return E(_Kx);default:_Ku=_Kx;continue;}}else{return new T0(1);}}};return new F(function(){return _Ks(_Kr.a,_Kq);});}},_Ky=function(_Kz,_KA,_KB,_KC){var _KD=E(_KA),_KE=E(_KC);if(!_KE._){var _KF=_KE.b,_KG=_KE.c,_KH=_KE.d,_KI=_KE.e;switch(B(A3(_Ka,_Kz,_KD,_KF))){case 0:return new F(function(){return _X(_KF,_KG,B(_Ky(_Kz,_KD,_KB,_KH)),_KI);});break;case 1:return E(_KE);default:return new F(function(){return _6(_KF,_KG,_KH,B(_Ky(_Kz,_KD,_KB,_KI)));});}}else{return new T5(0,1,E(_KD),_KB,E(_0),E(_0));}},_KJ=function(_KK,_KL,_KM,_KN){return new F(function(){return _Ky(_KK,_KL,_KM,_KN);});},_KO=function(_KP){return E(E(_KP).d);},_KQ=function(_KR){return E(E(_KR).f);},_KS=function(_KT,_KU,_KV,_KW){var _KX=E(_KU);if(!_KX._){var _KY=E(_KV);if(!_KY._){return E(_KW);}else{var _KZ=function(_L0,_L1){while(1){var _L2=E(_L1);if(!_L2._){if(!B(A3(_KQ,_KT,_L2.b,_L0))){return E(_L2);}else{_L1=_L2.d;continue;}}else{return new T0(1);}}};return new F(function(){return _KZ(_KY.a,_KW);});}}else{var _L3=_KX.a,_L4=E(_KV);if(!_L4._){var _L5=function(_L6,_L7){while(1){var _L8=E(_L7);if(!_L8._){if(!B(A3(_KO,_KT,_L8.b,_L6))){return E(_L8);}else{_L7=_L8.e;continue;}}else{return new T0(1);}}};return new F(function(){return _L5(_L3,_KW);});}else{var _L9=function(_La,_Lb,_Lc){while(1){var _Ld=E(_Lc);if(!_Ld._){var _Le=_Ld.b;if(!B(A3(_KO,_KT,_Le,_La))){if(!B(A3(_KQ,_KT,_Le,_Lb))){return E(_Ld);}else{_Lc=_Ld.d;continue;}}else{_Lc=_Ld.e;continue;}}else{return new T0(1);}}};return new F(function(){return _L9(_L3,_L4.a,_KW);});}}},_Lf=function(_Lg,_Lh,_Li,_Lj,_Lk){var _Ll=E(_Lk);if(!_Ll._){var _Lm=_Ll.b,_Ln=_Ll.c,_Lo=_Ll.d,_Lp=_Ll.e,_Lq=E(_Lj);if(!_Lq._){var _Lr=_Lq.b,_Ls=function(_Lt){var _Lu=new T1(1,E(_Lr));return new F(function(){return _2h(_Lr,_Lq.c,B(_Lf(_Lg,_Lh,_Lu,_Lq.d,B(_KS(_Lg,_Lh,_Lu,_Ll)))),B(_Lf(_Lg,_Lu,_Li,_Lq.e,B(_KS(_Lg,_Lu,_Li,_Ll)))));});};if(!E(_Lo)._){return new F(function(){return _Ls(_);});}else{if(!E(_Lp)._){return new F(function(){return _Ls(_);});}else{return new F(function(){return _KJ(_Lg,_Lm,_Ln,_Lq);});}}}else{return new F(function(){return _2h(_Lm,_Ln,B(_Kc(_Lg,_Lh,_Lo)),B(_Kn(_Lg,_Li,_Lp)));});}}else{return E(_Lj);}},_Lv=function(_Lw,_Lx,_Ly,_Lz,_LA,_LB,_LC,_LD,_LE,_LF,_LG,_LH,_LI){var _LJ=function(_LK){var _LL=new T1(1,E(_LA));return new F(function(){return _2h(_LA,_LB,B(_Lf(_Lw,_Lx,_LL,_LC,B(_KS(_Lw,_Lx,_LL,new T5(0,_LE,E(_LF),_LG,E(_LH),E(_LI)))))),B(_Lf(_Lw,_LL,_Ly,_LD,B(_KS(_Lw,_LL,_Ly,new T5(0,_LE,E(_LF),_LG,E(_LH),E(_LI)))))));});};if(!E(_LH)._){return new F(function(){return _LJ(_);});}else{if(!E(_LI)._){return new F(function(){return _LJ(_);});}else{return new F(function(){return _KJ(_Lw,_LF,_LG,new T5(0,_Lz,E(_LA),_LB,E(_LC),E(_LD)));});}}},_LM=function(_LN,_LO,_LP){var _LQ=new T(function(){var _LR=new T(function(){return E(E(_LP).b);}),_LS=B(_JD(function(_LT,_LU){var _LV=E(_LU);return new F(function(){return _Io(_LN,_LR,_LT,_LV.a,_LV.b);});},_LO));return new T2(0,_LS.a,_LS.b);}),_LW=new T(function(){return E(E(_LQ).a);});return new T2(0,new T(function(){var _LX=B(_K1(_K6,_LW));if(!_LX._){var _LY=E(E(_LQ).b);if(!_LY._){return B(_Lv(_Hs,_JP,_JP,_LX.a,_LX.b,_LX.c,_LX.d,_LX.e,_LY.a,_LY.b,_LY.c,_LY.d,_LY.e));}else{return E(_LX);}}else{return E(E(_LQ).b);}}),new T(function(){return B(_JQ(_1,_LW));}));},_LZ=function(_M0,_M1,_M2,_M3){while(1){var _M4=E(_M3);if(!_M4._){var _M5=_M4.d,_M6=_M4.e,_M7=E(_M4.b),_M8=E(_M7.a);if(_M0>=_M8){if(_M0!=_M8){_M1=_;_M3=_M6;continue;}else{var _M9=E(_M7.b);if(_M2>=_M9){if(_M2!=_M9){_M1=_;_M3=_M6;continue;}else{return true;}}else{_M1=_;_M3=_M5;continue;}}}else{_M1=_;_M3=_M5;continue;}}else{return false;}}},_Ma=function(_Mb,_Mc,_Md,_Me){while(1){var _Mf=E(_Me);if(!_Mf._){var _Mg=_Mf.d,_Mh=_Mf.e,_Mi=E(_Mf.b),_Mj=E(_Mi.a);if(_Mb>=_Mj){if(_Mb!=_Mj){_Mc=_;_Me=_Mh;continue;}else{var _Mk=E(_Md),_Ml=E(_Mi.b);if(_Mk>=_Ml){if(_Mk!=_Ml){return new F(function(){return _LZ(_Mb,_,_Mk,_Mh);});}else{return true;}}else{return new F(function(){return _LZ(_Mb,_,_Mk,_Mg);});}}}else{_Mc=_;_Me=_Mg;continue;}}else{return false;}}},_Mm=function(_Mn,_Mo,_Mp,_Mq,_Mr){var _Ms=E(_Mr);if(!_Ms._){var _Mt=_Ms.c,_Mu=_Ms.d,_Mv=_Ms.e,_Mw=E(_Ms.b),_Mx=E(_Mw.a);if(_Mn>=_Mx){if(_Mn!=_Mx){return new F(function(){return _6(_Mw,_Mt,_Mu,B(_Mm(_Mn,_,_Mp,_Mq,_Mv)));});}else{var _My=E(_Mw.b);if(_Mp>=_My){if(_Mp!=_My){return new F(function(){return _6(_Mw,_Mt,_Mu,B(_Mm(_Mn,_,_Mp,_Mq,_Mv)));});}else{return new T5(0,_Ms.a,E(new T2(0,_Mn,_Mp)),_Mq,E(_Mu),E(_Mv));}}else{return new F(function(){return _X(_Mw,_Mt,B(_Mm(_Mn,_,_Mp,_Mq,_Mu)),_Mv);});}}}else{return new F(function(){return _X(_Mw,_Mt,B(_Mm(_Mn,_,_Mp,_Mq,_Mu)),_Mv);});}}else{return new T5(0,1,E(new T2(0,_Mn,_Mp)),_Mq,E(_0),E(_0));}},_Mz=function(_MA,_MB,_MC,_MD,_ME){var _MF=E(_ME);if(!_MF._){var _MG=_MF.c,_MH=_MF.d,_MI=_MF.e,_MJ=E(_MF.b),_MK=E(_MJ.a);if(_MA>=_MK){if(_MA!=_MK){return new F(function(){return _6(_MJ,_MG,_MH,B(_Mz(_MA,_,_MC,_MD,_MI)));});}else{var _ML=E(_MC),_MM=E(_MJ.b);if(_ML>=_MM){if(_ML!=_MM){return new F(function(){return _6(_MJ,_MG,_MH,B(_Mm(_MA,_,_ML,_MD,_MI)));});}else{return new T5(0,_MF.a,E(new T2(0,_MA,_ML)),_MD,E(_MH),E(_MI));}}else{return new F(function(){return _X(_MJ,_MG,B(_Mm(_MA,_,_ML,_MD,_MH)),_MI);});}}}else{return new F(function(){return _X(_MJ,_MG,B(_Mz(_MA,_,_MC,_MD,_MH)),_MI);});}}else{return new T5(0,1,E(new T2(0,_MA,_MC)),_MD,E(_0),E(_0));}},_MN=function(_MO,_MP,_MQ,_MR){var _MS=E(_MR);if(!_MS._){var _MT=_MS.c,_MU=_MS.d,_MV=_MS.e,_MW=E(_MS.b),_MX=E(_MO),_MY=E(_MW.a);if(_MX>=_MY){if(_MX!=_MY){return new F(function(){return _6(_MW,_MT,_MU,B(_Mz(_MX,_,_MP,_MQ,_MV)));});}else{var _MZ=E(_MP),_N0=E(_MW.b);if(_MZ>=_N0){if(_MZ!=_N0){return new F(function(){return _6(_MW,_MT,_MU,B(_Mm(_MX,_,_MZ,_MQ,_MV)));});}else{return new T5(0,_MS.a,E(new T2(0,_MX,_MZ)),_MQ,E(_MU),E(_MV));}}else{return new F(function(){return _X(_MW,_MT,B(_Mm(_MX,_,_MZ,_MQ,_MU)),_MV);});}}}else{return new F(function(){return _X(_MW,_MT,B(_Mz(_MX,_,_MP,_MQ,_MU)),_MV);});}}else{return new T5(0,1,E(new T2(0,_MO,_MP)),_MQ,E(_0),E(_0));}},_N1=function(_N2,_N3,_N4){while(1){var _N5=B((function(_N6,_N7,_N8){var _N9=E(_N8);if(!_N9._){var _Na=_N9.c,_Nb=_N9.e,_Nc=E(_N9.b),_Nd=_Nc.a,_Ne=_Nc.b,_Nf=B(_N1(_N6,_N7,_N9.d)),_Ng=_Nf.a,_Nh=_Nf.b,_Ni=function(_Nj){return new F(function(){return _N1(new T(function(){return B(_MN(_Nd,_Ne,_Na,_Ng));}),new T2(1,new T3(7,_Nd,_Ne,_Na),_Nh),_Nb);});},_Nk=E(_Ng);if(!_Nk._){var _Nl=_Nk.d,_Nm=_Nk.e,_Nn=E(_Nk.b),_No=E(_Nd),_Np=E(_Nn.a);if(_No>=_Np){if(_No!=_Np){if(!B(_Ma(_No,_,_Ne,_Nm))){return new F(function(){return _Ni(_);});}else{_N2=_Nk;_N3=_Nh;_N4=_Nb;return __continue;}}else{var _Nq=E(_Ne),_Nr=E(_Nn.b);if(_Nq>=_Nr){if(_Nq!=_Nr){if(!B(_LZ(_No,_,_Nq,_Nm))){return new F(function(){return _Ni(_);});}else{_N2=_Nk;_N3=_Nh;_N4=_Nb;return __continue;}}else{_N2=_Nk;_N3=_Nh;_N4=_Nb;return __continue;}}else{if(!B(_LZ(_No,_,_Nq,_Nl))){return new F(function(){return _Ni(_);});}else{_N2=_Nk;_N3=_Nh;_N4=_Nb;return __continue;}}}}else{if(!B(_Ma(_No,_,_Ne,_Nl))){return new F(function(){return _Ni(_);});}else{_N2=_Nk;_N3=_Nh;_N4=_Nb;return __continue;}}}else{return new F(function(){return _Ni(_);});}}else{return new T2(0,_N6,_N7);}})(_N2,_N3,_N4));if(_N5!=__continue){return _N5;}}},_Ns=function(_Nt,_Nu){while(1){var _Nv=E(_Nt);switch(_Nv._){case 0:var _Nw=E(_Nu);if(!_Nw._){return new F(function(){return _GT(_Nv.a,_Nw.a);});}else{return false;}break;case 1:var _Nx=E(_Nu);if(_Nx._==1){if(!B(_Ns(_Nv.a,_Nx.a))){return false;}else{_Nt=_Nv.b;_Nu=_Nx.b;continue;}}else{return false;}break;case 2:var _Ny=E(_Nu);if(_Ny._==2){return new F(function(){return _GT(_Nv.a,_Ny.a);});}else{return false;}break;default:var _Nz=E(_Nu);if(_Nz._==3){if(E(_Nv.a)!=E(_Nz.a)){return false;}else{if(E(_Nv.b)!=E(_Nz.b)){return false;}else{_Nt=_Nv.c;_Nu=_Nz.c;continue;}}}else{return false;}}}},_NA=function(_NB,_NC){while(1){var _ND=E(_NB);switch(_ND._){case 0:var _NE=E(_NC);if(!_NE._){return new F(function(){return _GT(_ND.a,_NE.a);});}else{return false;}break;case 1:var _NF=E(_NC);if(_NF._==1){if(!B(_NA(_ND.a,_NF.a))){return false;}else{_NB=_ND.b;_NC=_NF.b;continue;}}else{return false;}break;case 2:var _NG=E(_NC);if(_NG._==2){if(!B(_NA(_ND.a,_NG.a))){return false;}else{_NB=_ND.b;_NC=_NG.b;continue;}}else{return false;}break;case 3:var _NH=E(_NC);if(_NH._==3){_NB=_ND.a;_NC=_NH.a;continue;}else{return false;}break;case 4:var _NI=E(_NC);if(_NI._==4){if(E(_ND.a)!=E(_NI.a)){return false;}else{if(E(_ND.b)!=E(_NI.b)){return false;}else{return new F(function(){return _GT(_ND.c,_NI.c);});}}}else{return false;}break;case 5:var _NJ=E(_NC);if(_NJ._==5){if(E(_ND.a)!=E(_NJ.a)){return false;}else{return new F(function(){return _GT(_ND.b,_NJ.b);});}}else{return false;}break;case 6:var _NK=E(_NC);if(_NK._==6){if(!B(_Ns(_ND.a,_NK.a))){return false;}else{return new F(function(){return _Ns(_ND.b,_NK.b);});}}else{return false;}break;case 7:return (E(_NC)._==7)?true:false;default:return (E(_NC)._==8)?true:false;}}},_NL=function(_NM,_NN){while(1){var _NO=E(_NM);switch(_NO._){case 0:return (E(_NN)._==0)?true:false;case 1:var _NP=E(_NN);if(_NP._==1){if(E(_NO.a)!=E(_NP.a)){return false;}else{if(E(_NO.b)!=E(_NP.b)){return false;}else{if(!B(_Ns(_NO.c,_NP.c))){return false;}else{if(E(_NO.d)!=E(_NP.d)){return false;}else{if(E(_NO.e)!=E(_NP.e)){return false;}else{if(!B(_NL(_NO.f,_NP.f))){return false;}else{_NM=_NO.g;_NN=_NP.g;continue;}}}}}}}else{return false;}break;case 2:var _NQ=E(_NN);if(_NQ._==2){if(E(_NO.a)!=E(_NQ.a)){return false;}else{_NM=_NO.b;_NN=_NQ.b;continue;}}else{return false;}break;case 3:var _NR=E(_NN);if(_NR._==3){if(E(_NO.a)!=E(_NR.a)){return false;}else{if(E(_NO.b)!=E(_NR.b)){return false;}else{if(E(_NO.c)!=E(_NR.c)){return false;}else{if(!B(_Ns(_NO.d,_NR.d))){return false;}else{if(E(_NO.e)!=E(_NR.e)){return false;}else{_NM=_NO.f;_NN=_NR.f;continue;}}}}}}else{return false;}break;case 4:var _NS=E(_NN);if(_NS._==4){if(!B(_NL(_NO.a,_NS.a))){return false;}else{_NM=_NO.b;_NN=_NS.b;continue;}}else{return false;}break;case 5:var _NT=E(_NN);if(_NT._==5){if(!B(_NA(_NO.a,_NT.a))){return false;}else{if(!B(_NL(_NO.b,_NT.b))){return false;}else{_NM=_NO.c;_NN=_NT.c;continue;}}}else{return false;}break;default:var _NU=E(_NN);if(_NU._==6){if(!B(_NA(_NO.a,_NU.a))){return false;}else{if(E(_NO.b)!=E(_NU.b)){return false;}else{if(!B(_NL(_NO.c,_NU.c))){return false;}else{_NM=_NO.d;_NN=_NU.d;continue;}}}}else{return false;}}}},_NV=function(_NW,_NX,_NY,_NZ){if(_NW!=_NY){return false;}else{return new F(function(){return _GT(_NX,_NZ);});}},_O0=function(_O1,_O2){var _O3=E(_O1),_O4=E(_O2);return new F(function(){return _NV(E(_O3.a),_O3.b,E(_O4.a),_O4.b);});},_O5=function(_O6,_O7,_O8,_O9){return (_O6!=_O8)?true:(E(_O7)!=E(_O9))?true:false;},_Oa=function(_Ob,_Oc){var _Od=E(_Ob),_Oe=E(_Oc);return new F(function(){return _O5(E(_Od.a),_Od.b,E(_Oe.a),_Oe.b);});},_Of=new T2(0,_O0,_Oa),_Og=new T2(0,_GT,_GW),_Oh=function(_Oi,_Oj,_Ok,_Ol,_Om,_On){return (!B(A3(_pR,_Oi,_Ok,_Om)))?true:(!B(A3(_pR,_Oj,_Ol,_On)))?true:false;},_Oo=function(_Op,_Oq,_Or,_Os){var _Ot=E(_Or),_Ou=E(_Os);return new F(function(){return _Oh(_Op,_Oq,_Ot.a,_Ot.b,_Ou.a,_Ou.b);});},_Ov=function(_Ow,_Ox,_Oy,_Oz,_OA,_OB){if(!B(A3(_pR,_Ow,_Oy,_OA))){return false;}else{return new F(function(){return A3(_pR,_Ox,_Oz,_OB);});}},_OC=function(_OD,_OE,_OF,_OG){var _OH=E(_OF),_OI=E(_OG);return new F(function(){return _Ov(_OD,_OE,_OH.a,_OH.b,_OI.a,_OI.b);});},_OJ=function(_OK,_OL){return new T2(0,function(_OM,_ON){return new F(function(){return _OC(_OK,_OL,_OM,_ON);});},function(_OM,_ON){return new F(function(){return _Oo(_OK,_OL,_OM,_ON);});});},_OO=function(_OP,_OQ,_OR){while(1){var _OS=E(_OQ);if(!_OS._){return (E(_OR)._==0)?true:false;}else{var _OT=E(_OR);if(!_OT._){return false;}else{if(!B(A3(_pR,_OP,_OS.a,_OT.a))){return false;}else{_OQ=_OS.b;_OR=_OT.b;continue;}}}}},_OU=function(_OV,_OW){var _OX=new T(function(){return B(_OJ(_OV,_OW));}),_OY=function(_OZ,_P0){var _P1=function(_P2){var _P3=function(_P4){if(_P2!=_P4){return false;}else{return new F(function(){return _OO(_OX,B(_hc(_1,_OZ)),B(_hc(_1,_P0)));});}},_P5=E(_P0);if(!_P5._){return new F(function(){return _P3(_P5.a);});}else{return new F(function(){return _P3(0);});}},_P6=E(_OZ);if(!_P6._){return new F(function(){return _P1(_P6.a);});}else{return new F(function(){return _P1(0);});}};return E(_OY);},_P7=new T(function(){return B(_OU(_Of,_Og));}),_P8=function(_P9,_Pa){var _Pb=E(_P9);if(!_Pb._){var _Pc=E(_Pa);if(!_Pc._){if(E(_Pb.a)!=E(_Pc.a)){return false;}else{return new F(function(){return _GT(_Pb.b,_Pc.b);});}}else{return false;}}else{return (E(_Pa)._==0)?false:true;}},_Pd=function(_Pe,_Pf,_Pg,_Ph){if(_Pe!=_Pg){return false;}else{return new F(function(){return _P8(_Pf,_Ph);});}},_Pi=function(_Pj,_Pk){var _Pl=E(_Pj),_Pm=E(_Pk);return new F(function(){return _Pd(E(_Pl.a),_Pl.b,E(_Pm.a),_Pm.b);});},_Pn=function(_Po,_Pp,_Pq,_Pr){if(_Po!=_Pq){return true;}else{var _Ps=E(_Pp);if(!_Ps._){var _Pt=E(_Pr);return (_Pt._==0)?(E(_Ps.a)!=E(_Pt.a))?true:(E(_Ps.b)!=E(_Pt.b))?true:false:true;}else{return (E(_Pr)._==0)?true:false;}}},_Pu=function(_Pv,_Pw){var _Px=E(_Pv),_Py=E(_Pw);return new F(function(){return _Pn(E(_Px.a),_Px.b,E(_Py.a),_Py.b);});},_Pz=new T2(0,_Pi,_Pu),_PA=new T(function(){return B(_OU(_GZ,_Pz));}),_PB=function(_PC,_PD,_PE,_PF){while(1){var _PG=E(_PF);if(!_PG._){var _PH=_PG.d,_PI=_PG.e,_PJ=E(_PG.b),_PK=E(_PJ.a);if(_PC>=_PK){if(_PC!=_PK){_PD=_;_PF=_PI;continue;}else{var _PL=E(_PJ.b);if(_PE>=_PL){if(_PE!=_PL){_PD=_;_PF=_PI;continue;}else{return new T1(1,_PG.c);}}else{_PD=_;_PF=_PH;continue;}}}else{_PD=_;_PF=_PH;continue;}}else{return __Z;}}},_PM=function(_PN,_PO,_PP,_PQ){while(1){var _PR=E(_PQ);if(!_PR._){var _PS=_PR.d,_PT=_PR.e,_PU=E(_PR.b),_PV=E(_PU.a);if(_PN>=_PV){if(_PN!=_PV){_PO=_;_PQ=_PT;continue;}else{var _PW=E(_PP),_PX=E(_PU.b);if(_PW>=_PX){if(_PW!=_PX){return new F(function(){return _PB(_PN,_,_PW,_PT);});}else{return new T1(1,_PR.c);}}else{return new F(function(){return _PB(_PN,_,_PW,_PS);});}}}else{_PO=_;_PQ=_PS;continue;}}else{return __Z;}}},_PY=function(_PZ,_Q0,_Q1,_Q2,_Q3){while(1){var _Q4=E(_Q3);if(!_Q4._){var _Q5=_Q4.c,_Q6=_Q4.d,_Q7=E(_Q4.b),_Q8=E(_PZ),_Q9=E(_Q7.a);if(_Q8>=_Q9){if(_Q8!=_Q9){_PZ=_Q8;_Q3=_Q6;continue;}else{var _Qa=E(_Q0),_Qb=E(_Q7.b);if(_Qa>=_Qb){if(_Qa!=_Qb){_PZ=_Q8;_Q0=_Qa;_Q3=_Q6;continue;}else{var _Qc=E(_Q1),_Qd=E(_Q7.c);if(_Qc>=_Qd){if(_Qc!=_Qd){_PZ=_Q8;_Q0=_Qa;_Q1=_Qc;_Q3=_Q6;continue;}else{var _Qe=E(_Q7.d);if(_Q2>=_Qe){if(_Q2!=_Qe){_PZ=_Q8;_Q0=_Qa;_Q1=_Qc;_Q3=_Q6;continue;}else{return true;}}else{_PZ=_Q8;_Q0=_Qa;_Q1=_Qc;_Q3=_Q5;continue;}}}else{_PZ=_Q8;_Q0=_Qa;_Q1=_Qc;_Q3=_Q5;continue;}}}else{_PZ=_Q8;_Q0=_Qa;_Q3=_Q5;continue;}}}else{_PZ=_Q8;_Q3=_Q5;continue;}}else{return false;}}},_Qf=function(_Qg,_Qh){return E(_Qg)+E(_Qh)|0;},_Qi=0,_Qj=function(_Qk,_Ql,_Qm){var _Qn=function(_Qo,_Qp){while(1){var _Qq=B((function(_Qr,_Qs){var _Qt=E(_Qs);if(!_Qt._){var _Qu=new T(function(){return B(_Qn(_Qr,_Qt.e));}),_Qv=function(_Qw){var _Qx=E(_Qt.c),_Qy=E(_Qx.b);if(!_Qy._){if(E(_Qx.a)!=E(_Ql)){return new F(function(){return A1(_Qu,_Qw);});}else{if(E(_Qy.b)>E(_Qm)){return new F(function(){return A1(_Qu,new T(function(){return B(_Qf(_Qw,_Qy.a));}));});}else{return new F(function(){return A1(_Qu,_Qw);});}}}else{return new F(function(){return A1(_Qu,_Qw);});}};_Qo=_Qv;_Qp=_Qt.d;return __continue;}else{return E(_Qr);}})(_Qo,_Qp));if(_Qq!=__continue){return _Qq;}}};return new F(function(){return A3(_Qn,_na,_Qk,_Qi);});},_Qz=function(_QA,_QB,_QC,_QD){while(1){var _QE=E(_QD);if(!_QE._){var _QF=_QE.d,_QG=_QE.e,_QH=E(_QE.b),_QI=E(_QH.a);if(_QA>=_QI){if(_QA!=_QI){_QB=_;_QD=_QG;continue;}else{var _QJ=E(_QH.b);if(_QC>=_QJ){if(_QC!=_QJ){_QB=_;_QD=_QG;continue;}else{return new T1(1,_QE.c);}}else{_QB=_;_QD=_QF;continue;}}}else{_QB=_;_QD=_QF;continue;}}else{return __Z;}}},_QK=function(_QL,_QM,_QN,_QO){while(1){var _QP=E(_QO);if(!_QP._){var _QQ=_QP.d,_QR=_QP.e,_QS=E(_QP.b),_QT=E(_QS.a);if(_QL>=_QT){if(_QL!=_QT){_QM=_;_QO=_QR;continue;}else{var _QU=E(_QN),_QV=E(_QS.b);if(_QU>=_QV){if(_QU!=_QV){return new F(function(){return _Qz(_QL,_,_QU,_QR);});}else{return new T1(1,_QP.c);}}else{return new F(function(){return _Qz(_QL,_,_QU,_QQ);});}}}else{_QM=_;_QO=_QQ;continue;}}else{return __Z;}}},_QW=function(_QX,_QY){while(1){var _QZ=E(_QY);if(!_QZ._){var _R0=E(_QZ.b);if(_QX>=_R0){if(_QX!=_R0){_QY=_QZ.e;continue;}else{return new T1(1,_QZ.c);}}else{_QY=_QZ.d;continue;}}else{return __Z;}}},_R1=function(_R2,_R3,_R4){while(1){var _R5=E(_R4);switch(_R5._){case 0:var _R6=B(_QW(E(_R5.a),_R2));if(!_R6._){return E(_Qi);}else{var _R7=E(E(_R6.a).b);return (_R7._==0)?E(_R7.a):E(_Qi);}break;case 1:return B(_R1(_R2,_R3,_R5.a))+B(_R1(_R2,_R3,_R5.b))|0;case 2:return E(_R5.a);default:var _R8=_R5.b,_R9=_R5.c,_Ra=E(_R3);if(!_Ra._){var _Rb=_Ra.d,_Rc=_Ra.e,_Rd=E(_Ra.b),_Re=E(_R5.a),_Rf=E(_Rd.a);if(_Re>=_Rf){if(_Re!=_Rf){var _Rg=B(_QK(_Re,_,_R8,_Rc));if(!_Rg._){_R3=_Ra;_R4=_R9;continue;}else{return E(_Rg.a);}}else{var _Rh=E(_R8),_Ri=E(_Rd.b);if(_Rh>=_Ri){if(_Rh!=_Ri){var _Rj=B(_Qz(_Re,_,_Rh,_Rc));if(!_Rj._){_R3=_Ra;_R4=_R9;continue;}else{return E(_Rj.a);}}else{return E(_Ra.c);}}else{var _Rk=B(_Qz(_Re,_,_Rh,_Rb));if(!_Rk._){_R3=_Ra;_R4=_R9;continue;}else{return E(_Rk.a);}}}}else{var _Rl=B(_QK(_Re,_,_R8,_Rb));if(!_Rl._){_R3=_Ra;_R4=_R9;continue;}else{return E(_Rl.a);}}}else{_R3=_0;_R4=_R9;continue;}}}},_Rm=__Z,_Rn=new T(function(){return B(unCStr("attempt to discount when insufficient cash available"));}),_Ro=new T(function(){return B(err(_Rn));}),_Rp=function(_Rq,_Rr){var _Rs=E(_Rr);if(!_Rs._){return (E(_Rq)==0)?__Z:E(_Ro);}else{var _Rt=_Rs.b,_Ru=E(_Rs.a),_Rv=_Ru.a,_Rw=E(_Ru.b),_Rx=_Rw.a,_Ry=E(_Rw.b);if(!_Ry._){var _Rz=_Ry.b,_RA=E(_Ry.a);return (_Rq>_RA)?(_RA>=_Rq)?E(_Rt):new T2(1,new T2(0,_Rv,new T2(0,_Rx,new T2(0,_Qi,_Rz))),new T(function(){return B(_Rp(_Rq-_RA|0,_Rt));})):new T2(1,new T2(0,_Rv,new T2(0,_Rx,new T2(0,_RA-_Rq|0,_Rz))),_1);}else{return E(_Rt);}}},_RB=function(_RC,_RD){var _RE=E(_RD);if(!_RE._){return (E(_RC)==0)?__Z:E(_Ro);}else{var _RF=_RE.b,_RG=E(_RE.a),_RH=_RG.a,_RI=E(_RG.b),_RJ=_RI.a,_RK=E(_RI.b);if(!_RK._){var _RL=_RK.b,_RM=E(_RC),_RN=E(_RK.a);return (_RM>_RN)?(_RN>=_RM)?E(_RF):new T2(1,new T2(0,_RH,new T2(0,_RJ,new T2(0,_Qi,_RL))),new T(function(){return B(_Rp(_RM-_RN|0,_RF));})):new T2(1,new T2(0,_RH,new T2(0,_RJ,new T2(0,_RN-_RM|0,_RL))),_1);}else{return E(_RF);}}},_RO=function(_RP,_RQ){var _RR=E(_RQ);if(!_RR._){var _RS=_RR.b,_RT=_RR.c,_RU=_RR.d,_RV=_RR.e;if(!B(A2(_RP,_RS,_RT))){return new F(function(){return _Jo(B(_RO(_RP,_RU)),B(_RO(_RP,_RV)));});}else{return new F(function(){return _2h(_RS,_RT,B(_RO(_RP,_RU)),B(_RO(_RP,_RV)));});}}else{return new T0(1);}},_RW=function(_RX,_RY){var _RZ=E(_RX);if(!_RZ._){var _S0=E(_RY);if(!_S0._){return new F(function(){return _Hd(_RZ.b,_S0.b);});}else{return 0;}}else{return (E(_RY)._==0)?2:1;}},_S1=function(_S2,_S3){return new F(function(){return _RW(E(E(_S2).b).b,E(E(_S3).b).b);});},_S4=new T2(1,_1,_1),_S5=function(_S6,_S7){var _S8=function(_S9,_Sa){var _Sb=E(_S9);if(!_Sb._){return E(_Sa);}else{var _Sc=_Sb.a,_Sd=E(_Sa);if(!_Sd._){return E(_Sb);}else{var _Se=_Sd.a;return (B(A2(_S6,_Sc,_Se))==2)?new T2(1,_Se,new T(function(){return B(_S8(_Sb,_Sd.b));})):new T2(1,_Sc,new T(function(){return B(_S8(_Sb.b,_Sd));}));}}},_Sf=function(_Sg){var _Sh=E(_Sg);if(!_Sh._){return __Z;}else{var _Si=E(_Sh.b);return (_Si._==0)?E(_Sh):new T2(1,new T(function(){return B(_S8(_Sh.a,_Si.a));}),new T(function(){return B(_Sf(_Si.b));}));}},_Sj=new T(function(){return B(_Sk(B(_Sf(_1))));}),_Sk=function(_Sl){while(1){var _Sm=E(_Sl);if(!_Sm._){return E(_Sj);}else{if(!E(_Sm.b)._){return E(_Sm.a);}else{_Sl=B(_Sf(_Sm));continue;}}}},_Sn=new T(function(){return B(_So(_1));}),_Sp=function(_Sq,_Sr,_Ss){while(1){var _St=B((function(_Su,_Sv,_Sw){var _Sx=E(_Sw);if(!_Sx._){return new T2(1,new T2(1,_Su,_Sv),_Sn);}else{var _Sy=_Sx.a;if(B(A2(_S6,_Su,_Sy))==2){var _Sz=new T2(1,_Su,_Sv);_Sq=_Sy;_Sr=_Sz;_Ss=_Sx.b;return __continue;}else{return new T2(1,new T2(1,_Su,_Sv),new T(function(){return B(_So(_Sx));}));}}})(_Sq,_Sr,_Ss));if(_St!=__continue){return _St;}}},_SA=function(_SB,_SC,_SD){while(1){var _SE=B((function(_SF,_SG,_SH){var _SI=E(_SH);if(!_SI._){return new T2(1,new T(function(){return B(A1(_SG,new T2(1,_SF,_1)));}),_Sn);}else{var _SJ=_SI.a,_SK=_SI.b;switch(B(A2(_S6,_SF,_SJ))){case 0:_SB=_SJ;_SC=function(_SL){return new F(function(){return A1(_SG,new T2(1,_SF,_SL));});};_SD=_SK;return __continue;case 1:_SB=_SJ;_SC=function(_SM){return new F(function(){return A1(_SG,new T2(1,_SF,_SM));});};_SD=_SK;return __continue;default:return new T2(1,new T(function(){return B(A1(_SG,new T2(1,_SF,_1)));}),new T(function(){return B(_So(_SI));}));}}})(_SB,_SC,_SD));if(_SE!=__continue){return _SE;}}},_So=function(_SN){var _SO=E(_SN);if(!_SO._){return E(_S4);}else{var _SP=_SO.a,_SQ=E(_SO.b);if(!_SQ._){return new T2(1,_SO,_1);}else{var _SR=_SQ.a,_SS=_SQ.b;if(B(A2(_S6,_SP,_SR))==2){return new F(function(){return _Sp(_SR,new T2(1,_SP,_1),_SS);});}else{return new F(function(){return _SA(_SR,function(_ST){return new T2(1,_SP,_ST);},_SS);});}}}};return new F(function(){return _Sk(B(_So(_S7)));});},_SU=function(_SV,_SW,_SX){var _SY=B(_EV(B(_RB(_SW,B(_S5(_S1,B(_hc(_1,B(_RO(function(_SZ,_T0){return new F(function(){return A1(_SV,_T0);});},_SX))))))))));if(!_SY._){var _T1=E(_SX);if(!_T1._){return new F(function(){return _Lv(_Hs,_JP,_JP,_SY.a,_SY.b,_SY.c,_SY.d,_SY.e,_T1.a,_T1.b,_T1.c,_T1.d,_T1.e);});}else{return E(_SY);}}else{return E(_SX);}},_T2=function(_T3,_T4){var _T5=E(_T3);return new F(function(){return _R1(_T5.a,_T5.b,_T4);});},_T6=function(_T7,_T8,_T9){var _Ta=E(_T9);if(!_Ta._){var _Tb=_Ta.d,_Tc=_Ta.e,_Td=E(_Ta.b),_Te=E(_T7),_Tf=E(_Td.a);if(_Te>=_Tf){if(_Te!=_Tf){return new F(function(){return _Ma(_Te,_,_T8,_Tc);});}else{var _Tg=E(_T8),_Th=E(_Td.b);if(_Tg>=_Th){if(_Tg!=_Th){return new F(function(){return _LZ(_Te,_,_Tg,_Tc);});}else{return true;}}else{return new F(function(){return _LZ(_Te,_,_Tg,_Tb);});}}}else{return new F(function(){return _Ma(_Te,_,_T8,_Tb);});}}else{return false;}},_Ti=function(_Tj,_Tk,_Tl){while(1){var _Tm=E(_Tk);switch(_Tm._){case 0:return (E(_Tm.a)>E(E(_Tl).b))?true:false;case 1:if(!B(_Ti(_Tj,_Tm.a,_Tl))){return false;}else{_Tk=_Tm.b;continue;}break;case 2:if(!B(_Ti(_Tj,_Tm.a,_Tl))){_Tk=_Tm.b;continue;}else{return true;}break;case 3:return (!B(_Ti(_Tj,_Tm.a,_Tl)))?true:false;case 4:var _Tn=_Tm.b,_To=_Tm.c,_Tp=E(E(_Tj).b);if(!_Tp._){var _Tq=_Tp.d,_Tr=_Tp.e,_Ts=E(_Tp.b),_Tt=E(_Tm.a),_Tu=E(_Ts.a);if(_Tt>=_Tu){if(_Tt!=_Tu){var _Tv=B(_QK(_Tt,_,_Tn,_Tr));if(!_Tv._){return false;}else{return new F(function(){return _GT(_Tv.a,_To);});}}else{var _Tw=E(_Tn),_Tx=E(_Ts.b);if(_Tw>=_Tx){if(_Tw!=_Tx){var _Ty=B(_Qz(_Tt,_,_Tw,_Tr));if(!_Ty._){return false;}else{return new F(function(){return _GT(_Ty.a,_To);});}}else{return new F(function(){return _GT(_Tp.c,_To);});}}else{var _Tz=B(_Qz(_Tt,_,_Tw,_Tq));if(!_Tz._){return false;}else{return new F(function(){return _GT(_Tz.a,_To);});}}}}else{var _TA=B(_QK(_Tt,_,_Tn,_Tq));if(!_TA._){return false;}else{return new F(function(){return _GT(_TA.a,_To);});}}}else{return false;}break;case 5:return new F(function(){return _T6(_Tm.a,_Tm.b,E(_Tj).b);});break;case 6:var _TB=E(_Tj),_TC=_TB.a,_TD=_TB.b;return B(_R1(_TC,_TD,_Tm.a))>=B(_R1(_TC,_TD,_Tm.b));case 7:return true;default:return false;}}},_TE=function(_TF,_TG,_TH,_TI){var _TJ=E(_TH);switch(_TJ._){case 0:return new T3(0,_TG,_Rm,_1);case 1:var _TK=_TJ.a,_TL=_TJ.b,_TM=_TJ.g,_TN=E(_TJ.e),_TO=E(E(_TI).b),_TP=_TN<=_TO,_TQ=new T(function(){var _TR=E(_TG);return B(_R1(_TR.a,_TR.b,_TJ.c));}),_TS=new T(function(){return E(_TJ.d)<=_TO;}),_TT=new T(function(){return B(_E2(E(_TK),new T2(0,_TL,new T(function(){if(!E(_TP)){if(!E(_TS)){return new T2(0,_TQ,_TN);}else{return new T0(1);}}else{return new T0(1);}})),E(_TG).a));});return (!E(_TP))?(!E(_TS))?(!B(_PY(_TK,_TL,_TQ,_TN,E(_TF).a)))?new T3(0,_TG,_TJ,_1):new T3(0,new T(function(){return new T2(0,_TT,E(_TG).b);}),_TJ.f,new T2(1,new T3(3,_TK,_TL,_TQ),_1)):new T3(0,new T(function(){return new T2(0,_TT,E(_TG).b);}),_TM,_1):new T3(0,new T(function(){return new T2(0,_TT,E(_TG).b);}),_TM,_1);case 2:var _TU=_TJ.b,_TV=E(_TG),_TW=_TV.a,_TX=E(_TJ.a),_TY=B(_QW(_TX,_TW));if(!_TY._){return new T3(0,_TV,_TJ,_1);}else{var _TZ=E(_TY.a),_U0=_TZ.a,_U1=E(_TZ.b);if(!_U1._){var _U2=_U1.a;return (!B(_HU(_TX,_,_U0,_U2,E(_TF).b)))?new T3(0,_TV,_TJ,_1):new T3(0,new T2(0,new T(function(){return B(_E2(_TX,new T2(0,_U0,_K5),_TW));}),_TV.b),_TU,new T2(1,new T3(4,_TX,_U0,_U2),_1));}else{return new T3(0,_TV,_TU,new T2(1,new T2(6,_TX,_U0),_1));}}break;case 3:var _U3=_TJ.a,_U4=_TJ.b,_U5=_TJ.c,_U6=_TJ.d,_U7=_TJ.f,_U8=E(E(_TI).b);if(E(_TJ.e)>_U8){var _U9=function(_Ua){var _Ub=E(_TG),_Uc=_Ub.a,_Ud=_Ub.b,_Ue=B(_R1(_Uc,_Ud,_U6));if(E(_Ua)!=_Ue){return new T3(0,_Ub,_TJ,_1);}else{if(B(_Qj(_Uc,_U4,_U8))<_Ue){return new T3(0,_Ub,_U7,new T2(1,new T4(2,_U3,_U4,_U5,_Ue),_1));}else{var _Uf=new T(function(){return B(_SU(function(_Ug){var _Uh=E(_Ug),_Ui=E(_Uh.b);return (_Ui._==0)?(E(_Uh.a)!=E(_U4))?false:(E(_Ui.b)>_U8)?true:false:false;},_Ue,_Uc));});return new T3(0,new T2(0,_Uf,_Ud),_U7,new T2(1,new T4(0,_U3,_U4,_U5,_Ue),_1));}}},_Uj=E(E(_TF).c);if(!_Uj._){var _Uk=_Uj.d,_Ul=_Uj.e,_Um=E(_Uj.b),_Un=E(_U3),_Uo=E(_Um.a);if(_Un>=_Uo){if(_Un!=_Uo){var _Up=B(_PM(_Un,_,_U5,_Ul));if(!_Up._){return new T3(0,_TG,_TJ,_1);}else{return new F(function(){return _U9(_Up.a);});}}else{var _Uq=E(_U5),_Ur=E(_Um.b);if(_Uq>=_Ur){if(_Uq!=_Ur){var _Us=B(_PB(_Un,_,_Uq,_Ul));if(!_Us._){return new T3(0,_TG,_TJ,_1);}else{return new F(function(){return _U9(_Us.a);});}}else{return new F(function(){return _U9(_Uj.c);});}}else{var _Ut=B(_PB(_Un,_,_Uq,_Uk));if(!_Ut._){return new T3(0,_TG,_TJ,_1);}else{return new F(function(){return _U9(_Ut.a);});}}}}else{var _Uu=B(_PM(_Un,_,_U5,_Uk));if(!_Uu._){return new T3(0,_TG,_TJ,_1);}else{return new F(function(){return _U9(_Uu.a);});}}}else{return new T3(0,_TG,_TJ,_1);}}else{return new T3(0,_TG,_U7,new T2(1,new T4(1,_U3,_U4,_U5,new T(function(){return B(_T2(_TG,_U6));})),_1));}break;case 4:var _Uv=new T(function(){var _Uw=B(_TE(_TF,_TG,_TJ.a,_TI));return new T3(0,_Uw.a,_Uw.b,_Uw.c);}),_Ux=new T(function(){var _Uy=B(_TE(_TF,new T(function(){return E(E(_Uv).a);}),_TJ.b,_TI));return new T3(0,_Uy.a,_Uy.b,_Uy.c);}),_Uz=new T(function(){return B(_hq(E(_Uv).c,new T(function(){return E(E(_Ux).c);},1)));}),_UA=new T(function(){var _UB=E(_Uv).b,_UC=E(_Ux).b,_UD=function(_UE){var _UF=E(_UC);switch(_UF._){case 0:return E(_UB);case 1:return new T2(4,_UB,_UF);case 2:return new T2(4,_UB,_UF);case 3:return new T2(4,_UB,_UF);case 4:return new T2(4,_UB,_UF);case 5:return new T2(4,_UB,_UF);default:return new T2(4,_UB,_UF);}};switch(E(_UB)._){case 0:return E(_UC);break;case 1:return B(_UD(_));break;case 2:return B(_UD(_));break;case 3:return B(_UD(_));break;case 4:return B(_UD(_));break;case 5:return B(_UD(_));break;default:return B(_UD(_));}});return new T3(0,new T(function(){return E(E(_Ux).a);}),_UA,_Uz);case 5:return (!B(_Ti(_TG,_TJ.a,_TI)))?new T3(0,_TG,_TJ.c,_1):new T3(0,_TG,_TJ.b,_1);default:var _UG=E(_TI);return (E(_TJ.b)>E(_UG.b))?(!B(_Ti(_TG,_TJ.a,_UG)))?new T3(0,_TG,_TJ,_1):new T3(0,_TG,_TJ.c,_1):new T3(0,_TG,_TJ.d,_1);}},_UH=function(_UI,_UJ,_UK,_UL,_UM){var _UN=E(_UL);switch(_UN._){case 0:return new T3(0,new T2(0,_UJ,_UK),_Rm,_1);case 1:var _UO=_UN.a,_UP=_UN.b,_UQ=_UN.g,_UR=E(_UN.e),_US=E(E(_UM).b),_UT=_UR<=_US,_UU=new T(function(){return B(_R1(_UJ,_UK,_UN.c));}),_UV=new T(function(){return E(_UN.d)<=_US;}),_UW=new T(function(){return B(_E2(E(_UO),new T2(0,_UP,new T(function(){if(!E(_UT)){if(!E(_UV)){return new T2(0,_UU,_UR);}else{return new T0(1);}}else{return new T0(1);}})),_UJ));});return (!E(_UT))?(!E(_UV))?(!B(_PY(_UO,_UP,_UU,_UR,E(_UI).a)))?new T3(0,new T2(0,_UJ,_UK),_UN,_1):new T3(0,new T2(0,_UW,_UK),_UN.f,new T2(1,new T3(3,_UO,_UP,_UU),_1)):new T3(0,new T2(0,_UW,_UK),_UQ,_1):new T3(0,new T2(0,_UW,_UK),_UQ,_1);case 2:var _UX=_UN.b,_UY=E(_UN.a),_UZ=B(_QW(_UY,_UJ));if(!_UZ._){return new T3(0,new T2(0,_UJ,_UK),_UN,_1);}else{var _V0=E(_UZ.a),_V1=_V0.a,_V2=E(_V0.b);if(!_V2._){var _V3=_V2.a;return (!B(_HU(_UY,_,_V1,_V3,E(_UI).b)))?new T3(0,new T2(0,_UJ,_UK),_UN,_1):new T3(0,new T2(0,new T(function(){return B(_E2(_UY,new T2(0,_V1,_K5),_UJ));}),_UK),_UX,new T2(1,new T3(4,_UY,_V1,_V3),_1));}else{return new T3(0,new T2(0,_UJ,_UK),_UX,new T2(1,new T2(6,_UY,_V1),_1));}}break;case 3:var _V4=_UN.a,_V5=_UN.b,_V6=_UN.c,_V7=_UN.d,_V8=_UN.f,_V9=E(E(_UM).b);if(E(_UN.e)>_V9){var _Va=function(_Vb){var _Vc=B(_R1(_UJ,_UK,_V7));if(E(_Vb)!=_Vc){return new T3(0,new T2(0,_UJ,_UK),_UN,_1);}else{if(B(_Qj(_UJ,_V5,_V9))<_Vc){return new T3(0,new T2(0,_UJ,_UK),_V8,new T2(1,new T4(2,_V4,_V5,_V6,_Vc),_1));}else{var _Vd=new T(function(){return B(_SU(function(_Ve){var _Vf=E(_Ve),_Vg=E(_Vf.b);return (_Vg._==0)?(E(_Vf.a)!=E(_V5))?false:(E(_Vg.b)>_V9)?true:false:false;},_Vc,_UJ));});return new T3(0,new T2(0,_Vd,_UK),_V8,new T2(1,new T4(0,_V4,_V5,_V6,_Vc),_1));}}},_Vh=E(E(_UI).c);if(!_Vh._){var _Vi=_Vh.d,_Vj=_Vh.e,_Vk=E(_Vh.b),_Vl=E(_V4),_Vm=E(_Vk.a);if(_Vl>=_Vm){if(_Vl!=_Vm){var _Vn=B(_PM(_Vl,_,_V6,_Vj));if(!_Vn._){return new T3(0,new T2(0,_UJ,_UK),_UN,_1);}else{return new F(function(){return _Va(_Vn.a);});}}else{var _Vo=E(_V6),_Vp=E(_Vk.b);if(_Vo>=_Vp){if(_Vo!=_Vp){var _Vq=B(_PB(_Vl,_,_Vo,_Vj));if(!_Vq._){return new T3(0,new T2(0,_UJ,_UK),_UN,_1);}else{return new F(function(){return _Va(_Vq.a);});}}else{return new F(function(){return _Va(_Vh.c);});}}else{var _Vr=B(_PB(_Vl,_,_Vo,_Vi));if(!_Vr._){return new T3(0,new T2(0,_UJ,_UK),_UN,_1);}else{return new F(function(){return _Va(_Vr.a);});}}}}else{var _Vs=B(_PM(_Vl,_,_V6,_Vi));if(!_Vs._){return new T3(0,new T2(0,_UJ,_UK),_UN,_1);}else{return new F(function(){return _Va(_Vs.a);});}}}else{return new T3(0,new T2(0,_UJ,_UK),_UN,_1);}}else{return new T3(0,new T2(0,_UJ,_UK),_V8,new T2(1,new T4(1,_V4,_V5,_V6,new T(function(){return B(_R1(_UJ,_UK,_V7));})),_1));}break;case 4:var _Vt=new T(function(){var _Vu=B(_UH(_UI,_UJ,_UK,_UN.a,_UM));return new T3(0,_Vu.a,_Vu.b,_Vu.c);}),_Vv=new T(function(){var _Vw=B(_TE(_UI,new T(function(){return E(E(_Vt).a);}),_UN.b,_UM));return new T3(0,_Vw.a,_Vw.b,_Vw.c);}),_Vx=new T(function(){return B(_hq(E(_Vt).c,new T(function(){return E(E(_Vv).c);},1)));}),_Vy=new T(function(){var _Vz=E(_Vt).b,_VA=E(_Vv).b,_VB=function(_VC){var _VD=E(_VA);switch(_VD._){case 0:return E(_Vz);case 1:return new T2(4,_Vz,_VD);case 2:return new T2(4,_Vz,_VD);case 3:return new T2(4,_Vz,_VD);case 4:return new T2(4,_Vz,_VD);case 5:return new T2(4,_Vz,_VD);default:return new T2(4,_Vz,_VD);}};switch(E(_Vz)._){case 0:return E(_VA);break;case 1:return B(_VB(_));break;case 2:return B(_VB(_));break;case 3:return B(_VB(_));break;case 4:return B(_VB(_));break;case 5:return B(_VB(_));break;default:return B(_VB(_));}});return new T3(0,new T(function(){return E(E(_Vv).a);}),_Vy,_Vx);case 5:return (!B(_Ti(new T2(0,_UJ,_UK),_UN.a,_UM)))?new T3(0,new T2(0,_UJ,_UK),_UN.c,_1):new T3(0,new T2(0,_UJ,_UK),_UN.b,_1);default:var _VE=E(_UM);return (E(_UN.b)>E(_VE.b))?(!B(_Ti(new T2(0,_UJ,_UK),_UN.a,_VE)))?new T3(0,new T2(0,_UJ,_UK),_UN,_1):new T3(0,new T2(0,_UJ,_UK),_UN.c,_1):new T3(0,new T2(0,_UJ,_UK),_UN.d,_1);}},_VF=function(_VG,_VH,_VI,_VJ,_VK,_VL){var _VM=B(_UH(_VG,_VH,_VI,_VJ,_VK)),_VN=_VM.b,_VO=_VM.c,_VP=E(_VM.a),_VQ=_VP.a,_VR=_VP.b,_VS=function(_VT){return new F(function(){return _VF(_VG,_VQ,_VR,_VN,_VK,new T(function(){return B(_hq(_VO,_VL));}));});};if(!B(A2(_PA,_VQ,_VH))){return new F(function(){return _VS(_);});}else{if(!B(A2(_P7,_VR,_VI))){return new F(function(){return _VS(_);});}else{if(!B(_NL(_VN,_VJ))){return new F(function(){return _VS(_);});}else{if(!E(_VO)._){return new T3(0,new T2(0,_VH,_VI),_VJ,_VL);}else{return new F(function(){return _VS(_);});}}}}},_VU=function(_VV,_VW,_VX,_VY){var _VZ=new T(function(){var _W0=B(_LM(_VV,new T(function(){return E(E(_VW).a);},1),_VY));return new T2(0,_W0.a,_W0.b);}),_W1=new T(function(){var _W2=B(_N1(new T(function(){return E(E(_VW).b);}),_1,E(_VV).d));return new T2(0,_W2.a,_W2.b);}),_W3=new T(function(){var _W4=E(_VW),_W5=B(_VF(_VV,new T(function(){return E(E(_VZ).a);}),new T(function(){return E(E(_W1).a);}),_VX,_VY,_1));return new T3(0,_W5.a,_W5.b,_W5.c);}),_W6=new T(function(){var _W7=new T(function(){return B(_hq(E(_VZ).b,new T(function(){return E(E(_W3).c);},1)));},1);return B(_hq(E(_W1).b,_W7));});return new T3(0,new T(function(){return E(E(_W3).a);}),new T(function(){return E(E(_W3).b);}),_W6);},_W8=function(_W9,_Wa){var _Wb=E(_W9),_Wc=E(_Wa);return (E(_Wb.a)!=E(_Wc.a))?true:(E(_Wb.b)!=E(_Wc.b))?true:(E(_Wb.c)!=E(_Wc.c))?true:(E(_Wb.d)!=E(_Wc.d))?true:false;},_Wd=function(_We,_Wf,_Wg,_Wh,_Wi,_Wj,_Wk,_Wl){if(_We!=_Wi){return false;}else{if(E(_Wf)!=E(_Wj)){return false;}else{if(E(_Wg)!=E(_Wk)){return false;}else{return new F(function(){return _GT(_Wh,_Wl);});}}}},_Wm=function(_Wn,_Wo){var _Wp=E(_Wn),_Wq=E(_Wo);return new F(function(){return _Wd(E(_Wp.a),_Wp.b,_Wp.c,_Wp.d,E(_Wq.a),_Wq.b,_Wq.c,_Wq.d);});},_Wr=new T2(0,_Wm,_W8),_Ws=function(_Wt,_Wu,_Wv,_Ww,_Wx,_Wy,_Wz,_WA){if(_Wt>=_Wx){if(_Wt!=_Wx){return false;}else{var _WB=E(_Wu),_WC=E(_Wy);if(_WB>=_WC){if(_WB!=_WC){return false;}else{var _WD=E(_Wv),_WE=E(_Wz);if(_WD>=_WE){if(_WD!=_WE){return false;}else{return new F(function(){return _Hp(_Ww,_WA);});}}else{return true;}}}else{return true;}}}else{return true;}},_WF=function(_WG,_WH){var _WI=E(_WG),_WJ=E(_WH);return new F(function(){return _Ws(E(_WI.a),_WI.b,_WI.c,_WI.d,E(_WJ.a),_WJ.b,_WJ.c,_WJ.d);});},_WK=function(_WL,_WM,_WN,_WO,_WP,_WQ,_WR,_WS){if(_WL>=_WP){if(_WL!=_WP){return false;}else{var _WT=E(_WM),_WU=E(_WQ);if(_WT>=_WU){if(_WT!=_WU){return false;}else{var _WV=E(_WN),_WW=E(_WR);if(_WV>=_WW){if(_WV!=_WW){return false;}else{return new F(function(){return _Hm(_WO,_WS);});}}else{return true;}}}else{return true;}}}else{return true;}},_WX=function(_WY,_WZ){var _X0=E(_WY),_X1=E(_WZ);return new F(function(){return _WK(E(_X0.a),_X0.b,_X0.c,_X0.d,E(_X1.a),_X1.b,_X1.c,_X1.d);});},_X2=function(_X3,_X4,_X5,_X6,_X7,_X8,_X9,_Xa){if(_X3>=_X7){if(_X3!=_X7){return true;}else{var _Xb=E(_X4),_Xc=E(_X8);if(_Xb>=_Xc){if(_Xb!=_Xc){return true;}else{var _Xd=E(_X5),_Xe=E(_X9);if(_Xd>=_Xe){if(_Xd!=_Xe){return true;}else{return new F(function(){return _Hj(_X6,_Xa);});}}else{return false;}}}else{return false;}}}else{return false;}},_Xf=function(_Xg,_Xh){var _Xi=E(_Xg),_Xj=E(_Xh);return new F(function(){return _X2(E(_Xi.a),_Xi.b,_Xi.c,_Xi.d,E(_Xj.a),_Xj.b,_Xj.c,_Xj.d);});},_Xk=function(_Xl,_Xm,_Xn,_Xo,_Xp,_Xq,_Xr,_Xs){if(_Xl>=_Xp){if(_Xl!=_Xp){return true;}else{var _Xt=E(_Xm),_Xu=E(_Xq);if(_Xt>=_Xu){if(_Xt!=_Xu){return true;}else{var _Xv=E(_Xn),_Xw=E(_Xr);if(_Xv>=_Xw){if(_Xv!=_Xw){return true;}else{return new F(function(){return _Hg(_Xo,_Xs);});}}else{return false;}}}else{return false;}}}else{return false;}},_Xx=function(_Xy,_Xz){var _XA=E(_Xy),_XB=E(_Xz);return new F(function(){return _Xk(E(_XA.a),_XA.b,_XA.c,_XA.d,E(_XB.a),_XB.b,_XB.c,_XB.d);});},_XC=function(_XD,_XE,_XF,_XG,_XH,_XI,_XJ,_XK){if(_XD>=_XH){if(_XD!=_XH){return 2;}else{var _XL=E(_XE),_XM=E(_XI);if(_XL>=_XM){if(_XL!=_XM){return 2;}else{var _XN=E(_XF),_XO=E(_XJ);if(_XN>=_XO){if(_XN!=_XO){return 2;}else{return new F(function(){return _Hd(_XG,_XK);});}}else{return 0;}}}else{return 0;}}}else{return 0;}},_XP=function(_XQ,_XR){var _XS=E(_XQ),_XT=E(_XR);return new F(function(){return _XC(E(_XS.a),_XS.b,_XS.c,_XS.d,E(_XT.a),_XT.b,_XT.c,_XT.d);});},_XU=function(_XV,_XW){var _XX=E(_XV),_XY=E(_XX.a),_XZ=E(_XW),_Y0=E(_XZ.a);if(_XY>=_Y0){if(_XY!=_Y0){return E(_XX);}else{var _Y1=E(_XX.b),_Y2=E(_XZ.b);if(_Y1>=_Y2){if(_Y1!=_Y2){return E(_XX);}else{var _Y3=E(_XX.c),_Y4=E(_XZ.c);return (_Y3>=_Y4)?(_Y3!=_Y4)?E(_XX):(E(_XX.d)>E(_XZ.d))?E(_XX):E(_XZ):E(_XZ);}}else{return E(_XZ);}}}else{return E(_XZ);}},_Y5=function(_Y6,_Y7){var _Y8=E(_Y6),_Y9=E(_Y8.a),_Ya=E(_Y7),_Yb=E(_Ya.a);if(_Y9>=_Yb){if(_Y9!=_Yb){return E(_Ya);}else{var _Yc=E(_Y8.b),_Yd=E(_Ya.b);if(_Yc>=_Yd){if(_Yc!=_Yd){return E(_Ya);}else{var _Ye=E(_Y8.c),_Yf=E(_Ya.c);return (_Ye>=_Yf)?(_Ye!=_Yf)?E(_Ya):(E(_Y8.d)>E(_Ya.d))?E(_Ya):E(_Y8):E(_Y8);}}else{return E(_Y8);}}}else{return E(_Y8);}},_Yg={_:0,a:_Wr,b:_XP,c:_WF,d:_WX,e:_Xf,f:_Xx,g:_XU,h:_Y5},_Yh=function(_Yi,_Yj,_Yk,_Yl){if(_Yi>=_Yk){if(_Yi!=_Yk){return 2;}else{return new F(function(){return _Hd(_Yj,_Yl);});}}else{return 0;}},_Ym=function(_Yn,_Yo){var _Yp=E(_Yn),_Yq=E(_Yo);return new F(function(){return _Yh(E(_Yp.a),_Yp.b,E(_Yq.a),_Yq.b);});},_Yr=function(_Ys,_Yt,_Yu,_Yv){if(_Ys>=_Yu){if(_Ys!=_Yu){return false;}else{return new F(function(){return _Hp(_Yt,_Yv);});}}else{return true;}},_Yw=function(_Yx,_Yy){var _Yz=E(_Yx),_YA=E(_Yy);return new F(function(){return _Yr(E(_Yz.a),_Yz.b,E(_YA.a),_YA.b);});},_YB=function(_YC,_YD,_YE,_YF){if(_YC>=_YE){if(_YC!=_YE){return false;}else{return new F(function(){return _Hm(_YD,_YF);});}}else{return true;}},_YG=function(_YH,_YI){var _YJ=E(_YH),_YK=E(_YI);return new F(function(){return _YB(E(_YJ.a),_YJ.b,E(_YK.a),_YK.b);});},_YL=function(_YM,_YN,_YO,_YP){if(_YM>=_YO){if(_YM!=_YO){return true;}else{return new F(function(){return _Hj(_YN,_YP);});}}else{return false;}},_YQ=function(_YR,_YS){var _YT=E(_YR),_YU=E(_YS);return new F(function(){return _YL(E(_YT.a),_YT.b,E(_YU.a),_YU.b);});},_YV=function(_YW,_YX,_YY,_YZ){if(_YW>=_YY){if(_YW!=_YY){return true;}else{return new F(function(){return _Hg(_YX,_YZ);});}}else{return false;}},_Z0=function(_Z1,_Z2){var _Z3=E(_Z1),_Z4=E(_Z2);return new F(function(){return _YV(E(_Z3.a),_Z3.b,E(_Z4.a),_Z4.b);});},_Z5=function(_Z6,_Z7){var _Z8=E(_Z6),_Z9=_Z8.b,_Za=E(_Z8.a),_Zb=E(_Z7),_Zc=_Zb.b,_Zd=E(_Zb.a);if(_Za>=_Zd){if(_Za!=_Zd){return new T2(0,_Za,_Z9);}else{var _Ze=E(_Z9),_Zf=E(_Zc);return (_Ze>_Zf)?new T2(0,_Za,_Ze):new T2(0,_Zd,_Zf);}}else{return new T2(0,_Zd,_Zc);}},_Zg=function(_Zh,_Zi){var _Zj=E(_Zh),_Zk=_Zj.b,_Zl=E(_Zj.a),_Zm=E(_Zi),_Zn=_Zm.b,_Zo=E(_Zm.a);if(_Zl>=_Zo){if(_Zl!=_Zo){return new T2(0,_Zo,_Zn);}else{var _Zp=E(_Zk),_Zq=E(_Zn);return (_Zp>_Zq)?new T2(0,_Zo,_Zq):new T2(0,_Zl,_Zp);}}else{return new T2(0,_Zl,_Zk);}},_Zr={_:0,a:_Of,b:_Ym,c:_Yw,d:_YG,e:_YQ,f:_Z0,g:_Z5,h:_Zg},_Zs=function(_Zt,_Zu,_Zv,_Zw){if(_Zt!=_Zv){return false;}else{return new F(function(){return _GT(_Zu,_Zw);});}},_Zx=function(_Zy,_Zz){var _ZA=E(_Zy),_ZB=E(_Zz);return new F(function(){return _Zs(E(_ZA.a),_ZA.b,E(_ZB.a),_ZB.b);});},_ZC=function(_ZD,_ZE,_ZF,_ZG){return (_ZD!=_ZF)?true:(E(_ZE)!=E(_ZG))?true:false;},_ZH=function(_ZI,_ZJ){var _ZK=E(_ZI),_ZL=E(_ZJ);return new F(function(){return _ZC(E(_ZK.a),_ZK.b,E(_ZL.a),_ZL.b);});},_ZM=new T2(0,_Zx,_ZH),_ZN=function(_ZO,_ZP,_ZQ,_ZR){if(_ZO>=_ZQ){if(_ZO!=_ZQ){return 2;}else{return new F(function(){return _Hd(_ZP,_ZR);});}}else{return 0;}},_ZS=function(_ZT,_ZU){var _ZV=E(_ZT),_ZW=E(_ZU);return new F(function(){return _ZN(E(_ZV.a),_ZV.b,E(_ZW.a),_ZW.b);});},_ZX=function(_ZY,_ZZ,_100,_101){if(_ZY>=_100){if(_ZY!=_100){return false;}else{return new F(function(){return _Hp(_ZZ,_101);});}}else{return true;}},_102=function(_103,_104){var _105=E(_103),_106=E(_104);return new F(function(){return _ZX(E(_105.a),_105.b,E(_106.a),_106.b);});},_107=function(_108,_109,_10a,_10b){if(_108>=_10a){if(_108!=_10a){return false;}else{return new F(function(){return _Hm(_109,_10b);});}}else{return true;}},_10c=function(_10d,_10e){var _10f=E(_10d),_10g=E(_10e);return new F(function(){return _107(E(_10f.a),_10f.b,E(_10g.a),_10g.b);});},_10h=function(_10i,_10j,_10k,_10l){if(_10i>=_10k){if(_10i!=_10k){return true;}else{return new F(function(){return _Hj(_10j,_10l);});}}else{return false;}},_10m=function(_10n,_10o){var _10p=E(_10n),_10q=E(_10o);return new F(function(){return _10h(E(_10p.a),_10p.b,E(_10q.a),_10q.b);});},_10r=function(_10s,_10t,_10u,_10v){if(_10s>=_10u){if(_10s!=_10u){return true;}else{return new F(function(){return _Hg(_10t,_10v);});}}else{return false;}},_10w=function(_10x,_10y){var _10z=E(_10x),_10A=E(_10y);return new F(function(){return _10r(E(_10z.a),_10z.b,E(_10A.a),_10A.b);});},_10B=function(_10C,_10D){var _10E=E(_10C),_10F=_10E.b,_10G=E(_10E.a),_10H=E(_10D),_10I=_10H.b,_10J=E(_10H.a);if(_10G>=_10J){if(_10G!=_10J){return new T2(0,_10G,_10F);}else{var _10K=E(_10F),_10L=E(_10I);return (_10K>_10L)?new T2(0,_10G,_10K):new T2(0,_10J,_10L);}}else{return new T2(0,_10J,_10I);}},_10M=function(_10N,_10O){var _10P=E(_10N),_10Q=_10P.b,_10R=E(_10P.a),_10S=E(_10O),_10T=_10S.b,_10U=E(_10S.a);if(_10R>=_10U){if(_10R!=_10U){return new T2(0,_10U,_10T);}else{var _10V=E(_10Q),_10W=E(_10T);return (_10V>_10W)?new T2(0,_10U,_10W):new T2(0,_10R,_10V);}}else{return new T2(0,_10R,_10Q);}},_10X={_:0,a:_ZM,b:_ZS,c:_102,d:_10c,e:_10m,f:_10w,g:_10B,h:_10M},_10Y=function(_10Z,_110){var _111=E(_10Z),_112=E(_110);return (E(_111.a)!=E(_112.a))?true:(E(_111.b)!=E(_112.b))?true:(E(_111.c)!=E(_112.c))?true:false;},_113=function(_114,_115,_116,_117,_118,_119){if(_114!=_117){return false;}else{if(E(_115)!=E(_118)){return false;}else{return new F(function(){return _GT(_116,_119);});}}},_11a=function(_11b,_11c){var _11d=E(_11b),_11e=E(_11c);return new F(function(){return _113(E(_11d.a),_11d.b,_11d.c,E(_11e.a),_11e.b,_11e.c);});},_11f=new T2(0,_11a,_10Y),_11g=function(_11h,_11i,_11j,_11k,_11l,_11m){if(_11h>=_11k){if(_11h!=_11k){return false;}else{var _11n=E(_11i),_11o=E(_11l);if(_11n>=_11o){if(_11n!=_11o){return false;}else{return new F(function(){return _Hp(_11j,_11m);});}}else{return true;}}}else{return true;}},_11p=function(_11q,_11r){var _11s=E(_11q),_11t=E(_11r);return new F(function(){return _11g(E(_11s.a),_11s.b,_11s.c,E(_11t.a),_11t.b,_11t.c);});},_11u=function(_11v,_11w,_11x,_11y,_11z,_11A){if(_11v>=_11y){if(_11v!=_11y){return false;}else{var _11B=E(_11w),_11C=E(_11z);if(_11B>=_11C){if(_11B!=_11C){return false;}else{return new F(function(){return _Hm(_11x,_11A);});}}else{return true;}}}else{return true;}},_11D=function(_11E,_11F){var _11G=E(_11E),_11H=E(_11F);return new F(function(){return _11u(E(_11G.a),_11G.b,_11G.c,E(_11H.a),_11H.b,_11H.c);});},_11I=function(_11J,_11K,_11L,_11M,_11N,_11O){if(_11J>=_11M){if(_11J!=_11M){return true;}else{var _11P=E(_11K),_11Q=E(_11N);if(_11P>=_11Q){if(_11P!=_11Q){return true;}else{return new F(function(){return _Hj(_11L,_11O);});}}else{return false;}}}else{return false;}},_11R=function(_11S,_11T){var _11U=E(_11S),_11V=E(_11T);return new F(function(){return _11I(E(_11U.a),_11U.b,_11U.c,E(_11V.a),_11V.b,_11V.c);});},_11W=function(_11X,_11Y,_11Z,_120,_121,_122){if(_11X>=_120){if(_11X!=_120){return true;}else{var _123=E(_11Y),_124=E(_121);if(_123>=_124){if(_123!=_124){return true;}else{return new F(function(){return _Hg(_11Z,_122);});}}else{return false;}}}else{return false;}},_125=function(_126,_127){var _128=E(_126),_129=E(_127);return new F(function(){return _11W(E(_128.a),_128.b,_128.c,E(_129.a),_129.b,_129.c);});},_12a=function(_12b,_12c,_12d,_12e,_12f,_12g){if(_12b>=_12e){if(_12b!=_12e){return 2;}else{var _12h=E(_12c),_12i=E(_12f);if(_12h>=_12i){if(_12h!=_12i){return 2;}else{return new F(function(){return _Hd(_12d,_12g);});}}else{return 0;}}}else{return 0;}},_12j=function(_12k,_12l){var _12m=E(_12k),_12n=E(_12l);return new F(function(){return _12a(E(_12m.a),_12m.b,_12m.c,E(_12n.a),_12n.b,_12n.c);});},_12o=function(_12p,_12q){var _12r=E(_12p),_12s=E(_12r.a),_12t=E(_12q),_12u=E(_12t.a);if(_12s>=_12u){if(_12s!=_12u){return E(_12r);}else{var _12v=E(_12r.b),_12w=E(_12t.b);return (_12v>=_12w)?(_12v!=_12w)?E(_12r):(E(_12r.c)>E(_12t.c))?E(_12r):E(_12t):E(_12t);}}else{return E(_12t);}},_12x=function(_12y,_12z){var _12A=E(_12y),_12B=E(_12A.a),_12C=E(_12z),_12D=E(_12C.a);if(_12B>=_12D){if(_12B!=_12D){return E(_12C);}else{var _12E=E(_12A.b),_12F=E(_12C.b);return (_12E>=_12F)?(_12E!=_12F)?E(_12C):(E(_12A.c)>E(_12C.c))?E(_12C):E(_12A):E(_12A);}}else{return E(_12A);}},_12G={_:0,a:_11f,b:_12j,c:_11p,d:_11D,e:_11R,f:_125,g:_12o,h:_12x},_12H=__Z,_12I=function(_12J,_12K,_12L){var _12M=E(_12K);if(!_12M._){return E(_12L);}else{var _12N=function(_12O,_12P){while(1){var _12Q=E(_12P);if(!_12Q._){var _12R=_12Q.b,_12S=_12Q.d;switch(B(A3(_Ka,_12J,_12O,_12R))){case 0:return new F(function(){return _7J(_12R,B(_12N(_12O,_12Q.c)),_12S);});break;case 1:return E(_12S);default:_12P=_12S;continue;}}else{return new T0(1);}}};return new F(function(){return _12N(_12M.a,_12L);});}},_12T=function(_12U,_12V,_12W){var _12X=E(_12V);if(!_12X._){return E(_12W);}else{var _12Y=function(_12Z,_130){while(1){var _131=E(_130);if(!_131._){var _132=_131.b,_133=_131.c;switch(B(A3(_Ka,_12U,_132,_12Z))){case 0:return new F(function(){return _7J(_132,_133,B(_12Y(_12Z,_131.d)));});break;case 1:return E(_133);default:_130=_133;continue;}}else{return new T0(1);}}};return new F(function(){return _12Y(_12X.a,_12W);});}},_134=function(_135,_136,_137){var _138=E(_136),_139=E(_137);if(!_139._){var _13a=_139.b,_13b=_139.c,_13c=_139.d;switch(B(A3(_Ka,_135,_138,_13a))){case 0:return new F(function(){return _6x(_13a,B(_134(_135,_138,_13b)),_13c);});break;case 1:return E(_139);default:return new F(function(){return _5N(_13a,_13b,B(_134(_135,_138,_13c)));});}}else{return new T4(0,1,E(_138),E(_5I),E(_5I));}},_13d=function(_13e,_13f,_13g){return new F(function(){return _134(_13e,_13f,_13g);});},_13h=function(_13i,_13j,_13k,_13l){var _13m=E(_13j);if(!_13m._){var _13n=E(_13k);if(!_13n._){return E(_13l);}else{var _13o=function(_13p,_13q){while(1){var _13r=E(_13q);if(!_13r._){if(!B(A3(_KQ,_13i,_13r.b,_13p))){return E(_13r);}else{_13q=_13r.c;continue;}}else{return new T0(1);}}};return new F(function(){return _13o(_13n.a,_13l);});}}else{var _13s=_13m.a,_13t=E(_13k);if(!_13t._){var _13u=function(_13v,_13w){while(1){var _13x=E(_13w);if(!_13x._){if(!B(A3(_KO,_13i,_13x.b,_13v))){return E(_13x);}else{_13w=_13x.d;continue;}}else{return new T0(1);}}};return new F(function(){return _13u(_13s,_13l);});}else{var _13y=function(_13z,_13A,_13B){while(1){var _13C=E(_13B);if(!_13C._){var _13D=_13C.b;if(!B(A3(_KO,_13i,_13D,_13z))){if(!B(A3(_KQ,_13i,_13D,_13A))){return E(_13C);}else{_13B=_13C.c;continue;}}else{_13B=_13C.d;continue;}}else{return new T0(1);}}};return new F(function(){return _13y(_13s,_13t.a,_13l);});}}},_13E=function(_13F,_13G,_13H,_13I,_13J){var _13K=E(_13J);if(!_13K._){var _13L=_13K.b,_13M=_13K.c,_13N=_13K.d,_13O=E(_13I);if(!_13O._){var _13P=_13O.b,_13Q=function(_13R){var _13S=new T1(1,E(_13P));return new F(function(){return _7J(_13P,B(_13E(_13F,_13G,_13S,_13O.c,B(_13h(_13F,_13G,_13S,_13K)))),B(_13E(_13F,_13S,_13H,_13O.d,B(_13h(_13F,_13S,_13H,_13K)))));});};if(!E(_13M)._){return new F(function(){return _13Q(_);});}else{if(!E(_13N)._){return new F(function(){return _13Q(_);});}else{return new F(function(){return _13d(_13F,_13L,_13O);});}}}else{return new F(function(){return _7J(_13L,B(_12I(_13F,_13G,_13M)),B(_12T(_13F,_13H,_13N)));});}}else{return E(_13I);}},_13T=function(_13U,_13V,_13W,_13X,_13Y,_13Z,_140,_141,_142,_143,_144){var _145=function(_146){var _147=new T1(1,E(_13Y));return new F(function(){return _7J(_13Y,B(_13E(_13U,_13V,_147,_13Z,B(_13h(_13U,_13V,_147,new T4(0,_141,E(_142),E(_143),E(_144)))))),B(_13E(_13U,_147,_13W,_140,B(_13h(_13U,_147,_13W,new T4(0,_141,E(_142),E(_143),E(_144)))))));});};if(!E(_143)._){return new F(function(){return _145(_);});}else{if(!E(_144)._){return new F(function(){return _145(_);});}else{return new F(function(){return _13d(_13U,_142,new T4(0,_13X,E(_13Y),E(_13Z),E(_140)));});}}},_148=function(_149,_14a,_14b,_14c,_14d,_14e,_14f,_14g){return new T4(0,new T(function(){var _14h=E(_149);if(!_14h._){var _14i=E(_14d);if(!_14i._){return B(_13T(_Yg,_12H,_12H,_14h.a,_14h.b,_14h.c,_14h.d,_14i.a,_14i.b,_14i.c,_14i.d));}else{return E(_14h);}}else{return E(_14d);}}),new T(function(){var _14j=E(_14a);if(!_14j._){var _14k=E(_14e);if(!_14k._){return B(_13T(_12G,_12H,_12H,_14j.a,_14j.b,_14j.c,_14j.d,_14k.a,_14k.b,_14k.c,_14k.d));}else{return E(_14j);}}else{return E(_14e);}}),new T(function(){var _14l=E(_14b);if(!_14l._){var _14m=E(_14f);if(!_14m._){return B(_Lv(_10X,_JP,_JP,_14l.a,_14l.b,_14l.c,_14l.d,_14l.e,_14m.a,_14m.b,_14m.c,_14m.d,_14m.e));}else{return E(_14l);}}else{return E(_14f);}}),new T(function(){var _14n=E(_14c);if(!_14n._){var _14o=E(_14g);if(!_14o._){return B(_Lv(_Zr,_JP,_JP,_14n.a,_14n.b,_14n.c,_14n.d,_14n.e,_14o.a,_14o.b,_14o.c,_14o.d,_14o.e));}else{return E(_14n);}}else{return E(_14g);}}));},_14p=function(_14q,_14r){while(1){var _14s=E(_14r);if(!_14s._){var _14t=E(_14s.b);if(_14q>=_14t){if(_14q!=_14t){_14r=_14s.e;continue;}else{return true;}}else{_14r=_14s.d;continue;}}else{return false;}}},_14u=function(_14v,_14w){while(1){var _14x=E(_14w);if(!_14x._){var _14y=E(_14x.b);if(_14v>=_14y){if(_14v!=_14y){_14w=_14x.e;continue;}else{return new T1(1,_14x.c);}}else{_14w=_14x.d;continue;}}else{return __Z;}}},_14z=function(_14A,_14B){var _14C=E(_14A);switch(_14C._){case 1:var _14D=E(_14B),_14E=_14D.a,_14F=E(_14C.a);return (!B(_14p(_14F,_14E)))?new T4(0,new T4(0,1,E(new T4(0,_14F,_14C.b,new T(function(){return B(_R1(_14E,_14D.b,_14C.c));}),_14C.e)),E(_5I),E(_5I)),_5I,_0,_0):new T4(0,_5I,_5I,_0,_0);case 2:var _14G=E(_14C.a),_14H=B(_14u(_14G,E(_14B).a));if(!_14H._){return new T4(0,_5I,_5I,_0,_0);}else{var _14I=E(_14H.a),_14J=E(_14I.b);return (_14J._==0)?new T4(0,_5I,new T4(0,1,E(new T3(0,_14G,_14I.a,_14J.a)),E(_5I),E(_5I)),_0,_0):new T4(0,_5I,_5I,_0,_0);}break;case 3:return new T4(0,_5I,_5I,new T5(0,1,E(new T2(0,_14C.a,_14C.c)),new T(function(){return B(_T2(_14B,_14C.d));}),E(_0),E(_0)),_0);case 4:var _14K=B(_14z(_14C.a,_14B)),_14L=B(_14z(_14C.b,_14B));return new F(function(){return _148(_14K.a,_14K.b,_14K.c,_14K.d,_14L.a,_14L.b,_14L.c,_14L.d);});break;default:return new T4(0,_5I,_5I,_0,_0);}},_14M=function(_14N,_14O){var _14P=new T(function(){var _14Q=function(_14R,_14S){while(1){var _14T=B((function(_14U,_14V){var _14W=E(_14V);if(!_14W._){var _14X=_14W.e,_14Y=new T(function(){var _14Z=E(_14W.c),_150=E(_14Z.b);if(!_150._){var _151=E(E(_14N).b);if(E(_150.b)>_151){var _152=function(_153,_154){while(1){var _155=B((function(_156,_157){var _158=E(_157);if(!_158._){var _159=_158.e,_15a=new T(function(){var _15b=E(_158.c),_15c=E(_15b.b);if(!_15c._){if(E(_15c.b)>_151){return B(_152(_156,_159));}else{return new T2(1,new T3(0,_158.b,_15b.a,_15c.a),new T(function(){return B(_152(_156,_159));}));}}else{return B(_152(_156,_159));}},1);_153=_15a;_154=_158.d;return __continue;}else{return E(_156);}})(_153,_154));if(_155!=__continue){return _155;}}};return B(_152(_14U,_14X));}else{var _15d=new T(function(){var _15e=function(_15f,_15g){while(1){var _15h=B((function(_15i,_15j){var _15k=E(_15j);if(!_15k._){var _15l=_15k.e,_15m=new T(function(){var _15n=E(_15k.c),_15o=E(_15n.b);if(!_15o._){if(E(_15o.b)>_151){return B(_15e(_15i,_15l));}else{return new T2(1,new T3(0,_15k.b,_15n.a,_15o.a),new T(function(){return B(_15e(_15i,_15l));}));}}else{return B(_15e(_15i,_15l));}},1);_15f=_15m;_15g=_15k.d;return __continue;}else{return E(_15i);}})(_15f,_15g));if(_15h!=__continue){return _15h;}}};return B(_15e(_14U,_14X));});return new T2(1,new T3(0,_14W.b,_14Z.a,_150.a),_15d);}}else{return B(_14Q(_14U,_14X));}},1);_14R=_14Y;_14S=_14W.d;return __continue;}else{return E(_14U);}})(_14R,_14S));if(_14T!=__continue){return _14T;}}};return B(_c2(B(_14Q(_1,_14O))));});return new T4(0,_5I,_14P,_0,_0);},_15p=function(_15q,_15r,_15s,_15t,_15u){while(1){var _15v=E(_15q);if(!_15v._){return new T4(0,_15r,_15s,_15t,_15u);}else{var _15w=E(_15v.a),_15x=B(_148(_15r,_15s,_15t,_15u,_15w.a,_15w.b,_15w.c,_15w.d));_15q=_15v.b;_15r=_15x.a;_15s=_15x.b;_15t=_15x.c;_15u=_15x.d;continue;}}},_15y=function(_15z,_15A,_15B,_15C,_15D,_15E){var _15F=E(_15z),_15G=B(_148(_15B,_15C,_15D,_15E,_15F.a,_15F.b,_15F.c,_15F.d));return new F(function(){return _15p(_15A,_15G.a,_15G.b,_15G.c,_15G.d);});},_15H=0,_15I=function(_15J){var _15K=E(_15J);switch(_15K._){case 1:var _15L=B(_15I(_15K.a));return new F(function(){return _15y(new T(function(){var _15M=B(_15I(_15K.b));return new T4(0,_15M.a,_15M.b,_15M.c,_15M.d);}),_1,_15L.a,_15L.b,_15L.c,_15L.d);});break;case 3:var _15N=B(_15I(_15K.c));return new F(function(){return _148(_5I,_5I,_0,new T5(0,1,E(new T2(0,_15K.a,_15K.b)),_15H,E(_0),E(_0)),_15N.a,_15N.b,_15N.c,_15N.d);});break;default:return new T4(0,_5I,_5I,_0,_0);}},_15O=function(_15P,_15Q,_15R,_15S){while(1){var _15T=E(_15S);if(!_15T._){var _15U=_15T.d,_15V=_15T.e,_15W=E(_15T.b),_15X=E(_15W.a);if(_15P>=_15X){if(_15P!=_15X){_15Q=_;_15S=_15V;continue;}else{var _15Y=E(_15W.b);if(_15R>=_15Y){if(_15R!=_15Y){_15Q=_;_15S=_15V;continue;}else{return true;}}else{_15Q=_;_15S=_15U;continue;}}}else{_15Q=_;_15S=_15U;continue;}}else{return false;}}},_15Z=function(_160,_161,_162,_163){while(1){var _164=E(_163);if(!_164._){var _165=_164.d,_166=_164.e,_167=E(_164.b),_168=E(_167.a);if(_160>=_168){if(_160!=_168){_161=_;_163=_166;continue;}else{var _169=E(_162),_16a=E(_167.b);if(_169>=_16a){if(_169!=_16a){return new F(function(){return _15O(_160,_,_169,_166);});}else{return true;}}else{return new F(function(){return _15O(_160,_,_169,_165);});}}}else{_161=_;_163=_165;continue;}}else{return false;}}},_16b=function(_16c,_16d,_16e,_16f,_16g){while(1){var _16h=E(_16c);if(!_16h._){return new T4(0,_16d,_16e,_16f,_16g);}else{var _16i=E(_16h.a),_16j=B(_148(_16d,_16e,_16f,_16g,_16i.a,_16i.b,_16i.c,_16i.d));_16c=_16h.b;_16d=_16j.a;_16e=_16j.b;_16f=_16j.c;_16g=_16j.d;continue;}}},_16k=function(_16l,_16m,_16n,_16o,_16p){while(1){var _16q=E(_16l);if(!_16q._){return new T4(0,_16m,_16n,_16o,_16p);}else{var _16r=E(_16q.a),_16s=B(_148(_16m,_16n,_16o,_16p,_16r.a,_16r.b,_16r.c,_16r.d));_16l=_16q.b;_16m=_16s.a;_16n=_16s.b;_16o=_16s.c;_16p=_16s.d;continue;}}},_16t=function(_16u,_16v,_16w,_16x,_16y){while(1){var _16z=E(_16u);if(!_16z._){return new T4(0,_16v,_16w,_16x,_16y);}else{var _16A=E(_16z.a),_16B=B(_148(_16v,_16w,_16x,_16y,_16A.a,_16A.b,_16A.c,_16A.d));_16u=_16z.b;_16v=_16B.a;_16w=_16B.b;_16x=_16B.c;_16y=_16B.d;continue;}}},_16C=function(_16D,_16E){var _16F=B(_15I(_16E));return new T4(0,_16F.a,_16F.b,_16F.c,_16F.d);},_16G=function(_16H,_16I){var _16J=B(_16K(_16H,_16I));return new T4(0,_16J.a,_16J.b,_16J.c,_16J.d);},_16K=function(_16L,_16M){while(1){var _16N=B((function(_16O,_16P){var _16Q=E(_16P);switch(_16Q._){case 1:var _16R=B(_16K(_16O,_16Q.a));return new F(function(){return _16t(new T2(1,new T(function(){return B(_16G(_16O,_16Q.b));}),_1),_16R.a,_16R.b,_16R.c,_16R.d);});break;case 2:var _16S=B(_16K(_16O,_16Q.a));return new F(function(){return _16k(new T2(1,new T(function(){return B(_16G(_16O,_16Q.b));}),_1),_16S.a,_16S.b,_16S.c,_16S.d);});break;case 3:var _16T=_16O;_16L=_16T;_16M=_16Q.a;return __continue;case 4:var _16U=_16Q.a,_16V=_16Q.b,_16W=E(E(_16O).b);if(!_16W._){var _16X=_16W.d,_16Y=_16W.e,_16Z=E(_16W.b),_170=E(_16U),_171=E(_16Z.a);if(_170>=_171){if(_170!=_171){return (!B(_15Z(_170,_,_16V,_16Y)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_170,_16V)),_15H,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}else{var _172=E(_16V),_173=E(_16Z.b);return (_172>=_173)?(_172!=_173)?(!B(_15O(_170,_,_172,_16Y)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_170,_172)),_15H,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0):new T4(0,_5I,_5I,_0,_0):(!B(_15O(_170,_,_172,_16X)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_170,_172)),_15H,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}}else{return (!B(_15Z(_170,_,_16V,_16X)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_170,_16V)),_15H,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}}else{return new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_16U,_16V)),_15H,E(_0),E(_0)));}break;case 5:var _174=_16Q.a,_175=_16Q.b,_176=E(E(_16O).b);if(!_176._){var _177=_176.d,_178=_176.e,_179=E(_176.b),_17a=E(_174),_17b=E(_179.a);if(_17a>=_17b){if(_17a!=_17b){return (!B(_15Z(_17a,_,_175,_178)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_17a,_175)),_15H,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}else{var _17c=E(_175),_17d=E(_179.b);return (_17c>=_17d)?(_17c!=_17d)?(!B(_15O(_17a,_,_17c,_178)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_17a,_17c)),_15H,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0):new T4(0,_5I,_5I,_0,_0):(!B(_15O(_17a,_,_17c,_177)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_17a,_17c)),_15H,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}}else{return (!B(_15Z(_17a,_,_175,_177)))?new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_17a,_175)),_15H,E(_0),E(_0))):new T4(0,_5I,_5I,_0,_0);}}else{return new T4(0,_5I,_5I,_0,new T5(0,1,E(new T2(0,_174,_175)),_15H,E(_0),E(_0)));}break;case 6:var _17e=B(_15I(_16Q.a));return new F(function(){return _16b(new T2(1,new T(function(){return B(_16C(_16O,_16Q.b));}),_1),_17e.a,_17e.b,_17e.c,_17e.d);});break;default:return new T4(0,_5I,_5I,_0,_0);}})(_16L,_16M));if(_16N!=__continue){return _16N;}}},_17f=function(_17g,_17h,_17i,_17j,_17k){while(1){var _17l=E(_17g);if(!_17l._){return new T4(0,_17h,_17i,_17j,_17k);}else{var _17m=E(_17l.a),_17n=B(_148(_17h,_17i,_17j,_17k,_17m.a,_17m.b,_17m.c,_17m.d));_17g=_17l.b;_17h=_17n.a;_17i=_17n.b;_17j=_17n.c;_17k=_17n.d;continue;}}},_17o=function(_17p,_17q){var _17r=B(_17s(_17p,_17q));return new T4(0,_17r.a,_17r.b,_17r.c,_17r.d);},_17s=function(_17t,_17u){while(1){var _17v=B((function(_17w,_17x){var _17y=E(_17x);switch(_17y._){case 0:return new T4(0,_5I,_5I,_0,_0);case 1:var _17z=B(_15I(_17y.c)),_17A=B(_17s(_17w,_17y.f)),_17B=B(_148(_17z.a,_17z.b,_17z.c,_17z.d,_17A.a,_17A.b,_17A.c,_17A.d)),_17C=B(_17s(_17w,_17y.g));return new F(function(){return _148(_17B.a,_17B.b,_17B.c,_17B.d,_17C.a,_17C.b,_17C.c,_17C.d);});break;case 2:var _17D=_17w;_17t=_17D;_17u=_17y.b;return __continue;case 3:var _17E=B(_15I(_17y.d)),_17F=B(_17s(_17w,_17y.f));return new F(function(){return _148(_17E.a,_17E.b,_17E.c,_17E.d,_17F.a,_17F.b,_17F.c,_17F.d);});break;case 4:var _17G=B(_17s(_17w,_17y.a));return new F(function(){return _17f(new T2(1,new T(function(){return B(_17o(_17w,_17y.b));}),_1),_17G.a,_17G.b,_17G.c,_17G.d);});break;case 5:var _17H=B(_16K(_17w,_17y.a)),_17I=B(_17s(_17w,_17y.b)),_17J=B(_148(_17H.a,_17H.b,_17H.c,_17H.d,_17I.a,_17I.b,_17I.c,_17I.d)),_17K=B(_17s(_17w,_17y.c));return new F(function(){return _148(_17J.a,_17J.b,_17J.c,_17J.d,_17K.a,_17K.b,_17K.c,_17K.d);});break;default:var _17L=B(_16K(_17w,_17y.a)),_17M=B(_17s(_17w,_17y.c)),_17N=B(_148(_17L.a,_17L.b,_17L.c,_17L.d,_17M.a,_17M.b,_17M.c,_17M.d)),_17O=B(_17s(_17w,_17y.d));return new F(function(){return _148(_17N.a,_17N.b,_17N.c,_17N.d,_17O.a,_17O.b,_17O.c,_17O.d);});}})(_17t,_17u));if(_17v!=__continue){return _17v;}}},_17P=function(_17Q,_17R,_17S,_17T,_17U){while(1){var _17V=E(_17Q);if(!_17V._){return new T4(0,_17R,_17S,_17T,_17U);}else{var _17W=E(_17V.a),_17X=B(_148(_17R,_17S,_17T,_17U,_17W.a,_17W.b,_17W.c,_17W.d));_17Q=_17V.b;_17R=_17X.a;_17S=_17X.b;_17T=_17X.c;_17U=_17X.d;continue;}}},_17Y=function(_17Z,_180,_181,_182,_183,_184){var _185=E(_17Z),_186=B(_148(_181,_182,_183,_184,_185.a,_185.b,_185.c,_185.d));return new F(function(){return _17P(_180,_186.a,_186.b,_186.c,_186.d);});},_187=function(_188,_189,_18a,_18b){var _18c=B(_VU(_189,_18b,_18a,_188)),_18d=_18c.a,_18e=_18c.b,_18f=B(_14z(_18e,_18d));return new F(function(){return _17Y(new T(function(){var _18g=B(_14M(_188,E(_18d).a));return new T4(0,_18g.a,_18g.b,_18g.c,_18g.d);}),new T2(1,new T(function(){var _18h=B(_17s(_18d,_18e));return new T4(0,_18h.a,_18h.b,_18h.c,_18h.d);}),_1),_18f.a,_18f.b,_18f.c,_18f.d);});},_18i="(function (t) {return document.getElementById(t).value})",_18j=new T(function(){return eval("(function () {return Blockly.Marlowe.workspaceToCode(demoWorkspace);})");}),_18k=new T(function(){return B(unCStr("contractState"));}),_18l=new T(function(){return B(unCStr("currBlock"));}),_18m=new T(function(){return eval("(function (x) { var node = document.getElementById(x); while (node.hasChildNodes()) { node.removeChild(node.lastChild); } })");}),_18n=new T(function(){return B(err(_ha));}),_18o=new T(function(){return B(err(_jS));}),_18p=new T(function(){return B(A3(_xS,_yl,_xn,_DB));}),_18q=new T(function(){return B(err(_ha));}),_18r=new T(function(){return B(err(_jS));}),_18s=function(_zv){return new F(function(){return _xH(_BM,_zv);});},_18t=function(_18u,_18v){return new F(function(){return _yv(_18s,_18v);});},_18w=new T(function(){return B(_yv(_18s,_jV));}),_18x=function(_zv){return new F(function(){return _l5(_18w,_zv);});},_18y=function(_18z){var _18A=new T(function(){return B(A3(_xH,_BM,_18z,_jV));});return function(_zc){return new F(function(){return _l5(_18A,_zc);});};},_18B=new T4(0,_18y,_18x,_18s,_18t),_18C=new T(function(){return B(unCStr("NotRedeemed"));}),_18D=new T(function(){return B(unCStr("ManuallyRedeemed"));}),_18E=function(_18F,_18G){var _18H=new T(function(){var _18I=new T(function(){return B(A1(_18G,_K5));});return B(_wQ(function(_18J){var _18K=E(_18J);return (_18K._==3)?(!B(_lT(_18K.a,_18D)))?new T0(2):E(_18I):new T0(2);}));}),_18L=function(_18M){return E(_18H);},_18N=new T(function(){if(E(_18F)>10){return new T0(2);}else{var _18O=new T(function(){var _18P=new T(function(){var _18Q=function(_18R){return new F(function(){return A3(_xS,_yl,_ze,function(_18S){return new F(function(){return A1(_18G,new T2(0,_18R,_18S));});});});};return B(A3(_xS,_yl,_ze,_18Q));});return B(_wQ(function(_18T){var _18U=E(_18T);return (_18U._==3)?(!B(_lT(_18U.a,_18C)))?new T0(2):E(_18P):new T0(2);}));}),_18V=function(_18W){return E(_18O);};return new T1(1,function(_18X){return new F(function(){return A2(_vx,_18X,_18V);});});}});return new F(function(){return _lf(new T1(1,function(_18Y){return new F(function(){return A2(_vx,_18Y,_18L);});}),_18N);});},_18Z=function(_zv){return new F(function(){return _xH(_18E,_zv);});},_190=function(_191,_192){return new F(function(){return _yv(_18Z,_192);});},_193=new T(function(){return B(_yv(_18Z,_jV));}),_194=function(_zv){return new F(function(){return _l5(_193,_zv);});},_195=function(_196){var _197=new T(function(){return B(A3(_xH,_18E,_196,_jV));});return function(_zc){return new F(function(){return _l5(_197,_zc);});};},_198=new T4(0,_195,_194,_18Z,_190),_199=function(_19a,_19b){return new F(function(){return _A0(_zd,_198,_19b);});},_19c=new T(function(){return B(_yv(_199,_jV));}),_19d=function(_zv){return new F(function(){return _l5(_19c,_zv);});},_19e=new T(function(){return B(_A0(_zd,_198,_jV));}),_19f=function(_zv){return new F(function(){return _l5(_19e,_zv);});},_19g=function(_19h,_zv){return new F(function(){return _19f(_zv);});},_19i=function(_19j,_19k){return new F(function(){return _yv(_199,_19k);});},_19l=new T4(0,_19g,_19d,_199,_19i),_19m=function(_19n,_19o){return new F(function(){return _A0(_18B,_19l,_19o);});},_19p=function(_19q,_19r){return new F(function(){return _yv(_19m,_19r);});},_19s=new T(function(){return B(_yv(_19p,_jV));}),_19t=function(_Av){return new F(function(){return _l5(_19s,_Av);});},_19u=function(_19v){return new F(function(){return _yv(_19p,_19v);});},_19w=function(_19x,_19y){return new F(function(){return _19u(_19y);});},_19z=new T(function(){return B(_yv(_19m,_jV));}),_19A=function(_Av){return new F(function(){return _l5(_19z,_Av);});},_19B=function(_19C,_Av){return new F(function(){return _19A(_Av);});},_19D=new T4(0,_19B,_19t,_19p,_19w),_19E=new T(function(){return B(_A0(_19D,_AF,_DB));}),_19F=42,_19G=new T(function(){return B(unCStr("actions"));}),_19H=function(_19I){while(1){var _19J=B((function(_19K){var _19L=E(_19K);if(!_19L._){return __Z;}else{var _19M=_19L.b,_19N=E(_19L.a);if(!E(_19N.b)._){return new T2(1,_19N.a,new T(function(){return B(_19H(_19M));}));}else{_19I=_19M;return __continue;}}})(_19I));if(_19J!=__continue){return _19J;}}},_19O=new T(function(){return B(err(_ha));}),_19P=new T(function(){return B(err(_jS));}),_19Q=new T(function(){return B(unCStr("ConstMoney"));}),_19R=new T(function(){return B(unCStr("AvailableMoney"));}),_19S=new T(function(){return B(unCStr("AddMoney"));}),_19T=new T(function(){return B(unCStr("MoneyFromChoice"));}),_19U=function(_19V,_19W){var _19X=new T(function(){var _19Y=new T(function(){var _19Z=new T(function(){if(_19V>10){return new T0(2);}else{var _1a0=new T(function(){var _1a1=new T(function(){var _1a2=function(_1a3){var _1a4=function(_1a5){return new F(function(){return A3(_xH,_1a6,_ze,function(_1a7){return new F(function(){return A1(_19W,new T3(3,_1a3,_1a5,_1a7));});});});};return new F(function(){return A3(_xS,_yl,_ze,_1a4);});};return B(A3(_xH,_zr,_ze,_1a2));});return B(_wQ(function(_1a8){var _1a9=E(_1a8);return (_1a9._==3)?(!B(_lT(_1a9.a,_19T)))?new T0(2):E(_1a1):new T0(2);}));}),_1aa=function(_1ab){return E(_1a0);};return new T1(1,function(_1ac){return new F(function(){return A2(_vx,_1ac,_1aa);});});}});if(_19V>10){return B(_lf(_jU,_19Z));}else{var _1ad=new T(function(){var _1ae=new T(function(){return B(A3(_xS,_yl,_ze,function(_1af){return new F(function(){return A1(_19W,new T1(2,_1af));});}));});return B(_wQ(function(_1ag){var _1ah=E(_1ag);return (_1ah._==3)?(!B(_lT(_1ah.a,_19Q)))?new T0(2):E(_1ae):new T0(2);}));}),_1ai=function(_1aj){return E(_1ad);};return B(_lf(new T1(1,function(_1ak){return new F(function(){return A2(_vx,_1ak,_1ai);});}),_19Z));}});if(_19V>10){return B(_lf(_jU,_19Y));}else{var _1al=new T(function(){var _1am=new T(function(){var _1an=function(_1ao){return new F(function(){return A3(_xH,_1a6,_ze,function(_1ap){return new F(function(){return A1(_19W,new T2(1,_1ao,_1ap));});});});};return B(A3(_xH,_1a6,_ze,_1an));});return B(_wQ(function(_1aq){var _1ar=E(_1aq);return (_1ar._==3)?(!B(_lT(_1ar.a,_19S)))?new T0(2):E(_1am):new T0(2);}));}),_1as=function(_1at){return E(_1al);};return B(_lf(new T1(1,function(_1au){return new F(function(){return A2(_vx,_1au,_1as);});}),_19Y));}});if(_19V>10){return new F(function(){return _lf(_jU,_19X);});}else{var _1av=new T(function(){var _1aw=new T(function(){return B(A3(_xH,_BM,_ze,function(_1ax){return new F(function(){return A1(_19W,new T1(0,_1ax));});}));});return B(_wQ(function(_1ay){var _1az=E(_1ay);return (_1az._==3)?(!B(_lT(_1az.a,_19R)))?new T0(2):E(_1aw):new T0(2);}));}),_1aA=function(_1aB){return E(_1av);};return new F(function(){return _lf(new T1(1,function(_1aC){return new F(function(){return A2(_vx,_1aC,_1aA);});}),_19X);});}},_1a6=function(_1aD,_1aE){return new F(function(){return _19U(E(_1aD),_1aE);});},_1aF=new T0(7),_1aG=function(_1aH,_1aI){return new F(function(){return A1(_1aI,_1aF);});},_1aJ=new T(function(){return B(unCStr("TrueObs"));}),_1aK=new T2(0,_1aJ,_1aG),_1aL=new T0(8),_1aM=function(_1aN,_1aO){return new F(function(){return A1(_1aO,_1aL);});},_1aP=new T(function(){return B(unCStr("FalseObs"));}),_1aQ=new T2(0,_1aP,_1aM),_1aR=new T2(1,_1aQ,_1),_1aS=new T2(1,_1aK,_1aR),_1aT=function(_1aU,_1aV,_1aW){var _1aX=E(_1aU);if(!_1aX._){return new T0(2);}else{var _1aY=E(_1aX.a),_1aZ=_1aY.a,_1b0=new T(function(){return B(A2(_1aY.b,_1aV,_1aW));}),_1b1=new T(function(){return B(_wQ(function(_1b2){var _1b3=E(_1b2);switch(_1b3._){case 3:return (!B(_lT(_1aZ,_1b3.a)))?new T0(2):E(_1b0);case 4:return (!B(_lT(_1aZ,_1b3.a)))?new T0(2):E(_1b0);default:return new T0(2);}}));}),_1b4=function(_1b5){return E(_1b1);};return new F(function(){return _lf(new T1(1,function(_1b6){return new F(function(){return A2(_vx,_1b6,_1b4);});}),new T(function(){return B(_1aT(_1aX.b,_1aV,_1aW));}));});}},_1b7=new T(function(){return B(unCStr("ValueGE"));}),_1b8=new T(function(){return B(unCStr("PersonChoseSomething"));}),_1b9=new T(function(){return B(unCStr("PersonChoseThis"));}),_1ba=new T(function(){return B(unCStr("BelowTimeout"));}),_1bb=new T(function(){return B(unCStr("AndObs"));}),_1bc=new T(function(){return B(unCStr("OrObs"));}),_1bd=new T(function(){return B(unCStr("NotObs"));}),_1be=function(_1bf,_1bg){var _1bh=new T(function(){var _1bi=E(_1bf),_1bj=new T(function(){var _1bk=new T(function(){var _1bl=new T(function(){var _1bm=new T(function(){var _1bn=new T(function(){var _1bo=new T(function(){if(_1bi>10){return new T0(2);}else{var _1bp=new T(function(){var _1bq=new T(function(){var _1br=function(_1bs){return new F(function(){return A3(_xH,_1a6,_ze,function(_1bt){return new F(function(){return A1(_1bg,new T2(6,_1bs,_1bt));});});});};return B(A3(_xH,_1a6,_ze,_1br));});return B(_wQ(function(_1bu){var _1bv=E(_1bu);return (_1bv._==3)?(!B(_lT(_1bv.a,_1b7)))?new T0(2):E(_1bq):new T0(2);}));}),_1bw=function(_1bx){return E(_1bp);};return new T1(1,function(_1by){return new F(function(){return A2(_vx,_1by,_1bw);});});}});if(_1bi>10){return B(_lf(_jU,_1bo));}else{var _1bz=new T(function(){var _1bA=new T(function(){var _1bB=function(_1bC){return new F(function(){return A3(_xS,_yl,_ze,function(_1bD){return new F(function(){return A1(_1bg,new T2(5,_1bC,_1bD));});});});};return B(A3(_xH,_zr,_ze,_1bB));});return B(_wQ(function(_1bE){var _1bF=E(_1bE);return (_1bF._==3)?(!B(_lT(_1bF.a,_1b8)))?new T0(2):E(_1bA):new T0(2);}));}),_1bG=function(_1bH){return E(_1bz);};return B(_lf(new T1(1,function(_1bI){return new F(function(){return A2(_vx,_1bI,_1bG);});}),_1bo));}});if(_1bi>10){return B(_lf(_jU,_1bn));}else{var _1bJ=new T(function(){var _1bK=new T(function(){var _1bL=function(_1bM){var _1bN=function(_1bO){return new F(function(){return A3(_xS,_yl,_ze,function(_1bP){return new F(function(){return A1(_1bg,new T3(4,_1bM,_1bO,_1bP));});});});};return new F(function(){return A3(_xS,_yl,_ze,_1bN);});};return B(A3(_xH,_zr,_ze,_1bL));});return B(_wQ(function(_1bQ){var _1bR=E(_1bQ);return (_1bR._==3)?(!B(_lT(_1bR.a,_1b9)))?new T0(2):E(_1bK):new T0(2);}));}),_1bS=function(_1bT){return E(_1bJ);};return B(_lf(new T1(1,function(_1bU){return new F(function(){return A2(_vx,_1bU,_1bS);});}),_1bn));}});if(_1bi>10){return B(_lf(_jU,_1bm));}else{var _1bV=new T(function(){var _1bW=new T(function(){return B(A3(_xH,_1be,_ze,function(_1bX){return new F(function(){return A1(_1bg,new T1(3,_1bX));});}));});return B(_wQ(function(_1bY){var _1bZ=E(_1bY);return (_1bZ._==3)?(!B(_lT(_1bZ.a,_1bd)))?new T0(2):E(_1bW):new T0(2);}));}),_1c0=function(_1c1){return E(_1bV);};return B(_lf(new T1(1,function(_1c2){return new F(function(){return A2(_vx,_1c2,_1c0);});}),_1bm));}});if(_1bi>10){return B(_lf(_jU,_1bl));}else{var _1c3=new T(function(){var _1c4=new T(function(){var _1c5=function(_1c6){return new F(function(){return A3(_xH,_1be,_ze,function(_1c7){return new F(function(){return A1(_1bg,new T2(2,_1c6,_1c7));});});});};return B(A3(_xH,_1be,_ze,_1c5));});return B(_wQ(function(_1c8){var _1c9=E(_1c8);return (_1c9._==3)?(!B(_lT(_1c9.a,_1bc)))?new T0(2):E(_1c4):new T0(2);}));}),_1ca=function(_1cb){return E(_1c3);};return B(_lf(new T1(1,function(_1cc){return new F(function(){return A2(_vx,_1cc,_1ca);});}),_1bl));}});if(_1bi>10){return B(_lf(_jU,_1bk));}else{var _1cd=new T(function(){var _1ce=new T(function(){var _1cf=function(_1cg){return new F(function(){return A3(_xH,_1be,_ze,function(_1ch){return new F(function(){return A1(_1bg,new T2(1,_1cg,_1ch));});});});};return B(A3(_xH,_1be,_ze,_1cf));});return B(_wQ(function(_1ci){var _1cj=E(_1ci);return (_1cj._==3)?(!B(_lT(_1cj.a,_1bb)))?new T0(2):E(_1ce):new T0(2);}));}),_1ck=function(_1cl){return E(_1cd);};return B(_lf(new T1(1,function(_1cm){return new F(function(){return A2(_vx,_1cm,_1ck);});}),_1bk));}});if(_1bi>10){return B(_lf(_jU,_1bj));}else{var _1cn=new T(function(){var _1co=new T(function(){return B(A3(_xS,_yl,_ze,function(_1cp){return new F(function(){return A1(_1bg,new T1(0,_1cp));});}));});return B(_wQ(function(_1cq){var _1cr=E(_1cq);return (_1cr._==3)?(!B(_lT(_1cr.a,_1ba)))?new T0(2):E(_1co):new T0(2);}));}),_1cs=function(_1ct){return E(_1cn);};return B(_lf(new T1(1,function(_1cu){return new F(function(){return A2(_vx,_1cu,_1cs);});}),_1bj));}});return new F(function(){return _lf(B(_1aT(_1aS,_1bf,_1bg)),_1bh);});},_1cv=new T(function(){return B(unCStr("Null"));}),_1cw=new T(function(){return B(unCStr("CommitCash"));}),_1cx=new T(function(){return B(unCStr("RedeemCC"));}),_1cy=new T(function(){return B(unCStr("Pay"));}),_1cz=new T(function(){return B(unCStr("Both"));}),_1cA=new T(function(){return B(unCStr("Choice"));}),_1cB=new T(function(){return B(unCStr("When"));}),_1cC=function(_1cD,_1cE){var _1cF=new T(function(){var _1cG=new T(function(){return B(A1(_1cE,_Rm));});return B(_wQ(function(_1cH){var _1cI=E(_1cH);return (_1cI._==3)?(!B(_lT(_1cI.a,_1cv)))?new T0(2):E(_1cG):new T0(2);}));}),_1cJ=function(_1cK){return E(_1cF);},_1cL=new T(function(){var _1cM=E(_1cD),_1cN=new T(function(){var _1cO=new T(function(){var _1cP=new T(function(){var _1cQ=new T(function(){var _1cR=new T(function(){if(_1cM>10){return new T0(2);}else{var _1cS=new T(function(){var _1cT=new T(function(){var _1cU=function(_1cV){var _1cW=function(_1cX){var _1cY=function(_1cZ){return new F(function(){return A3(_xH,_1cC,_ze,function(_1d0){return new F(function(){return A1(_1cE,new T4(6,_1cV,_1cX,_1cZ,_1d0));});});});};return new F(function(){return A3(_xH,_1cC,_ze,_1cY);});};return new F(function(){return A3(_xS,_yl,_ze,_1cW);});};return B(A3(_xH,_1be,_ze,_1cU));});return B(_wQ(function(_1d1){var _1d2=E(_1d1);return (_1d2._==3)?(!B(_lT(_1d2.a,_1cB)))?new T0(2):E(_1cT):new T0(2);}));}),_1d3=function(_1d4){return E(_1cS);};return new T1(1,function(_1d5){return new F(function(){return A2(_vx,_1d5,_1d3);});});}});if(_1cM>10){return B(_lf(_jU,_1cR));}else{var _1d6=new T(function(){var _1d7=new T(function(){var _1d8=function(_1d9){var _1da=function(_1db){return new F(function(){return A3(_xH,_1cC,_ze,function(_1dc){return new F(function(){return A1(_1cE,new T3(5,_1d9,_1db,_1dc));});});});};return new F(function(){return A3(_xH,_1cC,_ze,_1da);});};return B(A3(_xH,_1be,_ze,_1d8));});return B(_wQ(function(_1dd){var _1de=E(_1dd);return (_1de._==3)?(!B(_lT(_1de.a,_1cA)))?new T0(2):E(_1d7):new T0(2);}));}),_1df=function(_1dg){return E(_1d6);};return B(_lf(new T1(1,function(_1dh){return new F(function(){return A2(_vx,_1dh,_1df);});}),_1cR));}});if(_1cM>10){return B(_lf(_jU,_1cQ));}else{var _1di=new T(function(){var _1dj=new T(function(){var _1dk=function(_1dl){return new F(function(){return A3(_xH,_1cC,_ze,function(_1dm){return new F(function(){return A1(_1cE,new T2(4,_1dl,_1dm));});});});};return B(A3(_xH,_1cC,_ze,_1dk));});return B(_wQ(function(_1dn){var _1do=E(_1dn);return (_1do._==3)?(!B(_lT(_1do.a,_1cz)))?new T0(2):E(_1dj):new T0(2);}));}),_1dp=function(_1dq){return E(_1di);};return B(_lf(new T1(1,function(_1dr){return new F(function(){return A2(_vx,_1dr,_1dp);});}),_1cQ));}});if(_1cM>10){return B(_lf(_jU,_1cP));}else{var _1ds=new T(function(){var _1dt=new T(function(){var _1du=function(_1dv){var _1dw=function(_1dx){var _1dy=function(_1dz){var _1dA=function(_1dB){var _1dC=function(_1dD){return new F(function(){return A3(_xH,_1cC,_ze,function(_1dE){return new F(function(){return A1(_1cE,new T6(3,_1dv,_1dx,_1dz,_1dB,_1dD,_1dE));});});});};return new F(function(){return A3(_xS,_yl,_ze,_1dC);});};return new F(function(){return A3(_xH,_1a6,_ze,_1dA);});};return new F(function(){return A3(_xS,_yl,_ze,_1dy);});};return new F(function(){return A3(_xS,_yl,_ze,_1dw);});};return B(A3(_xH,_AS,_ze,_1du));});return B(_wQ(function(_1dF){var _1dG=E(_1dF);return (_1dG._==3)?(!B(_lT(_1dG.a,_1cy)))?new T0(2):E(_1dt):new T0(2);}));}),_1dH=function(_1dI){return E(_1ds);};return B(_lf(new T1(1,function(_1dJ){return new F(function(){return A2(_vx,_1dJ,_1dH);});}),_1cP));}});if(_1cM>10){return B(_lf(_jU,_1cO));}else{var _1dK=new T(function(){var _1dL=new T(function(){var _1dM=function(_1dN){return new F(function(){return A3(_xH,_1cC,_ze,function(_1dO){return new F(function(){return A1(_1cE,new T2(2,_1dN,_1dO));});});});};return B(A3(_xH,_BM,_ze,_1dM));});return B(_wQ(function(_1dP){var _1dQ=E(_1dP);return (_1dQ._==3)?(!B(_lT(_1dQ.a,_1cx)))?new T0(2):E(_1dL):new T0(2);}));}),_1dR=function(_1dS){return E(_1dK);};return B(_lf(new T1(1,function(_1dT){return new F(function(){return A2(_vx,_1dT,_1dR);});}),_1cO));}});if(_1cM>10){return B(_lf(_jU,_1cN));}else{var _1dU=new T(function(){var _1dV=new T(function(){var _1dW=function(_1dX){var _1dY=function(_1dZ){var _1e0=function(_1e1){var _1e2=function(_1e3){var _1e4=function(_1e5){var _1e6=function(_1e7){return new F(function(){return A3(_xH,_1cC,_ze,function(_1e8){return new F(function(){return A1(_1cE,{_:1,a:_1dX,b:_1dZ,c:_1e1,d:_1e3,e:_1e5,f:_1e7,g:_1e8});});});});};return new F(function(){return A3(_xH,_1cC,_ze,_1e6);});};return new F(function(){return A3(_xS,_yl,_ze,_1e4);});};return new F(function(){return A3(_xS,_yl,_ze,_1e2);});};return new F(function(){return A3(_xH,_1a6,_ze,_1e0);});};return new F(function(){return A3(_xS,_yl,_ze,_1dY);});};return B(A3(_xH,_BM,_ze,_1dW));});return B(_wQ(function(_1e9){var _1ea=E(_1e9);return (_1ea._==3)?(!B(_lT(_1ea.a,_1cw)))?new T0(2):E(_1dV):new T0(2);}));}),_1eb=function(_1ec){return E(_1dU);};return B(_lf(new T1(1,function(_1ed){return new F(function(){return A2(_vx,_1ed,_1eb);});}),_1cN));}});return new F(function(){return _lf(new T1(1,function(_1ee){return new F(function(){return A2(_vx,_1ee,_1cJ);});}),_1cL);});},_1ef=new T(function(){return B(A3(_xH,_1cC,_xn,_DB));}),_1eg=function(_1eh,_){var _1ei=__app0(E(_18j)),_1ej=eval(E(_18i)),_1ek=__app1(E(_1ej),toJSStr(E(_18l))),_1el=__app1(E(_1ej),toJSStr(E(_18k))),_1em=__app1(E(_18m),toJSStr(_19G)),_1en=new T(function(){var _1eo=B(_19H(B(_l5(_19E,new T(function(){var _1ep=String(_1el);return fromJSStr(_1ep);})))));if(!_1eo._){return E(_18r);}else{if(!E(_1eo.b)._){var _1eq=E(_1eo.a);return new T2(0,new T(function(){return B(_EV(_1eq.a));}),new T(function(){return B(_5s(_1eq.b));}));}else{return E(_18q);}}}),_1er=new T(function(){var _1es=B(_19H(B(_l5(_1ef,new T(function(){var _1et=String(_1ei);return fromJSStr(_1et);})))));if(!_1es._){return E(_19P);}else{if(!E(_1es.b)._){return E(_1es.a);}else{return E(_19O);}}}),_1eu=new T(function(){var _1ev=B(_19H(B(_l5(_18p,new T(function(){var _1ew=String(_1ek);return fromJSStr(_1ew);})))));if(!_1ev._){return E(_18o);}else{if(!E(_1ev.b)._){return E(_1ev.a);}else{return E(_18n);}}}),_1ex=B(_187(new T2(0,_19F,_1eu),_1eh,_1er,_1en));return new F(function(){return _GL(_1ex.a,_1ex.b,_1ex.c,_1ex.d,_);});},_1ey=new T(function(){return B(unCStr("contractInput"));}),_1ez="(function (t, s) {document.getElementById(t).value = s})",_1eA=function(_1eB,_1eC,_){var _1eD=eval(E(_1ez)),_1eE=__app2(E(_1eD),toJSStr(E(_1eB)),toJSStr(E(_1eC)));return new F(function(){return _F8(_);});},_1eF=function(_1eG,_1eH,_1eI,_){var _1eJ=E(_1ey),_1eK=toJSStr(_1eJ),_1eL=eval(E(_18i)),_1eM=__app1(E(_1eL),_1eK),_1eN=B(_19H(B(_l5(_DG,new T(function(){var _1eO=String(_1eM);return fromJSStr(_1eO);})))));if(!_1eN._){return E(_jT);}else{if(!E(_1eN.b)._){var _1eP=E(_1eN.a),_1eQ=B(_jD(new T(function(){return B(_gR(_1eP.a));},1),new T(function(){return B(_c2(_1eP.b));},1),new T(function(){return B(_dH(_1eI,_1eG,_1eH,B(_fb(_1eP.c))));},1),new T(function(){return B(_5s(_1eP.d));},1))),_1eR=B(_1eA(_1eJ,new T2(1,_1eQ.a,_1eQ.b),_)),_1eS=__app1(E(_1eL),_1eK),_1eT=new T(function(){var _1eU=B(_19H(B(_l5(_DG,new T(function(){var _1eV=String(_1eS);return fromJSStr(_1eV);})))));if(!_1eU._){return E(_jT);}else{if(!E(_1eU.b)._){var _1eW=E(_1eU.a);return new T4(0,new T(function(){return B(_gR(_1eW.a));}),new T(function(){return B(_c2(_1eW.b));}),new T(function(){return B(_fb(_1eW.c));}),new T(function(){return B(_5s(_1eW.d));}));}else{return E(_jR);}}});return new F(function(){return _1eg(_1eT,_);});}else{return E(_jR);}}},_1eX=function(_1eY,_1eZ,_1f0,_1f1,_1f2){var _1f3=E(_1f2);if(!_1f3._){var _1f4=_1f3.c,_1f5=_1f3.d,_1f6=E(_1f3.b),_1f7=E(_1f6.a);if(_1eY>=_1f7){if(_1eY!=_1f7){return new F(function(){return _5N(_1f6,_1f4,B(_1eX(_1eY,_,_1f0,_1f1,_1f5)));});}else{var _1f8=E(_1f6.b);if(_1f0>=_1f8){if(_1f0!=_1f8){return new F(function(){return _5N(_1f6,_1f4,B(_1eX(_1eY,_,_1f0,_1f1,_1f5)));});}else{var _1f9=E(_1f6.c);if(_1f1>=_1f9){if(_1f1!=_1f9){return new F(function(){return _5N(_1f6,_1f4,B(_1eX(_1eY,_,_1f0,_1f1,_1f5)));});}else{return new T4(0,_1f3.a,E(new T3(0,_1eY,_1f0,_1f1)),E(_1f4),E(_1f5));}}else{return new F(function(){return _6x(_1f6,B(_1eX(_1eY,_,_1f0,_1f1,_1f4)),_1f5);});}}}else{return new F(function(){return _6x(_1f6,B(_1eX(_1eY,_,_1f0,_1f1,_1f4)),_1f5);});}}}else{return new F(function(){return _6x(_1f6,B(_1eX(_1eY,_,_1f0,_1f1,_1f4)),_1f5);});}}else{return new T4(0,1,E(new T3(0,_1eY,_1f0,_1f1)),E(_5I),E(_5I));}},_1fa=function(_1fb,_1fc,_1fd,_1fe,_1ff){var _1fg=E(_1ff);if(!_1fg._){var _1fh=_1fg.c,_1fi=_1fg.d,_1fj=E(_1fg.b),_1fk=E(_1fj.a);if(_1fb>=_1fk){if(_1fb!=_1fk){return new F(function(){return _5N(_1fj,_1fh,B(_1fa(_1fb,_,_1fd,_1fe,_1fi)));});}else{var _1fl=E(_1fj.b);if(_1fd>=_1fl){if(_1fd!=_1fl){return new F(function(){return _5N(_1fj,_1fh,B(_1fa(_1fb,_,_1fd,_1fe,_1fi)));});}else{var _1fm=E(_1fe),_1fn=E(_1fj.c);if(_1fm>=_1fn){if(_1fm!=_1fn){return new F(function(){return _5N(_1fj,_1fh,B(_1eX(_1fb,_,_1fd,_1fm,_1fi)));});}else{return new T4(0,_1fg.a,E(new T3(0,_1fb,_1fd,_1fm)),E(_1fh),E(_1fi));}}else{return new F(function(){return _6x(_1fj,B(_1eX(_1fb,_,_1fd,_1fm,_1fh)),_1fi);});}}}else{return new F(function(){return _6x(_1fj,B(_1fa(_1fb,_,_1fd,_1fe,_1fh)),_1fi);});}}}else{return new F(function(){return _6x(_1fj,B(_1fa(_1fb,_,_1fd,_1fe,_1fh)),_1fi);});}}else{return new T4(0,1,E(new T3(0,_1fb,_1fd,_1fe)),E(_5I),E(_5I));}},_1fo=function(_1fp,_1fq,_1fr,_1fs,_1ft){var _1fu=E(_1ft);if(!_1fu._){var _1fv=_1fu.c,_1fw=_1fu.d,_1fx=E(_1fu.b),_1fy=E(_1fx.a);if(_1fp>=_1fy){if(_1fp!=_1fy){return new F(function(){return _5N(_1fx,_1fv,B(_1fo(_1fp,_,_1fr,_1fs,_1fw)));});}else{var _1fz=E(_1fr),_1fA=E(_1fx.b);if(_1fz>=_1fA){if(_1fz!=_1fA){return new F(function(){return _5N(_1fx,_1fv,B(_1fa(_1fp,_,_1fz,_1fs,_1fw)));});}else{var _1fB=E(_1fs),_1fC=E(_1fx.c);if(_1fB>=_1fC){if(_1fB!=_1fC){return new F(function(){return _5N(_1fx,_1fv,B(_1eX(_1fp,_,_1fz,_1fB,_1fw)));});}else{return new T4(0,_1fu.a,E(new T3(0,_1fp,_1fz,_1fB)),E(_1fv),E(_1fw));}}else{return new F(function(){return _6x(_1fx,B(_1eX(_1fp,_,_1fz,_1fB,_1fv)),_1fw);});}}}else{return new F(function(){return _6x(_1fx,B(_1fa(_1fp,_,_1fz,_1fs,_1fv)),_1fw);});}}}else{return new F(function(){return _6x(_1fx,B(_1fo(_1fp,_,_1fr,_1fs,_1fv)),_1fw);});}}else{return new T4(0,1,E(new T3(0,_1fp,_1fr,_1fs)),E(_5I),E(_5I));}},_1fD=function(_1fE,_1fF,_1fG,_1fH){var _1fI=E(_1fH);if(!_1fI._){var _1fJ=_1fI.c,_1fK=_1fI.d,_1fL=E(_1fI.b),_1fM=E(_1fE),_1fN=E(_1fL.a);if(_1fM>=_1fN){if(_1fM!=_1fN){return new F(function(){return _5N(_1fL,_1fJ,B(_1fo(_1fM,_,_1fF,_1fG,_1fK)));});}else{var _1fO=E(_1fF),_1fP=E(_1fL.b);if(_1fO>=_1fP){if(_1fO!=_1fP){return new F(function(){return _5N(_1fL,_1fJ,B(_1fa(_1fM,_,_1fO,_1fG,_1fK)));});}else{var _1fQ=E(_1fG),_1fR=E(_1fL.c);if(_1fQ>=_1fR){if(_1fQ!=_1fR){return new F(function(){return _5N(_1fL,_1fJ,B(_1eX(_1fM,_,_1fO,_1fQ,_1fK)));});}else{return new T4(0,_1fI.a,E(new T3(0,_1fM,_1fO,_1fQ)),E(_1fJ),E(_1fK));}}else{return new F(function(){return _6x(_1fL,B(_1eX(_1fM,_,_1fO,_1fQ,_1fJ)),_1fK);});}}}else{return new F(function(){return _6x(_1fL,B(_1fa(_1fM,_,_1fO,_1fG,_1fJ)),_1fK);});}}}else{return new F(function(){return _6x(_1fL,B(_1fo(_1fM,_,_1fF,_1fG,_1fJ)),_1fK);});}}else{return new T4(0,1,E(new T3(0,_1fE,_1fF,_1fG)),E(_5I),E(_5I));}},_1fS=function(_1fT,_1fU,_1fV,_){var _1fW=E(_1ey),_1fX=toJSStr(_1fW),_1fY=eval(E(_18i)),_1fZ=__app1(E(_1fY),_1fX),_1g0=B(_19H(B(_l5(_DG,new T(function(){var _1g1=String(_1fZ);return fromJSStr(_1g1);})))));if(!_1g0._){return E(_jT);}else{if(!E(_1g0.b)._){var _1g2=E(_1g0.a),_1g3=B(_jD(new T(function(){return B(_gR(_1g2.a));},1),new T(function(){return B(_1fD(_1fV,_1fT,_1fU,B(_c2(_1g2.b))));},1),new T(function(){return B(_fb(_1g2.c));},1),new T(function(){return B(_5s(_1g2.d));},1))),_1g4=B(_1eA(_1fW,new T2(1,_1g3.a,_1g3.b),_)),_1g5=__app1(E(_1fY),_1fX),_1g6=new T(function(){var _1g7=B(_19H(B(_l5(_DG,new T(function(){var _1g8=String(_1g5);return fromJSStr(_1g8);})))));if(!_1g7._){return E(_jT);}else{if(!E(_1g7.b)._){var _1g9=E(_1g7.a);return new T4(0,new T(function(){return B(_gR(_1g9.a));}),new T(function(){return B(_c2(_1g9.b));}),new T(function(){return B(_fb(_1g9.c));}),new T(function(){return B(_5s(_1g9.d));}));}else{return E(_jR);}}});return new F(function(){return _1eg(_1g6,_);});}else{return E(_jR);}}},_1ga=function(_1gb,_1gc,_1gd,_1ge,_){var _1gf=E(_1ey),_1gg=toJSStr(_1gf),_1gh=eval(E(_18i)),_1gi=__app1(E(_1gh),_1gg),_1gj=B(_19H(B(_l5(_DG,new T(function(){var _1gk=String(_1gi);return fromJSStr(_1gk);})))));if(!_1gj._){return E(_jT);}else{if(!E(_1gj.b)._){var _1gl=E(_1gj.a),_1gm=B(_jD(new T(function(){return B(_fr(_1gd,_1gb,_1gc,_1ge,B(_gR(_1gl.a))));},1),new T(function(){return B(_c2(_1gl.b));},1),new T(function(){return B(_fb(_1gl.c));},1),new T(function(){return B(_5s(_1gl.d));},1))),_1gn=B(_1eA(_1gf,new T2(1,_1gm.a,_1gm.b),_)),_1go=__app1(E(_1gh),_1gg),_1gp=new T(function(){var _1gq=B(_19H(B(_l5(_DG,new T(function(){var _1gr=String(_1go);return fromJSStr(_1gr);})))));if(!_1gq._){return E(_jT);}else{if(!E(_1gq.b)._){var _1gs=E(_1gq.a);return new T4(0,new T(function(){return B(_gR(_1gs.a));}),new T(function(){return B(_c2(_1gs.b));}),new T(function(){return B(_fb(_1gs.c));}),new T(function(){return B(_5s(_1gs.d));}));}else{return E(_jR);}}});return new F(function(){return _1eg(_1gp,_);});}else{return E(_jR);}}},_1gt=new T(function(){return B(err(_jS));}),_1gu=new T(function(){return B(unCStr("SICC"));}),_1gv=new T(function(){return B(unCStr("SIRC"));}),_1gw=new T(function(){return B(unCStr("SIP"));}),_1gx=11,_1gy=function(_1gz,_1gA){var _1gB=new T(function(){var _1gC=new T(function(){if(_1gz>10){return new T0(2);}else{var _1gD=new T(function(){var _1gE=new T(function(){var _1gF=function(_1gG){var _1gH=function(_1gI){return new F(function(){return A3(_xS,_yl,_1gx,function(_1gJ){return new F(function(){return A1(_1gA,new T3(2,_1gG,_1gI,_1gJ));});});});};return new F(function(){return A3(_xS,_yl,_1gx,_1gH);});};return B(A3(_xH,_AS,_1gx,_1gF));});return B(_wQ(function(_1gK){var _1gL=E(_1gK);return (_1gL._==3)?(!B(_lT(_1gL.a,_1gw)))?new T0(2):E(_1gE):new T0(2);}));}),_1gM=function(_1gN){return E(_1gD);};return new T1(1,function(_1gO){return new F(function(){return A2(_vx,_1gO,_1gM);});});}});if(_1gz>10){return B(_lf(_jU,_1gC));}else{var _1gP=new T(function(){var _1gQ=new T(function(){var _1gR=function(_1gS){var _1gT=function(_1gU){return new F(function(){return A3(_xS,_yl,_1gx,function(_1gV){return new F(function(){return A1(_1gA,new T3(1,_1gS,_1gU,_1gV));});});});};return new F(function(){return A3(_xS,_yl,_1gx,_1gT);});};return B(A3(_xH,_BM,_1gx,_1gR));});return B(_wQ(function(_1gW){var _1gX=E(_1gW);return (_1gX._==3)?(!B(_lT(_1gX.a,_1gv)))?new T0(2):E(_1gQ):new T0(2);}));}),_1gY=function(_1gZ){return E(_1gP);};return B(_lf(new T1(1,function(_1h0){return new F(function(){return A2(_vx,_1h0,_1gY);});}),_1gC));}});if(_1gz>10){return new F(function(){return _lf(_jU,_1gB);});}else{var _1h1=new T(function(){var _1h2=new T(function(){var _1h3=function(_1h4){var _1h5=function(_1h6){var _1h7=function(_1h8){return new F(function(){return A3(_xS,_yl,_1gx,function(_1h9){return new F(function(){return A1(_1gA,new T4(0,_1h4,_1h6,_1h8,_1h9));});});});};return new F(function(){return A3(_xS,_yl,_1gx,_1h7);});};return new F(function(){return A3(_xS,_yl,_1gx,_1h5);});};return B(A3(_xH,_BM,_1gx,_1h3));});return B(_wQ(function(_1ha){var _1hb=E(_1ha);return (_1hb._==3)?(!B(_lT(_1hb.a,_1gu)))?new T0(2):E(_1h2):new T0(2);}));}),_1hc=function(_1hd){return E(_1h1);};return new F(function(){return _lf(new T1(1,function(_1he){return new F(function(){return A2(_vx,_1he,_1hc);});}),_1gB);});}},_1hf=function(_1hg,_1hh){return new F(function(){return _1gy(E(_1hg),_1hh);});},_1hi=new T(function(){return B(A3(_xH,_1hf,_xn,_DB));}),_1hj=function(_1hk,_){var _1hl=B(_19H(B(_l5(_1hi,_1hk))));if(!_1hl._){return E(_1gt);}else{if(!E(_1hl.b)._){var _1hm=E(_1hl.a);switch(_1hm._){case 0:return new F(function(){return _1ga(_1hm.b,_1hm.c,_1hm.a,_1hm.d,_);});break;case 1:return new F(function(){return _1fS(_1hm.b,_1hm.c,_1hm.a,_);});break;default:return new F(function(){return _1eF(_1hm.b,_1hm.c,_1hm.a,_);});}}else{return E(_hb);}}},_1hn=function(_1ho,_1hp,_1hq,_){var _1hr=E(_1ey),_1hs=toJSStr(_1hr),_1ht=eval(E(_18i)),_1hu=__app1(E(_1ht),_1hs),_1hv=B(_19H(B(_l5(_DG,new T(function(){var _1hw=String(_1hu);return fromJSStr(_1hw);})))));if(!_1hv._){return E(_jT);}else{if(!E(_1hv.b)._){var _1hx=E(_1hv.a),_1hy=B(_jD(new T(function(){return B(_gR(_1hx.a));},1),new T(function(){return B(_c2(_1hx.b));},1),new T(function(){return B(_fb(_1hx.c));},1),new T(function(){return B(_3Y(_1hq,_1ho,_1hp,B(_5s(_1hx.d))));},1))),_1hz=B(_1eA(_1hr,new T2(1,_1hy.a,_1hy.b),_)),_1hA=__app1(E(_1ht),_1hs),_1hB=new T(function(){var _1hC=B(_19H(B(_l5(_DG,new T(function(){var _1hD=String(_1hA);return fromJSStr(_1hD);})))));if(!_1hC._){return E(_jT);}else{if(!E(_1hC.b)._){var _1hE=E(_1hC.a);return new T4(0,new T(function(){return B(_gR(_1hE.a));}),new T(function(){return B(_c2(_1hE.b));}),new T(function(){return B(_fb(_1hE.c));}),new T(function(){return B(_5s(_1hE.d));}));}else{return E(_jR);}}});return new F(function(){return _1eg(_1hB,_);});}else{return E(_jR);}}},_1hF=new T(function(){return B(err(_ha));}),_1hG=new T(function(){return B(err(_jS));}),_1hH=new T(function(){return B(_A0(_zE,_zd,_DB));}),_1hI=function(_1hJ,_1hK,_){var _1hL=new T(function(){var _1hM=B(_19H(B(_l5(_1hH,_1hJ))));if(!_1hM._){return E(_1hG);}else{if(!E(_1hM.b)._){var _1hN=E(_1hM.a);return new T2(0,_1hN.a,_1hN.b);}else{return E(_1hF);}}});return new F(function(){return _1hn(new T(function(){return E(E(_1hL).b);}),_1hK,new T(function(){return E(E(_1hL).a);}),_);});},_1hO=new T(function(){return B(unCStr("When"));}),_1hP=new T(function(){return B(unCStr("Choice"));}),_1hQ=new T(function(){return B(unCStr("Both"));}),_1hR=new T(function(){return B(unCStr("Pay"));}),_1hS=new T(function(){return B(unCStr("RedeemCC"));}),_1hT=new T(function(){return B(unCStr("CommitCash"));}),_1hU=new T(function(){return B(unCStr("Null"));}),_1hV=32,_1hW=new T2(1,_1hV,_1),_1hX=function(_1hY){var _1hZ=E(_1hY);return (_1hZ==1)?E(_1hW):new T2(1,_1hV,new T(function(){return B(_1hX(_1hZ-1|0));}));},_1i0=new T(function(){return B(unCStr("head"));}),_1i1=new T(function(){return B(_io(_1i0));}),_1i2=function(_1i3){return new F(function(){return _hA(0,E(_1i3),_1);});},_1i4=new T(function(){return B(unCStr("IdentPay"));}),_1i5=new T(function(){return B(unCStr("ValueGE"));}),_1i6=new T(function(){return B(unCStr("PersonChoseSomething"));}),_1i7=new T(function(){return B(unCStr("PersonChoseThis"));}),_1i8=new T(function(){return B(unCStr("NotObs"));}),_1i9=new T(function(){return B(unCStr("OrObs"));}),_1ia=new T(function(){return B(unCStr("AndObs"));}),_1ib=new T(function(){return B(unCStr("BelowTimeout"));}),_1ic=new T(function(){return B(unCStr("IdentChoice"));}),_1id=new T(function(){return B(unCStr("IdentCC"));}),_1ie=new T(function(){return B(unCStr("MoneyFromChoice"));}),_1if=new T(function(){return B(unCStr("ConstMoney"));}),_1ig=new T(function(){return B(unCStr("AddMoney"));}),_1ih=new T(function(){return B(unCStr("AvailableMoney"));}),_1ii=new T(function(){return B(unCStr("FalseObs"));}),_1ij=new T(function(){return B(unCStr("TrueObs"));}),_1ik=function(_1il){var _1im=E(_1il);switch(_1im._){case 0:var _1in=E(_1im.a);switch(_1in._){case 0:return new T2(0,_1hU,_1);case 1:return new T2(0,_1hT,new T2(1,new T1(3,_1in.a),new T2(1,new T1(6,_1in.b),new T2(1,new T1(2,_1in.c),new T2(1,new T1(6,_1in.d),new T2(1,new T1(6,_1in.e),new T2(1,new T1(0,_1in.f),new T2(1,new T1(0,_1in.g),_1))))))));case 2:return new T2(0,_1hS,new T2(1,new T1(3,_1in.a),new T2(1,new T1(0,_1in.b),_1)));case 3:return new T2(0,_1hR,new T2(1,new T1(5,_1in.a),new T2(1,new T1(6,_1in.b),new T2(1,new T1(6,_1in.c),new T2(1,new T1(2,_1in.d),new T2(1,new T1(6,_1in.e),new T2(1,new T1(0,_1in.f),_1)))))));case 4:return new T2(0,_1hQ,new T2(1,new T1(0,_1in.a),new T2(1,new T1(0,_1in.b),_1)));case 5:return new T2(0,_1hP,new T2(1,new T1(1,_1in.a),new T2(1,new T1(0,_1in.b),new T2(1,new T1(0,_1in.c),_1))));default:return new T2(0,_1hO,new T2(1,new T1(1,_1in.a),new T2(1,new T1(6,_1in.b),new T2(1,new T1(0,_1in.c),new T2(1,new T1(0,_1in.d),_1)))));}break;case 1:var _1io=E(_1im.a);switch(_1io._){case 0:return new T2(0,_1ib,new T2(1,new T1(6,_1io.a),_1));case 1:return new T2(0,_1ia,new T2(1,new T1(1,_1io.a),new T2(1,new T1(1,_1io.b),_1)));case 2:return new T2(0,_1i9,new T2(1,new T1(1,_1io.a),new T2(1,new T1(1,_1io.b),_1)));case 3:return new T2(0,_1i8,new T2(1,new T1(1,_1io.a),_1));case 4:return new T2(0,_1i7,new T2(1,new T1(4,_1io.a),new T2(1,new T1(6,_1io.b),new T2(1,new T1(6,_1io.c),_1))));case 5:return new T2(0,_1i6,new T2(1,new T1(4,_1io.a),new T2(1,new T1(6,_1io.b),_1)));case 6:return new T2(0,_1i5,new T2(1,new T1(2,_1io.a),new T2(1,new T1(2,_1io.b),_1)));case 7:return new T2(0,_1ij,_1);default:return new T2(0,_1ii,_1);}break;case 2:var _1ip=E(_1im.a);switch(_1ip._){case 0:return new T2(0,_1ih,new T2(1,new T1(3,_1ip.a),_1));case 1:return new T2(0,_1ig,new T2(1,new T1(2,_1ip.a),new T2(1,new T1(2,_1ip.b),_1)));case 2:return new T2(0,_1if,new T2(1,new T1(6,_1ip.a),_1));default:return new T2(0,_1ie,new T2(1,new T1(4,_1ip.a),new T2(1,new T1(6,_1ip.b),new T2(1,new T1(2,_1ip.c),_1))));}break;case 3:return new T2(0,_1id,new T2(1,new T1(6,_1im.a),_1));case 4:return new T2(0,_1ic,new T2(1,new T1(6,_1im.a),_1));case 5:return new T2(0,_1i4,new T2(1,new T1(6,_1im.a),_1));default:return new T2(0,new T(function(){return B(_1i2(_1im.a));}),_1);}},_1iq=function(_1ir){var _1is=B(_1ik(_1ir)),_1it=_1is.a,_1iu=E(_1is.b);if(!_1iu._){return new T1(0,new T2(0,_1it,_1));}else{switch(E(_1ir)._){case 0:return new T1(2,new T2(0,_1it,_1iu));case 1:return new T1(2,new T2(0,_1it,_1iu));case 2:return new T1(2,new T2(0,_1it,_1iu));default:return new T1(1,new T2(0,_1it,_1iu));}}},_1iv=function(_1iw,_1ix){var _1iy=E(_1ix);if(!_1iy._){return __Z;}else{var _1iz=_1iy.a,_1iA=new T(function(){var _1iB=B(_kG(new T(function(){return B(A1(_1iw,_1iz));}),_1iy.b));return new T2(0,_1iB.a,_1iB.b);});return new T2(1,new T2(1,_1iz,new T(function(){return E(E(_1iA).a);})),new T(function(){return B(_1iv(_1iw,E(_1iA).b));}));}},_1iC=function(_1iD){var _1iE=E(_1iD);if(!_1iE._){return __Z;}else{return new F(function(){return _hq(_1iE.a,new T(function(){return B(_1iC(_1iE.b));},1));});}},_1iF=function(_1iG,_1iH){return (E(_1iG)._==2)?false:(E(_1iH)._==2)?false:true;},_1iI=function(_1iJ,_1iK){var _1iL=E(_1iK);return (_1iL._==0)?__Z:new T2(1,_1iJ,new T2(1,_1iL.a,new T(function(){return B(_1iI(_1iJ,_1iL.b));})));},_1iM=new T(function(){return B(unCStr("\n"));}),_1iN=new T(function(){return B(unCStr("tail"));}),_1iO=new T(function(){return B(_io(_1iN));}),_1iP=function(_1iQ,_1iR,_1iS){var _1iT=E(_1iS);if(!_1iT._){return E(_1iR);}else{var _1iU=new T(function(){return (E(_1iQ)+B(_oy(_1iR,0))|0)+1|0;}),_1iV=new T(function(){return B(_1iv(_1iF,B(_oD(_1iq,_1iT))));}),_1iW=new T(function(){var _1iX=E(_1iV);if(!_1iX._){return E(_1iO);}else{var _1iY=new T(function(){var _1iZ=E(_1iU);if(0>=_1iZ){return __Z;}else{return B(_1hX(_1iZ));}}),_1j0=function(_1j1){var _1j2=new T(function(){var _1j3=function(_1j4){var _1j5=E(_1j4);if(!_1j5._){return __Z;}else{var _1j6=new T(function(){return B(_hq(B(_1j7(_1iU,_1j5.a)),new T(function(){return B(_1j3(_1j5.b));},1)));});return new T2(1,_1hV,_1j6);}},_1j8=B(_1j3(_1j1));if(!_1j8._){return __Z;}else{return E(_1j8.b);}},1);return new F(function(){return _hq(_1iY,_1j2);});};return B(_1iI(_1iM,B(_oD(_1j0,_1iX.b))));}}),_1j9=new T(function(){var _1ja=new T(function(){var _1jb=E(_1iV);if(!_1jb._){return E(_1i1);}else{var _1jc=function(_1jd){var _1je=E(_1jd);if(!_1je._){return __Z;}else{var _1jf=new T(function(){return B(_hq(B(_1j7(_1iU,_1je.a)),new T(function(){return B(_1jc(_1je.b));},1)));});return new T2(1,_1hV,_1jf);}};return B(_1jc(_1jb.a));}},1);return B(_hq(_1iR,_1ja));});return new F(function(){return _1iC(new T2(1,_1j9,_1iW));});}},_1jg=new T(function(){return B(unCStr(")"));}),_1j7=function(_1jh,_1ji){var _1jj=E(_1ji);switch(_1jj._){case 0:var _1jk=E(_1jj.a);return new F(function(){return _1jl(0,_1jk.a,_1jk.b);});break;case 1:return new F(function(){return unAppCStr("(",new T(function(){var _1jm=E(_1jj.a);return B(_hq(B(_1jl(0,_1jm.a,_1jm.b)),_1jg));}));});break;default:var _1jn=new T(function(){var _1jo=E(_1jj.a);return B(_hq(B(_1iP(new T(function(){return E(_1jh)+1|0;},1),_1jo.a,_1jo.b)),_1jg));});return new F(function(){return unAppCStr("(",_1jn);});}},_1jl=function(_1jp,_1jq,_1jr){var _1js=E(_1jr);if(!_1js._){return E(_1jq);}else{var _1jt=new T(function(){return (_1jp+B(_oy(_1jq,0))|0)+1|0;}),_1ju=new T(function(){return B(_1iv(_1iF,B(_oD(_1iq,_1js))));}),_1jv=new T(function(){var _1jw=E(_1ju);if(!_1jw._){return E(_1iO);}else{var _1jx=new T(function(){var _1jy=E(_1jt);if(0>=_1jy){return __Z;}else{return B(_1hX(_1jy));}}),_1jz=function(_1jA){var _1jB=new T(function(){var _1jC=function(_1jD){var _1jE=E(_1jD);if(!_1jE._){return __Z;}else{var _1jF=new T(function(){return B(_hq(B(_1j7(_1jt,_1jE.a)),new T(function(){return B(_1jC(_1jE.b));},1)));});return new T2(1,_1hV,_1jF);}},_1jG=B(_1jC(_1jA));if(!_1jG._){return __Z;}else{return E(_1jG.b);}},1);return new F(function(){return _hq(_1jx,_1jB);});};return B(_1iI(_1iM,B(_oD(_1jz,_1jw.b))));}}),_1jH=new T(function(){var _1jI=new T(function(){var _1jJ=E(_1ju);if(!_1jJ._){return E(_1i1);}else{var _1jK=function(_1jL){var _1jM=E(_1jL);if(!_1jM._){return __Z;}else{var _1jN=new T(function(){return B(_hq(B(_1j7(_1jt,_1jM.a)),new T(function(){return B(_1jK(_1jM.b));},1)));});return new T2(1,_1hV,_1jN);}};return B(_1jK(_1jJ.a));}},1);return B(_hq(_1jq,_1jI));});return new F(function(){return _1iC(new T2(1,_1jH,_1jv));});}},_1jO=new T(function(){return B(_1jl(0,_1hU,_1));}),_1jP=function(_1jQ,_){return new T(function(){var _1jR=B(_19H(B(_l5(_1ef,_1jQ))));if(!_1jR._){return E(_19P);}else{if(!E(_1jR.b)._){var _1jS=E(_1jR.a);switch(_1jS._){case 0:return E(_1jO);break;case 1:return B(_1jl(0,_1hT,new T2(1,new T1(3,_1jS.a),new T2(1,new T1(6,_1jS.b),new T2(1,new T1(2,_1jS.c),new T2(1,new T1(6,_1jS.d),new T2(1,new T1(6,_1jS.e),new T2(1,new T1(0,_1jS.f),new T2(1,new T1(0,_1jS.g),_1)))))))));break;case 2:return B(_1jl(0,_1hS,new T2(1,new T1(3,_1jS.a),new T2(1,new T1(0,_1jS.b),_1))));break;case 3:return B(_1jl(0,_1hR,new T2(1,new T1(5,_1jS.a),new T2(1,new T1(6,_1jS.b),new T2(1,new T1(6,_1jS.c),new T2(1,new T1(2,_1jS.d),new T2(1,new T1(6,_1jS.e),new T2(1,new T1(0,_1jS.f),_1))))))));break;case 4:return B(_1jl(0,_1hQ,new T2(1,new T1(0,_1jS.a),new T2(1,new T1(0,_1jS.b),_1))));break;case 5:return B(_1jl(0,_1hP,new T2(1,new T1(1,_1jS.a),new T2(1,new T1(0,_1jS.b),new T2(1,new T1(0,_1jS.c),_1)))));break;default:return B(_1jl(0,_1hO,new T2(1,new T1(1,_1jS.a),new T2(1,new T1(6,_1jS.b),new T2(1,new T1(0,_1jS.c),new T2(1,new T1(0,_1jS.d),_1))))));}}else{return E(_19O);}}});},_1jT=new T(function(){return B(unCStr("codeArea"));}),_1jU=function(_){var _1jV=__app0(E(_18j)),_1jW=B(_1jP(new T(function(){var _1jX=String(_1jV);return fromJSStr(_1jX);}),_)),_1jY=B(_1eA(_1jT,_1jW,_)),_1jZ=eval(E(_18i)),_1k0=__app1(E(_1jZ),toJSStr(E(_1ey))),_1k1=new T(function(){var _1k2=B(_19H(B(_l5(_DG,new T(function(){var _1k3=String(_1k0);return fromJSStr(_1k3);})))));if(!_1k2._){return E(_jT);}else{if(!E(_1k2.b)._){var _1k4=E(_1k2.a);return new T4(0,new T(function(){return B(_gR(_1k4.a));}),new T(function(){return B(_c2(_1k4.b));}),new T(function(){return B(_fb(_1k4.c));}),new T(function(){return B(_5s(_1k4.d));}));}else{return E(_jR);}}});return new F(function(){return _1eg(_1k1,_);});},_1k5="(function (b) { return (b.inputList.length); })",_1k6="(function (b, x) { return (b.inputList[x]); })",_1k7=function(_1k8,_1k9,_){var _1ka=eval(E(_1k6)),_1kb=__app2(E(_1ka),_1k8,_1k9);return new T1(0,_1kb);},_1kc=function(_1kd,_1ke,_1kf,_){var _1kg=E(_1kf);if(!_1kg._){return _1;}else{var _1kh=B(_1k7(_1kd,E(_1kg.a),_)),_1ki=B(_1kc(_1kd,_,_1kg.b,_));return new T2(1,_1kh,_1ki);}},_1kj=function(_1kk,_1kl){if(_1kk<=_1kl){var _1km=function(_1kn){return new T2(1,_1kn,new T(function(){if(_1kn!=_1kl){return B(_1km(_1kn+1|0));}else{return __Z;}}));};return new F(function(){return _1km(_1kk);});}else{return __Z;}},_1ko=function(_1kp,_){var _1kq=eval(E(_1k5)),_1kr=__app1(E(_1kq),_1kp),_1ks=Number(_1kr),_1kt=jsTrunc(_1ks);return new F(function(){return _1kc(_1kp,_,new T(function(){return B(_1kj(0,_1kt-1|0));}),_);});},_1ku="(function (y, ip) {y.previousConnection.connect(ip.connection);})",_1kv="(function (x) { return x.name; })",_1kw=new T(function(){return B(unCStr("\""));}),_1kx=function(_1ky){return new F(function(){return err(B(unAppCStr("No input matches \"",new T(function(){return B(_hq(_1ky,_1kw));}))));});},_1kz=function(_1kA,_1kB,_){var _1kC=E(_1kB);if(!_1kC._){return new F(function(){return _1kx(_1kA);});}else{var _1kD=E(_1kC.a),_1kE=E(_1kv),_1kF=eval(_1kE),_1kG=__app1(E(_1kF),E(_1kD.a)),_1kH=String(_1kG);if(!B(_lT(fromJSStr(_1kH),_1kA))){var _1kI=function(_1kJ,_1kK,_){while(1){var _1kL=E(_1kK);if(!_1kL._){return new F(function(){return _1kx(_1kJ);});}else{var _1kM=E(_1kL.a),_1kN=eval(_1kE),_1kO=__app1(E(_1kN),E(_1kM.a)),_1kP=String(_1kO);if(!B(_lT(fromJSStr(_1kP),_1kJ))){_1kK=_1kL.b;continue;}else{return _1kM;}}}};return new F(function(){return _1kI(_1kA,_1kC.b,_);});}else{return _1kD;}}},_1kQ=function(_1kR,_1kS,_1kT,_){var _1kU=B(_1ko(_1kS,_)),_1kV=B(_1kz(_1kR,_1kU,_)),_1kW=eval(E(_1ku)),_1kX=__app2(E(_1kW),E(E(_1kT).a),E(E(_1kV).a));return new F(function(){return _F8(_);});},_1kY="(function (y, ip) {y.outputConnection.connect(ip.connection);})",_1kZ=function(_1l0,_1l1,_1l2,_){var _1l3=B(_1ko(_1l1,_)),_1l4=B(_1kz(_1l0,_1l3,_)),_1l5=eval(E(_1kY)),_1l6=__app2(E(_1l5),E(E(_1l2).a),E(E(_1l4).a));return new F(function(){return _F8(_);});},_1l7=function(_1l8){return new F(function(){return err(B(unAppCStr("No fieldrow matches \"",new T(function(){return B(_hq(_1l8,_1kw));}))));});},_1l9=function(_1la,_1lb,_){var _1lc=E(_1lb);if(!_1lc._){return new F(function(){return _1l7(_1la);});}else{var _1ld=E(_1lc.a),_1le=E(_1kv),_1lf=eval(_1le),_1lg=__app1(E(_1lf),E(_1ld.a)),_1lh=String(_1lg);if(!B(_lT(fromJSStr(_1lh),_1la))){var _1li=function(_1lj,_1lk,_){while(1){var _1ll=E(_1lk);if(!_1ll._){return new F(function(){return _1l7(_1lj);});}else{var _1lm=E(_1ll.a),_1ln=eval(_1le),_1lo=__app1(E(_1ln),E(_1lm.a)),_1lp=String(_1lo);if(!B(_lT(fromJSStr(_1lp),_1lj))){_1lk=_1ll.b;continue;}else{return _1lm;}}}};return new F(function(){return _1li(_1la,_1lc.b,_);});}else{return _1ld;}}},_1lq="(function (b) { return (b.fieldRow.length); })",_1lr="(function (b, x) { return (b.fieldRow[x]); })",_1ls=function(_1lt,_1lu,_){var _1lv=eval(E(_1lr)),_1lw=__app2(E(_1lv),_1lt,_1lu);return new T1(0,_1lw);},_1lx=function(_1ly,_1lz,_1lA,_){var _1lB=E(_1lA);if(!_1lB._){return _1;}else{var _1lC=B(_1ls(_1ly,E(_1lB.a),_)),_1lD=B(_1lx(_1ly,_,_1lB.b,_));return new T2(1,_1lC,_1lD);}},_1lE=function(_1lF,_){var _1lG=eval(E(_1lq)),_1lH=__app1(E(_1lG),_1lF),_1lI=Number(_1lH),_1lJ=jsTrunc(_1lI);return new F(function(){return _1lx(_1lF,_,new T(function(){return B(_1kj(0,_1lJ-1|0));}),_);});},_1lK=function(_1lL,_){var _1lM=E(_1lL);if(!_1lM._){return _1;}else{var _1lN=B(_1lE(E(E(_1lM.a).a),_)),_1lO=B(_1lK(_1lM.b,_));return new T2(1,_1lN,_1lO);}},_1lP=function(_1lQ){var _1lR=E(_1lQ);if(!_1lR._){return __Z;}else{return new F(function(){return _hq(_1lR.a,new T(function(){return B(_1lP(_1lR.b));},1));});}},_1lS=function(_1lT,_1lU,_){var _1lV=B(_1ko(_1lU,_)),_1lW=B(_1lK(_1lV,_));return new F(function(){return _1l9(_1lT,B(_1lP(_1lW)),_);});},_1lX=function(_1lY,_1lZ,_1m0,_){var _1m1=B(_1ko(_1lZ,_)),_1m2=B(_1kz(_1lY,_1m1,_)),_1m3=eval(E(_1kY)),_1m4=__app2(E(_1m3),E(E(_1m0).a),E(E(_1m2).a));return new F(function(){return _F8(_);});},_1m5=new T(function(){return B(unCStr("contract_commitcash"));}),_1m6=new T(function(){return B(unCStr("contract_redeemcc"));}),_1m7=new T(function(){return B(unCStr("contract_pay"));}),_1m8=new T(function(){return B(unCStr("contract_both"));}),_1m9=new T(function(){return B(unCStr("contract_choice"));}),_1ma=new T(function(){return B(unCStr("contract_when"));}),_1mb="(function (x) {var c = demoWorkspace.newBlock(x); c.initSvg(); return c;})",_1mc=function(_1md,_){var _1me=eval(E(_1mb)),_1mf=__app1(E(_1me),toJSStr(E(_1md)));return new T1(0,_1mf);},_1mg=new T(function(){return B(unCStr("payer_id"));}),_1mh=new T(function(){return B(unCStr("pay_id"));}),_1mi=new T(function(){return B(unCStr("ccommit_id"));}),_1mj=new T(function(){return B(unCStr("end_expiration"));}),_1mk=new T(function(){return B(unCStr("start_expiration"));}),_1ml=new T(function(){return B(unCStr("person_id"));}),_1mm=new T(function(){return B(unCStr("contract_null"));}),_1mn=new T(function(){return B(unCStr("contract2"));}),_1mo=new T(function(){return B(unCStr("contract1"));}),_1mp=new T(function(){return B(unCStr("observation"));}),_1mq=new T(function(){return B(unCStr("timeout"));}),_1mr=new T(function(){return B(unCStr("contract"));}),_1ms=new T(function(){return B(unCStr("expiration"));}),_1mt=new T(function(){return B(unCStr("ammount"));}),_1mu=new T(function(){return B(unCStr("payee_id"));}),_1mv=new T(function(){return B(unCStr("value_available_money"));}),_1mw=new T(function(){return B(unCStr("value_add_money"));}),_1mx=new T(function(){return B(unCStr("value_const_money"));}),_1my=new T(function(){return B(unCStr("money_from_choice"));}),_1mz=new T(function(){return B(unCStr("value2"));}),_1mA=new T(function(){return B(unCStr("value1"));}),_1mB=new T(function(){return B(unCStr("choice_id"));}),_1mC=new T(function(){return B(unCStr("default"));}),_1mD=new T(function(){return B(unCStr("money"));}),_1mE=new T(function(){return B(unCStr("commit_id"));}),_1mF="(function (b, s) { return (b.setText(s)); })",_1mG=function(_1mH,_){var _1mI=E(_1mH);switch(_1mI._){case 0:var _1mJ=B(_1mc(_1mv,_)),_1mK=E(_1mJ),_1mL=B(_1lS(_1mE,E(_1mK.a),_)),_1mM=eval(E(_1mF)),_1mN=__app2(E(_1mM),E(E(_1mL).a),toJSStr(B(_hA(0,E(_1mI.a),_1))));return _1mK;case 1:var _1mO=B(_1mG(_1mI.a,_)),_1mP=B(_1mG(_1mI.b,_)),_1mQ=B(_1mc(_1mw,_)),_1mR=E(_1mQ),_1mS=E(_1mR.a),_1mT=B(_1kZ(_1mA,_1mS,_1mO,_)),_1mU=B(_1kZ(_1mz,_1mS,_1mP,_));return _1mR;case 2:var _1mV=B(_1mc(_1mx,_)),_1mW=E(_1mV),_1mX=B(_1lS(_1mD,E(_1mW.a),_)),_1mY=eval(E(_1mF)),_1mZ=__app2(E(_1mY),E(E(_1mX).a),toJSStr(B(_hA(0,E(_1mI.a),_1))));return _1mW;default:var _1n0=B(_1mG(_1mI.c,_)),_1n1=B(_1mc(_1my,_)),_1n2=E(_1n1),_1n3=E(_1n2.a),_1n4=B(_1lS(_1mB,_1n3,_)),_1n5=eval(E(_1mF)),_1n6=__app2(E(_1n5),E(E(_1n4).a),toJSStr(B(_hA(0,E(_1mI.a),_1)))),_1n7=B(_1lS(_1ml,_1n3,_)),_1n8=__app2(E(_1n5),E(E(_1n7).a),toJSStr(B(_hA(0,E(_1mI.b),_1)))),_1n9=B(_1kZ(_1mC,_1n3,_1n0,_));return _1n2;}},_1na=new T(function(){return B(unCStr("observation_personchosethis"));}),_1nb=new T(function(){return B(unCStr("observation_personchosesomething"));}),_1nc=new T(function(){return B(unCStr("observation_value_ge"));}),_1nd=new T(function(){return B(unCStr("observation_trueobs"));}),_1ne=new T(function(){return B(unCStr("observation_falseobs"));}),_1nf=new T(function(){return B(unCStr("observation_belowtimeout"));}),_1ng=new T(function(){return B(unCStr("observation_andobs"));}),_1nh=new T(function(){return B(unCStr("observation_orobs"));}),_1ni=new T(function(){return B(unCStr("observation_notobs"));}),_1nj=new T(function(){return B(unCStr("person"));}),_1nk=new T(function(){return B(unCStr("choice_value"));}),_1nl=new T(function(){return B(unCStr("observation2"));}),_1nm=new T(function(){return B(unCStr("observation1"));}),_1nn=new T(function(){return B(unCStr("block_number"));}),_1no=function(_1np,_){var _1nq=E(_1np);switch(_1nq._){case 0:var _1nr=B(_1mc(_1nf,_)),_1ns=E(_1nr),_1nt=B(_1lS(_1nn,E(_1ns.a),_)),_1nu=eval(E(_1mF)),_1nv=__app2(E(_1nu),E(E(_1nt).a),toJSStr(B(_hA(0,E(_1nq.a),_1))));return _1ns;case 1:var _1nw=B(_1no(_1nq.a,_)),_1nx=B(_1no(_1nq.b,_)),_1ny=B(_1mc(_1ng,_)),_1nz=E(_1ny),_1nA=E(_1nz.a),_1nB=B(_1lX(_1nm,_1nA,_1nw,_)),_1nC=B(_1lX(_1nl,_1nA,_1nx,_));return _1nz;case 2:var _1nD=B(_1no(_1nq.a,_)),_1nE=B(_1no(_1nq.b,_)),_1nF=B(_1mc(_1nh,_)),_1nG=E(_1nF),_1nH=E(_1nG.a),_1nI=B(_1lX(_1nm,_1nH,_1nD,_)),_1nJ=B(_1lX(_1nl,_1nH,_1nE,_));return _1nG;case 3:var _1nK=B(_1no(_1nq.a,_)),_1nL=B(_1mc(_1ni,_)),_1nM=E(_1nL),_1nN=B(_1lX(_1mp,E(_1nM.a),_1nK,_));return _1nM;case 4:var _1nO=B(_1mc(_1na,_)),_1nP=E(_1nO),_1nQ=E(_1nP.a),_1nR=B(_1lS(_1mB,_1nQ,_)),_1nS=eval(E(_1mF)),_1nT=__app2(E(_1nS),E(E(_1nR).a),toJSStr(B(_hA(0,E(_1nq.a),_1)))),_1nU=B(_1lS(_1nj,_1nQ,_)),_1nV=__app2(E(_1nS),E(E(_1nU).a),toJSStr(B(_hA(0,E(_1nq.b),_1)))),_1nW=B(_1lS(_1nk,_1nQ,_)),_1nX=__app2(E(_1nS),E(E(_1nW).a),toJSStr(B(_hA(0,E(_1nq.c),_1))));return _1nP;case 5:var _1nY=B(_1mc(_1nb,_)),_1nZ=E(_1nY),_1o0=E(_1nZ.a),_1o1=B(_1lS(_1mB,_1o0,_)),_1o2=eval(E(_1mF)),_1o3=__app2(E(_1o2),E(E(_1o1).a),toJSStr(B(_hA(0,E(_1nq.a),_1)))),_1o4=B(_1lS(_1nj,_1o0,_)),_1o5=__app2(E(_1o2),E(E(_1o4).a),toJSStr(B(_hA(0,E(_1nq.b),_1))));return _1nZ;case 6:var _1o6=B(_1mG(_1nq.a,_)),_1o7=B(_1mG(_1nq.b,_)),_1o8=B(_1mc(_1nc,_)),_1o9=E(_1o8),_1oa=E(_1o9.a),_1ob=B(_1kZ(_1mA,_1oa,_1o6,_)),_1oc=B(_1kZ(_1mz,_1oa,_1o7,_));return _1o9;case 7:return new F(function(){return _1mc(_1nd,_);});break;default:return new F(function(){return _1mc(_1ne,_);});}},_1od=function(_1oe,_){var _1of=E(_1oe);switch(_1of._){case 0:return new F(function(){return _1mc(_1mm,_);});break;case 1:var _1og=B(_1od(_1of.f,_)),_1oh=B(_1od(_1of.g,_)),_1oi=B(_1mG(_1of.c,_)),_1oj=B(_1mc(_1m5,_)),_1ok=E(_1oj),_1ol=E(_1ok.a),_1om=B(_1lS(_1mi,_1ol,_)),_1on=eval(E(_1mF)),_1oo=__app2(E(_1on),E(E(_1om).a),toJSStr(B(_hA(0,E(_1of.a),_1)))),_1op=B(_1lS(_1ml,_1ol,_)),_1oq=__app2(E(_1on),E(E(_1op).a),toJSStr(B(_hA(0,E(_1of.b),_1)))),_1or=B(_1kZ(_1mt,_1ol,_1oi,_)),_1os=B(_1lS(_1mk,_1ol,_)),_1ot=__app2(E(_1on),E(E(_1os).a),toJSStr(B(_hA(0,E(_1of.d),_1)))),_1ou=B(_1lS(_1mj,_1ol,_)),_1ov=__app2(E(_1on),E(E(_1ou).a),toJSStr(B(_hA(0,E(_1of.e),_1)))),_1ow=B(_1kQ(_1mo,_1ol,_1og,_)),_1ox=B(_1kQ(_1mn,_1ol,_1oh,_));return _1ok;case 2:var _1oy=B(_1od(_1of.b,_)),_1oz=B(_1mc(_1m6,_)),_1oA=E(_1oz),_1oB=E(_1oA.a),_1oC=B(_1lS(_1mi,_1oB,_)),_1oD=eval(E(_1mF)),_1oE=__app2(E(_1oD),E(E(_1oC).a),toJSStr(B(_hA(0,E(_1of.a),_1)))),_1oF=B(_1kQ(_1mr,_1oB,_1oy,_));return _1oA;case 3:var _1oG=B(_1od(_1of.f,_)),_1oH=B(_1mc(_1m7,_)),_1oI=B(_1mG(_1of.d,_)),_1oJ=E(_1oH),_1oK=E(_1oJ.a),_1oL=B(_1lS(_1mh,_1oK,_)),_1oM=eval(E(_1mF)),_1oN=__app2(E(_1oM),E(E(_1oL).a),toJSStr(B(_hA(0,E(_1of.a),_1)))),_1oO=B(_1lS(_1mg,_1oK,_)),_1oP=__app2(E(_1oM),E(E(_1oO).a),toJSStr(B(_hA(0,E(_1of.b),_1)))),_1oQ=B(_1lS(_1mu,_1oK,_)),_1oR=__app2(E(_1oM),E(E(_1oQ).a),toJSStr(B(_hA(0,E(_1of.c),_1)))),_1oS=B(_1kZ(_1mt,_1oK,_1oI,_)),_1oT=B(_1lS(_1ms,_1oK,_)),_1oU=__app2(E(_1oM),E(E(_1oT).a),toJSStr(B(_hA(0,E(_1of.e),_1)))),_1oV=B(_1kQ(_1mr,_1oK,_1oG,_));return _1oJ;case 4:var _1oW=B(_1od(_1of.a,_)),_1oX=B(_1od(_1of.b,_)),_1oY=B(_1mc(_1m8,_)),_1oZ=E(_1oY),_1p0=E(_1oZ.a),_1p1=B(_1kQ(_1mo,_1p0,_1oW,_)),_1p2=B(_1kQ(_1mn,_1p0,_1oX,_));return _1oZ;case 5:var _1p3=B(_1no(_1of.a,_)),_1p4=B(_1od(_1of.b,_)),_1p5=B(_1od(_1of.c,_)),_1p6=B(_1mc(_1m9,_)),_1p7=E(_1p6),_1p8=E(_1p7.a),_1p9=B(_1lX(_1mp,_1p8,_1p3,_)),_1pa=B(_1kQ(_1mo,_1p8,_1p4,_)),_1pb=B(_1kQ(_1mn,_1p8,_1p5,_));return _1p7;default:var _1pc=B(_1no(_1of.a,_)),_1pd=B(_1od(_1of.c,_)),_1pe=B(_1od(_1of.d,_)),_1pf=B(_1mc(_1ma,_)),_1pg=E(_1pf),_1ph=E(_1pg.a),_1pi=B(_1lS(_1mq,_1ph,_)),_1pj=eval(E(_1mF)),_1pk=__app2(E(_1pj),E(E(_1pi).a),toJSStr(B(_hA(0,E(_1of.b),_1)))),_1pl=B(_1lX(_1mp,_1ph,_1pc,_)),_1pm=B(_1kQ(_1mo,_1ph,_1pd,_)),_1pn=B(_1kQ(_1mn,_1ph,_1pe,_));return _1pg;}},_1po=new T(function(){return eval("(function () {var i; var b = demoWorkspace.getAllBlocks(); for (i = b.length - 1; i > 0; --i) { if (b[i] !== undefined) { b[i].dispose() } };})");}),_1pp=new T(function(){return eval("(function() {return (demoWorkspace.getAllBlocks()[0]);})");}),_1pq=new T(function(){return B(unCStr("base_contract"));}),_1pr=new T(function(){return eval("(function() { demoWorkspace.render(); onresize(); })");}),_1ps=function(_1pt,_){var _1pu=__app0(E(_1po)),_1pv=__app0(E(_1pp)),_1pw=B(_19H(B(_l5(_1ef,_1pt))));if(!_1pw._){return E(_19P);}else{if(!E(_1pw.b)._){var _1px=B(_1od(_1pw.a,_)),_1py=B(_1kQ(_1pq,_1pv,_1px,_)),_1pz=__app0(E(_1pr)),_1pA=eval(E(_18i)),_1pB=__app1(E(_1pA),toJSStr(E(_1ey))),_1pC=new T(function(){var _1pD=B(_19H(B(_l5(_DG,new T(function(){var _1pE=String(_1pB);return fromJSStr(_1pE);})))));if(!_1pD._){return E(_jT);}else{if(!E(_1pD.b)._){var _1pF=E(_1pD.a);return new T4(0,new T(function(){return B(_gR(_1pF.a));}),new T(function(){return B(_c2(_1pF.b));}),new T(function(){return B(_fb(_1pF.c));}),new T(function(){return B(_5s(_1pF.d));}));}else{return E(_jR);}}});return new F(function(){return _1eg(_1pC,_);});}else{return E(_19O);}}},_1pG=function(_){var _1pH=eval(E(_18i)),_1pI=__app1(E(_1pH),toJSStr(E(_1jT)));return new F(function(){return _1ps(new T(function(){var _1pJ=String(_1pI);return fromJSStr(_1pJ);}),_);});},_1pK=new T(function(){return B(unCStr("contractOutput"));}),_1pL=new T(function(){return B(unCStr("([], [], [], [])"));}),_1pM=new T(function(){return B(unCStr("([], [])"));}),_1pN=new T(function(){return B(_hA(0,0,_1));}),_1pO=function(_){var _1pP=__app0(E(_1po)),_1pQ=B(_1eA(_1jT,_1,_)),_1pR=B(_1eA(_18l,_1pN,_)),_1pS=B(_1eA(_18k,_1pM,_)),_1pT=B(_1eA(_1ey,_1pL,_));return new F(function(){return _1eA(_1pK,_1,_);});},_1pU=1000,_1pV=new T1(2,_1pU),_1pW=0,_1pX=new T1(2,_1pW),_1pY=4,_1pZ=new T3(3,_1pY,_1pY,_1pX),_1q0=3,_1q1=new T3(3,_1q0,_1q0,_1pX),_1q2=new T2(1,_1q1,_1pZ),_1q3=2,_1q4=new T3(3,_1q3,_1q3,_1pX),_1q5=1,_1q6=new T3(3,_1q5,_1q5,_1pX),_1q7=new T2(1,_1q6,_1q4),_1q8=new T2(1,_1q7,_1q2),_1q9=new T2(6,_1q8,_1pV),_1qa=new T1(0,_1q3),_1qb=20,_1qc=5,_1qd=new T6(3,_1q3,_1q3,_1qc,_1qa,_1qb,_Rm),_1qe=new T1(0,_1q5),_1qf=new T6(3,_1q5,_1q5,_1qc,_1qe,_1qb,_Rm),_1qg=new T2(4,_1qf,_1qd),_1qh=new T1(0,_1q0),_1qi=new T6(3,_1q0,_1q0,_1qc,_1qh,_1qb,_Rm),_1qj=new T1(0,_1pY),_1qk=new T6(3,_1pY,_1pY,_1qc,_1qj,_1qb,_Rm),_1ql=new T2(4,_1qi,_1qk),_1qm=new T2(4,_1qg,_1ql),_1qn=new T3(5,_1q9,_1qm,_Rm),_1qo=10,_1qp=new T4(6,_1aL,_1qo,_Rm,_1qn),_1qq=new T1(0,_1qp),_1qr=new T2(1,_1qq,_1),_1qs={_:1,a:_1pY,b:_1pY,c:_1pZ,d:_1qo,e:_1qb,f:_Rm,g:_Rm},_1qt=new T1(2,_1q5),_1qu=new T2(6,_1pZ,_1qt),_1qv=new T2(5,_1pY,_1pY),_1qw=new T2(1,_1qv,_1qu),_1qx=new T4(6,_1qw,_1qo,_1qs,_Rm),_1qy={_:1,a:_1q0,b:_1q0,c:_1q1,d:_1qo,e:_1qb,f:_Rm,g:_Rm},_1qz=new T2(6,_1q1,_1qt),_1qA=new T2(5,_1q0,_1q0),_1qB=new T2(1,_1qA,_1qz),_1qC=new T4(6,_1qB,_1qo,_1qy,_Rm),_1qD=new T2(4,_1qC,_1qx),_1qE={_:1,a:_1q3,b:_1q3,c:_1q4,d:_1qo,e:_1qb,f:_Rm,g:_Rm},_1qF=new T2(6,_1q4,_1qt),_1qG=new T2(5,_1q3,_1q3),_1qH=new T2(1,_1qG,_1qF),_1qI=new T4(6,_1qH,_1qo,_1qE,_Rm),_1qJ={_:1,a:_1q5,b:_1q5,c:_1q6,d:_1qo,e:_1qb,f:_Rm,g:_Rm},_1qK=new T2(6,_1q6,_1qt),_1qL=new T2(5,_1q5,_1q5),_1qM=new T2(1,_1qL,_1qK),_1qN=new T4(6,_1qM,_1qo,_1qJ,_Rm),_1qO=new T2(4,_1qN,_1qI),_1qP=new T2(4,_1qO,_1qD),_1qQ=new T1(0,_1qP),_1qR=new T2(1,_1qQ,_1qr),_1qS=new T(function(){return B(_1jl(0,_1hQ,_1qR));}),_1qT=function(_){var _1qU=B(_1pO(_)),_1qV=B(_1eA(_1jT,_1qS,_)),_1qW=eval(E(_18i)),_1qX=__app1(E(_1qW),toJSStr(E(_1jT)));return new F(function(){return _1ps(new T(function(){var _1qY=String(_1qX);return fromJSStr(_1qY);}),_);});},_1qZ=1,_1r0=new T1(3,_1qZ),_1r1=new T1(6,_1qZ),_1r2=100,_1r3=new T1(2,_1r2),_1r4=new T1(2,_1r3),_1r5=10,_1r6=new T1(6,_1r5),_1r7=200,_1r8=new T1(6,_1r7),_1r9=20,_1ra=new T1(2,_1r9),_1rb=new T2(2,_1qZ,_Rm),_1rc=new T2(5,_1qZ,_1qZ),_1rd=2,_1re=new T2(2,_1rd,_Rm),_1rf=new T2(4,_1rb,_1re),_1rg=new T6(3,_1qZ,_1rd,_1qZ,_1ra,_1r7,_1rf),_1rh=new T4(6,_1rc,_1r2,_1rf,_1rg),_1ri={_:1,a:_1rd,b:_1rd,c:_1ra,d:_1r9,e:_1r7,f:_1rh,g:_1rb},_1rj=new T1(0,_1ri),_1rk=new T1(0,_Rm),_1rl=new T2(1,_1rk,_1),_1rm=new T2(1,_1rj,_1rl),_1rn=new T2(1,_1r8,_1rm),_1ro=new T2(1,_1r6,_1rn),_1rp=new T2(1,_1r4,_1ro),_1rq=new T2(1,_1r1,_1rp),_1rr=new T2(1,_1r0,_1rq),_1rs=new T(function(){return B(_1jl(0,_1hT,_1rr));}),_1rt=function(_){var _1ru=B(_1pO(_)),_1rv=B(_1eA(_1jT,_1rs,_)),_1rw=eval(E(_18i)),_1rx=__app1(E(_1rw),toJSStr(E(_1jT)));return new F(function(){return _1ps(new T(function(){var _1ry=String(_1rx);return fromJSStr(_1ry);}),_);});},_1rz=1,_1rA=new T1(3,_1rz),_1rB=new T1(6,_1rz),_1rC=450,_1rD=new T1(2,_1rC),_1rE=new T1(2,_1rD),_1rF=10,_1rG=new T1(6,_1rF),_1rH=100,_1rI=new T1(6,_1rH),_1rJ=90,_1rK=3,_1rL=0,_1rM=new T3(4,_1rK,_1rK,_1rL),_1rN=2,_1rO=new T3(4,_1rN,_1rN,_1rL),_1rP=new T2(1,_1rO,_1rM),_1rQ=new T2(2,_1rO,_1rM),_1rR=new T3(4,_1rz,_1rz,_1rL),_1rS=new T2(1,_1rR,_1rQ),_1rT=new T2(2,_1rS,_1rP),_1rU=new T3(4,_1rK,_1rK,_1rz),_1rV=new T3(4,_1rN,_1rN,_1rz),_1rW=new T2(1,_1rV,_1rU),_1rX=new T2(2,_1rV,_1rU),_1rY=new T3(4,_1rz,_1rz,_1rz),_1rZ=new T2(1,_1rY,_1rX),_1s0=new T2(2,_1rZ,_1rW),_1s1=new T2(2,_1rT,_1s0),_1s2=new T2(2,_1rz,_Rm),_1s3=new T1(0,_1rz),_1s4=new T6(3,_1rz,_1rz,_1rN,_1s3,_1rH,_1s2),_1s5=new T3(5,_1s0,_1s4,_1s2),_1s6=new T4(6,_1s1,_1rJ,_1s5,_1s2),_1s7=new T1(0,_1s6),_1s8=new T2(1,_1s7,_1rl),_1s9=new T2(1,_1rI,_1s8),_1sa=new T2(1,_1rG,_1s9),_1sb=new T2(1,_1rE,_1sa),_1sc=new T2(1,_1rB,_1sb),_1sd=new T2(1,_1rA,_1sc),_1se=new T(function(){return B(_1jl(0,_1hT,_1sd));}),_1sf=function(_){var _1sg=B(_1pO(_)),_1sh=B(_1eA(_1jT,_1se,_)),_1si=eval(E(_18i)),_1sj=__app1(E(_1si),toJSStr(E(_1jT)));return new F(function(){return _1ps(new T(function(){var _1sk=String(_1sj);return fromJSStr(_1sk);}),_);});},_1sl=new T(function(){return B(unCStr("NotRedeemed "));}),_1sm=function(_1sn,_1so,_1sp){var _1sq=E(_1so);if(!_1sq._){var _1sr=function(_1ss){return new F(function(){return _hA(11,E(_1sq.a),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1sq.b),_1ss));})));});};if(E(_1sn)<11){return new F(function(){return _hq(_1sl,new T(function(){return B(_1sr(_1sp));},1));});}else{var _1st=new T(function(){return B(_hq(_1sl,new T(function(){return B(_1sr(new T2(1,_hy,_1sp)));},1)));});return new T2(1,_hz,_1st);}}else{return new F(function(){return _hq(_18D,_1sp);});}},_1su=0,_1sv=function(_1sw,_1sx,_1sy){var _1sz=new T(function(){var _1sA=function(_1sB){var _1sC=E(_1sx),_1sD=new T(function(){return B(A3(_is,_hk,new T2(1,function(_1sE){return new F(function(){return _hA(0,E(_1sC.a),_1sE);});},new T2(1,function(_Av){return new F(function(){return _1sm(_1su,_1sC.b,_Av);});},_1)),new T2(1,_hy,_1sB)));});return new T2(1,_hz,_1sD);};return B(A3(_is,_hk,new T2(1,function(_1sF){return new F(function(){return _hF(0,_1sw,_1sF);});},new T2(1,_1sA,_1)),new T2(1,_hy,_1sy)));});return new T2(0,_hz,_1sz);},_1sG=function(_1sH,_1sI){var _1sJ=E(_1sH),_1sK=B(_1sv(_1sJ.a,_1sJ.b,_1sI));return new T2(1,_1sK.a,_1sK.b);},_1sL=function(_1sM,_1sN){return new F(function(){return _iR(_1sG,_1sM,_1sN);});},_1sO=new T(function(){return B(unCStr("ChoiceMade "));}),_1sP=new T(function(){return B(unCStr("DuplicateRedeem "));}),_1sQ=new T(function(){return B(unCStr("ExpiredCommitRedeemed "));}),_1sR=new T(function(){return B(unCStr("CommitRedeemed "));}),_1sS=new T(function(){return B(unCStr("SuccessfulCommit "));}),_1sT=new T(function(){return B(unCStr("FailedPay "));}),_1sU=new T(function(){return B(unCStr("ExpiredPay "));}),_1sV=new T(function(){return B(unCStr("SuccessfulPay "));}),_1sW=function(_1sX,_1sY,_1sZ){var _1t0=E(_1sY);switch(_1t0._){case 0:var _1t1=function(_1t2){var _1t3=new T(function(){var _1t4=new T(function(){return B(_hA(11,E(_1t0.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1t0.d),_1t2));}))));});return B(_hA(11,E(_1t0.b),new T2(1,_hK,_1t4)));});return new F(function(){return _ih(11,_1t0.a,new T2(1,_hK,_1t3));});};if(_1sX<11){return new F(function(){return _hq(_1sV,new T(function(){return B(_1t1(_1sZ));},1));});}else{var _1t5=new T(function(){return B(_hq(_1sV,new T(function(){return B(_1t1(new T2(1,_hy,_1sZ)));},1)));});return new T2(1,_hz,_1t5);}break;case 1:var _1t6=function(_1t7){var _1t8=new T(function(){var _1t9=new T(function(){return B(_hA(11,E(_1t0.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1t0.d),_1t7));}))));});return B(_hA(11,E(_1t0.b),new T2(1,_hK,_1t9)));});return new F(function(){return _ih(11,_1t0.a,new T2(1,_hK,_1t8));});};if(_1sX<11){return new F(function(){return _hq(_1sU,new T(function(){return B(_1t6(_1sZ));},1));});}else{var _1ta=new T(function(){return B(_hq(_1sU,new T(function(){return B(_1t6(new T2(1,_hy,_1sZ)));},1)));});return new T2(1,_hz,_1ta);}break;case 2:var _1tb=function(_1tc){var _1td=new T(function(){var _1te=new T(function(){return B(_hA(11,E(_1t0.c),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1t0.d),_1tc));}))));});return B(_hA(11,E(_1t0.b),new T2(1,_hK,_1te)));});return new F(function(){return _ih(11,_1t0.a,new T2(1,_hK,_1td));});};if(_1sX<11){return new F(function(){return _hq(_1sT,new T(function(){return B(_1tb(_1sZ));},1));});}else{var _1tf=new T(function(){return B(_hq(_1sT,new T(function(){return B(_1tb(new T2(1,_hy,_1sZ)));},1)));});return new T2(1,_hz,_1tf);}break;case 3:var _1tg=function(_1th){var _1ti=new T(function(){var _1tj=new T(function(){return B(_hA(11,E(_1t0.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1t0.c),_1th));}))));});return B(_hF(11,_1t0.a,new T2(1,_hK,_1tj)));},1);return new F(function(){return _hq(_1sS,_1ti);});};if(_1sX<11){return new F(function(){return _1tg(_1sZ);});}else{return new T2(1,_hz,new T(function(){return B(_1tg(new T2(1,_hy,_1sZ)));}));}break;case 4:var _1tk=function(_1tl){var _1tm=new T(function(){var _1tn=new T(function(){return B(_hA(11,E(_1t0.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1t0.c),_1tl));}))));});return B(_hF(11,_1t0.a,new T2(1,_hK,_1tn)));},1);return new F(function(){return _hq(_1sR,_1tm);});};if(_1sX<11){return new F(function(){return _1tk(_1sZ);});}else{return new T2(1,_hz,new T(function(){return B(_1tk(new T2(1,_hy,_1sZ)));}));}break;case 5:var _1to=function(_1tp){var _1tq=new T(function(){var _1tr=new T(function(){return B(_hA(11,E(_1t0.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1t0.c),_1tp));}))));});return B(_hF(11,_1t0.a,new T2(1,_hK,_1tr)));},1);return new F(function(){return _hq(_1sQ,_1tq);});};if(_1sX<11){return new F(function(){return _1to(_1sZ);});}else{return new T2(1,_hz,new T(function(){return B(_1to(new T2(1,_hy,_1sZ)));}));}break;case 6:var _1ts=function(_1tt){return new F(function(){return _hF(11,_1t0.a,new T2(1,_hK,new T(function(){return B(_hA(11,E(_1t0.b),_1tt));})));});};if(_1sX<11){return new F(function(){return _hq(_1sP,new T(function(){return B(_1ts(_1sZ));},1));});}else{var _1tu=new T(function(){return B(_hq(_1sP,new T(function(){return B(_1ts(new T2(1,_hy,_1sZ)));},1)));});return new T2(1,_hz,_1tu);}break;default:var _1tv=function(_1tw){var _1tx=new T(function(){var _1ty=new T(function(){return B(_hA(11,E(_1t0.b),new T2(1,_hK,new T(function(){return B(_hA(11,E(_1t0.c),_1tw));}))));});return B(_j6(11,_1t0.a,new T2(1,_hK,_1ty)));},1);return new F(function(){return _hq(_1sO,_1tx);});};if(_1sX<11){return new F(function(){return _1tv(_1sZ);});}else{return new T2(1,_hz,new T(function(){return B(_1tv(new T2(1,_hy,_1sZ)));}));}}},_1tz=new T(function(){return B(unAppCStr("[]",_1));}),_1tA=new T2(1,_iP,_1),_1tB=function(_1tC){var _1tD=E(_1tC);if(!_1tD._){return E(_1tA);}else{var _1tE=new T(function(){return B(_1sW(0,_1tD.a,new T(function(){return B(_1tB(_1tD.b));})));});return new T2(1,_hj,_1tE);}},_1tF=function(_){var _1tG=E(_1ey),_1tH=toJSStr(_1tG),_1tI=eval(E(_18i)),_1tJ=_1tI,_1tK=__app1(E(_1tJ),_1tH),_1tL=E(_18k),_1tM=__app1(E(_1tJ),toJSStr(_1tL)),_1tN=__app0(E(_18j)),_1tO=E(_18l),_1tP=__app1(E(_1tJ),toJSStr(_1tO)),_1tQ=new T(function(){var _1tR=B(_19H(B(_l5(_18p,new T(function(){var _1tS=String(_1tP);return fromJSStr(_1tS);})))));if(!_1tR._){return E(_18o);}else{if(!E(_1tR.b)._){return E(_1tR.a);}else{return E(_18n);}}}),_1tT=new T(function(){var _1tU=B(_19H(B(_l5(_1ef,new T(function(){var _1tV=String(_1tN);return fromJSStr(_1tV);})))));if(!_1tU._){return E(_19P);}else{if(!E(_1tU.b)._){return E(_1tU.a);}else{return E(_19O);}}}),_1tW=new T(function(){var _1tX=B(_19H(B(_l5(_19E,new T(function(){var _1tY=String(_1tM);return fromJSStr(_1tY);})))));if(!_1tX._){return E(_18r);}else{if(!E(_1tX.b)._){var _1tZ=E(_1tX.a);return new T2(0,new T(function(){return B(_EV(_1tZ.a));}),new T(function(){return B(_5s(_1tZ.b));}));}else{return E(_18q);}}}),_1u0=new T(function(){var _1u1=B(_19H(B(_l5(_DG,new T(function(){var _1u2=String(_1tK);return fromJSStr(_1u2);})))));if(!_1u1._){return E(_jT);}else{if(!E(_1u1.b)._){var _1u3=E(_1u1.a);return new T4(0,new T(function(){return B(_gR(_1u3.a));}),new T(function(){return B(_c2(_1u3.b));}),new T(function(){return B(_fb(_1u3.c));}),new T(function(){return B(_5s(_1u3.d));}));}else{return E(_jR);}}}),_1u4=B(_VU(_1u0,_1tW,_1tT,new T2(0,_19F,_1tQ))),_1u5=function(_,_1u6){var _1u7=function(_,_1u8){var _1u9=E(_1u4.a),_1ua=new T(function(){var _1ub=new T(function(){return B(_hc(_1,_1u9.b));}),_1uc=new T(function(){return B(_hc(_1,_1u9.a));});return B(A3(_is,_hk,new T2(1,function(_1ud){return new F(function(){return _1sL(_1uc,_1ud);});},new T2(1,function(_1ue){return new F(function(){return _js(_1ub,_1ue);});},_1)),_jv));}),_1uf=B(_1eA(_1tL,new T2(1,_hz,_1ua),_)),_1ug=B(_1eA(_1tG,_1pL,_)),_1uh=B(_1eA(_1tO,B(_hA(0,E(_1tQ)+1|0,_1)),_)),_1ui=__app1(E(_1tJ),toJSStr(E(_1jT))),_1uj=B(_1ps(new T(function(){var _1uk=String(_1ui);return fromJSStr(_1uk);}),_)),_1ul=__app1(E(_1tJ),_1tH),_1um=new T(function(){var _1un=B(_19H(B(_l5(_DG,new T(function(){var _1uo=String(_1ul);return fromJSStr(_1uo);})))));if(!_1un._){return E(_jT);}else{if(!E(_1un.b)._){var _1up=E(_1un.a);return new T4(0,new T(function(){return B(_gR(_1up.a));}),new T(function(){return B(_c2(_1up.b));}),new T(function(){return B(_fb(_1up.c));}),new T(function(){return B(_5s(_1up.d));}));}else{return E(_jR);}}});return new F(function(){return _1eg(_1um,_);});},_1uq=E(_1u4.b);switch(_1uq._){case 0:var _1ur=B(_1eA(_1jT,_1jO,_));return new F(function(){return _1u7(_,_1ur);});break;case 1:var _1us=B(_1eA(_1jT,B(_1jl(0,_1hT,new T2(1,new T1(3,_1uq.a),new T2(1,new T1(6,_1uq.b),new T2(1,new T1(2,_1uq.c),new T2(1,new T1(6,_1uq.d),new T2(1,new T1(6,_1uq.e),new T2(1,new T1(0,_1uq.f),new T2(1,new T1(0,_1uq.g),_1))))))))),_));return new F(function(){return _1u7(_,_1us);});break;case 2:var _1ut=B(_1eA(_1jT,B(_1jl(0,_1hS,new T2(1,new T1(3,_1uq.a),new T2(1,new T1(0,_1uq.b),_1)))),_));return new F(function(){return _1u7(_,_1ut);});break;case 3:var _1uu=B(_1eA(_1jT,B(_1jl(0,_1hR,new T2(1,new T1(5,_1uq.a),new T2(1,new T1(6,_1uq.b),new T2(1,new T1(6,_1uq.c),new T2(1,new T1(2,_1uq.d),new T2(1,new T1(6,_1uq.e),new T2(1,new T1(0,_1uq.f),_1)))))))),_));return new F(function(){return _1u7(_,_1uu);});break;case 4:var _1uv=B(_1eA(_1jT,B(_1jl(0,_1hQ,new T2(1,new T1(0,_1uq.a),new T2(1,new T1(0,_1uq.b),_1)))),_));return new F(function(){return _1u7(_,_1uv);});break;case 5:var _1uw=B(_1eA(_1jT,B(_1jl(0,_1hP,new T2(1,new T1(1,_1uq.a),new T2(1,new T1(0,_1uq.b),new T2(1,new T1(0,_1uq.c),_1))))),_));return new F(function(){return _1u7(_,_1uw);});break;default:var _1ux=B(_1eA(_1jT,B(_1jl(0,_1hO,new T2(1,new T1(1,_1uq.a),new T2(1,new T1(6,_1uq.b),new T2(1,new T1(0,_1uq.c),new T2(1,new T1(0,_1uq.d),_1)))))),_));return new F(function(){return _1u7(_,_1ux);});}},_1uy=E(_1u4.c);if(!_1uy._){var _1uz=B(_1eA(_1pK,_1tz,_));return new F(function(){return _1u5(_,_1uz);});}else{var _1uA=new T(function(){return B(_1sW(0,_1uy.a,new T(function(){return B(_1tB(_1uy.b));})));}),_1uB=B(_1eA(_1pK,new T2(1,_iQ,_1uA),_));return new F(function(){return _1u5(_,_1uB);});}},_1uC=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uD=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uE=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uF=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uG=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uH=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uI=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uJ=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uK=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uL=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uM=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uN=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uO=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uP=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1uQ=function(_){return new F(function(){return __jsNull();});},_1uR=function(_1uS){var _1uT=B(A1(_1uS,_));return E(_1uT);},_1uU=new T(function(){return B(_1uR(_1uQ));}),_1uV=new T(function(){return E(_1uU);}),_1uW=function(_){var _1uX=eval(E(_18i)),_1uY=__app1(E(_1uX),toJSStr(E(_1ey))),_1uZ=new T(function(){var _1v0=B(_19H(B(_l5(_DG,new T(function(){var _1v1=String(_1uY);return fromJSStr(_1v1);})))));if(!_1v0._){return E(_jT);}else{if(!E(_1v0.b)._){var _1v2=E(_1v0.a);return new T4(0,new T(function(){return B(_gR(_1v2.a));}),new T(function(){return B(_c2(_1v2.b));}),new T(function(){return B(_fb(_1v2.c));}),new T(function(){return B(_5s(_1v2.d));}));}else{return E(_jR);}}});return new F(function(){return _1eg(_1uZ,_);});},_1v3=function(_){var _1v4=eval(E(_18i)),_1v5=__app1(E(_1v4),toJSStr(E(_1jT))),_1v6=B(_1ps(new T(function(){var _1v7=String(_1v5);return fromJSStr(_1v7);}),_)),_1v8=__createJSFunc(0,function(_){var _1v9=B(_1pO(_));return _1uV;}),_1va=__app2(E(_1uM),"clear_workspace",_1v8),_1vb=__createJSFunc(0,function(_){var _1vc=B(_1jU(_));return _1uV;}),_1vd=__app2(E(_1uL),"b2c",_1vb),_1ve=__createJSFunc(0,function(_){var _1vf=B(_1pG(_));return _1uV;}),_1vg=__app2(E(_1uK),"c2b",_1ve),_1vh=function(_1vi){var _1vj=new T(function(){var _1vk=Number(E(_1vi));return jsTrunc(_1vk);}),_1vl=function(_1vm){var _1vn=new T(function(){var _1vo=Number(E(_1vm));return jsTrunc(_1vo);}),_1vp=function(_1vq){var _1vr=new T(function(){var _1vs=Number(E(_1vq));return jsTrunc(_1vs);}),_1vt=function(_1vu,_){var _1vv=B(_1ga(_1vj,_1vn,_1vr,new T(function(){var _1vw=Number(E(_1vu));return jsTrunc(_1vw);}),_));return _1uV;};return E(_1vt);};return E(_1vp);};return E(_1vl);},_1vx=__createJSFunc(5,E(_1vh)),_1vy=__app2(E(_1uJ),"commit",_1vx),_1vz=function(_1vA){var _1vB=new T(function(){var _1vC=Number(E(_1vA));return jsTrunc(_1vC);}),_1vD=function(_1vE){var _1vF=new T(function(){var _1vG=Number(E(_1vE));return jsTrunc(_1vG);}),_1vH=function(_1vI,_){var _1vJ=B(_1fS(_1vB,_1vF,new T(function(){var _1vK=Number(E(_1vI));return jsTrunc(_1vK);}),_));return _1uV;};return E(_1vH);};return E(_1vD);},_1vL=__createJSFunc(4,E(_1vz)),_1vM=__app2(E(_1uI),"redeem",_1vL),_1vN=function(_1vO){var _1vP=new T(function(){var _1vQ=Number(E(_1vO));return jsTrunc(_1vQ);}),_1vR=function(_1vS){var _1vT=new T(function(){var _1vU=Number(E(_1vS));return jsTrunc(_1vU);}),_1vV=function(_1vW,_){var _1vX=B(_1eF(_1vP,_1vT,new T(function(){var _1vY=Number(E(_1vW));return jsTrunc(_1vY);}),_));return _1uV;};return E(_1vV);};return E(_1vR);},_1vZ=__createJSFunc(4,E(_1vN)),_1w0=__app2(E(_1uH),"claim",_1vZ),_1w1=function(_1w2){var _1w3=new T(function(){var _1w4=Number(E(_1w2));return jsTrunc(_1w4);}),_1w5=function(_1w6){var _1w7=new T(function(){var _1w8=Number(E(_1w6));return jsTrunc(_1w8);}),_1w9=function(_1wa,_){var _1wb=B(_1hn(_1w3,_1w7,new T(function(){var _1wc=Number(E(_1wa));return jsTrunc(_1wc);}),_));return _1uV;};return E(_1w9);};return E(_1w5);},_1wd=__createJSFunc(4,E(_1w1)),_1we=__app2(E(_1uG),"choose",_1wd),_1wf=__createJSFunc(0,function(_){var _1wg=B(_1tF(_));return _1uV;}),_1wh=__app2(E(_1uF),"execute",_1wf),_1wi=__createJSFunc(0,function(_){var _1wj=B(_1uW(_));return _1uV;}),_1wk=__app2(E(_1uE),"refreshActions",_1wi),_1wl=function(_1wm,_){var _1wn=B(_1hj(new T(function(){var _1wo=String(E(_1wm));return fromJSStr(_1wo);}),_));return _1uV;},_1wp=__createJSFunc(2,E(_1wl)),_1wq=__app2(E(_1uD),"addAction",_1wp),_1wr=function(_1ws){var _1wt=new T(function(){var _1wu=String(E(_1ws));return fromJSStr(_1wu);}),_1wv=function(_1ww,_){var _1wx=B(_1hI(_1wt,new T(function(){var _1wy=Number(E(_1ww));return jsTrunc(_1wy);}),_));return _1uV;};return E(_1wv);},_1wz=__createJSFunc(3,E(_1wr)),_1wA=__app2(E(_1uC),"addActionWithNum",_1wz),_1wB=__createJSFunc(0,function(_){var _1wC=B(_1rt(_));return _1uV;}),_1wD=__app2(E(_1uP),"depositIncentive",_1wB),_1wE=__createJSFunc(0,function(_){var _1wF=B(_1qT(_));return _1uV;}),_1wG=__app2(E(_1uO),"crowdFunding",_1wE),_1wH=__createJSFunc(0,function(_){var _1wI=B(_1sf(_));return _1uV;}),_1wJ=__app2(E(_1uN),"escrow",_1wH),_1wK=__app1(E(_1v4),toJSStr(E(_1ey))),_1wL=new T(function(){var _1wM=B(_19H(B(_l5(_DG,new T(function(){var _1wN=String(_1wK);return fromJSStr(_1wN);})))));if(!_1wM._){return E(_jT);}else{if(!E(_1wM.b)._){var _1wO=E(_1wM.a);return new T4(0,new T(function(){return B(_gR(_1wO.a));}),new T(function(){return B(_c2(_1wO.b));}),new T(function(){return B(_fb(_1wO.c));}),new T(function(){return B(_5s(_1wO.d));}));}else{return E(_jR);}}}),_1wP=B(_1eg(_1wL,_));return _h9;},_1wQ=function(_){return new F(function(){return _1v3(_);});};
var hasteMain = function() {B(A(_1wQ, [0]));};window.onload = hasteMain;
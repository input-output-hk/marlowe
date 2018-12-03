# Meadow (local server-side version)
Under `meadow-sc` you can find a Meadow version that uses local server-side compilation through Ajax.

It can be compiled using:

```
stack build
```

And deployed using:

```
stack exec meadow-sc-exe
```

## DISCLAIMER

Do not run this local server in a computer exposed to an untrusted network! The code sent by clients is compiled and run in the server without any safety check. Thus, any client using this version of Meadow will be able to run arbitrary code in the machine hosting it.



# Meadow (local server-side version)
Under `meadow-sc` you can find a Meadow version that uses local server-side compilation through Ajax.

In order to compile the local server-side version of Meadow, make sure you are in the inner `meadow-sc` folder (the one that contains the `stack.yaml` file, not this folder), otherwise the semantics of Marlowe will be compiled instead:

```
cd meadow-sc
```

Then the project can be compiled by using stack:

```
stack build
```

And deployed using:

```
stack exec meadow-sc-exe
```

After this, the tool should be available in http://localhost:8080/

## DISCLAIMER

Do not run this local server in a computer exposed to an untrusted network! The code sent by clients is compiled and run in the server without any safety check. Thus, any client using this version of Meadow will be able to run arbitrary code in the machine hosting it.

## Troubleshooting

Compilation of this project requires one of the latest versions of stack. If compilation does not work, please, try to install the latest version.

Additionally, when testing this in mac we found a run time issue between stack and libgmp that had already been reported here:

https://ghc.haskell.org/trac/ghc/ticket/15105

A workaround that worked for us was to remove the file `HSinteger-gmp-1.0.2.0.o` as suggested in the following comment:

https://ghc.haskell.org/trac/ghc/ticket/15105#comment:10

But this may have side-effects on other stack haskell projects, do at your own risk.


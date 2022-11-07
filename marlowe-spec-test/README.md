# Marlowe Spec Test

This tool is a test suite that checks if a particular Marlowe implementation conforms to the specification.

The tool receives as an argument the path to a process (with no arguments) that we call "client process". The client process listens for semantic requests over `stdin` and replies via `stdout`, any `stderr` message is just printed.

## Usage

**Important Note**

We haven't packaged the tool yet, so in order to run it, you need to be inside the `nix develop` shell and execute it with `cabal run`.

```bash
# Whenever you see something like
$ marlowe-spec -c <path/to/cli>
# For the moment replace it with
[nix-shell] $ cabal run marlowe-spec -- -c <path/to/cli>
```

### Get help

To list all available options, you can invoke the tool with `--help`

```bash
$ marlowe-spec --help

Mmm... tasty test suite

Usage: marlowe-spec [-p|--pattern PATTERN] [-t|--timeout DURATION]
                    [-l|--list-tests] [-j|--num-threads NUMBER] [-q|--quiet]
                    [--hide-successes] [--color never|always|auto]
                    [--ansi-tricks ARG] [-c|--cli-path CLI_PATH] [--trace-cp]

Available options:
  -h,--help                Show this help text
  -p,--pattern PATTERN     Select only tests which satisfy a pattern or awk
                           expression
  -t,--timeout DURATION    Timeout for individual tests (suffixes: ms,s,m,h;
                           default: s)
  -l,--list-tests          Do not run the tests; just print their names
  -j,--num-threads NUMBER  Number of threads to use for tests execution
                           (default: # of cores/capabilities)
  -q,--quiet               Do not produce any output; indicate success only by
                           the exit code
  --hide-successes         Do not print tests that passed successfully
  --color never|always|auto
                           When to use colored output (default: auto)
  --ansi-tricks ARG        Enable various ANSI terminal tricks. Can be set to
                           'true' or 'false'. (default: true)
  -c,--cli-path CLI_PATH   Path to the client application to test
  --trace-cp               Trace client process
```
### Run the test suite
In order to run the test suite, you need to pass the process to test via the `-c` parameter.

```bash
$ marlowe-spec -c <path/to/cli>
```

This command will call the client process and run all the available tests. If a particular test fails, it will also print a helper to run the failed test.

### List the tests
In order to list all the tests you can pass the `--list-test` argument

```bash
$ marlowe-spec -c <path/to/cli> --list-tests
```

### Filter tests to run
You can use a [Tasty pattern](https://github.com/UnkindPartition/tasty#patterns) to limit the tests to run. For example

```bash
$ marlowe-spec -c <path/to/cli> -p '/Invalid type/'
```

### Add debug information
When a test fails, it can be useful to inspect the request that the driver is asking and what the client is responding. You can add `--trace-cp` to print this information.

## Request/Response
The testing tool (also known as the driver) makes requests to the client process via `stdin` and listens to responses via `stdout`. For the moment, the two processes communicates via `Json`, but we plan to add `CBOR` in the future.

The requests are enclosed with triple backtick

```markdown
  \`\`\` request \`\`\`
```

The possible requests are:
* Test roundtrip serialization
* Generate random value
* Compute transaction
* Play trace

All responses are wrapped to provide some common cases

### Response wrap

If the request is not known by the client process, it should reply `"UnknownRequest"`. Similarly, if its known but not implemented, it should reply `"RequestNotImplemented"`.

If a request is known, but it is malformed or faulty somehow, then an `InvalidRequest` should be responded as follow

```json
{"invalid-request": "some string that explains what went wrong"}
```

If the request was processed succesfully, then a `RequestResponse` should be responded. The payload will depend on the request type.

```json
{"request-response": "a valid JSON with the response of the request"}
```

### Test roundtrip serialization

This request allows to test that the client process serializes the different types as defined in the specification. The client process needs to `decode` the payload and re`encode` it.

There are three possible responses:

#### **Serialization success**
If the client process was able to `decode` and re`encode` the value.

```json
{"serialization-success": "valid json"}
```

#### **Unknown type**
If the type is unknown

```json
{"unknown-type": "the invalid type as a string"}
```

#### **Serialization error**
If the client process was unable to `decode` the value.

```json
{"serialization-error": "A string with the error"}
```

#### Example
For example, for this request

```json
{
    "request": "test-roundtrip-serialization",
    "typeId": "Core.Value",
    "json": {"add": 1, "and": 2}
}
```

The expected response is

```json
{
    "request-response": {"serialization-success": {"and": 2, "add": 1 }}
}
```

The order of the fields or spaces do not matter as long as the tool is able to decode it.

### Generate random value

The Marlowe specification is agnostic of the blockchain that implements it, so some types that might be valid for the tool, might not be valid for the client process. For that reason we need a way to ask the client process to generate some values for some types (like `Token` or `Address`).

The Request is encoded as

```json
{
    "request": "generate-random-value",
    "typeId": "Core.Token",
}
```

And the payload of the `request-response` should be the serialized type.

### Compute transaction

The request to compute a transaction should be encoded as

```json
{
    "request": "compute-transaction",
    "transactionInput": <Transaction serialized>,
    "coreContract": <Contract serialized>,
    "state": <State serialized>
}
```

The payload of the `request-response` is a serialized `TransactionOutput`

### Play trace

The request is encoded as

```json
{
    "request": "playtrace",
    "transactionInput": <Transaction array serialized>,
    "coreContract": <Contract serialized>,
    "initialTime": <Posix time>
}
```

The payload of the `request-response` is a serialized `TransactionOutput`



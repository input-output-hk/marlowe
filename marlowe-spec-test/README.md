# Marlowe Spec Test

This documentation refers to the Marlowe Test Spec Driver, a test suite that checks that a particular Marlowe implementation conforms to the specification.

The driver receives as an argument the path to a program that we call "client process". The client process is called with no arguments, and it listens for requests over `stdin` and replies via `stdout`, any `stderr` message is treated as debug information.

![Architecture diagram](https://docs.google.com/drawings/d/e/2PACX-1vSWg9lWSHGXEbEjjCEka9Vywz0nt1JaKxOycxOfsvNIv7UopNwSPoqLKx3mieNAzsceu4tb5ISs_yGY/pub?w=949&h=707)

## Usage

**Important Note**

We haven't packaged the driver yet, so in order to run it, you need to be inside the `nix develop` shell and execute it with `cabal run`.

```bash
# Whenever you see something like
$ marlowe-spec -c <path/to/cli>
# For the moment replace it with
[nix-shell] $ cabal run marlowe-spec -- -c <path/to/cli>
```

### Get help

To list all available options, you can invoke the driver with `--help`

```bash
$ marlowe-spec --help

Mmm... tasty test suite

Usage: marlowe-spec [-p|--pattern PATTERN] [-t|--timeout DURATION]
                    [-l|--list-tests] [-j|--num-threads NUMBER] [-q|--quiet]
                    [--hide-successes] [--color never|always|auto]
                    [--ansi-tricks ARG] [-c|--cli-path CLI_PATH]
                    [--trace-cp TRACE_CP] [--pool-size POOL_SIZE]
                    [--quickcheck-tests NUMBER] [--quickcheck-replay SEED]
                    [--quickcheck-show-replay] [--quickcheck-max-size NUMBER]
                    [--quickcheck-max-ratio NUMBER] [--quickcheck-verbose]
                    [--quickcheck-shrinks NUMBER]

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
  --trace-cp TRACE_CP      If provided, filepath of the client process trace log
  --pool-size POOL_SIZE    Number of client process to spawn (default 10)
  --quickcheck-tests NUMBER
                           Number of test cases for QuickCheck to generate.
                           Underscores accepted: e.g. 10_000_000
  --quickcheck-replay SEED Random seed to use for replaying a previous test run
                           (use same --quickcheck-max-size)
  --quickcheck-show-replay Show a replay token for replaying tests
  --quickcheck-max-size NUMBER
                           Size of the biggest test cases quickcheck generates
  --quickcheck-max-ratio NUMBER
                           Maximum number of discared tests per successful test
                           before giving up
  --quickcheck-verbose     Show the generated test cases
  --quickcheck-shrinks NUMBER
                           Number of shrinks allowed before QuickCheck will fail
                           a test
```
### Run the test suite
In order to run the test suite, you need to pass the path to the program to test via the `-c` parameter.

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
When a test fails, it can be useful to inspect the request that the driver is asking and what the client is responding. You can add `--trace-cp <path/to/log/file>` to log this information.

## Request/Response
The driver makes requests to the client process via `stdin` and listens to responses via `stdout`. For the moment, the two processes communicates via `Json`, but we plan to add `CBOR` in the future.

The requests are enclosed with triple backtick

```markdown
  \`\`\` request \`\`\`
```

The possible requests are:
* Test roundtrip serialization
* Generate random value
* Compute transaction
* Play trace
* Eval value

All responses are wrapped to provide some common cases

### Response wrap

- If the request is not known by the client process, it should reply:
```json
"UnknownRequest"
```

- Similarly, if its known but not implemented, it should reply:

```json
"RequestNotImplemented"
```

- If a request is known, but it is malformed or faulty somehow, then an `InvalidRequest` should be responded as follow

```json
{"invalid-request": "some string that explains what went wrong"}
```

- If the request was processed succesfully, then a `RequestResponse` should be responded. The payload will depend on the request type.

```json
{"request-response": <JSON payload>}
```

### Test roundtrip serialization

This request allows to test that the client process serializes the different types as defined in the specification. The client process needs to `decode` the payload and re`encode` it.

There are three possible responses:

- If the client process was able to `decode` and re`encode` the value.

```json
{"serialization-success": <JSON payload>}
```

- If the type is unknown

```json
{"unknown-type": "the invalid type as a string"}
```

- If the client process was unable to `decode` the value.

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

The order of the fields or spaces does not matter as long as it is a valid json.

### Generate random value

The Marlowe specification is agnostic of the blockchain that implements it, so some types that might be valid for the driver, might not be valid for the client process. For that reason we need a way to ask the client process to generate some values for two types `Core.Token` and `Core.Party`.

The Request is encoded as

```json
{
    "request": "generate-random-value",
    "typeId": <Core.Token | Core.Party>,
    "seed": <Optional Int>,
    "size": <Optional Int>
}
```

The `seed` value is always sent but is optional to use. It allows tests to be reproducible, it is expected that for the same seed the same response is returned.

The `size` value is always sent but is optional to use. It allows the tests to "shrink". When a property fails, the test framework will try a smaller value to try to see what is the minimum value for which it fails.

The payload of the `request-response` can be one of the following:

- If the value was correctly generated

```json
{"value": <Valid json>}
```

- If the type is unknown

```json
{"unknown-type": "the invalid type as a string"}
```

#### Example
For example, for this request

```json
{
    "request": "generate-random-value",
    "typeId": "Core.Token"
}
```
a valid response could be

```json
{
  "request-response": {
    "value": { "token_name": "375ADmDK4", "currency_symbol": "51eb5D8D2d" }
  }
}
```
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

### Eval Value

The request is encoded as

```json
{
    "request": "eval-value",
    "environment": <Environment serialized>,
    "state": <State serialized>,
    "value": <Value serialized>
}
```

The payload of the `request-response` is an integer


#### Example
For example, for this request

```json
{
    "request": "evalValue",
    "environment": {"timeInterval": [10, 20] },
    "state": { "accounts": [], "boundValues": [], "choices": [], "minTime": 5},
    "value": "time_interval_start"
}
```
a valid response could be

```json
{
  "request-response": 10
}
```
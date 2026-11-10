# Model reconstruction regressions

Run the suite against a built CSB executable:

```sh
python3 tests/sampling/test_models.py build/csb -v
```

To register it with CTest, configure with `-DENABLE_SAMPLING_TESTS=ON`, build,
then run:

```sh
ctest --test-dir build --output-on-failure -R sampling-models
```

These tests require Python 3.7 or newer and CMSGen/UniGen support. They work
with static builds and do not require lit, GTest, or another SMT solver. Exact
counting tests run when Ganak is available. The build workflow enables this
suite for Linux and macOS.

The fixtures cover both issue #14 reproducers, forced Boolean assignments,
Boolean connectives, mixed Boolean/bitvector arithmetic, projection witnesses,
UNSAT, and unused variables including a 65-bit vector. Tests evaluate returned
assignments against the constraints, compare seeded sample sequences, check
repeated `get-model` calls, and verify small model counts independently.
They also exercise UniGen and MiniSat model reconstruction with simplifications
enabled. Model definition order is ignored when comparing assignments.

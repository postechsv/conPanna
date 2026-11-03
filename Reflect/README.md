# Certification by reflection (experimental branch `reflection-test`)

`udf_reflect` closes a completeness obligation `complete P U` by evaluating a checker of the
stored UDF certificate in the kernel, with a soundness theorem proved once
(`Reflect.complete_of_check`). Design and correctness argument:
`documentation/reflection-design.md`.

These modules are outside the `conPanna` library. `Reflect/build.sh FILE...` compiles them
(and checks test files) against the main tree's build, without writing to it:

```
Reflect/build.sh Reflect/Core.lean Reflect/Check.lean Reflect/Eval.lean Reflect/AcuStep.lean \
  Reflect/AcuSound.lean Reflect/Sound.lean Reflect/Tactic.lean
Reflect/build.sh experiments/reflection/tests/GermanAll.lean   # 75 German obligations
```

Tests (`experiments/reflection/tests/`): `*All.lean` close the completeness obligations of an
example by `udf_reflect`; `*Replay.lean` the same obligations by `udf_certify`, for comparison.
Certificates are read from `producer/.cache/udf/` (copied from the main tree).

Not covered (the checker returns `false`, and `udf_certify` remains): ACU systems of more than
one row, or with coefficients other than −1, 0, 1.

# DAG sharing results

The recommended independent patch saves 16 coordinates. It replaces only the logarithm polynomial evaluator. The resulting system has 1,256 active rational coordinates, including the original input, and 1,213 quadratic residuals. Its normalized sum of residual squares is an integer polynomial of degree four. The fixed coefficient remains S = 3^(2^27).

`log-replacement.cjs` replaces the baseline text starting at `function log(name,p,e){` and ending immediately before `const LU=`. `prepare_log.py` makes this replacement against the immutable baseline and writes the runnable candidate in `log-candidate/build_source.cjs`.

The raw candidate has 1,288 coordinates, 1,245 residuals, and 1,198 gate coordinates. The baseline compiler removes 32 coordinates, as before. `log-candidate/measured-census.json` records the exact count. `log-candidate/compiled-ir.json` is an exact residual-system specification of the candidate polynomial: sum the squares of its normalized residuals. No large expansion of S is needed.

## Algebraic identity and witness maps

Write P(w) = sum from j=0 to12 of a_j w^j, with the unchanged baseline rational coefficients. There is a unique monic Q(w) of degree6 such that P(w) - a_12 Q(w)^2 has degree at most5. The patch determines the six remaining coefficients of Q from degrees11 down to6. It divides only by the fixed nonzero rational numbers2 and a_12. The resulting exact coefficients are in `log-candidate/square-completion.json`.

Compute w² and w³. Every power through w^6 is a polynomial of degree at most two in 1,w,w²,w³. Therefore Q(w) needs one field quadratic assignment. The remainder R(w), of degree at most5, is also quadratic in those coordinates. One final field assignment produces a_12 Q(w)^2 + R(w). This uses four field assignments for P rather than the baseline's five. Each field assignment uses two rational coordinates. Eight order52 logarithms save16 rational coordinates. The two order16 logarithms retain their previous coordinate count and exact value.

For the forward witness map, keep all original base coordinates and evaluate the new assignment gates in dependency order. At a replaced logarithm, compute the new powers, Q, and P from its unchanged f and z inputs. The polynomial identity gives the original logarithm output. All later gates therefore receive identical semantic inputs. Keep every original quotient witness, or recompute it where its unchanged domain permits. Every original structural row remains zero.

For the reverse witness map, keep the base coordinates and evaluate the baseline logarithm assignment gates from the new system's f and z inputs. Their output equals the new output by the same identity. Evaluate all baseline assignment gates in dependency order and retain the unchanged quotient witnesses. This reconstructs a baseline solution. Neither map divides by a witness or changes a nonzero-domain obligation. The input coordinate is fixed pointwise.

Each compiler elimination is a constant-linear substitution with the full reverse reconstruction formula in `log-candidate/reduction-certificate.json`. Normalization multiplies rows by nonzero rational constants. Finally, over Q, a sum of squares vanishes exactly when every residual vanishes. These steps preserve the projection onto the input.

## Independent verification

`verify-log.cjs` uses the independently implemented baseline checker, not the builder's polynomial routines. It checks every raw gate equation, replays the compiler certificate, and compares the final residual system. It then expands each actual emitted logarithm circuit in four independent rational symbols f0,f1,z0,z1 and compares it with the original coefficient recurrence and polynomial expression over Q(sqrt(2)). All ten comparisons passed. The receipt is `log-candidate/independent-check.json`.

Reproduction commands, using the supplied Python and Node runtimes:

```text
python prepare_log.py
node log-candidate/build_source.cjs
python census.py log-candidate
node verify-log.cjs
```

Run these commands from this directory, or use absolute script paths. `census.py` accepts the candidate directory as its argument.

The patch is independent of detector and symmetric-coefficient changes, field quotient changes, and later compiler eliminations. It preserves the arithmetic assumptions of the baseline, including the Frei–Tinková qualification.

## Superseded interpolation experiment

The top-level `prepare.py`, `build_source.cjs`, `raw-*.json`, `compiled-ir.json`, and `symmetric-replacement.cjs` describe an earlier exact rational interpolation product tree. It measured 1,238 variables, saving34. The detector worker's fused quadratic convolution saves42 in that same block, so the interpolation experiment is not recommended for integration and its saving must not be added to that worker's saving. No claim of sub1,000 variables is made for this worker's candidate alone.

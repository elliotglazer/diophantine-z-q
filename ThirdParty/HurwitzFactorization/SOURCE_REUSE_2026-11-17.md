# Coarse Hurwitz source-reuse and notice-location addendum

**Unposted proposal for the new coarse consumer only.** No existing source,
notice, branch, PR or proof history is changed by this document. It gives actual
source and notice locations; it is not a licensing, native-check or acceptance
verdict.

## Exact reused sources and preserved original material

The twenty new coarse modules reuse the existing generic QuaternionAlgebra
BaseChange from [PR130](https://github.com/elliotglazer/diophantine-z-q/pull/130),
head `1c1eeabb26315bc9065a2829b08067befbc454a8`, and exact A/B entry + Coordinates
from [PR135](https://github.com/elliotglazer/diophantine-z-q/pull/135),
head `4ead48d4918ac158f765cda889333888a5cd182f`. No second implementation,
namespace, carrier, provider or alias is supplied.

Complete original FLT texts are preserved by that dependency history at:

- `ThirdParty/CloudB4W28FineModuli/LICENSE`, 11,345 bytes,
  SHA256 `746bc52848eabf8765635fe532e0680756a10b18e7b3fb26e7433ab4edf34034`;
- `ThirdParty/CloudB4W28FineModuli/NOTICE.upstream`, 7,128 bytes,
  SHA256 `42b1821f19a6aaa25e6811d22ab8f2fdc6433d4a37bc810b1cfafa5b6dd6b0b6`;
- `ThirdParty/CloudB4W28FineModuli/ATTRIBUTION.upstream.md`, 50,635 bytes,
  SHA256 `698fb76c8d80b2ed78ebd48b271f2ee5815b3654fb8ec5c699b21b16ce0d9698`.

These exact full texts match the original coarse source bank's LICENSE, NOTICE
and ATTRIBUTION beside Reconstruction. The historical bank and its path/source
records remain unchanged. In the new delivery, the copies of the two producer
license files keep their supplied names:
`ThirdParty/HurwitzFactorization/LICENSE.FLT` and `LICENSE.TauCeti`.
The complete FLT NOTICE/ATTRIBUTION are the preserved dependency files named
above, not an invented missing notice or a replacement abbreviated text.

Some inherited source comments say NOTICE/ATTRIBUTION are “alongside”. That
locator describes the original source/bank layout. The current selected
facet-free review cut lists the two coarse licenses and canonical dependency
notices, but **does not list separate coarse NOTICE/ATTRIBUTION files** at those
historical paths. This addendum reconciles the actual locations without editing
those source comments or old notices, and without claiming repository-wide
absence or a new license/compliance ruling.

## Source cuts and compatibility scope

- FLT revision `6e837e75355538c7f80bab5b956861e86c4eacc2`:
  `Definitions/Def_Submodule_FiniteAdeleBox.lean`, source blob
  `f266b98a211105fb86233a4a5149c485e96fc9f5`, supplies the actual ordered
  noncommutative box definitions;
  `P2M/Sol/S_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits.lean`,
  `StabBox:272–358`, blob `dee63ff10cb0a55b3b28896ce1fc56da1f5ef6a8`, supplies
  the actual stabilizer-to-unit/inverse mechanism;
  `P2M/Sol/S_Submodule_finiteAdeleBox_ofFiniteIdele.lean`, blob
  `b160e600371172d07b3d0905b981ceef97617692`, supplies reconstruction passages
  `396–595, 657–673, 741–751, 797–829`.
- Tau Ceti revision `5a01f5fe3621126cccf9ba22e700493cbc7b7156`:
  scalar integral-component, denominator and finite-CRT cuts from
  `RingTheory/DedekindDomain/FiniteAdeleRing/Basic.lean:112–128,206–212,229–308`,
  `RingTheory/DedekindDomain/AdicValuation/Approximation.lean:45–58`, and
  `AdicValuation/Completion.lean:313–324,387–417`. The current scalar proof uses
  actual Mathlib valuation/density/CRT primitives on the same carrier; no Tau
  Ceti topology/Henselian extension world is imported.
- Lean4.35.0 and Mathlib
  `56a005855ea17e0b0958f73ec801ae140b0a1679` remain pinned. All current carriers,
  map equations, integral-coordinate signs and source-compatible hypotheses
  stay genuine; source code is not renamed or cleaned up by this addendum.

The current source epoch is ScalarFiniteAdeles 12,287 bytes SHA256
`e37d4e71a0e05442cbc6b3cc82905b332839b1f833d60c116a8031c2b971a39d`
and ActualFactorization 10,381 bytes SHA256
`e78d19a81897b440d1015a133dab34fef4ebb8aab81ece4245014e6199dd2fc3`.
Historical nineteen-file/R3 and earlier scalar attempts are source/failure
history, not approval of this changed route. The full new literal theorem uses
a whole nonzero Quaternion ℚ witness, not a central scalar, and retains both
actual residual-unit and actual unit-inverse all-prime coordinate clauses.

The BDE review is source/math/producer-record evidence only. The printed type
still has fourteen `⋯` omissions; source literal `@` assignments are separate
complete statement-use evidence, not a fully unelided printer, reviewer-native
or current-head CI/App/Protocol B certificate. Neither this addendum nor its
proposed placement authorizes a new base/ref/PR, readiness, review trigger,
merge, Local2/Hfx, R1 or H10 completion.

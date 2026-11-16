import Mathlib.Tactic
import ZInQKernel.Contrib.OneProof.JonesPall.Representation

/-!
# Exact `hJP`: Jones–Pall's squarefree 1-mod-8 representation

This upstream supplier writes the exact full expanded statement of the fork's
`JonesPallX2Y2Z16`. Its H29 defining module is not yet accepted on upstream main.
No H29 proposition or assembly is copied or implicitly admitted.

The helper proof reuses the canonical common Atlas/Ankeny source provider from
fork PR #36 and upstream draft PR #131, Mathlib's two-square criterion, and the integral quaternion annihilator
descent in this contribution. Shared source/license files remain at the canonical
`LegendreThreeSquares/Atlas.lean` path, byte-identical. Complete licenses and
historical notices are preserved outside Contrib; the current transfer index
names their exact upstream locations and shared-source status.
-/

namespace ZInQ.Contrib.OneProof.JonesPall

/-- Exactly the open `hJP` proposition, without additional hypotheses. -/
theorem jonesPall_proof :
    ∀ n : ℕ, Squarefree n → n % 8 = 1 →
      ∃ x y z : ℤ, (n : ℤ) = x ^ 2 + y ^ 2 + 16 * z ^ 2 :=
  jonesPall_representation

end ZInQ.Contrib.OneProof.JonesPall

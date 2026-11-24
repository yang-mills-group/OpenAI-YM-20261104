import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFiniteWardMatrix
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentFourMaxwellWardReadings

set_option autoImplicit false

noncomputable section
namespace PhysicalMatching.H7IndependentFiledMaxwellWardAction
open H7StandaloneFiniteWardMatrix H7IndependentFourMaxwellWardReadings

theorem filedAction (a b : ℂ) (u : Coords) :
    act (leading a b) u = ![u 0, -u 1, -u 2, a * u 1 + b * u 2 + u 3] := by
  change (leading a b).mulVec u = _
  exact inverseAction a b u

theorem filedTwice (a b : ℂ) (u : Coords) :
    act (leading a b) (act (leading a b) u) = u := by
  rw [filedAction, filedAction]
  funext i
  fin_cases i <;> simp <;> ring

theorem actualTwice (L : Matrix4)
    (rows : ∀ i j, L i j = leading (L 3 1) (L 3 2) i j) (u : Coords) :
    act L (act L u) = u := by
  have h : L = leading (L 3 1) (L 3 2) := funext fun i => funext fun j => rows i j
  calc
    act L (act L u) = act (leading (L 3 1) (L 3 2)) (act (leading (L 3 1) (L 3 2)) u) :=
      congrArg (fun A : Matrix4 => act A (act A u)) h
    _ = u := filedTwice _ _ _

end PhysicalMatching.H7IndependentFiledMaxwellWardAction

import YM.Integration.PhysicalOPEApproximation

/-! Literal complete-product data for physical OPE matching. The family,
input frame and fixed macroscopic detector are unchanged. The comparison
field is supplied explicitly; no estimate or prescription identity is
part of this definition. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.PhysicalMSOPEReadout
open Spec OPE OPE.Orbits PhysMS
open scoped Classical

variable {G : Gauge} {C : Family G} {S : Table C.book}
    (J : ℝ → PhysMS.tower S) {D : ℕ} (U : Detector S D)
    {I : Type} [Fintype I] {d : I → ℕ}
    (v : (i : I) → (Climb.Bel C.book).Field (d i))

/-- Actual normalized complete-product samples minus the samples of an
explicit comparison field, at the unchanged macroscopic detector. -/
def candidateResidual (r : ℝ) (x : I → E4) (z : S.Field D) (i : Fin U.size) : ℂ :=
  whole S x (Frame.born J r v) (positions S (U.listen i)).ofLp
    (fun j => (tags S (U.listen i) j).2) -
      witnessAt S D (U.listen i) z

end YM.Integration.PhysicalMSOPEReadout

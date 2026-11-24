import YM.Integration.WilsonPhysicalPositionHalfRange

/-! Symmetry of the actual reflected Maxwell form follows from positivity on
complex fields, including mixtures of a real arm and an imaginary arm. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionBornInner
open Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot Maxwell Maxwell.Free
open PertExtension.Rigidity.Positive
open scoped Classical BigOperators ComplexOrder
variable {G:Gauge}{C:Family G}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

theorem reflected {d:ℕ}(a:Axis)(v w:D d):
    gram C.labels (hierarchy C.labels) a v w=gram C.labels (hierarchy C.labels) a w v:=by
  let B:=gramC C.labels (hierarchy C.labels) (d:=d) a
  have diagonal (x:D d):(B x x).im=0:=by
    by_cases e:x=0
    · simp [e]
    exact (Complex.lt_def.mp (gramC_pos C.labels (hierarchy C.labels) a e)).2.symm
  have mixed:=diagonal (v+Complex.I • w)
  simp only [map_add,LinearMap.add_apply,map_smulₛₗ,LinearMap.smul_apply,RingHom.id_apply,
    smul_eq_mul,Complex.add_im,Complex.add_re,Complex.mul_im,Complex.mul_re,
    Complex.conj_I,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,diagonal] at mixed
  change (B v w).re=(B w v).re
  linarith

theorem symmetric {d:ℕ}(v w:D d):
    positive C.labels (hierarchy C.labels) v w=positive C.labels (hierarchy C.labels) w v:=by
  unfold positive
  simp only [LinearMap.sum_apply,LinearMap.BilinForm.comp_apply]
  exact Finset.sum_congr rfl fun s _=>reflected (C:=C) 0 _ _

end YM.Integration.WilsonPhysicalPositionBornInner
end

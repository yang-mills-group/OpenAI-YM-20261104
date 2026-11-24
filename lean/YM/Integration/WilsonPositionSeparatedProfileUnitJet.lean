import YM.RG05Readout.Suede.Silver
import YM.RG05Readout.Velvet.Gather

/-! The zeroth physical gauge jet reads a genuine signed coefficient at the identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileUnitJet
open Function Set Filter MeasureTheory Labels Lattice Wilson RG Source Analysis Next.Foundations
open ProjectorNext.Equivariance Trace.Physical Push.Local RG05Readout Address Native
open scoped Classical Topology BigOperators ContDiff
variable {G : Gauge} {n : Side} (F : Labels.Frame G 0) (A : Hol G) (R : RG.Rep G n) (o : Site n)

theorem gauge_zero (J : Jet G) : A.testLinks 0 o J 0 = 1 := by
  funext x
  exact congrFun (A.flat 0 J) _

theorem projection (q : Coefficient F n) (h : q.Format o A R) :
    Germ.projection F A R.p.threshold o q = q.x := by
  have zero (i : ℕ) : Germ.vector F A R.p.threshold o (q.regular i) = 0 := by
    apply Germ.probes_injective F
    intro p
    rw [Germ.vector,Germ.charged F A _ (Germ.computed A (h.smooth i) o (Nat.zero_le _)) p,map_zero]
    have order : p.2.val=0 := by have := p.2.isLt; omega
    rw [Germ.jet,order,iteratedDeriv_zero,Function.comp_apply,gauge_zero]
    exact h.identity_null i
  rw [Germ.projection]
  simp_rw [zero]
  simp

theorem identical {C : Family G} {R : RG.Rep G n} {o : Site n} {κ bill : ℝ}
    {tape : Tape G n} {raw M : Palette C 0} (printed : Printed C 0 R o κ tape raw M bill) : M=raw := by
  cases printed with
  | bind low tail necklace format bounded actual label jet price =>
    rw [label,jet]
    funext i
    obtain rfl := Suede.equal_letter i
    exact projection (C.labels.level 0) C.params R o (low Suede.pip) (format Suede.pip)

end YM.Integration.WilsonPositionSeparatedProfileUnitJet

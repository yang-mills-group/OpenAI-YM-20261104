import YM.Integration.WilsonPhysicalThermalWickLabels

/-! The finite field-count of each genuine chosen label is within the
horizon of its original registered heating stamps. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickRankBound
open Lattice Wilson RG Labels MvPolynomial
open scoped BigOperators Classical
variable {G:Gauge}{d:ℕ}
theorem monomial (m:Key G→₀ℕ):
    (Finsupp.weight bidegree m).2≤(Finsupp.weight bidegree m).1:=by
  induction m using Finsupp.induction_linear with
  | zero=>simp
  | add a b ha hb=>simpa only [map_add,Prod.fst_add,Prod.snd_add] using Nat.add_le_add ha hb
  | single i b=>
    simp [Finsupp.weight_apply,bidegree,generation]
    nlinarith

theorem original (F:Frame G d)(i:F.Index):(F.grades i).2≤d:=by
  have nz:(F.basis i).val≠0:=fun h=>(F.basis.ne_zero i) (Subtype.ext h)
  have entry:∃m,coeff m (F.basis i).val≠0:=by
    by_contra! no
    exact nz (MvPolynomial.ext _ _ fun m=>by simpa only [coeff_zero] using no m)
  obtain ⟨m,hm⟩:=entry
  have weight:=((pure_grade _ _).mp (F.pure i)) hm
  exact (weight ▸ monomial m).trans (F.bound i)

end YM.Integration.WilsonPhysicalThermalWickRankBound
end

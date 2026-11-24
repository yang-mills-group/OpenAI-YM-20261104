import YM.Integration.WilsonPositionProgramTrialSiteGauge
import YM.Pert.Lattice.Action

/-! The site fixing uses the actual divergence and the original color norm,
including the factor of one quarter in the inversion action. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialGaugeAction
open Lattice Gauge FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension PertExtension.Series PertExtension.Orb PertExtension.Chart
open Function Finset FVA2 FVA2.Trans FVA2.Wilson FVA2.Wilson.FP Precision Inherit Push.Loops TreeBasis
open PertExtension.GaussianScore FVA2.GermLaplace
open WilsonPositionProgramTrialSiteGauge (reporter link)
open scoped Classical BigOperators RealInnerProductSpace
variable (G : Gauge) (n : Side)

def mass : ↥(Pert.Orb.Mean G n) →ₗ[ℝ] Module.Dual ℝ ↥(Pert.Orb.Mean G n) where
  toFun f := {
    toFun g := (∑ x : Site n, inner ℝ (f.val x) (g.val x))/2
    map_add' g h := by
      simp [inner_add_right,Finset.sum_add_distrib,add_div]
    map_smul' r g := by
      simp [real_inner_smul_right,←Finset.mul_sum,mul_div_assoc]}
  map_add' f g := by
    ext h
    simp [inner_add_left,Finset.sum_add_distrib,add_div]
  map_smul' r f := by
    ext h
    simp [real_inner_smul_left,←Finset.mul_sum,mul_div_assoc]

def siteLaw : Law ↥(Pert.Orb.Mean G n) := GermLaplace.pd (mass G n)
  (by
    intro f g
    change (∑x:Site n, inner ℝ (f.val x) (g.val x))/2=(∑x:Site n, inner ℝ (g.val x) (f.val x))/2
    congr 1
    exact Finset.sum_congr rfl (fun x _=>real_inner_comm _ _)) (by
    intro f nonzero
    have some : ∃x:Site n, f.val x≠0 := by
      by_contra! h
      exact nonzero (Subtype.ext (funext h))
    obtain ⟨x,hx⟩:=some
    change 0 < (∑ x : Site n, inner ℝ (f.val x) (f.val x))/2
    simp only [real_inner_self_eq_norm_sq]
    exact div_pos (Finset.sum_pos' (fun _ _=>sq_nonneg _) ⟨x,Finset.mem_univ _,sq_pos_of_pos (norm_pos_iff.mpr hx)⟩) (by norm_num))

theorem price (f : ↥(Pert.Orb.Mean G n)) :
    Rates.value (siteLaw G n) f = (∑ x : Site n, ‖f.val x‖^2)/4 := by
  change (∑ x : Site n, inner ℝ (f.val x) (f.val x))/2/2=_
  simp only [real_inner_self_eq_norm_sq]
  ring

theorem original (even : Even n.val) (A : Cone G n) :
    let R := reporter G n even
    let good := WilsonPositionProgramTrialSiteGauge.original G n even
    finances (Repoint.issue G (staple n) R good) (matchW R good (siteLaw G n)) A =
      pricing G n A+Pert.Orb.fixing (link G n even A) := by
  intro R good
  rw [paid_W,price]
  rfl

end YM.Integration.WilsonPositionProgramTrialGaugeAction

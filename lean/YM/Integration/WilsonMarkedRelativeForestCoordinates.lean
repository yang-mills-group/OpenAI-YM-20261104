import YM.Integration.WilsonMarkedRelativeForestChart
import YM.Next.STATIONARY.Lift.Pathways

/-! The actual flattened absolute link coordinates of the relative forest
chart, including its scalar coupling and the Haar free-link variables. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedRelativeForestCoordinates
open Function Filter Finset Lattice Exterior Stationary Tree Work.F03
open WilsonMarkedRelativeForestChart
open scoped Topology ContDiff Classical

variable {G:Gauge} {c f:Side} {g:Ratio c f}

def field (F:Forest g) (z:ChartVars F G):Stationary.Link G f:=
  (Stationary.arm G f 1).symm (axisLog F z)

theorem contraction (n:Side) (z:Bid.Dir G n):
    ‖(Stationary.arm G n 1).symm z‖≤‖z‖:=by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2
  intro i
  exact (PiLp.norm_apply_le (z (i.1,i.2.1)) i.2.2).trans (norm_le_pi_norm z _)

theorem smooth (F:Forest g):ContDiffAt ℝ ω (field (G:=G) F) 0:=
  (Stationary.arm G f 1).symm.contDiff.contDiffAt.comp 0 (inclusion_smooth F).snd

theorem bound (F:Forest g)(r:ℕ):
    ‖iteratedFDeriv ℝ r (field (G:=G) F) 0‖ ≤ ‖iteratedFDeriv ℝ r (localLog G) 0‖:=by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro v
  let L:Bid.Dir G f→L[ℝ]Stationary.Link G f:=(Stationary.arm G f 1).symm.toContinuousLinearMap
  have h:ContDiffAt ℝ ∞ (axisLog (G:=G) F) 0:=((inclusion_smooth F (G:=G)).snd).of_le le_top
  have formula:=DFunLike.congr_fun (L.iteratedFDeriv_comp_left h (by exact_mod_cast le_top)) v
  change ‖iteratedFDeriv ℝ r (L ∘ axisLog F) 0 v‖≤_
  rw [formula]
  exact (contraction f _).trans (full F r v)

theorem actual (F:Forest g):
    (fun z:ChartVars F G=>Stationary.input G f (field F z))=ᶠ[𝓝 0]live F:=by
  simpa only [field,Stationary.input,ContinuousLinearEquiv.apply_symm_apply] using
    (inclusion_works F (G:=G))

def joint (F:Forest g) (z:ℝ×ChartVars F G):ℝ×Stationary.Link G f:=(z.1,field F z.2)

theorem joint_smooth (F:Forest g):ContDiffAt ℝ ω (joint (G:=G) F) 0:=
  contDiffAt_fst.prodMk ((smooth F).comp (f:=(Prod.snd:ℝ×ChartVars F G→ChartVars F G)) 0 contDiffAt_snd)

end YM.Integration.WilsonMarkedRelativeForestCoordinates
end

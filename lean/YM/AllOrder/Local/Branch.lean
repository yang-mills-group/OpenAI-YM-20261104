import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.IsolatedZeros
import YM.AllOrder.Local.Taylor
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Lens

/-!
# Unitary origin for taking log of flat jet perturbation.

Keep normalization after smearing. No factor depending on total
normalizer `Ω`/volume. Use price on reduced log at the origin, then
Taylor comp rule or the full jet receipt.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Local.Log
open Function Filter Set Metric Lattice Wilson RG Gauge Pressure Push.AbsoluteSums
open ConnectedActivityE6 Blaze Brush PhysicalNext Repeat Lantern Poll
open scoped Topology Classical ContDiff
variable {a b C K D J t : ℝ} {j : ℕ}

abbrev slope1 (z:ℝ):= dslope Real.log 1 z
lemma price1 (j:ℕ) {a b:ℝ} (ha:0<a): ∃ C : ℝ, 0<C ∧ ∀ x:ℝ,x∈Icc a b→ Brush j C 1 (slope1) x := by
  refine Brush.compact isCompact_Icc fun x hx=> ?_
  rcases eq_or_ne x 1 with h|h
  · subst x; obtain ⟨p,hp⟩:= analyticAt_log zero_lt_one; exact hp.has_fpower_series_dslope_fslope.analyticAt.contDiffAt
  have ht : 0<x:= ha.trans_le hx.1
  refine (show ContDiffAt ℝ (↑j) (slope Real.log 1) x from ?_).congr_of_eventuallyEq (dslope_eventuallyEq_slope_of_ne Real.log h)
  rw [show slope Real.log 1=(fun x=> (Real.log x-Real.log 1)/(x-1)) from funext fun z=> slope_def_field ..]; exact ((analyticAt_log ht).contDiffAt.sub contDiffAt_const).div (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.mpr h)

lemma priceInv (j:ℕ) : ∃ C : ℝ,0<C ∧ Brush j C 1 (fun z:ℝ=> z⁻¹) 1 := by
  obtain ⟨C,hC,hv⟩:= Brush.neighborhood (1:ℝ) (k:=j) (show ContDiffAt ℝ (↑j) (fun z:ℝ=> z⁻¹) 1 from contDiffAt_id.inv one_ne_zero)
  exact ⟨C,hC,hv.self_of_nhds⟩

def t2 (j:ℕ) (a:ℝ):= a*(1+(1+1))^j

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E→ℝ}
lemma same_price (hg : Brush j t 1 (f-g) 0) (he : Brush j C 1 g 0) (h : 0 < f 0) (hx:g 0=1)
    (hv : Brush j K 1 (fun z:ℝ=>z⁻¹) 1) (hh : Brush j J 1 slope1 (f 0)) :
    let w := t2 j (t*clump j C K)
    Brush j (t2 j (w * clump j (1+w) J)) 1 (Real.log ∘ f-Real.log ∘ g) 0 := by
  intro w
  let i:E→ℝ:= (f-g)*fun x=> (g x)⁻¹; let F:=1+i
  have hF x (h:g x≠0) : F x= f x / g x := by change 1+(f x-g x)*(g x)⁻¹=f x/g x; field_simp; ring
  have hh' : Brush j w 1 i 0 := (hg.paints (composite he (hx.symm ▸ hv))).trim
  have ht: Brush j 1 1 (1:E→ℝ) 0:= by simpa only [norm_one] using! Brush.certified (x:=(0:E)) (k:=j) zero_le_one (1:ℝ)
  have he': Brush j (1+w) 1 F 0:= ht.gathering hh'
  have hs: F 0=f 0:= by rw [hF _ (hx.symm ▸ one_ne_zero),hx,div_one]
  refine ((hh'.paints (composite he' (hs.symm ▸ hh))).trim).shimmy ?_
  have hfg : ContinuousAt f 0:= by rw [show f=f-g+g from (sub_add_cancel ..).symm]; exact hg.smooth.continuousAt.add he.smooth.continuousAt
  filter_upwards [hfg.eventually_ne h.ne', he.smooth.continuousAt.eventually_ne (hx.symm ▸ one_ne_zero)] with x ha hb
  have hk:= sub_smul_dslope Real.log 1 (F x); rw [Real.log_one,sub_zero, show F x-1=i x by change 1+i x-1=_; ring] at hk
  change Real.log _-Real.log _= i x*_ ; change i x*slope1 (F x)= Real.log _ at hk; rw [←Real.log_div ha hb]; change _=i x*slope1 (F x); rw [hk,←hF _ hb]

end YM.AllOrder.Local.Log

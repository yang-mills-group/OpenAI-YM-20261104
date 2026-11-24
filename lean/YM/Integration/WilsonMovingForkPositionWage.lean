import YM.Integration.WilsonMovingForkGridPrice
import YM.Integration.WilsonMovingForkFarCost
import YM.Integration.WilsonThermometerWeakPairClock

/-! The original spectral-tube salaries for a finite mixed-radius panel,
in units of the near scale. The worst relative dilation occurs only once
per actual incoming color. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkPositionWage
open Function Filter Finset Set Metric Extraction Table Spec PhysMS Trace Trace.Pilot Climb
open GapsContact GapsContact.Ascent FVA2 FVA2.Register MS MS.Land RG17 WilsonPositionHomogeneousFrame
open FVA2.Scale PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {H:(Bel R.family.book).Hierarchy}(J:ℝ→tower S)(Z:WilsonPrescription G)

theorem original {g:ℝ→ℝ}(simple:G.Simple)(hg:Coupling G g)(lead:Leading F J)
    (owed:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d){n:ℕ}(d:Fin n→ℕ)(B:ℕ):
    ∃D:ℝ,0 ≤ D ∧ ∀ᶠ r in trail,∀ρ:Fin n→ℝ,(∀i,r ≤ ρ i ∧ ρ i ≤ r/(g r)^B) →
      ∀v:(i:Fin n)→Free R.family (d i),
      (∏i,Ascent.cost F (d i) r (homogeneous F J Z (ρ i) (d i) (v i)))*(g r)^(B*(∑i,(d i+1)))
        ≤ D*(∏i,‖v i‖):=by
  choose C cn charged using fun i=>WilsonMovingForkFarCost.original F J Z lead owed simple (d i)
  choose δ tiny admits using fun i=>mem_nhdsGT_iff_exists_Ioc_subset.mp (charged i)
  refine ⟨∏i,C i,prod_nonneg (fun i _=>cn i),?_⟩
  have reaches:Tendsto (fun r=>r/(g r)^B) trail trail:=WilsonThermometerWeakPairClock.small simple g hg B
  have fit:∀ᶠr in trail,∀i,r/(g r)^B ≤ δ i:=eventually_all.mpr (fun i=>
    reaches.eventually ((ge_mem_nhds (tiny i)).filter_mono nhdsWithin_le_nhds))
  filter_upwards [fit,hg.positive,self_mem_nhdsWithin] with r window gp (rp:0<r)
  intro ρ span v
  have entry(i:Fin n):Ascent.cost F (d i) r (homogeneous F J Z (ρ i) (d i) (v i))*
      (g r)^(B*(d i+1)) ≤ C i*‖v i‖:=by
    have pos:=rp.trans_le (span i).1
    let s:=r/ρ i
    have sp:0<s:=div_pos rp pos
    have one:s ≤ 1:=(div_le_one pos).mpr (span i).1
    have below:(g r)^B ≤ s:=by
      apply (le_div_iff₀ pos).mpr
      simpa only [mul_comm] using (le_div_iff₀ (pow_pos gp _)).mp (span i).2
    have fee:=admits i ⟨pos,(span i).2.trans (window i)⟩ s ⟨sp,one⟩ (v i)
    have coordinate:(s*ρ i)=r:=div_mul_cancel₀ r pos.ne'
    have engineering:-(d i:ℝ)-1=-((d i+1:ℕ):ℝ):=by push_cast;ring
    rw [coordinate,engineering,Real.rpow_neg sp.le,Real.rpow_natCast] at fee
    have gain:(g r)^(B*(d i+1)) ≤ s^(d i+1):=by
      rw [pow_mul];exact pow_le_pow_left₀ (pow_nonneg gp.le _) below _
    have wallet:0≤Ascent.cost F (d i) r (homogeneous F J Z (ρ i) (d i) (v i)):=Ascent.cost_pos _ _ _ _
    exact ((mul_le_mul_of_nonneg_left gain wallet).trans (mul_le_mul_of_nonneg_right fee (pow_nonneg sp.le _))).trans_eq
      (by field_simp)
  have whole:=prod_le_prod (s:=univ) (g:=fun i=>C i*‖v i‖)
    (fun i _=>mul_nonneg (Ascent.cost_pos ..) (pow_nonneg gp.le _)) (fun i _=>entry i)
  simpa only [prod_mul_distrib,Finset.prod_pow_eq_pow_sum,←Finset.mul_sum] using! whole

end YM.Integration.WilsonMovingForkPositionWage

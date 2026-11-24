import YM.Integration.FVA1Physical.Wilson.FluctuationChart
import YM.MSbar.Geneva.Snow
import YM.Next.SCHEDULE.Support

/-! The thermal field used as a local forest copy is completely clear of
plaquette flags. The true field sharing the collar with it is clear on the
collar, regardless of the period or the curvature outside it. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Filter MeasureTheory Set Finset Lattice RG YM.Wilson Precision Exterior
open MSbar MSbar.Midpoint MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Mosaic
open Push.Uniform Pressure YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology
variable {G:Gauge} {n:Side}

theorem chart_clear (J:Voice G) (cle:Clear G J) {t v g:ℝ} (hg:0 < g)
    (rad:shade G*v ≤ J.r) (ht:J.C*(shade G*v) ≤ t/4) (W:Config G n)
    (good:W∈regularInputs g (v/g)) : flags t W=∅ := by
  let Z:=g • chartLog g W
  have hz:‖Z‖ ≤ v := by
    dsimp only [Z]
    rw [norm_smul,Real.norm_of_nonneg hg.le]
    exact (mul_le_mul_of_nonneg_left good.2 hg.le).trans_eq (by field_simp)
  have same:palace Z=W := recover_chartLog hg.ne' W (Set.mem_univ_pi.mp good.1)
  apply voids (r:=t) _ le_rfl
  intro e _
  have bound:= (pain Z e).trans (mul_le_mul_of_nonneg_left hz (shade_pos G).le)
  change G.chord (W e) ≤ t/4
  rw [←same,show palace Z e=G.lieExp (Wave.panel G n Z e) from mul_one _]
  exact ((cle.small _ (bound.trans rad)).2.trans (mul_le_mul_of_nonneg_left bound (zero_le_one.trans cle.cost))).trans ht

theorem thermal_flags (P:Palisade) (J:Voice G) (cle:Clear G J) (D:ℝ) :
    ∀ᶠ y:ℝ in atTop, ∀ {n:Side} {g:ℝ}, 0 < g → ∀ W:Config G n,
      W∈regularInputs g (D*room y/g) → flags (temp y) W=∅ := by
  have small:Tendsto (fun y:ℝ=>shade G*D*room y) atTop (𝓝 0):=by
    simpa only [zero_mul,zero_add] using hotel_physical_small P J 0 (shade G*D)
  filter_upwards [small.eventually (ge_mem_nhds cle.depth),
    fluctuation_below_skies (4*J.C*shade G*D),Geneva.music (tendsto_id: Tendsto (fun y:ℝ=>y) atTop atTop) 1 1,
    eventually_gt_atTop (1:ℝ)] with y rad scale poly high
  intro n g hg W good
  have ht:skies y ≤ temp y := by
    have logp:(Real.log y)^2 ≤ bbP y:=by simpa only [id_eq,one_mul,pow_one,hatW,Alto.flurry] using poly
    unfold skies distance
    rw [Real.rpow_neg (zero_lt_one.trans high).le,←Real.sqrt_eq_rpow,temp_shape]
    calc (Real.sqrt y)⁻¹*Real.log y*Real.log y = cue y*(Real.log y)^2 := by unfold cue;ring
         _ ≤ _ := mul_le_mul_of_nonneg_left logp (inv_nonneg.mpr (Real.sqrt_nonneg _))
  exact chart_clear J cle hg (by linarith only [rad]) (by linarith only [scale,ht]) W good

theorem thermal_parent_flags (P:Palisade) (J:Voice G) (cle:Clear G J) (D:ℝ) (B:Patch) :
    ∀ᶠ x:ℝ in atTop, ∀ {n:Side} {g:ℝ}, 0 < g → ∀ W:Config G n,
      W∈regularInputs g (D*room (tip G B.L x)/g) → flags (temp x) W=∅ := by
  have small:Tendsto (fun y:ℝ=>shade G*D*room y) atTop (𝓝 0):=by
    simpa only [zero_mul,zero_add] using hotel_physical_small P J 0 (shade G*D)
  let rise:=Work.E09.betaF_growth G B.L
  filter_upwards [rise.eventually (small.eventually (ge_mem_nhds cle.depth)),
    rise.eventually (fluctuation_below_skies D),tale B J cle,rise.eventually_gt_atTop 1]
    with x rad width coarse high
  intro n g hg W good
  let y:=tip G B.L x
  have hJ: 0 ≤ J.C*shade G:=mul_nonneg (zero_le_one.trans cle.cost) (shade_pos G).le
  have hs:0 ≤ skies y := by
    unfold skies distance
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans high).le _) (Real.log_nonneg high.le)) (Real.log_nonneg high.le)
  have h:J.C*shade G*(D*room y) ≤ J.C*shade G*skies y := mul_le_mul_of_nonneg_left width hJ
  change 8*J.C*shade G*skies y ≤ temp x at coarse
  exact chart_clear J cle hg (by linarith only [rad]) (by linarith only [h,coarse,mul_nonneg hJ hs]) W good

theorem copied_collar {U W:Config G n} {z:Site n} {m:ℕ} {t:ℝ} (clear:flags t W=∅)
    (agree:Agrees (halo (m+8) {z}) U W) : Healthy t (halo m {z}) U := by
  have inside:inspected (halo m {z}) ⊆ halo (m+8) {z}:=by
    intro e he
    obtain ⟨s,hs,d⟩:=halo_spec.mp (Next.Scheduling.flag_layer _ he)
    obtain ⟨q,hq,d'⟩:=halo_spec.mp hs
    exact halo_spec.mpr ⟨q,hq,(separation_triangle q s e).trans (Nat.add_le_add d' d)⟩
  have h:=flags_agree t U W (halo m {z}) (agrees_mono agree inside)
  unfold Healthy
  rw [Finset.disjoint_iff_inter_eq_empty,h,clear]
  simp

end YM.Integration.FVA1Physical.Round2.Curvature

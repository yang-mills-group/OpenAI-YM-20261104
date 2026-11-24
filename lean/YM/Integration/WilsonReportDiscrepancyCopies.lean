import YM.Integration.WilsonCutoffDiscrepancyPrice
import YM.RG16.Unmasked.Pace

/-! Adjacent reporting scales and any finite roster of independently priced
signed source columns use a common subexponential allowance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportDiscrepancyCopies
open Function Set Filter Lattice RG RG16 RG16.Literal Push.RelayDifference
open WilsonCutoffDiscrepancyPrice
open scoped Topology BigOperators
variable {G : Gauge} (C : Family G)

theorem monotone (E : ℕ → ℝ) (h : FullVolume.Sluggish C (fun i => E i.1)) :
    Monotone (room C E) := by
  intro i j hij
  apply csSup_le ⟨1,mem_insert ..⟩
  rintro t (ht|⟨N,rfl⟩)
  · rw [ht]; exact (heard C E h j).1
  · apply le_trans _ ((heard C E h j).2 N)
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonpos_left _ (by norm_num [gamma])
    apply max_le_max le_rfl
    exact sub_le_sub_left ((OPE.scale_mono C.S).monotone hij) _

theorem finite {ι : Type*} (s : Finset ι) (E : ι → ℕ → ℝ)
    (h : ∀ i∈s, FullVolume.Sluggish C (fun j => E i j.1)) {δ : ℝ} (hd : 0<δ) :
    ∃ K : ℝ, 1≤K ∧ ∀ k, (∏ i∈s, room C (E i) k) ≤ K*Real.exp (δ*C.S.scale k) := by
  classical
  induction s using Finset.induction_on generalizing δ with
  | empty =>
    refine ⟨1,le_rfl,fun k=>?_⟩
    simp only [Finset.prod_empty,one_mul]
    exact Real.one_le_exp (mul_nonneg hd.le (Shoot.scale_nn C.path.levels k))
  | @insert i s hi ih =>
    obtain ⟨a,ha,pa⟩:=presold C (E i) (h i (Finset.mem_insert_self i s)) (half_pos hd)
    obtain ⟨b,hb,pb⟩:=ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) (half_pos hd)
    refine ⟨a*b,one_le_mul_of_one_le_of_one_le ha hb,fun k => ?_⟩
    rw [Finset.prod_insert hi]
    have pos : 0≤∏ j∈s, room C (E j) k := Finset.prod_nonneg (fun j hj =>
      zero_le_one.trans (heard C (E j) (h j (Finset.mem_insert_of_mem hj)) k).1)
    apply (mul_le_mul (pa k) (pb k) pos (mul_nonneg (zero_le_one.trans ha) (Real.exp_pos _).le)).trans_eq
    rw [mul_mul_mul_comm,← Real.exp_add]
    congr 2; ring

theorem grade (hG : G.Simple) (E : ℕ → ℝ)
    (h : FullVolume.Sluggish C (fun i => E i.1))
    (pace : ∀ k, ((C.S.block k).val:ℝ) ≤ Real.log (Lambda C.path.levels k))
    (q : ℕ) {δ : ℝ} (hd : 0<δ) : ∀ᶠ k in atTop,
    (room C E (k+1)/room C E k)^q ≤ Real.exp (δ*(C.path.levels.clock.coverSize k:ℝ)) := by
  let β:= C.path.levels.clock.hatBeta
  have ht : Tendsto β atTop atTop := tendsto_atTop_add_const_left _ _
    (C.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
  filter_upwards [(Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop (2*(q:ℝ)*gamma/δ)] with k hg hδ
  change 2≤Real.log (β k) at hg
  change 2*(q:ℝ)*gamma/δ ≤ Real.log (β k) at hδ
  have hg' : 0≤Real.log (β k) := by linarith
  have hγ : 0≤gamma := by norm_num [gamma]
  have hpos : 0<room C E k := zero_lt_one.trans_le (heard C E h k).1
  have hr : room C E (k+1)/room C E k ≤ Real.exp (gamma*Real.log ((C.S.block k).val:ℝ)) :=
    (div_le_iff₀ hpos).mpr ((adjacent C E h k).trans_eq (mul_comm ..))
  apply (pow_le_pow_left₀ (div_nonneg (zero_le_one.trans (heard C E h _).1) hpos.le) hr q).trans
  rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
  have hu := (Real.log_le_self (Nat.cast_nonneg (C.S.block k).val)).trans
    ((pace k).trans (Real.log_le_self (lambda_pos C k).le))
  change _ ≤ 2+Real.log (β k) at hu
  have hv : Real.log ((C.S.block k).val:ℝ) ≤ 2*Real.log (β k) := by linarith
  have haz := mul_le_mul_of_nonneg_left hv (mul_nonneg (Nat.cast_nonneg q) hγ)
  have hsz := mul_le_mul_of_nonneg_right ((div_le_iff₀ hd).mp hδ) hg'
  have hc : (Real.log (β k))^2 ≤ (C.path.levels.clock.coverSize k:ℝ) := Nat.le_ceil _
  exact le_trans (by linarith only [haz,hsz] : (q:ℝ)*(gamma*Real.log ((C.S.block k).val:ℝ))
    ≤ δ*(Real.log (β k))^2) (mul_le_mul_of_nonneg_left hc hd.le)

end YM.Integration.WilsonReportDiscrepancyCopies

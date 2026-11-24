import YM.FullVolume.Nectar.Emits

/-! The same native positive coefficient tariff pays the value and the
divided difference on a short chart segment. There is no factor counting
the field sites, labels, or coefficient list. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility
open RG Wilson FullVolume.Ray FullVolume.Ray.Weigh PhysicalNext.Repeat.Luna
open PhysicalNext.Repeat.Jams Push Push.AbsoluteSums GridApprox.Nil
open MergeProof MergeProof.Accent Lattice Marker
open scoped BigOperators Classical

theorem scout_from_tip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q c : ℝ} {f : ℝ→E} (h : Scout q f c) (s : sun) :
    ‖f s.val-f 0‖ ≤ |s.val| * c := by
  obtain ⟨b,hb,series⟩ := h.scored
  have at0 : (0:ℝ)∈sun := by constructor <;> norm_num
  have sum := (series s.val s.property).sub (series 0 at0)
  let u (k : ℕ) := (s.val/q)^k • b k - (0/q)^k • b k
  have hq : 0<q := zero_lt_one.trans_le h.ray
  have ratio : |s.val/q|≤|s.val| := by
    rw [abs_div,abs_of_pos hq]; exact div_le_self (abs_nonneg _) h.ray
  have term (k : ℕ) : ‖u k‖ ≤ |s.val| * ‖b k‖ := by
    cases k with
    | zero => simp [u]; positivity
    | succ k =>
      simp only [u,zero_div,zero_pow (Nat.succ_ne_zero k),zero_smul,sub_zero,
        norm_smul,Real.norm_eq_abs,pow_succ,abs_mul,abs_pow]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) (ratio_le h.ray s.property))).trans ratio
  have budget : SumBudget (fun k=> ‖u k‖) (|s.val| * c) :=
    budget_mono (budget_scale (abs_nonneg s.val) hb) (fun _=>norm_nonneg _) term
  rw [← sum.tsum_eq]
  exact (norm_tsum_le_tsum_norm budget.2.1).trans budget.2.2

private theorem same_tariff {q c θ : ℝ} {f : sun→ℂ}
    (h : Scout q (phraseS f) c) (s : sun) (hθ : 0<θ) (short : |s.val|≤θ) :
    ‖f tip‖≤c ∧ ‖f s-f tip‖/θ≤c := by
  have at0 := h.held tip.property
  rw [phrased] at at0
  have d := scout_from_tip h s
  change ‖phraseS f s.val-phraseS f tip.val‖≤_ at d
  rw [phrased,phrased] at d
  exact ⟨at0,(div_le_iff₀ hθ).mpr (by
    rw [mul_comm c]; exact d.trans (mul_le_mul_of_nonneg_right short h.nonneg))⟩

theorem marked_secant {I V Y : Type} [DecidableEq V] {B : Census V}
    {n : Side} {b : ℕ} {X : I→Support n} {w : V→ℝ} {q e C θ : ℝ}
    {F : sun→I→Y→Poly B} (h : Ankh w q F b X e C)
    (s : sun) (hθ : 0<θ) (short : |s.val|≤θ) :
    ∃ (a : I→ℝ) (v : I→Sheet B), Summable a ∧ Ac.Hit X b a e C ∧
      (∀ i, 0≤v i ∧ wordsPrice w (v i)≤a i) ∧
      ∀ i U S, ‖(F tip i U).part S‖≤v i S ∧
        ‖(F s i U).part S-(F tip i U).part S‖/θ≤v i S := by
  obtain ⟨a,ha,hit,price⟩ := h.beam
  choose v pos scout bill using fun i => (price i).2
  exact ⟨a,v,ha,hit,fun i=>⟨pos i,bill i⟩,
    fun i U S=>same_tariff (scout i S U) s hθ short⟩

theorem single_secant {I : Type} {G : Gauge} {n : Side} {X : I→Support n}
    {F : sun → I → Config G n → ℂ} {B : BudgetPoint} {q e C θ : ℝ}
    (h : RollsUp B X F q e C) (s : sun) (hθ : 0<θ) (short : |s.val|≤θ) :
    ∃ a : I→ℝ, Brill B X a e C ∧ ∀ i U, ‖F tip i U‖≤a i ∧
      ‖F s i U-F tip i U‖/θ≤a i := by
  obtain ⟨a,bill,scout⟩ := h.funds
  exact ⟨a,bill,fun i U=>same_tariff (scout i U) s hθ short⟩

end YM.Integration.InletSusceptibility

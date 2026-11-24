import YangMills.WilsonProof.NativeSupport.CalibratedCorridor

/-! Extract normalized connected coefficients and their support-resolved
absolute bill from the calibrated terminal read. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open Function Finset MeasureTheory Lattice RG Wilson Marker
open MergeProof MergeProof.Accent Extra.Multi Extra.Trajectories Push.GridApprox.Nil
open RGGapR2
open scoped Classical BigOperators

variable {V : Type} [Fintype V] [DecidableEq V] {G : Gauge} {n : Side}

omit [Fintype V] in
private lemma empty_field (B : Census V) :
    field (fun _ : Box n => (0 : Poly B)) ∅ = 1 := by
  classical
  unfold field
  rw [sum_eq_single ∅]
  · simp [grid, Pattern]
  · intro b _ hb
    unfold grid
    split
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hb
      exact prod_eq_zero hi rfl
    · rfl
  · simp

omit [Fintype V] in
private lemma flow_at_pin {B : Census V} {o : V → Site n} {t : ℝ}
    {i : Box n} {K : Config G n → Poly B} (h : Flow o i K t)
    {U : Config G n} (clean : flags t U = ∅) : K U = 0 := by
  by_contra hK
  obtain ⟨he, ⟨x,hx⟩, -⟩ := h.permits U hK
  rw [clean, inter_empty] at he
  exact notMem_empty x (he ▸ hx)

theorem calibrated_terminal (R : Rep G n) (B : Census V)
    (X : Config G n → Poly B) (o : V → Site n) (w : V → ℝ) (a cap : ℝ)
    {b c : ℝ} (vac : R.activities.Valid R.p b c)
    (h : Rough.Freight R B X o w a cap) (hw : ∀ i, 0 ≤ w i) :
    ∃ H : Support n → Poly B,
      (∀ Z, (H Z).part B.quiet = 0) ∧
      (∀ Z s, (H Z).part s ≠ 0 → s.val.image o ⊆ Z) ∧
      (X 1).part B.quiet = (Real.exp (R.exponent 1) : ℂ) ∧
      ((X 1).part B.quiet)⁻¹ • X 1 = Poly.pass (∑ Z, H Z) ∧
      ∀ i : V, ∑ Z : Support n,
        (∑ s ∈ univ.filter (fun s : B.Mode => i ∈ s.val),
          Poly.toll w s * ‖(H Z).part s‖) * Real.exp (a * coverNumber R.p.B Z) ≤ cap := by
  classical
  obtain ⟨H,K, ledger, cost, -, hX⟩ := h
  have clean := UVNext.CouplingReset.flags_one (G:=G) (n:=n) R.p
  have gas : (fun i : Box n => (exclaim R.activities B+K) i (1 : Config G n)) =
      fun _ => 0 := by
    funext i
    change exclaim R.activities B i 1 + K i 1 = 0
    rw [flow_at_pin (granular R.activities R.p B (o:=o) vac i) clean,
      flow_at_pin (ledger.flag i).1 clean, add_zero]
  have pin : X 1 = (Real.exp (R.exponent 1) : ℂ) • Poly.pass (∑ Z, H Z 1) := by
    rw [hX, play, clean, gas, empty_field, mul_one]
  have silent := fun Z => (ledger.exp Z).sil (1 : Config G n)
  have q : (X 1).part B.quiet = (Real.exp (R.exponent 1) : ℂ) := by
    rw [pin, Poly.part_smul, Poly.pass_part _ (by simp only [Poly.part_sum, silent, sum_const_zero]),
      mul_one]
  have paid_root (Z : Support n) (s : B.Mode) := (ledger.exp Z).toBorne.place s (1 : Config G n)
  refine ⟨fun Z => H Z 1, silent, paid_root, q, ?_, ?_⟩
  · rw [q, pin, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)), one_smul]
  · intro i
    obtain ⟨v, -, hit, loci⟩ := cost
    apply le_trans _ (Budget.cap (hit (o i)) univ)
    apply Finset.sum_le_sum
    intro Z _
    change _ ≤ if o i ∈ Z then v Z * Real.exp (a * coverNumber R.p.B Z) else 0
    split
    · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      obtain ⟨sheet, sheet_nonneg, bound, bill⟩ := loci Z
      apply le_trans _ bill
      unfold wordsPrice
      apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg
        (filter_subset (fun s : B.Mode => i ∈ s.val) univ) ?_)
      · apply Finset.sum_le_sum
        intro s _
        exact mul_le_mul_of_nonneg_left (bound 1 s) (Finset.prod_nonneg fun j _ => hw j)
      · intro s _ _
        exact mul_nonneg (Finset.prod_nonneg fun j _ => hw j) (sheet_nonneg s)
    · rename_i outside
      have zero (s : B.Mode) (hs : s ∈ univ.filter (fun s : B.Mode => i ∈ s.val)) :
          (H Z 1).part s = 0 := by
        by_contra hn
        exact outside (paid_root Z s hn (mem_image_of_mem o (mem_filter.mp hs).2))
      rw [sum_eq_zero (fun s hs => by rw [zero s hs, norm_zero, mul_zero]), zero_mul]

end YM.Integration.InletSusceptibility

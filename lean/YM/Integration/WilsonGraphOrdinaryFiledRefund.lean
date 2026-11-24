import YM.Integration.WilsonGraphOrdinaryFiledInputs

noncomputable section
namespace YM.Integration.AppointedOrdinaryRefund
set_option maxRecDepth 18000
set_option maxHeartbeats 5000000
open YangMills YangMills.Matching
open YM.XSpace YM.XSpace.Normalize YM.FVA2 YM.FVA2.Dframe
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Project YM.FVA2.O.Canon
open YM.FVA2.Scale YM.Answer.ContinuumLimit PowerSeries
open scoped BigOperators Classical

variable {G : YM.Gauge} {n h : ℕ}

abbrev inputWeight (F : Scale.Frames G) (s : Scan G n) (w : LivesP s) (e : Fin n → ℕ) : ℂ :=
  ∏ i, coeff (e i) (cue (seats F) (s i) (own (w i)))

private theorem moveThree {A B C D X : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [AddCommMonoid X] (z : A → B → C → D → X) :
    (∑ a, ∑ b, ∑ c, ∑ d, z a b c d) = ∑ b, ∑ c, ∑ d, ∑ a, z a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

/-- One true output coordinate of the full signed receipt on a specified marked input word. -/
theorem scalar (F U : Scale.Frames G) (c : PowerSeries ℂ) (f : ℕ → ℝ)
    (hc : ∀ i, coeff i c = (f i : ℂ)) (hf : f 0 = 0) (L : Draft G n)
    (s : Scan G n) (t : Toon G h) (k : ℕ) :
    coeff k (O.Project.refund (seats F) (seats U) c L s (Dframe.flash t)) =
      ∑ e : Fin n → Fin (k+1), ∑ j : Fin (k+1), ∑ b : Fin (k+1),
        if b.val + (∑ i, (e i).val) ≤ k then
          (couplingPower f j.val (k-(b.val+∑ i, (e i).val)) : ℂ) *
            ∑ z : Grade G t.1.val,
              (∑ w : LivesP s, inputWeight F s w (fun i => (e i).val) *
                coeff j.val (L (decode s w) (own z))) * coeff b.val (seats U t.1.val z t.2)
        else 0 := by
  let term (z : Grade G t.1.val) (w : LivesP s) (e : Fin n → Fin (k+1)) (j b : Fin (k+1)) : ℂ :=
    if b.val + (∑ i, (e i).val) ≤ k then
      (couplingPower f j.val (k-(b.val+∑ i, (e i).val)) : ℂ) *
        (coeff b.val (seats U t.1.val z t.2) * inputWeight F s w (fun i => (e i).val)) *
        coeff j.val (L (decode s w) (own z))
    else 0
  calc
    _ = ∑ z : Grade G t.1.val, ∑ w : LivesP s,
        coeff k (((∏ i, cue (seats F) (s i) (own (w i))) * (L (decode s w) (own z)).subst c) *
          seats U t.1.val z t.2) := by
      change coeff k (∑ z : Grade G t.1.val, (∑ w : LivesP s,
        (∏ i, cue (seats F) (s i) (own (w i))) * (L (decode s w) (own z)).subst c) *
        seats U t.1.val z t.2) = _
      simp only [Finset.sum_mul, map_sum]
    _ = ∑ z, ∑ w, ∑ e, ∑ j, ∑ b, term z w e j b :=
      Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ =>
        AppointedOrdinaryFiledInputs.withOutput (fun i => cue (seats F) (s i) (own (w i)))
          (seats U t.1.val z t.2) c (L (decode s w) (own z)) f hc hf k
    _ = ∑ z, ∑ e, ∑ j, ∑ b, ∑ w, term z w e j b :=
      Finset.sum_congr rfl fun z _ => moveThree (term z)
    _ = ∑ e, ∑ j, ∑ b, ∑ z, ∑ w, term z w e j b :=
      moveThree (fun z e j b => ∑ w, term z w e j b)
    _ = _ := by
      refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun b _ => ?_
      by_cases fits : b.val + (∑ i, (e i).val) ≤ k
      · simp only [term, fits, if_true, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => by ring
      · simp [term, fits]

/-- Assemble the entire cap-h field, acting by its actual outgoing coefficient matrix. -/
theorem vector (F U : Scale.Frames G) (HU : Civil U) (c : PowerSeries ℂ) (f : ℕ → ℝ)
    (hc : ∀ i, coeff i c = (f i : ℂ)) (hf : f 0 = 0) (L : Draft G n)
    (s : Scan G n) (h k : ℕ) :
    AppointedNullaryRefund.assemble G h (fun t =>
      coeff k (O.Project.refund (seats F) (seats U) c L s (Dframe.flash t))) =
      ∑ e : Fin n → Fin (k+1), ∑ j : Fin (k+1), ∑ b : Fin (k+1),
        if b.val + (∑ i, (e i).val) ≤ k then
          (couplingPower f j.val (k-(b.val+∑ i, (e i).val)) : ℂ) •
            coeff b.val (U h) (∑ w : LivesP s, inputWeight F s w (fun i => (e i).val) •
              AppointedNullaryRefund.assemble G h (fun t => coeff j.val (L (decode s w) (Dframe.flash t))))
        else 0 := by
  let A := AppointedNullaryRefund.assemble G h
  let arrived (e : Fin n → Fin (k+1)) (j : Fin (k+1)) (t : Toon G h) :=
    ∑ w : LivesP s, inputWeight F s w (fun i => (e i).val) * coeff j.val (L (decode s w) (Dframe.flash t))
  let line (e : Fin n → Fin (k+1)) (j b : Fin (k+1)) (t : Toon G h) : ℂ :=
    if b.val + (∑ i, (e i).val) ≤ k then
      (couplingPower f j.val (k-(b.val+∑ i, (e i).val)) : ℂ) *
        ∑ z : Grade G t.1.val, arrived e j ⟨t.1,z⟩ * coeff b.val (seats U t.1.val z t.2)
    else 0
  have bank (e : Fin n → Fin (k+1)) (j : Fin (k+1)) :
      (∑ w : LivesP s, inputWeight F s w (fun i => (e i).val) •
        A (fun t => coeff j.val (L (decode s w) (Dframe.flash t)))) = A (arrived e j) := by
    calc
      _ = A (∑ w : LivesP s, inputWeight F s w (fun i => (e i).val) •
          (fun t : Toon G h => coeff j.val (L (decode s w) (Dframe.flash t)))) := by
        rw [map_sum]
        simp only [map_smul]
      _ = _ := by
        apply congrArg A
        funext t
        simp only [arrived, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have coordinates : (fun t : Toon G h => coeff k (O.Project.refund (seats F) (seats U) c L s (Dframe.flash t))) =
      ∑ e : Fin n → Fin (k+1), ∑ j : Fin (k+1), ∑ b : Fin (k+1), line e j b := by
    funext t
    simp only [Finset.sum_apply]
    exact scalar F U c f hc hf L s t k
  conv_lhs => rw [coordinates]; simp only [map_sum]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun b _ => ?_
  by_cases fits : b.val + (∑ i, (e i).val) ≤ k
  · rw [if_pos fits, bank]
    rw [AppointedNullaryRefund.action U HU, ← map_smul]
    apply congrArg A
    funext t
    simp only [line, fits, if_true, Pi.smul_apply, smul_eq_mul]
  · rw [if_neg fits]
    have zero : line e j b = 0 := by funext t; simp [line, fits]
    rw [zero, map_zero]

/-- A finite original roster keeps its signed weights inside the common field and heater refund. -/
theorem roster {I : Type*} [Fintype I] (α : I → ℂ) (s : I → Scan G n)
    (F U : Scale.Frames G) (HU : Civil U) (c : PowerSeries ℂ) (f : ℕ → ℝ)
    (hc : ∀ i, coeff i c = (f i : ℂ)) (hf : f 0 = 0) (L : Draft G n) (h k : ℕ) :
    AppointedNullaryRefund.assemble G h (fun t =>
      coeff k (∑ a : I, PowerSeries.C (α a) * O.Project.refund (seats F) (seats U) c L (s a) (Dframe.flash t))) =
      ∑ e : Fin n → Fin (k+1), ∑ j : Fin (k+1), ∑ b : Fin (k+1),
        if b.val + (∑ i, (e i).val) ≤ k then
          (couplingPower f j.val (k-(b.val+∑ i, (e i).val)) : ℂ) •
            coeff b.val (U h) (∑ a : I, α a • ∑ w : LivesP (s a),
              inputWeight F (s a) w (fun i => (e i).val) •
                AppointedNullaryRefund.assemble G h (fun t => coeff j.val (L (decode (s a) w) (Dframe.flash t))))
        else 0 := by
  let A := AppointedNullaryRefund.assemble G h
  let line (a : I) (t : Toon G h) :=
    coeff k (O.Project.refund (seats F) (seats U) c L (s a) (Dframe.flash t))
  let field (a : I) (e : Fin n → Fin (k+1)) (j : Fin (k+1)) :=
    ∑ w : LivesP (s a), inputWeight F (s a) w (fun i => (e i).val) •
      A (fun t => coeff j.val (L (decode (s a) w) (Dframe.flash t)))
  let charge (a : I) (e : Fin n → Fin (k+1)) (j b : Fin (k+1)) : Sec G h :=
    if b.val + (∑ i, (e i).val) ≤ k then
      (couplingPower f j.val (k-(b.val+∑ i, (e i).val)) : ℂ) • coeff b.val (U h) (field a e j)
    else 0
  have enrolled : (fun t : Toon G h => coeff k (∑ a : I, PowerSeries.C (α a) *
      O.Project.refund (seats F) (seats U) c L (s a) (Dframe.flash t))) = ∑ a : I, α a • line a := by
    funext t
    simp only [line, map_sum, coeff_C_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ = ∑ a : I, α a • A (line a) := by
      rw [enrolled]
      change A (∑ a : I, α a • line a) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun a _ => A.map_smul (α a) (line a)
    _ = ∑ a : I, ∑ e, ∑ j, ∑ b, α a • charge a e j b := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have paid : A (line a) = ∑ e, ∑ j, ∑ b, charge a e j b := vector F U HU c f hc hf L (s a) h k
      rw [paid]
      simp only [Finset.smul_sum]
    _ = ∑ e, ∑ j, ∑ b, ∑ a : I, α a • charge a e j b := moveThree _
    _ = _ := by
      refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun b _ => ?_
      by_cases fits : b.val + (∑ i, (e i).val) ≤ k
      · let z : ℂ := couplingPower f j.val (k-(b.val+∑ i, (e i).val))
        let T := coeff b.val (U h)
        calc
          _ = ∑ a : I, z • T (α a • field a e j) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            simp only [charge, fits, if_true, map_smul]
            exact smul_comm _ _ _
          _ = z • T (∑ a : I, α a • field a e j) := by
            rw [map_sum T (fun a : I => α a • field a e j) Finset.univ, Finset.smul_sum]
          _ = _ := by rw [if_pos fits]
      · simp [charge, fits]

end YM.Integration.AppointedOrdinaryRefund


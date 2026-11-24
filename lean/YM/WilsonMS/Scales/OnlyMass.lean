import YM.WilsonMS.Scales.MassN
/-!
# Intrinsic strict grade calibration

Entrywise algebra on compared coefficients. If two leading-close graded
adjustments differ at next order, conjugation by any t still has the same
strict off-block piece. It dies at infinity by the grading palette. Thus N
was characterized on just the Wilson prediction (after its own scale output
was fixed), not postulated as whatever would help matching. Uses the full
family B, not a reference to analytic beta.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.GFlow
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Logarithm
open PowerSeries (coeff mk X C constantCoeff invOfUnit)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates FrameX Ice
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d k n m j : ℕ}
local notation "BΨ" => Ensure.deck G
variable {A P Q : Guard G d}
section cube

lemma agent (s : ℝ) {c : Cn} (hx : Clean c) (hp : CloseP P) (h : CloseP Q) :
    CloseP (compass s c P Q) :=
  ((duties s h).invert.times hp).times (h.substitute hx)

lemma turning (s : ℝ) {T P : Guard G d} (c : Cn) (h : CloseP T) :
    P * coupon c T = buryD s T * compass s c P T := by
  unfold compass
  rw [← mul_assoc, ← mul_assoc, (antidote (duties s h)).1, one_mul]

private lemma load_mul (c : Cn) (h : Rooted c) (T V : Guard G d) :
    coupon c (T * V) = coupon c T * coupon c V := by
  apply PowerSeries.ext
  intro k
  let F := fun i => coeff i T
  let Q := fun i => coeff i V
  let A := (Algebra.lmul ℂ (FieldEnd G d)).toLinearMap
  have hV : pairW A F Q = (fun i => coeff i (T * V)) :=
    funext fun i => Eq.symm (PowerSeries.coeff_mul i T V)
  unfold coupon
  rw [PowerSeries.coeff_mk, ← hV, ← substitute_pair h, PowerSeries.coeff_mul]
  simp_rw [PowerSeries.coeff_mk]
  rfl

lemma interlink (hx : CloseP P) (h : CloseP A) (hq : P * A = Q) {c : Cn} (hv : Rooted c) (t : ℝ)
    (Z : Guard G d) : compass t c Z P * coupon c A = buryD t A * compass t c Z Q := by
  apply (duties t hx).1.seed.mul_right_inj.mp
  rw [← mul_assoc (buryD t P), ← turning t c hx, mul_assoc, ← load_mul c hv, hq, ←
    mul_assoc (buryD t P), ← wedge, hq,
    turning t c (T := Q) (P := Z)
      (by
        rw [← hq]
        exact hx.times h)]

variable (hi : 0 < n) (h : ∀ i : ℕ, 0 < i → i < n → coeff i P = 0) (hp : CloseP P)

lemma reset_point {c : Cn} (hc : Aware c) (hv : 0 < n) (h : ∀ i : ℕ, 0 < i → i < n → coeff i P = 0) :
    coeff n (coupon c P) = coeff n P := by
  unfold coupon
  rw [PowerSeries.coeff_mk, rules, Finset.sum_eq_single_of_mem n (Finset.mem_Iic.mpr le_rfl),
    root_first hc.root hc.paid, one_smul]
  intro b hb he
  by_cases hz : b = 0
  · subst b
    rw [cut, pow_zero, PowerSeries.coeff_one, if_neg (Nat.ne_of_gt hv), zero_smul]
  rw [h b (Nat.pos_of_ne_zero hz) (lt_of_le_of_ne (Finset.mem_Iic.mp hb) he), smul_zero]

lemma reset_bank {i' : ℕ} {c : Cn} (hc : Aware c) (hj : 0 < i') (h' : i' < n)
    (h : ∀ i : ℕ, 0 < i → i < n → coeff i P = 0) : coeff i' (coupon c P) = 0 := by
  rw [reset_point hc hj (fun i hu hh => h _ hu (hh.trans h')), h i' hj h']
include hp

lemma diagonal_unchanged (t : ℝ) (n : ℕ) : shadows (coeff n (buryD t P)) = shadows (coeff n P) := by
  have H (r : ℝ) : Flat (window G d r) := by
    unfold Flat
    apply LinearMap.ext
    intro x
    rw [levy]
    simp_rw [pane]
    convert road r x |>.symm using 1
    exact
      Finset.sum_congr rfl fun j _ => by
        rw [show ∀ (v : ℝ) (p : Sec G d), tileK G d j (v • p) = v • tileK G d j p from fun v p =>
            map_smul ((tileK G d j).restrictScalars ℝ) v p,
          tileD, if_pos rfl]
  rw [deep_move, mul_diag, mul_diag (tierFlat (H (-t))) (filter_emb hp n), H _, H _]
  · obtain h := on_time (n := n) (A := printM P) t (Mass.print.exactly n)
    rwa [deep_move, printed] at h
  · let V := coeff n P
    intro i j hi x
    rw [Module.End.mul_apply]
    refine
      tile_day _ _ hi (Nat.le_of_lt_succ i.isLt) (window_cap (-t) _ (Nat.le_of_lt_succ i.isLt) ?_)
    have he := tile_key (G := G) i x
    by_cases hN : n = 0
    subst n
    rw [hp.zeroC]
    exact he
    exact (show _ from (may_change _).mp (positiveC hp hN)).2.1 _ (Nat.le_of_lt_succ i.isLt) _ he
  exact tierFlat (H _)
include hi h

lemma tick_fee {Q : Guard G d} (hx : CloseP Q) : coeff n (P * Q) = coeff n P + coeff n Q := by
  rw [PowerSeries.coeff_mul]
  let J := Finset.antidiagonal n
  have hV : (n, 0) ∈ J := by simp [J]
  have he : (0, n) ∈ J.erase (n, 0) := by
    have h : n ≠ 0 := (by omega)
    simp [J, h]
  rw [← Finset.add_sum_erase _ _ hV, ← Finset.add_sum_erase _ _ he, Finset.sum_eq_zero ?_]
  swap
  · intro i hs
    obtain ⟨hh, hL, ht⟩ :=
      show i ≠ (0, n) ∧ i ≠ (n, 0) ∧ i ∈ J from
        ⟨(Finset.mem_erase.mp hs).1, (Finset.mem_erase.mp ((Finset.mem_erase.mp hs).2)).1,
          (Finset.mem_erase.mp ((Finset.mem_erase.mp hs).2)).2⟩
    obtain hK := Finset.mem_antidiagonal.mp ht
    rw [h i.1
        (by
          contrapose hh
          exact
            Prod.ext
              (by
                dsimp
                omega)
              (by
                dsimp
                omega))
        (by
          contrapose hL
          exact
            Prod.ext
              (by
                dsimp
                omega)
              (by
                dsimp
                omega)),
      zero_mul]
  rw [hp.zeroC, hx.zeroC, mul_one, one_mul, add_zero]

lemma tack_fee {Q : Guard G d} (hx : CloseP Q) : coeff n (Q * P) = coeff n Q + coeff n P := by
  rw [PowerSeries.coeff_mul]
  let J := Finset.antidiagonal n
  have hV : (n, 0) ∈ J := by simp [J]
  have he : (0, n) ∈ J.erase (n, 0) := by
    have h : n ≠ 0 := (by omega)
    simp [J, h]
  rw [← Finset.add_sum_erase _ _ hV, ← Finset.add_sum_erase _ _ he, Finset.sum_eq_zero ?_]
  swap
  · intro i hs
    obtain ⟨hh, hL, ht⟩ :=
      show i ≠ (0, n) ∧ i ≠ (n, 0) ∧ i ∈ J from
        ⟨(Finset.mem_erase.mp hs).1, (Finset.mem_erase.mp ((Finset.mem_erase.mp hs).2)).1,
          (Finset.mem_erase.mp ((Finset.mem_erase.mp hs).2)).2⟩
    obtain hK := Finset.mem_antidiagonal.mp ht
    rw [h i.2
        (by
          contrapose hL
          exact
            Prod.ext
              (by
                dsimp
                omega)
              (by
                dsimp
                omega))
        (by
          contrapose hh
          exact
            Prod.ext
              (by
                dsimp
                omega)
              (by
                dsimp
                omega)),
      mul_zero]
  rw [hp.zeroC, hx.zeroC, mul_one, one_mul, add_zero]
end cube

/-- Any two adjustments obeying the mass-independent rule coincide. This
only involves the intrinsic scale data of the posed X array. No MS frame
in the criterion. -/
lemma Anchored.unique {X : Scheme G} {Ψ : Traveling G} (h : ∀ t, Linked X t (Ψ.Q t) (Ψ.r t))
    (hp : Anchored Ψ P) (hq : Anchored Ψ Q) : P = Q := by
  let B := vault P * Q
  have hB : CloseP B := hp.nearN.invert.times hq.nearN
  have heB : P * B = Q := by
    unfold B
    rw [← mul_assoc, (antidote hp.nearN).1, one_mul]
  have H : PureDrop B := foldDrop (dropV hp.nearN hp.strict) hq.strict hp.nearN.invert hq.nearN
  have he (n) (hn : 0 < n) : coeff n B = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hI (i : ℕ) (hi : 0 < i) (ht : i < n) := ih _ ht hi
      have he : shadows (coeff n B) = 0 := by
        rw [← printed, H, PowerSeries.coeff_one, if_neg (Nat.ne_of_gt hn)]
      have hv (s : ℝ) : coeff n B = coeff n (buryD s B) := by
        let R := Ψ.r s
        let T := Ψ.Q s d
        let L := compass s R T P
        let V := compass s R T Q
        have hA : Aware R := (h s).normal
        have hs := (h s).ground d
        have hh := congr_arg (coeff n) (interlink hp.nearN hB heB hA.root s T)
        change coeff n (L * coupon R B) = coeff n (buryD s B * V) at hh
        rw [tick_fee hn (fun i hi hx => (by rw [deep_move, hI _ hi hx, mul_zero, zero_mul]))
            (duties s hB) (agent s hA.clean hs hq.nearN),
          tack_fee hn (fun i hi ht => reset_bank hA hi ht hI) (hB.substitute hA.clean)
            (agent s hA.clean hs hp.nearN),
          reset_point hA hn hI] at hh
        have hx := congr_arg shadows hh
        rw [tile_sum, tile_sum, Mass.exactly (hp.grade s) n, Mass.exactly (hq.grade s) n,
          diagonal_unchanged hB, he, zero_add, add_zero] at hx
        rw [hx, add_comm (coeff n V)] at hh
        apply LinearMap.ext
        intro v
        exact
          add_right_cancel
            (DFunLike.congr_fun hh v :
              coeff n B v + coeff n V v = coeff n (buryD s B) v + coeff n V v)
      have heP (x : Sec G d) (L : Sec G d →ₗ[ℂ] ℂ) : L (coeff n B x) = 0 := by
        obtain hh := exchange_cost hB L n x
        simp_rw [printed, he, LinearMap.zero_apply, map_zero, ← hv] at hh
        exact tendsto_nhds_unique tendsto_const_nhds hh
      apply LinearMap.ext
      intro x
      apply (Daylight BΨ d).equivFun.injective
      funext i
      rw [LinearMap.zero_apply, map_zero]
      exact heP x ((Daylight BΨ d).coord i)
  suffices hp : B = 1 by rw [← heB, hp, mul_one]
  refine PowerSeries.ext fun i => ?_
  rw [PowerSeries.coeff_one]
  split_ifs with hv
  subst i
  exact hB.zeroC
  exact he i (Nat.pos_of_ne_zero hv)
end YM.WilsonMS.GFlow

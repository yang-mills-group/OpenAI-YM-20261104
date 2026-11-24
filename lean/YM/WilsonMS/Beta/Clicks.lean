import YM.WilsonMS.Beta.Gather
/-!
# Resolve contributions from all splittings of a top cubic

Ghost cancellation, trident, spin pricing. Set up for repeated uses of the
Betafunction-form probes AA, CU, SCC from marginal jets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BetaValue
open Function Filter Set Finset MeasureTheory Metric
open LoopRank Lattice MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect
  Native
open Book Convolve City Logarithm Signal Landau.Detect.Mark Wind High Knobs
open LogTime LogTime.IntervalFamily Outlook Land Arc Wire Rock Path Oceans Plum Alps Garment Color
  Pearl
open Arts Motif Halo
open Complex (I)
open scoped Topology ContDiff BigOperators
variable {G : Gauge}
variable (r : ℝ) (F : Law G) (i j : CI G) (p q : QP) (x y : Axis) (w μ : Legs (Lane4 G))
local notation "K" => HeatLine G r
local notation "W" => Detect.W
local notation "Ψ(" a "," b "," w ")" => radius parity K a b (Cubic G) F w μ

abbrev press_hit (w : Legs (Lane4 G)) :=
  fieldDim ghostNo w
section selection

private lemma lost_hit (a b : BH G) (l : Legs (Lane4 G)) (h : ghostNo a + fieldDim ghostNo l ≠ 0) :
    Ψ(a,b,l) = 0 := by
  unfold radius
  dsimp only
  rw [cubic_charge (_ :: l)
      (show fieldDim ghostNo ((a, -net l) :: l) ≠ 0 from
        (by
          rw [field_cons]
          exact h))]
  ring

lemma empty_hit (l : Legs (Lane4 G)) (h : fieldDim ghostNo l ≠ 0) (hx : fieldDim ghostNo l ≠ 1)
    (ht : fieldDim ghostNo l ≠ -1) : HitM K F l μ = 0 := by
  rw [group_hit]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.sum_eq_zero (s := Finset.univ)
      (fun a _ => Finset.sum_eq_zero (fun b _ => lost_hit r F μ _ _ l ?_)),
    Finset.sum_eq_zero (s := Finset.univ) ?_, add_zero]
  swap
  · change 0 + _ ≠ _
    rwa [zero_add]
  intro a _
  rw [lost_hit r F μ (Uℓ a i) (Cℓ i) _ (show -1 + _ ≠ 0 from (by omega)),
    lost_hit r F μ (Cℓ i) (Uℓ a i) _ (show 1 + fieldDim ghostNo l ≠ 0 from (by omega)), add_zero]

lemma θ_W (l : Legs (Lane4 G)) (h : fieldDim ghostNo l = 0) :
    HitM K F l μ = ∑ i : CI G, ∑ a : Axis, ∑ b : Axis, Ψ(Aℓ a i,Aℓ b i,l) := by
  rw [group_hit]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_zero (f := fun a => Ψ(Uℓ a i,Cℓ i,l) + Ψ(Cℓ i,Uℓ a i,l)) ?_, add_zero]
  intro a _
  rw [lost_hit r F μ (Uℓ a i) (Cℓ i) l (show (-1 : ℤ) + fieldDim ghostNo l ≠ 0 from (by omega)),
    lost_hit r F μ (Cℓ i) (Uℓ a i) l (show (1 : ℤ) + fieldDim ghostNo l ≠ 0 from (by omega)),
    add_zero]

lemma θ_U (l : Legs (Lane4 G)) (h : fieldDim ghostNo l = 1) :
    HitM K F l μ = ∑ i : CI G, ∑ a : Axis, Ψ(Uℓ a i,Cℓ i,l) := by
  rw [group_hit]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_zero (f := fun a : Axis => ∑ b : Axis, Ψ(Aℓ a i,Aℓ b i,l)) ?_, zero_add]
  · apply Finset.sum_congr rfl
    intro a _
    rw [lost_hit r F μ (Cℓ i) (Uℓ a i) l (show 1 + fieldDim ghostNo l ≠ 0 from (by omega)), add_zero]
  intro a _
  exact
    Finset.sum_eq_zero fun b _ =>
      lost_hit r F μ (Aℓ a i) (Aℓ b i) l (show 0 + fieldDim ghostNo l ≠ 0 from (by omega))

lemma θ_C (l : Legs (Lane4 G)) (h : fieldDim ghostNo l = -1) :
    HitM K F l μ = ∑ i : CI G, ∑ a : Axis, Ψ(Cℓ i,Uℓ a i,l) := by
  rw [group_hit]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_zero (f := fun a : Axis => ∑ b : Axis, Ψ(Aℓ a i,Aℓ b i,l)) ?_, zero_add]
  · apply Finset.sum_congr rfl
    intro a _
    rw [lost_hit r F μ (Uℓ a i) (Cℓ i) l (show -1 + fieldDim ghostNo l ≠ 0 from (by omega)), zero_add]
  intro a _
  exact
    Finset.sum_eq_zero fun b _ =>
      lost_hit r F μ (Aℓ a i) (Aℓ b i) l (show 0 + fieldDim ghostNo l ≠ 0 from (by omega))
end selection
section color

abbrev Lace (r : ℝ) (p : QP) (a b : Axis) : ℂ :=
  (City.brush r p * precision a b p : ℝ)

abbrev SpanH (r : ℝ) (p : QP) (a : Axis) : ℂ :=
  I * (City.brush r p : ℂ) * (p.sq : ℂ) * p a

lemma atAA (i : CI G) : K (Aℓ x i) (Aℓ y i) p = Lace r p x y :=
  if_pos rfl

lemma atUC (i : CI G) : K (Uℓ x i) (Cℓ i) p = SpanH r p x := by
  simp [HeatLine, LegsK, Landau.choir, SpanH, L0]
  ring

lemma atCU (i : CI G) : K (Cℓ i) (Uℓ x i) p = SpanH r p x :=
  (show K (Cℓ i) (Uℓ x i) p = K (Uℓ x i) (Cℓ i) p from rfl).trans (atUC ..)
local notation "s" => p + q

lemma clickWW :
    HitM K F [W x i p, W y j q] μ =
      ∑ k : CI G,
        ∑ a : Axis,
          ∑ b : Axis,
            2 * Lace r (-s) a b * (Cubic G [W a k (-s), W x i p, W y j q]) * F (W b k s :: μ) := by
  let w := [W x i p, W y j q]
  rw [θ_W _ _ μ w rfl]
  simp_rw [radius,
    show net w = s from
      (by
        unfold w
        simp [net, Detect.W, qnote]),
    neg_neg, atAA (G := G)]
  change
    (∑ k : CI G,
        ∑ a : Axis,
          ∑ b : Axis, 2 * Lace r _ a b * ((1 : ℂ) * Cubic G ((_, _) :: w)) * F ((Aℓ b k, s) :: μ)) =
      _
  simp only [one_mul]
  rfl

lemma clickWC :
    HitM K F [W x i p, C j q] μ =
      ∑ k : CI G, 2 * SpanH r (-(p + q)) x * (-fColor k i j) * F (C k (p + q) :: μ) := by
  rw [θ_U _ _ μ _ (show fieldDim ghostNo [W x i p, C j q] = 1 from rfl)]
  refine Finset.sum_congr rfl fun k _ => ?_
  let l := [W x i p, C j q]
  have hn : net l = s := by simp [net, l, Detect.W, C, qnote]
  have ht (a : Axis) :
    Ψ(Uℓ a k,Cℓ k,l) = 2 * SpanH r (-s) a * (-(if a = x then fColor k i j else 0)) * F (C k s :: μ) := by
    unfold radius
    dsimp only
    rw [hn, neg_neg, atUC (G := G)]
    change _ * ((-1 : ℂ) * Cubic G [U a k _, W x i p, C j q]) * _ = _
    rw [CAplus k i j (-s) p q a x (by abel), neg_one_mul]
  rw [Finset.sum_eq_single x, ht, if_pos rfl]
  intro b _ hB
  rw [ht b, if_neg hB, neg_zero, mul_zero, zero_mul]
  simp

lemma ahead (t : QP) (he : p + (q + t) = 0) (a : CI G) :
    Cubic G [W x i p, U y j q, C a t] = if y = x then fColor j i a else 0 := by
  rw [← add_assoc, add_eq_zero_iff_eq_neg'] at he
  subst t
  exact forward_AC i j p q x y a

lemma ClickUC :
    HitM K F [U x i p, C j q] μ =
      ∑ k : CI G, ∑ b : Axis, 2 * Lace r (-s) x b * fColor i k j * F (W b k s :: μ) := by
  let l := [U x i p, C j q]
  have hx : fieldDim ghostNo l = 0 := rfl
  rw [θ_W _ _ μ _ hx]
  refine Finset.sum_congr rfl fun k _ => ?_
  have he : net l = s := by simp [net, l, U, C, qnote]
  have h (a b : Axis) :
    Ψ(Aℓ a k,Aℓ b k,l) =
      2 * Lace r (-s) a b * (if x = a then fColor i k j else 0) * F (W b k s :: μ) := by
    unfold radius
    dsimp only
    rw [he, neg_neg, atAA]
    change _ * ((1 : ℂ) * Cubic G [W a k (-s), U x i p, C j q]) * _ = _
    rw [ahead k i _ p a x q (by abel) j, one_mul]
  rw [Finset.sum_eq_single x]
  · apply Finset.sum_congr rfl
    intro b _
    rw [h, if_pos rfl]
  · intro a ha ht
    exact Finset.sum_eq_zero fun b _ => by rw [h, if_neg ht.symm, mul_zero, zero_mul]
  simp

lemma clickUW :
    HitM K F [U x i p, W y j q] μ =
      (if x = y then ∑ k : CI G, ∑ a : Axis, 2 * SpanH r (-s) a * fColor i j k * F (U a k s :: μ)
      else 0) := by
  let l := [U x i p, W y j q]
  rw [θ_C _ _ μ l rfl]
  have he (a : Axis) (k : CI G) :
    Ψ(Cℓ k,Uℓ a k,l) = 2 * SpanH r (-s) a * (if x = y then fColor i j k else 0) * F (U a k s :: μ) := by
    unfold radius
    dsimp only
    rw [show net l = s from (by simp [l, U, Detect.W, qnote, net]), neg_neg, atCU]
    have h : Cubic G [C k (-s), U x i p, W y j q] = -(if x = y then fColor i j k else 0) := by
      rw [show Cubic G [C k (-s), U x i p, W y j q] = (-1) * Cubic G [U x i p, C k (-s), W y j q] from
          cubic_swap [] [W y j q] (C k (-s)) (U x i p),
        show Cubic G [U x i p, C k (-s), W y j q] = (1 : ℂ) * Cubic G [U x i p, W y j q, C k (-s)]
          from cubic_swap [U x i p] [] (C k (-s)) (W y j q)]
      rw [CAplus i j k p q (-s) x y (by abel)]
      ring
    change _ * ((-1 : ℂ) * Cubic G [C k (-s), U x i p, W y j q]) * _ = _
    rw [h, neg_one_mul, neg_neg]
  simp_rw [he]
  by_cases hx : x = y <;> simp only [hx, ↓reduceIte, mul_zero, zero_mul, Finset.sum_const_zero]

lemma clickSC :
    HitM K F [S i p, C j q] μ =
      ∑ k : CI G, ∑ a : Axis, 2 * SpanH r (-s) a * (-fColor i k j) * F (U a k s :: μ) := by
  let l := [S i p, C j q]
  rw [θ_C _ _ μ l rfl]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
  unfold radius
  dsimp only
  rw [show net l = s from (by simp [l, S, C, qnote, net]), neg_neg, atCU]
  change _ * ((-1 : ℂ) * Cubic G [C k (-s), S i p, C j q]) * _ = _
  rw [show Cubic G [C k (-s), S i p, C j q] = 1 * Cubic G [S i p, C k (-s), C j q] from
      cubic_swap [] [C j q] (C k (-s)) (S i p),
    CStar i k j p (-s) q (by abel), one_mul, neg_one_mul]
end color
end YM.WilsonMS.BetaValue

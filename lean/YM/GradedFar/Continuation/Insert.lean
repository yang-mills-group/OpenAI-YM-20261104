import YM.GradedFar.Continuation.Tally

/-!
# Budget for using all Far columns also on the comparison with physical data

Algebraic pricing part of M.2 first line. This module is exercised in the physical continuation
(with `A` the change on exact homogeneous physical fields, `Y0` the evaluated
**physical** kernel in the same r labels).
-/
namespace YM.FVA2.GradedFar.Continuation
noncomputable section
open Filter Set Real Topology Function PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m ℓ : ℕ} {N : WilsonPrescription G} {d : Fin n → ℕ} {e : Fin m → ℕ}
  {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)

def row (N : WilsonPrescription G) (x : Points n) (u : Inputs G d) (y : Points m)
    (v : Inputs G e) (s : ℝ) := ∑ a : Choices G e,
  C (combo v a) * Subarray.bare (ordinary N) x u (roll a) (squeeze (-s) y)
lemma on_basis (x : Points n) (u : Inputs G d) (y : Points m) (v : Choices G e) (s : ℝ) :
    row N x u y (basisInputs v) s = Subarray.bare (ordinary N) x u (roll v) (squeeze (-s) y) := by
  unfold row; rw [Finset.sum_eq_single v]
  · rw [combo, Finset.prod_eq_one (by intro k hk; exact (pivotδ (v k) (v k)).trans (if_pos rfl)), map_one,one_mul]
  · intro b _ hb; suffices h : combo (basisInputs v) b=0 by rw [h,map_zero,zero_mul]
    obtain ⟨j,hj⟩ := Function.ne_iff.mp hb
    exact Finset.prod_eq_zero (i:=j) (Finset.mem_univ j) ((pivotδ (b j) (v j)).trans (if_neg hj.symm))
  simp
lemma all_spell (x : Points n) (u : Inputs G d) (y : Points m) (v : Inputs G e) (s : ℝ) :
    Yx N M x y u v s = ∑ c : Choices G e, factors c (exterior N M (-s) v) * row N x u y (basisInputs c) s := by
  simp_rw [on_basis,Yx,applyFar,Subarray.bare,Finset.mul_sum]
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_left_comm ..

include H

/-- This is the prediction of G.9, with constant inputs, in the same order. -/
lemma coeff_row (x : Points n) (u : Inputs G d) (y : Points m) (v : Inputs G e) (s : ℝ)
    (hd : ∀ i, d i ≤ ℓ) (he : ∀ i, e i ≤ ℓ) (hp : forest x (squeeze (-s) y) ∈ conf (n+m)) (j : ℕ) :
    coeff j (row N x u y v s) = Measure.outlook N.scheme N.criterion ℓ _ ⟨forest x (squeeze (-s) y),hp⟩ j
        (Fin.append (installedInputs hd u) (installedInputs he v)) := by
  simp_rw [row,map_sum,coeff_C_mul,Subarray.bare_coeff H _ _ _ hp (Subarray.tactic _ he) hd j]
  exact (expand_far _ (installedInputs hd u) v he).symm

section
variable {I : Type} (b : Board I) {t : I → ℝ}
  (v : I → Inputs G e) (W : I → Inputs G e) {L : ℝ} (hv : ∀ i, Within L (v i))
include hv
lemma prices_K (c : Choices G e) (k : ℕ) (p : Fin m) : Ledger b k (-(heft (roll c p):ℝ))
    (fun i => mode (exterior N M (-b.s i) (v i) p) (c p)) :=
  Ledger.from_charge (price_column H (c p) (fun i => v i p) _ fun i => hv i p) id
variable {b}
  (ht : ∀ᶠ i in b.l, |t i| ≤ 2*b.g i) (k : ℕ)
  -- the G.1 input for the converted fields, k := p the order we're matching *through*.
  (hA : ∀ c : Choices G e, ∀ j, ∃ k' : ℕ, k + 5 ≤ k' ∧ Bill b (k+2) 0 (fun i =>
        coord (c j) (W i j) - crop k' (t i) (mode (exterior N M (-b.s i) (v i) j) (c j))))
local notation "fee_x" => fun (j : Choices G e) i => factors j (exterior N M (-b.s i) (v i))
include ht hA
/-- Replace each physical A-coordinate by its separately evaluated series and recrop the
product. `k'` in the hypothesis can be arbitrarily high. May also discard its contribution from
all the higher-than-`k` order leg terms *at the same log budget*. By the graded pricing this is
possible without losing even one engineering power of T from doing it; thus the subsequent
`true_pay` proof only needs to multiply through the `k`-crop ones. -/
lemma product_comparison (c : Choices G e) : Priced b k t (-(totalG (roll c):ℝ))
    (fun i => combo (W i) c) (fee_x c) := by
  have hu (j : Fin m) : Priced b k t (-(heft (roll c j):ℝ)) (fun i => coord (c j) (W i j))
        (fun i => mode (exterior N M (-b.s i) (v i) j) (c j)) := by
    let B i := mode (exterior N M (-b.s i) (v i) j) (c j)
    have hk (k) : Ledger b k (-(heft (roll c j):ℝ)) B := prices_K H b v hv c k j
    obtain ⟨k',hk',he⟩ := hA c j
    refine ⟨hk k,?_⟩
    exact ((he.mono_fee (show -(heft (roll c j):ℝ) ≤ 0 by simp) (Nat.le_succ _)).plus
      ((hk k').below ht (by omega))).apply_eq (Eventually.of_forall fun i => sub_add_sub_cancel ..)
  dsimp only
  unfold totalG; rw [Nat.cast_sum,← Finset.sum_neg_distrib]
  exact Priced.product ht _ _ fun j _ => hu j

variable {X : Set (Points n)} {Y : Set (Points m)} (hX : IsCompact X) (hx : X ⊆ conf n)
  (hY : IsCompact Y) (hy : Y ⊆ O.Enh.Outside m) (x : I → X) (y : I → Y)
  (u : I → Inputs G d) {R : ℝ} (hu : ∀ i, Within R (u i))
include hX hx hY hy hu
omit v hv ht hA W in
lemma prices_at (c : Choices G e) : Ledger b k (totalG (roll c))
    (fun i => row N (x i).val (u i) (y i).val (basisInputs c) (b.s i)) := by
  have earn : ChargeP (k+1) (totalG (roll c)) (fun i s => Subarray.bare (ordinary N) (x i).val (u i)
        (roll c) (squeeze (-s) (y i).val)) :=
    ChargeP.sum _ fun a _ => (combo_price u a _ hu).times ((full_fare H (roll a) (roll c) hX hx hY hy k 0).pull
      (fun i => (x i,y i)))
  simp_rw [on_basis]
  exact Ledger.from_charge earn id

/-- W are actual Far input values in the r-frame (from applying the frame change A).
Price needed from using long-exterior Taylor G.9 here is *only* at the all-r-homes
basis labels. The program propagates that price to W and charges the same residual on {
it versus the full polynomial with K(s) in every Far input}.
-/
theorem true_pay (F : I → MultilinearMap ℂ (fun i => Sec G (e i)) ℂ)
    (hF : ∀ c : Choices G e, Bill b (k+1) 0 (fun i => F i (basisInputs c)-
      crop k (t i) (row N (x i).val (u i) (y i).val (basisInputs c) (b.s i)))) :
    Bill b (k+1) (-((∑ j, e j : ℕ):ℝ)) (fun i => F i (W i)-
        crop k (t i) (Yx N M (x i).val (y i).val (u i) (v i) (b.s i))) := by
  simp_rw [basis_spelling (F _) (W _), all_spell,crop_sum,← Finset.sum_sub_distrib]
  refine Bill.sum _ fun c _ => ?_
  let Q i := row N (x i).val (u i) (y i).val (basisInputs c) (b.s i)
  let P i := fee_x c i
  let a i := combo (W i) c
  have fQ : Priced b k t (-(totalG (roll c):ℝ)) a P := product_comparison H v W hv ht k hA c
  have hq := (fQ.weight ht).times (hF c)
  rw [add_zero] at hq
  have hK : Ledger b k (totalG (roll c)) Q := prices_at H k hX hx hY hy x y u hu c
  have hg := fQ.mul_exact ht hK
  rw [neg_add_cancel] at hg
  apply (hq.plus (hg.mono_fee (by change -(totalG (roll c):ℝ) ≤ 0; exact neg_nonpos.mpr (Nat.cast_nonneg _)) le_rfl)).mono_fee ?_ le_rfl |>.apply_eq (Eventually.of_forall fun i => ?_)
  · exact neg_le_neg (Nat.cast_le.mpr (Finset.sum_le_sum fun j _ => Dframe.size_le (c j)))
  rw [mul_sub]; dsimp only [P,Q,a]; abel
end
end
end YM.FVA2.GradedFar.Continuation

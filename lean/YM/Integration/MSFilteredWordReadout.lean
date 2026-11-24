import YM.Integration.MSMeasuredFeeField
import YM.Integration.MSCommonMeasuredRows

/-! The actual finite full field tensor in a fixed engineering cap, with
the original funding and every coefficient of every independently marked port. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.MSFilteredWordReadout

open Filter Function Finset FVA2 Lattice MS MS.Local.Physical MS.Menus MS.Land MS.Rake
open MS.Dial MS.Orbit MSPhysicalDeckChange MSFeeCoordinates MSFeeReadout
open MSNormalizedFeeReadout MSCommonMeasuredRows MSMeasuredFeeField
open scoped Classical BigOperators

variable {G : Gauge} {A B : Deck G} {I W : Type} [LinearOrder W] [Fintype W]
variable (V : Warehouse G) (P : Prescription A) (E : Fees B A) {h d : ℕ}

theorem own (b : Glyph B h) (a : Glyph A b.size) (l : b.size ≤ d) :
    MSMeasuredFeeField.raw P E b (MSFeeCoordinates.extend l a) = receiver P (E b.size b.2) a := by
  have e : (MSFeeCoordinates.extend l a).size ≤ b.size := remaining a
  rw [MSMeasuredFeeField.raw, dif_pos e]
  rfl

omit [Fintype W] in
theorem sum_extend {K : Type*} [CommSemiring K] (e d : W → ℕ) (s : Finset W)
    (l : ∀ i, e i ≤ d i) (p : (i : s) → Glyph A (d i.val) → K)
    (F : Slots A d s → K) (hz : ∀ (i : s) a, e i.val < a.size → p i a = 0) :
    ∑ a : Slots A d s, (∏ i : s, p i (a i))*F a =
      ∑ a : Slots A e s, (∏ i : s, p i (MSFeeCoordinates.extend (l i.val) (a i))) *
       F (fun i => MSFeeCoordinates.extend (l i.val) (a i)) := by
  let f (a : Slots A d s) := (∏ i : s, p i (a i))*F a
  have off (a : Slots A d s) (he : ¬ fits d s e a) : f a = 0 := by
    obtain ⟨i, h⟩ := not_forall.mp he
    unfold f
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (hz i (a i) (lt_of_not_ge h)), zero_mul]
  have hx : (∑ a : Slots A d s, f a) = ∑ a : {a : Slots A d s // fits d s e a}, f a.val := by
    rw [← Finset.sum_subtype (p := fits d s e)
      ((Finset.univ : Finset (Slots A d s)).filter (fits d s e)) (fun a => by simp) f]
    apply (Finset.sum_subset (Finset.filter_subset ..) ?_).symm
    intro a _ ha
    exact off a (by simpa using ha)
  change (∑ a : Slots A d s, f a) = _
  rw [hx, ← (Equiv.sum_comp (subslots (B := A) d s e l) (fun a => f a.val))]
  rfl

omit [Fintype W] in
theorem scalar (θ : ℝ) (s : Finset W) (a : W → ℤ) :
    ∏ i ∈ s, Port.τ (a i) θ = Port.τ (∑ i ∈ s, a i) θ := by
  induction s using Finset.induction_on with
  | empty => simp [Port.τ]
  | insert i s hi h =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, h]
    simp only [Port.τ, zpow_add₀ (Real.exp_ne_zero θ), Complex.ofReal_mul]

def lift {b : W → Glyph B h} (a : Slots A (fun i => (b i).size) Finset.univ) :
    Slots A (fun _ : W => h) Finset.univ :=
  fun i => MSFeeCoordinates.extend (remaining (b i.val)) (a i)

theorem coefficients (μ θ : ℝ) (b : W → Glyph B h)
    (a : Slots A (fun i => (b i).size) Finset.univ) :
    transition P (fun i => (b i).size) μ θ (fun i => E (b i).size (b i).2) a =
      ∏ i : (Finset.univ : Finset W), charged P E μ θ (b i.val) (lift (b := b) a i) := by
  classical
  simp only [transition, charged, lift, own, Finset.prod_mul_distrib, ← map_prod]
  congr 1
  rw [scalar]
  congr 2
  have att (g : W → ℤ) : (∑ i : W, g i) = ∑ i : (Finset.univ : Finset W), g i.val := by
    let e : (Finset.univ : Finset W) ≃ W := ⟨Subtype.val, fun i => ⟨i, Finset.mem_univ _⟩, fun _ => rfl, fun _ => rfl⟩
    exact (e.sum_comp g).symm
  simp only [MS.Vane.charge, dimensions, Finset.sum_sub_distrib, Nat.cast_sum]
  exact congrArg₂ (· - ·) (att (fun i => ((b i).size : ℤ)))
    (att (fun i => ((a ⟨i, Finset.mem_univ _⟩).size : ℤ)))

theorem actual (μ : ℝ) (T : Trial I W) (j : I) (b : W → Glyph B h) :
    marked V P E (ColorCode.labelAt B ∘ b) T μ j =
      ∑ a : Slots A (fun _ : W => h) Finset.univ,
        (∏ i : (Finset.univ : Finset W), charged P E μ (T.profile.θ j) (b i.val) (a i)) *
          native V P (word (fun _ : W => h) a) T μ j := by
  classical
  rw [sum_extend (fun i => (b i).size) (fun _ : W => h) Finset.univ
    (fun i => remaining (b i))]
  · rw [marked, written]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact congrArg₂ (· * ·) (coefficients P E μ (T.profile.θ j) b a) rfl
  · intro i a h
    rw [charged, above P E _ _ h, map_zero, map_zero, mul_zero]

end YM.Integration.MSFilteredWordReadout

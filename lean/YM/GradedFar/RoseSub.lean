import YM.GradedFar.Subarray
import YM.XSpace.Tamarack
/-! Galop to subarrays in the empty/unit convention, coefficientwise. -/
namespace YM.FVA2.GradedFar.Subarray
noncomputable section
open Set Filter Function Real PowerSeries
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m : ℕ}
  (w : Fin m ↪ Fin n) (d : ℕ) (Y : Initialize G) {V : Store G} (κ : Rose.Pick V)
lemma measureX_unit (q : Sample n) (v : Tags G d n)
    (hv : ∀ i ∉ range w, v i = leaf G d) (j : ℕ) :
    Rose.measureₓ Y κ d q j v = Rose.measureₓ Y κ d (sample w q) j (v ∘ w) := by
  rw [Rose.measure_paid,Rose.measure_paid]; unfold Rose.turn
  have h (k) : Rose.cooked Y V d q k v = Rose.cooked Y V d (sample w q) k (v ∘ w) := by
    rw [Rose.cooks,Rose.cooks]
    let B := deck (V.layout Y q.F d)
    refine dates_kernel w (V:=leaf G d) (fun i k => coeff k B (v i)) (fun i hi k => by rw [hv i hi, Rose.prime_deck])
      (live Y d q) (live Y d (sample w q)) ?_ k
    intro i u hu
    rw [Rose.lit_up, Rose.lit_up]
    apply congrArg (coeff i)
    unfold Rose.numberA
    have ht : (∏ j, Rose.regal Y d q (chartV q j) (u j)) =
        ∏ i, Rose.regal Y d q (chartV q (w i)) (u (w i)) := by
      refine (Fintype.prod_of_injective w w.injective _ _ (fun i hi => ?_) (fun _ => rfl)).symm
      rw [hu i hi, Rose.oak]
    rw [ht]; rfl
  exact Finset.sum_congr rfl fun i _ => congrArg ((Rose.α Y κ q.F j i) • ·) (h i)

lemma measureX_empty (q : Sample 0) (u : Tags G d 0) (j : ℕ) : Rose.measureₓ Y κ d q j u = coeff j 1 := by
  rw [Rose.measure_paid,Rose.turn_coins]
  have h : mk (fun k => Rose.cooked Y V d q k u) = 1 := by
    ext k
    rw [coeff_mk]
    rw [Rose.cooks, empty_slots (fun i k => coeff k (deck (V.layout Y q.F d)) (u i)) u (live Y d q), Rose.lit_up, Rose.numberA, Fin.prod_univ_zero,
      XSpace.Bare.normalize_unit] -- empty uses univ n
  rw [h, ← coe_substAlgHom (Rose.χday ..),map_one]
end
end YM.FVA2.GradedFar.Subarray

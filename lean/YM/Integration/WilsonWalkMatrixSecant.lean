import YM.Integration.WilsonMatrixInversion
import Mathlib.Algebra.Order.Chebyshev

/-! Second-order cancellation along an original oriented Wilson walk. Every
occurrence refers to its actual link, including repeated and reversed links. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWalkMatrixSecant
open Lattice Wilson
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c : Side}

def occurrences (x : Site c) : Walk → List (Edge (Site c))
  | [] => []
  | d :: w => d.used x :: occurrences (x + d.vec) w

@[simp] theorem length_occurrences (x : Site c) (w : Walk) :
    (occurrences x w).length = w.length := by
  induction w generalizing x <;> simp [occurrences, *]

private def Pair (a b q : G.El) (r : ℝ) : Prop :=
  ‖G.mat a - G.mat q‖ ≤ r ∧ ‖G.mat b - G.mat q‖ ≤ r ∧
    ‖(G.mat a - G.mat q) + (G.mat b - G.mat q)‖ ≤ r^2

private theorem link_pair (g q : G.El) :
    Pair (g*q) (g⁻¹*q) q ‖G.mat g - 1‖ := by
  have submat (u : G.El) : G.mat (u*q) - G.mat q = (G.mat u-1)*G.mat q := by
    rw [G.mat_mul, sub_mul, one_mul]
  have opp : ‖G.mat g⁻¹-1‖ = ‖G.mat g-1‖ :=
    (norm_sub_rev ..).trans (WilsonMatrixInversion.opposite G g)
  have alg : (G.mat g-1)+(G.mat g⁻¹-1)=(G.mat g-1)*(1-G.mat g⁻¹) := by
    rw [sub_mul,mul_sub,mul_one,← G.mat_mul,mul_inv_cancel,G.mat_one,one_mul]
    abel
  refine ⟨?_,?_,?_⟩
  · rw [submat,Gauge.frob_mul_eq _ _ (G.mat_mul_star _)]
  · rw [submat,Gauge.frob_mul_eq _ _ (G.mat_mul_star _),opp]
  · rw [submat,submat,←add_mul,Gauge.frob_mul_eq _ _ (G.mat_mul_star _),alg]
    exact (norm_mul_le ..).trans_eq (by rw [WilsonMatrixInversion.opposite, pow_two])

private theorem inverse_pair {a b q : G.El} {r : ℝ} (h : Pair a b q r) :
    Pair a⁻¹ b⁻¹ q⁻¹ r := by
  simpa only [Pair,G.mat_inv,←star_sub,←star_add,norm_star] using h

private theorem mul_distance (a q y p : G.El) :
    ‖G.mat (a*y) - G.mat (q*p)‖ ≤ ‖G.mat a-G.mat q‖ + ‖G.mat y-G.mat p‖ := by
  have eqn : G.mat (a*y) - G.mat (q*p) =
      (G.mat a-G.mat q)*G.mat y + G.mat q*(G.mat y-G.mat p) := by
    simp only [G.mat_mul,sub_mul,mul_sub]
    abel
  rw [eqn]
  exact (norm_add_le ..).trans_eq (by rw [Gauge.frob_mul_eq _ _ (G.mat_mul_star y),
    Gauge.mul_frob_eq _ _ (G.mat_star_mul q)])

private theorem mul_pair {a b q y z p : G.El} {r s : ℝ}
    (h : Pair a b q r) (k : Pair y z p s) : Pair (a*y) (b*z) (q*p) (r+s) := by
  refine ⟨(mul_distance ..).trans (add_le_add h.1 k.1),
    (mul_distance ..).trans (add_le_add h.2.1 k.2.1),?_⟩
  let X := ((G.mat a-G.mat q)+(G.mat b-G.mat q))*G.mat p
  let Y := G.mat q*((G.mat y-G.mat p)+(G.mat z-G.mat p))
  let Z := (G.mat a-G.mat q)*(G.mat y-G.mat p)
  let W := (G.mat b-G.mat q)*(G.mat z-G.mat p)
  have hx : ‖X‖ ≤ r^2 := by
    dsimp only [X]; rw [Gauge.frob_mul_eq _ _ (G.mat_mul_star p)]; exact h.2.2
  have hy : ‖Y‖ ≤ s^2 := by
    dsimp only [Y]; rw [Gauge.mul_frob_eq _ _ (G.mat_star_mul q)]; exact k.2.2
  have hr : 0 ≤ r := (norm_nonneg _).trans h.1
  have hz : ‖Z‖ ≤ r*s := (norm_mul_le ..).trans (mul_le_mul h.1 k.1 (norm_nonneg _) hr)
  have hw : ‖W‖ ≤ r*s := (norm_mul_le ..).trans (mul_le_mul h.2.1 k.2.1 (norm_nonneg _) hr)
  have eqn : (G.mat (a*y)-G.mat (q*p))+(G.mat (b*z)-G.mat (q*p))=X+Y+Z+W := by
    dsimp only [X,Y,Z,W]
    simp only [G.mat_mul,sub_mul,mul_sub,add_mul,mul_add]
    abel
  rw [eqn]
  have hxy := (norm_add_le X Y).trans (add_le_add hx hy)
  have hxyz := (norm_add_le (X+Y) Z).trans (add_le_add hxy hz)
  exact ((norm_add_le (X+Y+Z) W).trans (add_le_add hxyz hw)).trans_eq (by ring)

private theorem travel_pair (g Q : Config G c) (x : Site c) (w : Walk) :
    Pair (travel (g*Q) x w) (travel (g⁻¹*Q) x w) (travel Q x w)
      (((occurrences x w).map (fun e => ‖G.mat (g e)-1‖)).sum) := by
  induction w generalizing x with
  | nil => simp [occurrences,travel,Pair]
  | cons d w ih =>
    have h := link_pair (g (d.used x)) (Q (d.used x))
    have hd : Pair (d.read (g*Q) x) (d.read (g⁻¹*Q) x) (d.read Q x) ‖G.mat (g (d.used x))-1‖ := by
      by_cases hn : d.neg = true
      · simpa only [Step.read,if_pos hn,Pi.mul_apply,Pi.inv_apply] using inverse_pair h
      · simpa only [Step.read,if_neg hn,Pi.mul_apply,Pi.inv_apply] using h
    exact mul_pair hd (ih (x+d.vec))

/-- The two original walk displacements under common direct and inverse
link noise each cost the sum of the actual observed link chords. -/
theorem variation (g Q : Config G c) (x : Site c) (w : Walk) :
    ‖G.mat (travel (g*Q) x w) - G.mat (travel Q x w)‖ ≤
      ((occurrences x w).map (fun e => ‖G.mat (g e)-1‖)).sum ∧
    ‖G.mat (travel (g⁻¹*Q) x w) - G.mat (travel Q x w)‖ ≤
      ((occurrences x w).map (fun e => ‖G.mat (g e)-1‖)).sum := by
  have h := travel_pair g Q x w
  exact ⟨h.1,h.2.1⟩

private theorem indexed_sum {α : Type*} (f : α → ℝ) (l : List α) :
    (l.map f).sum = ∑ j : Fin l.length, f (l.get j) := by
  nth_rw 1 [←List.ofFn_get l]
  rw [List.map_ofFn,List.sum_ofFn]
  rfl

/-- A single simultaneous inversion cancels the linear term of the complete
matrix word. The price counts each traversed edge with its multiplicity. -/
theorem secant (g Q : Config G c) (x : Site c) (w : Walk) :
    ‖(G.mat (travel (g*Q) x w)-G.mat (travel Q x w))+
      (G.mat (travel (g⁻¹*Q) x w)-G.mat (travel Q x w))‖ ≤
    (w.length : ℝ) * (2*(G.repDim:ℝ)) *
      ((occurrences x w).map (fun e => G.price (g e))).sum := by
  let E := occurrences x w
  let d (i : Fin E.length) := ‖G.mat (g (E.get i))-1‖
  have h := (travel_pair g Q x w).2.2
  rw [indexed_sum] at h
  have hc : (∑ i, d i)^2 ≤ (E.length:ℝ)*∑ i, (d i)^2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin E.length))) (f := d))
  apply (h.trans hc).trans_eq
  have hs : ∀ i, (d i)^2 = (2*(G.repDim:ℝ))*G.price (g (E.get i)) :=
    fun i => (WilsonMatrixInversion.square G _).trans (by ring)
  simp_rw [hs]
  rw [←Finset.mul_sum, indexed_sum]
  dsimp only [E]
  conv_lhs => lhs; rw [length_occurrences]
  exact (mul_assoc ..).symm

end YM.Integration.WilsonWalkMatrixSecant
end

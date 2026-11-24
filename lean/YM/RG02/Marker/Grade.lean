import YM.RG02.Marker.Partition
import YM.RG02.Marker.Product
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Simultaneous grading

Copy the *parameter*, not the random variable. Arbitrary finite
powers can be combined with arbitrary admitted finite insertion orders
by taking a product census with (formal) distinct coupling marks.
An entry carrying k copies of this parameter reads `k!` times the
coefficient; this map respects products. Use `encode` to work in this
finite algebra. The power series API stands for *formal* all-orders
germs (or zero extension from some fixed order); the encoding only
uses the first finite number of coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Grade
open Marker Multi Extra.Trajectories Marks Finset
open scoped BigOperators
variable {ι J : Type} [DecidableEq ι] [DecidableEq J] {R : Census ι}

section Copies
variable (J) [Fintype J]

/-- One mark per copy. -/
def manyX : Poly (full J) := Multi.lambda _ (fun _ => 1)

variable {J}
lemma manyX_nil (k : ℕ) (h : Fintype.card J < k) : manyX J ^ k = 0 := Poly.stops _ (lambda_quiet _) _ h

-- homogeneous determination via scalings. statement also true in any census,
-- but this power-copy calculus uses the full one.
theorem copy_power (k : ℕ) (s : (full J).Mode) : (manyX J^k).part s =
    if k=s.val.card then (k.factorial:ℂ) else 0 := by
  let N := max k (Fintype.card J)
  let R := full J
  let x := manyX J
  have hx : x.part R.quiet=0 := lambda_quiet ..
  let w i := ((i:ℕ).factorial:ℂ)⁻¹ * (x^i).part s
  have he : ∑ i∈range (N+1), Polynomial.monomial i (w i) = Polynomial.monomial s.val.card 1 := by
    apply Polynomial.funext
    intro r
    have ht : (r • x).part R.quiet=0 := by simp only [Poly.part_smul,hx,mul_zero]
    have hb : r • x = Multi.lambda R fun _ => r := by
      unfold x manyX Multi.lambda; rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Multi.send_scale, mul_one]
    have hl : (∑ i∈range (N+1), Polynomial.monomial i (w i)).eval r = (Poly.pass (r • x)).part s := by
      rw [pass_extended _ ht (le_max_right ..),Poly.part_sum,Polynomial.eval_finsetSum]
      refine sum_congr rfl fun i _ => ?_
      rw [Polynomial.eval_monomial, smul_pow, Poly.part_smul, Poly.part_smul]
      unfold w; ring
    rw [hl,hb,Polynomial.eval_monomial,show (Poly.pass (Multi.lambda R fun _ => r)).part s=(∏ _∈s.val,r) from pass_fire (fun _ => r) s,prod_const,one_mul]
  have hg : w k = (Polynomial.monomial s.val.card (1:ℂ)).coeff k := by
    rw [← he, Polynomial.finsetSum_coeff,sum_eq_single_of_mem k (mem_range.mpr (Nat.lt_succ_of_le (le_max_left ..)))]
    · simp
    intro j _ hj; simp [Polynomial.coeff_monomial,hj]
  have hi : (k.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  rw [Polynomial.coeff_monomial] at hg
  unfold w at hg
  by_cases h : k = s.val.card
  · rw [if_pos h]
    rw [if_pos h.symm] at hg
    exact (inv_mul_eq_iff_eq_mul₀ hi).mp (hg.trans rfl) |>.trans (mul_one _)
  rw [if_neg h]
  rw [if_neg (Ne.symm h)] at hg
  exact (inv_mul_eq_iff_eq_mul₀ hi).mp hg |>.trans (mul_zero _)
end Copies

section Encode
open PowerSeries

abbrev mixed (r : ℕ) (R : Census ι) := Marks.together (Marks.full (Fin r)) R

def token (r : ℕ) (R : Census ι) := Pair.embedL R (manyX (Fin r))

def encode (r : ℕ) (x : PowerSeries (Poly R)) : Poly (mixed r R) :=
  ∑ k∈range (r+1), (token r R)^k * Pair.embedR (Marks.full (Fin r)) (PowerSeries.coeff k x)

variable {r : ℕ}

@[simp] lemma token_nil (k : ℕ) (hk : r < k) : (token r R)^k = 0 := by
  unfold token; rw [← map_pow,manyX_nil _ (by simp [hk]),map_zero]

theorem encode_part (x : PowerSeries (Poly R)) (t : (mixed r R).Mode) :
    (encode r x).part t = ((Pair.fst t).val.card.factorial:ℂ) *
        (coeff (Pair.fst t).val.card x).part (Pair.snd t) := by
  unfold encode token
  rw [Poly.part_sum]
  let k := (Pair.fst t).val.card
  have hp : k ≤ r := by simpa using card_le_univ (Pair.fst t).val
  rw [sum_eq_single_of_mem k (Finset.mem_range.mpr (by omega))]
  · rw [← map_pow, Pair.part_product, copy_power k, if_pos (show _ from rfl)]
  intro j _ hj; rw [← map_pow, Pair.part_product, copy_power j, if_neg hj, zero_mul]

@[simp] theorem encode_add (x y : PowerSeries (Poly R)) : encode r (x+y) = encode r x+encode r y := by
  unfold encode; simp only [map_add,mul_add,Finset.sum_add_distrib]
@[simp] theorem encode_zero : encode r (0 : PowerSeries (Poly R))=0 := by simp [encode]
@[simp] theorem encode_one : encode r (1 : PowerSeries (Poly R))=1 := by
  unfold encode; rw [Finset.sum_eq_single 0,PowerSeries.coeff_one,if_pos rfl,map_one,pow_zero,mul_one]
  · intro i _ hi; simp [PowerSeries.coeff_one,hi]
  simp

@[simp] theorem encode_mul (x y : PowerSeries (Poly R)) : encode r (x*y) = encode r x*encode r y := by
  let b (t : ℕ × ℕ) := token r R^(t.1+t.2) * Pair.embedR (full (Fin r)) (coeff t.1 x * coeff t.2 y)
  have he : encode r (x*y) = ∑ k∈range (r+1), ∑ a∈Finset.antidiagonal k, b a := by
    unfold encode
    apply sum_congr rfl; intro i _; rw [PowerSeries.coeff_mul, map_sum, mul_sum]
    apply sum_congr rfl; intro j hj; unfold b; rw [Finset.mem_antidiagonal.mp hj]
  let S := range (r+1)
  let T := (S ×ˢ S).filter (fun i => i.1+i.2 ≤ r)
  have h (j : ℕ×ℕ) (hj : j∈T) : j.1+j.2∈S := mem_range.mpr <| Nat.lt_succ_of_le (mem_filter.mp hj).2
  rw [he]; change (∑ k∈S, ∑ a∈_,b a) = _
  calc
    _ = ∑ k∈S, ∑ a∈T.filter (fun a => a.1+a.2=k), b a := by
      refine sum_congr rfl fun k hk => sum_congr ?_ (fun _ _ => rfl)
      ext p; simp only [T,S,Finset.mem_filter,Finset.mem_product,Finset.mem_range,Finset.mem_antidiagonal] at *; omega
    _ = ∑ a∈T,b a := sum_fiberwise_of_maps_to h _
    _ = ∑ a∈S ×ˢ S,b a := by
      apply sum_subset (filter_subset ..)
      intro j hj hv
      rw [show b j=_ from rfl]; unfold b; rw [token_nil _ (by
        apply Nat.lt_of_not_ge; exact fun ht => hv (mem_filter.mpr ⟨hj,ht⟩)),zero_mul]
    _ = _ := by
      unfold encode; rw [sum_mul_sum,sum_product]; apply sum_congr rfl; intro i _
      apply sum_congr rfl; intro j _
      simp only [b,map_mul,pow_add]; ac_rfl

def encodeHom (r : ℕ) (R : Census ι) : PowerSeries (Poly R) →+* Poly (mixed r R) where
  toFun := encode r
  map_add' := encode_add
  map_mul' := encode_mul
  map_zero' := encode_zero
  map_one' := encode_one

@[simp] theorem encode_pow (x : PowerSeries (Poly R)) (k : ℕ) : encode r (x^k) = encode r x^k :=
  map_pow (encodeHom r R) x k

theorem encode_same {x y : PowerSeries (Poly R)} : encode r x=encode r y ↔
    ∀ i, i≤r → coeff i x=coeff i y := by
  constructor
  · intro h i hi
    ext a
    obtain ⟨z, -, he⟩ := exists_subset_card_eq (s:= @Finset.univ (Fin r) _) (by simpa using hi)
    let t : (full (Fin r)).Mode := ⟨z,mem_univ z⟩
    let p := Pair.mk t a
    apply mul_left_cancel₀ (show (i.factorial : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr i.factorial_ne_zero)
    have hb := congrArg (fun v : Poly (mixed r R) => v.part p) h
    simpa only [encode_part,p, Pair.fst_mk, Pair.snd_mk,t,he] using hb
  intro h; unfold encode; exact sum_congr rfl fun k hk => by rw [h k (Nat.le_of_lt_succ (mem_range.mp hk))]

end Encode
end YM.RG02.Grade

import YM.RG02.Marker.Series

/-!
# Evaluating finite coupled/source Taylor polynomials

*Keep* truncation overflow prior to propagating an error. The multiplication
is the actual disjoint-merge law. Estimates use only the binding `price`
with the *same* weights as both factors.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG02.Evaluation
open Marker Extra.Trajectories Finset Grade PowerSeries Marks
open scoped BigOperators
variable {ι : Type} [DecidableEq ι] {B : Census ι}

def hist (x : Script B) (r : ℕ) (t : ℂ) : Poly B := ∑ i∈range (r+1), t^i • coeff i x

def solo (x : PowerSeries ℂ) (r : ℕ) (t : ℂ) : ℂ := ∑ i∈range (r+1), t^i * coeff i x

@[simp] lemma hist_zero (r : ℕ) (t : ℂ) : hist (0:Script B) r t=0 := by simp [hist]
@[simp] lemma hist_one (r : ℕ) (t : ℂ) : hist (1:Script B) r t=1 := by
  unfold hist; rw [sum_eq_single 0]
  · simp
  · intro i _ h; rw [PowerSeries.coeff_one, if_neg h,smul_zero]
  simp

lemma hist_add (x y : Script B) (r : ℕ) (t : ℂ) : hist (x+y) r t = hist x r t+hist y r t := by
  unfold hist; simp only [map_add,smul_add,sum_add_distrib]
lemma hist_sub (x y : Script B) (r : ℕ) (t : ℂ) : hist (x-y) r t = hist x r t-hist y r t := by
  unfold hist; simp only [map_sub,smul_sub,sum_sub_distrib]
lemma hist_smul (c : ℂ) (x : Script B) (r : ℕ) (t : ℂ) : hist (c • x) r t=c • hist x r t := by
  unfold hist; simp only [coeff_smul,smul_sum]
  apply sum_congr rfl; intro i _; rw [smul_comm]
lemma hist_sum {I : Type*} (s : Finset I) (f : I → Script B) (r : ℕ) (t : ℂ) :
    hist (∑ i∈s,f i) r t=∑ i∈s,hist (f i) r t := by
  unfold hist; simp only [map_sum,smul_sum]; exact sum_comm

def over (r : ℕ) := ((range (r+1)) ×ˢ (range (r+1))).filter (fun i=> r < i.1 + i.2)

def overflow (x y : Script B) (r : ℕ) (t : ℂ) :=
  ∑ p∈over r,t^(p.1+p.2) • ((coeff p.1 x)*(coeff p.2 y))

/-- Exact on *whole tables*, at actual g. Don't assume evaluation
is a homomorphism (only combining the series in `encode`). -/
theorem multiply (x y : Script B) (r : ℕ) (t : ℂ) :
    hist x r t * hist y r t = hist (x*y) r t + overflow x y r t := by
  let w (p : ℕ × ℕ) := t^(p.1+p.2) • (coeff p.1 x * coeff p.2 y)
  let R := range (r+1)
  let S := R ×ˢ R
  let q (p : ℕ × ℕ) := p.1+p.2
  let T := S.filter (fun i=> q i≤r)
  have he : hist x r t * hist y r t = ∑ i∈S,w i := by
    unfold hist; rw [sum_mul_sum]; symm
    rw [show S = _ from rfl]; unfold S; rw [sum_product]; apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _; simp only [w,pow_add, mul_smul,smul_mul_assoc,mul_smul_comm]
    rw [smul_comm]
  rw [he,show ∑ i∈S,w i = ∑ i∈T,w i+∑ i∈over r,w i by
    simpa only [not_le,S,R,T,q,over] using (sum_filter_add_sum_filter_not S (fun i => q i≤r) w).symm]
  congr 1
  have ht : ∀ i∈T,q i∈ R := fun i hi => mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hi).2)
  rw [← sum_fiberwise_of_maps_to ht w]; refine sum_congr rfl fun k hk => ?_
  have ha : T.filter (fun i=>q i=k) = Finset.antidiagonal k := by
    ext j; simp only [R,T,S,mem_filter,mem_product,mem_range,q,mem_antidiagonal] at *; omega
  rw [ha,PowerSeries.coeff_mul,smul_sum]; exact sum_congr rfl fun i hi => by unfold w; rw [mem_antidiagonal.mp hi]

lemma hist_den (x : Script B) (r : ℕ) (t : ℂ) :
    (hist x r t).part B.quiet=solo (den x) r t := by
  unfold hist; rw [Poly.part_sum]; simp only [solo,den,coeff_map,Poly.part_smul]; rfl
lemma scalar_hist (x : PowerSeries ℂ) (r : ℕ) (t : ℂ) :
    hist (scalar B x) r t=Poly.bead B (solo x r t) := by
  unfold hist solo; rw [map_sum]; simp only [scalar, coeff_map, map_mul, Poly.product_bead]

def cost (w : ι → ℝ) (x y : Script B) (r : ℕ) :=
  ∑ p∈over r, Poly.price w (coeff p.1 x) * Poly.price w (coeff p.2 y)

variable {w : ι → ℝ} (hw : ∀ i, 0<w i)
include hw

lemma hist_cost (x : Script B) (r : ℕ) (t : ℂ) :
    Poly.price w (hist x r t) ≤ ∑ i∈range (r+1), ‖t‖^i * Poly.price w (coeff i x) := by
  simpa only [hist,Poly.adapted,norm_pow] using
    (Poly.batch hw (range (r+1)) (fun i : ℕ => (t^i) • coeff i x))

/-- Price even disconnected vacuum terms that survive overflow,
exact norm weights. No implicit loss of η. At arbitrary number of markers,
but the RHS coefficient prices must still be estimated. -/
theorem overflow_cost {t : ℂ} (ht : ‖t‖≤1) (x y : Script B) (r : ℕ) :
    Poly.price w (overflow x y r t) ≤ ‖t‖^(r+1)*cost w x y r := by
  apply (Poly.batch hw ..).trans
  rw [cost,mul_sum]; refine sum_le_sum fun i hi => ?_
  rw [Poly.adapted,norm_pow]; exact mul_le_mul (pow_le_pow_of_le_one (norm_nonneg t) ht (mem_filter.mp hi).2)
    (Poly.multiplication hw _ _) (Poly.nonnegative hw _) (by positivity)

end YM.RG02.Evaluation

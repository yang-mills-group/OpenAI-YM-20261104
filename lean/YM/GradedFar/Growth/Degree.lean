import YM.GradedFar.Growth.Passage

/-!
# Booking crop and substitution on an operator or value
-/
namespace YM.FVA2.GradedFar.Growth
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open Continuation
open scoped Topology BigOperators Classical ContDiff
open MS.Book.Program
variable {G : Gauge} {n d : ℕ} {I J : Type} {a b : ℝ} {p : ℕ}

abbrev Portion (E : Type) := ℕ → E
def blend {E : Type} [AddCommMonoid E] [SMul ℂ E] (K : Portion E) (p : ℕ) (t : ℂ) : E :=
    ∑ i∈Finset.range (p+1), t^i • K i
def earn {E : Type} [SMul ℂ E] (t : ℂ) (x : Portion E) (q : ℕ) := t^q • x q
abbrev tells (V : PowerSeries ℂ) : Portion ℂ := fun i=> coeff i V
abbrev names (V : Guard G d) : Portion (Maps G d) := fun i=> chairs G d (coeff i V)
lemma crop_by (x : PowerSeries ℂ) (p : ℕ) (t : ℝ) : crop p t x= blend (tells x) p (t:ℂ) := by
  simpa only [blend, tells, smul_eq_mul] using (crop_eq p t x)
lemma column_by (x : Guard G d) (p : ℕ) (t : ℝ) : chairs G d (atColumn x p t) = blend (names x) p (t:ℂ) := by
    unfold atColumn blend; rw [map_sum]; simp_rw [_root_.map_smul]
lemma composition_tells (x y : PowerSeries ℂ) (hx : Rooted x) : tells (y.subst x)=Program.substitute x (tells y) := by
    funext i; unfold tells; rw [← Constants.actual_subst _ _ hx,coeff_mk]
lemma composition_names (y : Guard G d) (x : PowerSeries ℂ) : names (Reg.Point.stepV x y)=Program.substitute x (names y) := by
    funext i; unfold names; rw [Reg.Point.stepV,coeff_mk,rules,rules,map_sum]; simp_rw [_root_.map_smul]
lemma blend_substitute {E : Type} [AddCommGroup E] [Module ℂ E] (t : ℂ) (x : PowerSeries ℂ) (y : Portion E) (p : ℕ) (hx : Rooted x):
    blend (Program.substitute x y) p t= ∑ i∈Finset.range (p+1), blend (tells (x^i)) p t • y i := by
    have he (i : ℕ) : Finset.Iic i=Finset.range (i+1) := by ext; simp
    unfold blend; simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i hi
    simp_rw [larger hx (Finset.mem_range_succ_iff.mp hi), Finset.smul_sum,smul_smul,smul_eq_mul,he]
section ring
variable {E : Type} [Ring E] [Algebra ℂ E]
abbrev revenue (x y : Portion E) : Portion E := fun i=> ∑ j∈Finset.HasAntidiagonal.antidiagonal i, x j.1 * y j.2
lemma revenue_tells (x y : PowerSeries ℂ) : tells (x*y)=revenue (tells x) (tells y) := funext fun _=> coeff_mul ..
lemma revenue_names (x y : Guard G d) : names (x*y)=revenue (names x) (names y) := by
    funext i; unfold names; rw [coeff_mul,map_sum]; simp_rw [chairs_mul]
lemma compose_blend (x y : Portion E) (p : ℕ) (t : ℂ) :
    blend x p t * blend y p t= blend (revenue x y) p t +
      ∑ z∈pairsAbove p, t^(z.1+z.2) • (x z.1*y z.2) := by
    let S := ((Finset.range (p+1)) ×ˢ (Finset.range (p+1)))
    let A (z : ℕ × ℕ) := t^(z.1+z.2) • (x z.1*y z.2)
    -- analogous Crop identity but works noncommutatively
    have hp : blend x p t * blend y p t=∑ z∈S,A z := by
      unfold blend S
      rw [Finset.sum_product, Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; unfold A; rw [pow_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    have hU : blend (revenue x y) p t= ∑ z∈S with z.1+z.2∈ Finset.range (p+1), A z := by
      rw [← Finset.sum_fiberwise_eq_sum_filter S (Finset.range (p+1)) (fun q=>q.1+q.2)]
      refine Finset.sum_congr rfl fun i hi=> ?_; unfold revenue; rw [Finset.smul_sum]
      have hi:= Finset.mem_range_succ_iff.mp hi
      rw [show S.filter (fun q=> q.1+q.2=i)=Finset.HasAntidiagonal.antidiagonal i by ext q; simp only [S, Finset.mem_filter,Finset.mem_product,Finset.mem_range_succ_iff,Finset.HasAntidiagonal.mem_antidiagonal]; omega]
      exact Finset.sum_congr rfl fun q hq=>by unfold A; rw [Finset.HasAntidiagonal.mem_antidiagonal.mp hq]
    rw [hp,hU, ← Finset.sum_filter_add_sum_filter_not S (fun z=> z.1+z.2∈Finset.range (p+1))]; rcongr _; simp
end ring

variable (Q : Board I)
def Stock {E : Type} [NormedAddCommGroup E] (Q : Board I) (p : ℕ) (a : ℝ) (x : I→Portion E) := ∀ k≤p,Bill Q 0 a (fun i=> x i k)
namespace Stock
section
variable {E : Type} [NormedRing E] [NormedAlgebra ℂ E]{x y : I→Portion E}
lemma product (hx : Stock Q p a x) (hy : Stock Q p b y) : Stock Q p (a+b) (fun i=> revenue (x i) (y i)) := by
    cases ‹NormedAlgebra ℂ E›
    intro j hj; refine Bill.sum _ ?_ ; intro i hi; have hk:= Finset.HasAntidiagonal.mem_antidiagonal.mp hi
    exact product_fe Q (hx _ (by omega)) (hy _ (by omega))
variable (t : I→ℂ) (ht : Bill Q 1 0 t)
include ht
lemma powers (k : ℕ) : Bill Q k 0 (fun i=> t i^k) := by
    induction k with | zero => simpa only [pow_zero] using no_cost Q (1:ℂ) | succ k h=> simpa only [pow_succ,add_zero] using Bill.prod h ht
lemma past (hx : Stock Q p a x) (hy : Stock Q p b y) :
    Bill Q (p+1) (a+b) (fun i=> blend (x i) p (t i)*blend (y i) p (t i)-blend (revenue (x i) (y i)) p (t i)) := by
  simp_rw [compose_blend,add_sub_cancel_left]
  refine Bill.sum _ fun i hi=> ?_; obtain ⟨⟨h1,h2⟩,hk⟩:= (mem_pairsAbove p i).1 hi
  simpa only [add_zero, zero_add] using product_scalar Q ((powers Q t ht (i.1+i.2)).mono_fee le_rfl (show p+1 ≤ i.1+i.2 from hk))
    (product_fe Q (hx i.1 h1) (hy i.2 h2))
end
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : I→PowerSeries ℂ} {y : I→Portion E}
    (hx : Stock Q p 0 (fun i=>tells (x i))) (hr : ∀ i, Rooted (x i))
    (t : I→ℂ) (ht : Bill Q 1 0 t)
include hx
lemma pulse (k : ℕ) : Stock Q p 0 (fun i=> tells (x i^k)) := by
    induction k with
    | zero => intro j _; simp only [pow_zero]; exact no_cost Q (coeff j (1:PowerSeries ℂ))
    | succ k h=> simp_rw [pow_succ,revenue_tells]; have h := product Q h hx; rw [add_zero] at h; exact h
lemma charged (hy : Stock Q p a y) : Stock Q p a (fun i=> Program.substitute (x i) (y i)) := by
    intro j hj; simp_rw [rules]; refine Bill.sum _ fun k hk=> ?_
    simpa only [zero_add] using product_scalar Q (pulse Q hx k j hj) (hy k ((Finset.mem_Iic.mp hk).trans hj))
include ht
omit hx hr in
lemma cost (x : Stock Q p a y) : Bill Q 0 a (fun i=> blend (y i) p (t i)) := by
    unfold blend; refine Bill.sum _ fun j hj=> ?_
    simpa only [zero_add] using product_scalar Q ((powers Q t ht j).mono_fee le_rfl (Nat.zero_le _)) (x j (Finset.mem_range_succ_iff.mp hj))
lemma paid_pow (k : ℕ) : Bill Q (p+1) 0 (fun i=> (blend (tells (x i)) p (t i))^k - blend (tells (x i^k)) p (t i)) := by
    induction k with
    | zero => simp [blend, tells]; exact Bill.from_zero _
    | succ k ih =>
      let X i:=blend (tells (x i)) p (t i); let y' i:=blend (tells (x i^k)) p (t i)
      have hk := ih.earns (cost Q t ht hx)
      have he:= hk.plus (past Q t ht (pulse Q hx k) hx)
      rw [add_zero (0:ℝ)] at he; simp_rw [pow_succ, revenue_tells]
      apply he.apply_eq (Eventually.of_forall fun i=>?_)
      rw [sub_mul]; abel
include hr
lemma chopped (hy : Stock Q p a y) :
    Bill Q (p+1) a (fun i=> blend (y i) p (blend (tells (x i)) p (t i)) -
      blend (Program.substitute (x i) (y i)) p (t i)) := by
    have he i : blend (y i) p (blend (tells (x i)) p (t i)) -
      blend (Program.substitute (x i) (y i)) p (t i)= ∑ j∈Finset.range (p+1),
        ((blend (tells (x i)) p (t i))^j - blend (tells (x i^j)) p (t i)) • y i j := by
      rw [blend_substitute _ _ _ _ (hr i), blend,← Finset.sum_sub_distrib]; simp only [sub_smul]
    simp_rw [he]; exact Bill.sum _ fun j hj=> by simpa only [add_zero,zero_add] using product_scalar Q (paid_pow Q hx t ht j) (hy j (Finset.mem_range_succ_iff.mp hj))
end
end Stock
end
end YM.FVA2.GradedFar.Growth

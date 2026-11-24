import YM.GradedFar.Crop
import YM.MS.Book.Triang
/-!
# Before log-power-scale frame-composition along the field forecast

Estimates for separately performed substitutions, operator compositions and truncations,
in any cap/norm. Everything is coefficient-first, no valuations from numerical convergence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.Cart
open Function Filter Set PowerSeries
open MS.Book.Program MS.Book.Convolve
open scoped Topology BigOperators Classical
variable {I : Type*} {L : I → ℝ} {J : Type*} {z : I → ℂ} {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] {f f' : I → E} {g : I → F}

abbrev poly (L : I → ℝ) (u : I → ℝ) := ∃ C:ℝ, 0 ≤ C ∧ ∃ k:ℕ, ∀ i, u i ≤ C*(1+|L i|)^k
namespace poly
lemma use {L : I → ℝ} {f g : I→ℝ} (h : poly L f) (hv : ∀ i, g i ≤ f i) : poly L g := by
  obtain ⟨C,hC,k,h⟩:= h; exact ⟨C,hC,k,fun i=> (hv i).trans (h i)⟩
lemma bounded {w : I→ℝ} (h : ∃ C, ∀ i,w i ≤ C): poly L w:=by
 obtain ⟨C,hC⟩:= h; exact ⟨max 0 C,le_max_left ..,0,fun i=>by simpa using (hC i).trans (le_max_right ..)⟩
lemma upgrade {u:I→ℝ}(h:poly L u): ∀ᶠ k:ℕ in atTop,∃ C:ℝ,0≤C ∧ ∀ i,u i≤ C*(1+|L i|)^k:=by
 obtain ⟨C,hC,p,hp⟩:=h; filter_upwards [eventually_ge_atTop p] with k hk; refine ⟨C,hC,fun i=>(hp i).trans ?_⟩; gcongr; exact le_add_of_nonneg_right (abs_nonneg _)
lemma limit {u:I→ℝ}{j:ℕ} (h:∃ C:ℝ,0≤C ∧ ∀ i,u i≤ C*(1+|L i|)^j):
    ∀ᶠ C:ℝ in atTop,∀ i,u i≤ C*(1+|L i|)^j:=by
  obtain ⟨C,hC,h⟩:=h; filter_upwards [eventually_ge_atTop C] with c hc i; exact
    (h i).trans (mul_le_mul_of_nonneg_right hc (by positivity))
lemma restore {u:I→ℝ} (h: ∀ᶠ k:ℕ in atTop, ∀ᶠ C:ℝ in atTop, ∀ i,u i≤ C*(1+|L i|)^k):poly L u:=by
 obtain ⟨k,hk⟩:=h.exists; obtain ⟨C,hC,h⟩:= (hk.and (eventually_ge_atTop 0)).exists; exact ⟨C,h,k,hC⟩
lemma all {a:J→I→ℝ} [Finite J] (hf: ∀ i,poly L (a i)):
    ∀ᶠ k:ℕ in atTop, ∀ᶠ C:ℝ in atTop, ∀ i j,a j i≤ C*(1+|L i|)^k:=by
 filter_upwards [eventually_all.mpr fun i=> (hf i).upgrade] with k hk
 filter_upwards [eventually_all.mpr fun i=> limit (hk i)] with C hC i j; exact hC j i
lemma grows {u v:I→ℝ} (hu:poly L u)(hv:poly L v): poly L (fun i=> u i+v i):=by
 obtain ⟨k,⟨C,hC,h₁⟩,D,hD,h₂⟩:= (hu.upgrade.and hv.upgrade).exists
 exact ⟨C+D,add_nonneg hC hD,k,fun i=> (add_le_add (h₁ i) (h₂ i)).trans_eq (add_mul ..).symm⟩
end poly

def Charge (L:I→ℝ)(f:I→E) := poly L (fun i=> ‖f i‖)
namespace Charge
set_option linter.unusedSectionVars false -- reuse on E F G
lemma cap (hf: ∃ C:ℝ, ∀ i, ‖f i‖ ≤ C): Charge L f := poly.bounded hf
lemma const (a:E): Charge L (fun _=> a) := cap ⟨‖a‖,fun _=>le_rfl⟩
lemma id : Charge L (fun i=> ((L i:ℝ):ℂ)):= ⟨1,zero_le_one,1,fun i=>by simp⟩
lemma add (h: Charge L f)(hv:Charge L f'): Charge L (fun i=> f i+f' i):=
 poly.use (poly.grows h hv) fun _=> norm_add_le ..
lemma sum (s:Finset J) {u:J→I→E}(h: ∀ i∈s,Charge L (u i)): Charge L (fun i=>∑ j∈s,u j i):=by
 induction s using Finset.induction_on with
 | empty=> simp only [Finset.sum_empty]; exact const _
 | insert i s hi ih => simp_rw [Finset.sum_insert hi]; exact add (h i (Finset.mem_insert_self ..)) (ih fun j hj=>h _ (Finset.mem_insert_of_mem hj))
lemma under (m:E→F→G)(C : ℝ)(hC:0≤C)(hm:∀ e f, ‖m e f‖ ≤ C * ‖e‖ * ‖f‖) (he:Charge L f)(hf:Charge L g): Charge L (fun i=> m (f i) (g i)):=by
 obtain ⟨A,hA,k,H⟩:= he; obtain ⟨B,hB,n,H'⟩:= hf; refine ⟨C*A*B,by positivity,k+n,fun i=> (hm _ _).trans ?_⟩;
 calc
   _ ≤ C*(A*(1+|L i|)^k)*(B*(1+|L i|)^n) := by
     specialize H i; specialize H' i; gcongr
   _ = _ := by rw [pow_add]; ring
lemma smul {t:I→ℂ}(he:Charge L t)(hf:Charge L f) : Charge L (fun i=> t i • f i):=
  he.under (· • ·) 1 zero_le_one (fun t x=> by rw [one_mul]; exact (norm_smul ..).le) hf
lemma mul {t v:I→ℂ}(he:Charge L t)(hf:Charge L v) : Charge L (fun i=> t i * v i):= he.smul hf
lemma pow {t:I→ℂ}(h:Charge L t)(n:ℕ): Charge L (fun i=> t i^n):=by
 induction n with
 | zero=> simp_rw [pow_zero]; exact const _
 | succ n ih=> simp_rw [pow_succ]; exact ih.mul h
lemma neg (h:Charge L f): Charge L (fun i=>-f i) := poly.use h (fun i=> le_of_eq (norm_neg (f i)))
lemma across {p : Polynomial ℂ} {t:I→ℂ}(he:Charge L t) : Charge L (fun i=> p.eval (t i)) := by
 induction p using Polynomial.induction_on' with
 | add p q _ _=> simp_rw [Polynomial.eval_add]; exact add ‹_› ‹_›
 | monomial n a=> simp_rw [Polynomial.eval_monomial]; exact (const a).mul (he.pow n)
end Charge

def operation (p:ℕ)(z:ℂ) (f:ℕ→E) := ∑ k ∈ Finset.range (p+1), z^k • f k
abbrev ofPS (f:PowerSeries ℂ) (k:ℕ) := coeff k f
lemma op_crop (p:ℕ)(z:ℝ) (f:PowerSeries ℂ): crop p z f=operation p z (ofPS f):= crop_eq ..
lemma apply_through (p:ℕ)(z:ℂ)(t:Cn)(h:Rooted t) (f:ℕ→E):
    operation p z (substitute t f) = ∑ k∈Finset.range (p+1), operation p z (ofPS (t^k)) • f k:=by
 unfold operation; simp_rw [Finset.sum_smul]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i hi=>?_
 rw [larger h (Nat.le_of_lt_succ (Finset.mem_range.mp hi)), ← Nat.range_succ_eq_Iic, Finset.smul_sum]; simp only [smul_smul,cut,ofPS,smul_eq_mul]

structure Hands {E F G:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][NormedAddCommGroup F][NormedSpace ℂ F][NormedAddCommGroup G][NormedSpace ℂ G]
    (A:E→ₗ[ℂ]F→ₗ[ℂ]G): Prop where
 price : ∃ C:ℝ, 0≤C ∧ ∀ u v, ‖A u v‖≤ C*‖u‖*‖v‖
variable {A : E→ₗ[ℂ] F→ₗ[ℂ] G}
lemma Hands.charge (h:Hands A)(he:Charge L f)(hf:Charge L g): Charge L (fun i=> A (f i) (g i)):= by
 obtain ⟨C,hC,h⟩:= h.price; exact he.under (fun i j=> A i j) C hC h hf

def outsidePay (p:ℕ)(z:ℂ)(A : E→ₗ[ℂ] F→ₗ[ℂ] G)(f:ℕ→E)(g:ℕ→F): G:=
  ∑ x∈skipped p,z^(x.1+x.2-(p+1)) • A (f x.1) (g x.2)
lemma pair (p:ℕ)(z:ℂ)(A : E→ₗ[ℂ] F→ₗ[ℂ] G)(f:ℕ→E)(g:ℕ→F):
    A (operation p z f) (operation p z g) - operation p z (pairW A f g) = z^(p+1) • outsidePay p z A f g:=by
  -- general vector-pair version of `Crop.separate`
  let low (x : ℕ × ℕ) := x.1+x.2 ≤ p
  letI : DecidablePred low := fun i => Nat.decLe (i.1+i.2) p
  let S := Finset.range (p+1)
  let term (x : ℕ×ℕ) := z^(x.1+x.2) • A (f x.1) (g x.2)
  have hu : (S.product S).filter low = S.biUnion (fun i => Finset.antidiagonal i) := by
    ext ⟨i,j⟩
    simp only [S, Finset.mem_range, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_biUnion,
      Finset.mem_antidiagonal, low]
    constructor
    · intro h; exact ⟨i+j, by omega, rfl⟩
    rintro ⟨k,hk,h⟩; omega
  have hd : Set.PairwiseDisjoint (↑S) (fun i : ℕ => Finset.antidiagonal i) := by
    intro i _ j _ h; apply Finset.disjoint_left.mpr
    intro v hx hy; exact h ((Finset.mem_antidiagonal.mp hx).symm.trans (Finset.mem_antidiagonal.mp hy))
  have small : ∑ x ∈ (S.product S).filter low, term x = operation p z (pairW A f g) := by
    rw [hu, Finset.sum_biUnion hd, operation]
    simp_rw [paired, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x hx => by
      simp only [term, Finset.mem_antidiagonal.mp hx]
  rw [sub_eq_iff_eq_add,add_comm]
  calc
    _ = ∑ x ∈ S.product S, term x := by
      rw [Finset.product_eq_sprod, Finset.sum_product, operation, operation]; simp_rw [map_sum, LinearMap.sum_apply]; rw [Finset.sum_comm];
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        unfold term; dsimp only; rw [map_smul A,LinearMap.smul_apply,map_smul, smul_smul,pow_add]
    _ = ∑ x ∈ (S.product S).filter low, term x + ∑ x ∈ skipped p, term x :=
      (Finset.sum_filter_add_sum_filter_not _ low _).symm
    _ = _ := by
      rw [small, outsidePay, Finset.smul_sum, add_right_inj]
      exact Finset.sum_congr rfl fun x hx => by
        rw [smul_smul, ← pow_add, Nat.add_sub_of_le (skipped_spec x hx).2.2]
end YM.FVA2.GradedFar.Cart

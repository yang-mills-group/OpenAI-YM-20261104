import YM.RG06.Weak.Coeffs
import YM.Labels.Grading
/-!
# Slot division and multi-mark coefficients (unmasked bare operator level)

If each leg has zero constant term and every monomial has at least l legs,
this is literal division by l coupling powers AFTER computing the Taylor
coefficients of the full bare stencil. No cancellation assumed based on label
names. Products use independent marker indices (may of course pick
equal operators or locations) and *ordinary* products; no 1/n!, log,
vacuum or internal Wick pairing here. The results apply also before
geometric restriction in configuration space.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Weak
open scoped Topology ContDiff Classical BigOperators
open Finset Function

variable {ι : Type*}

-- factor degree in an unconstrained stencil formula (NOT engineering).
def count (b : ι→₀ ℕ):= b.sum (fun _ k=>k)

theorem scalar_count {S : Type*} [CommSemiring S] (f : ι→ S) (t : S) (b : ι→₀ ℕ) :
    (∏ i∈b.support,(f i * t)^(b i))=(∏ i∈b.support,f i^b i) * t^count b := by
  simp_rw [mul_pow]; rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; rfl

def monoval {S : Type*} [CommSemiring S] (f : ι→ S) (b : ι→₀ ℕ) := ∏ i∈b.support,f i^b i

/-- Substitute the divided letters: keep excess powers explicitly.
Independent procedure on the stencil formula. -/
def divideRecipe (l : ℕ) {S : Type*} [CommSemiring S] (C : ℂ→+* S) (X : S) (a : ι→ S)
    (p : MvPolynomial ι ℂ) : S := ∑ b∈p.support,
          (C (MvPolynomial.coeff b p) * monoval a b) * X^(count b-l)

theorem divideRecipe_exact (l : ℕ) {S : Type*} [CommSemiring S] (C : ℂ→+* S) (X : S) (a : ι→ S)
    (p : MvPolynomial ι ℂ) (h : ∀ b∈p.support,l ≤ count b) :
    divideRecipe l C X a p * X^l=MvPolynomial.eval₂Hom C (fun i=>a i * X) p := by
  unfold divideRecipe
  rw [MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_eq,Finset.sum_mul]; apply Finset.sum_congr rfl; intro b hb
  rw [scalar_count,mul_assoc,←pow_add, Nat.sub_add_cancel (h b hb),mul_assoc]; rfl

theorem divideRecipe_same (l : ℕ) {S : Type*} [CommSemiring S] (C : ℂ→+* S) (X : S) (a : ι→ S)
    (p : MvPolynomial ι ℂ) (h : ∀ b∈p.support,count b=l) :
    divideRecipe l C X a p=MvPolynomial.eval₂Hom C a p:=by
  rw [MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_eq]; unfold divideRecipe monoval
  apply Finset.sum_congr rfl; intro b hb; rw [h b hb,Nat.sub_self,pow_zero,mul_one]

theorem eval_hom (l : ℕ) {S : Type*} [CommSemiring S] (C : ℂ→+* S) (X : S) (a : ι→ S)
    (p : MvPolynomial ι ℂ) (h : ∀ b∈p.support,count b=l) :
    MvPolynomial.eval₂Hom C (fun i=>a i * X) p = MvPolynomial.eval₂Hom C a p * X^l:= by rw [← divideRecipe_exact l C X a p (fun i hi=>(h i hi).ge),divideRecipe_same l C X a p h]

/-- Scalar stencil polynomial, product convention. -/
theorem WritesPS.eval {a : ι→ℝ→ℂ} {b : ι → PowerSeries ℂ} (h : ∀ i, WritesPS (a i) (b i)) (p : MvPolynomial ι ℂ) : WritesPS
    (fun t=> MvPolynomial.eval (fun i=>a i t) p)
    (MvPolynomial.eval₂Hom PowerSeries.C b p) := by
  induction p using MvPolynomial.induction_on with
  | C z=>simp_rw [MvPolynomial.eval_C, MvPolynomial.eval₂Hom_C]; exact WritesPS.constant _
  | add p q hp hq=> simp only [map_add]; exact WritesPS.plus hp hq
  | mul_X p i hp=> simp only [map_mul,MvPolynomial.eval_X,MvPolynomial.eval₂Hom_X']; exact WritesPS.times hp (h i)

def DeSlot (l : ℕ)(v : ℝ→ℂ)(V : PowerSeries ℂ) := WritesPS v (V * PowerSeries.X^l)

theorem DeSlot.coeff {l : ℕ} {v : ℝ→ℂ} {V : PowerSeries ℂ} (h : DeSlot l v V) (k : ℕ) : (↑k.factorial:ℝ)⁻¹ • iteratedDeriv k v 0=
    if l≤k then PowerSeries.coeff (k-l) V else 0 := by rw [Writes.coeff h,PowerSeries.coeff_mul_X_pow']

theorem DeSlot.excess {l : ℕ} {v : ℝ→ℂ} {V : PowerSeries ℂ} (h : DeSlot l v V) (n : ℕ) : (↑((n+l).factorial):ℝ)⁻¹ • iteratedDeriv (n+l) v 0=PowerSeries.coeff n V := by rw [Writes.coeff h,PowerSeries.coeff_mul_X_pow]

def peel (F : ℕ → ℂ):=PowerSeries.mk (fun n=>F (n+1))

theorem peel_exact {F : ℕ→ℂ} (hF : F 0 = 0) : peel F * PowerSeries.X=PowerSeries.mk F:=by
  ext n; cases n <;> simp [peel,hF]

theorem peel_slot {f : ℝ→ℂ} {F : ℕ→ℂ} (he : Writes f F) (hf : f 0=0) : DeSlot 1 f (peel F) := by unfold DeSlot; rw [pow_one,peel_exact (he.origin.trans hf)]; exact he.ps

theorem DeSlot.adjoin {l k : ℕ}{f g : ℝ→ℂ}{F H : PowerSeries ℂ} (h : DeSlot l f F) (hg : DeSlot k g H): DeSlot (l+k) (f*g) (F*H):= by
  have he := WritesPS.times h hg
  unfold DeSlot
  rw [pow_add,mul_mul_mul_comm]; exact he

theorem DeSlot.eval (l : ℕ) {a : ι→ℝ→ℂ}{b : ι→PowerSeries ℂ}(p : MvPolynomial ι ℂ)(h :∀ i,DeSlot 1 (a i) (b i)) (hp : ∀ v∈p.support,l ≤ count v) :
    DeSlot l (fun t=>MvPolynomial.eval (fun i=>a i t) p)
      (divideRecipe l PowerSeries.C PowerSeries.X b p) := by
  unfold DeSlot; rw [divideRecipe_exact l PowerSeries.C PowerSeries.X b p hp]
  apply WritesPS.eval; intro i; simpa only [DeSlot,pow_one] using h i

/-- Multi-mark product before capture. Locations can collide in this
kinematic statement; says nothing about extending through contacts. -/
theorem DeSlot.ordinary (q : Finset ι) {l : ι→ℕ} {a : ι→ℝ→ℂ}{b : ι→PowerSeries ℂ}(h :∀ i∈q,DeSlot (l i) (a i) (b i)) :
    DeSlot (∑ i∈q,l i) (∏ i∈q,a i) (∏ i∈q,b i):= by
    induction q using Finset.induction_on with
    | empty=> rw [Finset.sum_empty,Finset.prod_empty, Finset.prod_empty]; change DeSlot 0 (fun _=>1) _; simpa only [DeSlot,pow_zero,mul_one, map_one] using (WritesPS.constant (1:ℂ))
    | @insert i q he ih=>
      rw [Finset.sum_insert he,Finset.prod_insert he,Finset.prod_insert he]; exact DeSlot.adjoin (h _ (Finset.mem_insert_self ..)) (ih (fun v hv=>h v (Finset.mem_insert_of_mem hv)))

open Labels

theorem sameGrade {G : Gauge}{d w l : ℕ} {v : Label G d} (h : v∈Labels.Grade (w,l)) (b : Labels.Key G →₀ℕ) (hb:b∈ v.val.support) : count b=l := congrArg Prod.snd ((Labels.weight_slot b).symm.trans ((Labels.pure_grade _ _).mp h (MvPolynomial.mem_support_iff.mp hb)))

end YM.RG06.Weak

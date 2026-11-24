import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Real.Basic
/-!
 # Interpolating finite **inherited E** perturbation. Real interval contained in physical price disk. Basis-independent power-series bounds not inferred from bounded unrelated coordinates.
 At *fixed total Taylor order* in log perturbation, finite polynomial in inherited (kept hard exact). `Transfer` lets us calculate its actual coarse-field germ after all integrations and orbit operations. `Lipschitz` charges ℓ-independent sharp loss for degrees 0–2; ℓ-dependent polynomial sampling strings for remaining; no dependence on number of E addresses, measures or other representation/dimension.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Reel
open Function Finset
open scoped BigOperators Classical
-- basic monomial convention
variable {ι E F : Type*}
section poly
variable [AddCommGroup E][Module ℝ E][AddCommGroup F][Module ℝ F]
variable {w:ι → ℝ}{n m:ℕ}{P : Submodule ℝ E}{f g:ι→E}
inductive Filled (P:Submodule ℝ E)(n:ℕ)(w:ι→ℝ): (ι→E)→Prop where
 | shoots (k:ℕ)(h:k≤n)(x:E)(he:x∈P): Filled P n w (fun i=> w i^k • x)
 | adds {f g : ι→E} : Filled P n w f → Filled P n w g → Filled P n w (f+g)

lemma Filled.steady (x:E)(he:x∈P):Filled P n w (fun _=>x):= by simpa using (Filled.shoots (P:=P) (w:=w) 0 (Nat.zero_le n) x he)
namespace Filled
lemma land (h:Filled P n w f) (i:ι): f i∈P := by
  induction h with
  | shoots a _ x hx => exact P.smul_mem _ hx
  | adds _ _ ih hg=> exact P.add_mem ih hg
lemma onward (h:Filled P m w f)(he:m≤n):Filled P n w f:= by
  induction h with
  | shoots a h x he'=> exact shoots a (le_trans h he) x he'
  | adds _ _ ih ih'=> exact ih.adds ih'
lemma transfers (h:Filled P m w f)(a:E→F){U:Submodule ℝ F}(ha: ∀ i∈P, a i ∈U) (hx:∀ i∈P, ∀ j∈P,a (i+j)=a i+a j)(hv:∀ i∈P,∀ c:ℝ,a (c • i) = c • a i):
    Filled U m w (a ∘ f):= by
  induction h with
  | shoots k hr x he => simpa only [Function.comp_def,hv x he] using! shoots (P:=U) (w:=w) k hr (a x) (ha x he)
  | @adds f g hf hg ih ih'=>
     rw [show a∘(f+g)=a∘f+a∘g from funext fun i=> hx (f i) (hf.land i) (g i) (hg.land i)]; exact ih.adds ih'
lemma scaling (h:Filled P n w f)(c:ℝ): Filled P n w (fun i=> c • f i):= h.transfers (c • ·) (fun _ ↦ P.smul_mem _) (fun _ _ _ _=>smul_add ..) (fun _ _ _=>smul_comm ..)
lemma group {S:Type*} (U:Finset S) (f:S→ι→E) (h:∀ s∈U, Filled P n w (f s)): Filled P n w (∑ s ∈ U,f s):= by
  induction U using Finset.induction_on with
  | empty=> rw [sum_empty]; exact Filled.steady _ (zero_mem _)
  | insert s U hs ih=> rw [sum_insert hs]; exact (h s (mem_insert_self ..)).adds (ih fun z hz=> h z (mem_insert_of_mem hz)) -- warning?

lemma times (h:Filled P n w f)(hg:Filled P m w g) (a:E→E→F){U:Submodule ℝ F}(ha: ∀ i∈P, ∀ j∈P,a i j∈U)
    (h₁:∀ i j k,a (i+j) k=a i k+a j k)(h₂:∀ i j k,a i (j+k)=a i j+a i k)(h₃:∀ (c d:ℝ) i j,a (c • i) (d • j)=(c*d) • a i j):
    Filled U (n+m) w (fun i=> a (f i) (g i)):= by
  induction h with
  | @adds f g _ _ ih ih' => simpa only [Pi.add_apply,h₁] using! ih.adds ih'
  | shoots k h x he=>
    induction hg with
    | shoots k' hk z hz=> simpa only [h₃,pow_add] using! (shoots (P:=U) (w:=w) (k+k') (add_le_add h hk) (a x z) (ha x he z hz))
    | adds _ _ ih ih'=> simpa only [Pi.add_apply,h₂] using! ih.adds ih'
end Filled
end poly
section power
variable [Ring E][Module ℝ E]{w:ι → ℝ}{n m:ℕ}{P : Submodule ℝ E}{f g:ι→E}
namespace Filled
lemma power (h:Filled P n w f)(k:ℕ) (hw : (1:E)∈P)(hm:∀ x∈P,∀ y∈P,x*y∈P)(ha:∀ (c d:ℝ)(x y:E),(c • x)*(d • y)=(c*d) • (x*y)): Filled P (n*k) w (f^k):= by
   induction k with
   | zero=> simp only [pow_zero,mul_zero]; exact steady _ hw
   | succ k ih=> rw [pow_succ,mul_add,mul_one]; exact ih.times h (·*·) hm (fun _ _ _=>add_mul ..) (fun _ _ _=>mul_add ..) ha
end Filled
end power
variable [CommRing E] [Module ℝ E] {P:Submodule ℝ E}{w:ι→ℝ}
lemma Filled.accumulate {X:Type*} (A:Finset X) (v:X→ι→E)(n:X→ℕ)(h:∀ i∈A,Filled P (n i) w (v i))(hp:(1:E)∈P)(hm:∀ x∈P,∀ y∈P,x*y∈P)(ha:∀ (c d:ℝ)(x y:E),(c • x)*(d • y)=(c*d) • (x*y)):
    Filled P (∑ i∈A,n i) w (∏ i∈A,v i):= by
  induction A using Finset.induction_on with
  | empty=> rw [prod_empty]; exact steady _ hp
  | insert i A hi ih=> rw [prod_insert hi,sum_insert hi]; exact (h i (mem_insert_self ..)).times (ih fun z hz=> h z (mem_insert_of_mem hz)) (·*·) hm (fun _ _ _=>add_mul ..) (fun _ _ _=>mul_add ..) ha
end YM.LocalTaylorR2.Reel

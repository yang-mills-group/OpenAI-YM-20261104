import YM.MSbar.Super.Foot
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Derivative germs on stencil slots

Use direction test, assigned at site or form level, and germ `fderiv`. For
Bose slots when in Grassmann alphabet; nonnegotiable ordering later when also
with odd fields. Keep recursive order of derivation (front to last). Not a claim
approximating any actual physical quantity, use the indicated germ hypotheses to
invoke Taylor results. Bounds on stencils logically downstream.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Origin
open Function Filter Topology Super
open scoped BigOperators ContDiff InnerProductSpace
variable {α β E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup M] [NormedSpace ℝ M]
variable {f g : E → G} {x : E}
abbrev Eager (f : E → G) (x : E) := ContDiffAt ℝ ω f x

def stunt (f : E → G) (a x : E) := fderiv ℝ f x a
lemma stunt_eager (h : Eager f x) (a : E) : Eager (stunt f a) x := (h.fderiv_right (m:=ω) (by simp)).clm_apply contDiffAt_const
lemma stunt_again (h : Eager f x) (a b : E) : stunt (stunt f a) b x = fderiv ℝ (fderiv ℝ f) x b a := by
  unfold stunt
  let T := ContinuousLinearMap.apply ℝ G a
  have hd := (h.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  change (fderiv ℝ (T ∘ fderiv ℝ f) x) b = _; rw [fderiv_comp _ T.differentiableAt hd,T.fderiv]; rfl
lemma stunt_symm (h : Eager f x) (a b : E) : stunt (stunt f a) b x=stunt (stunt f b) a x := by rw [stunt_again h,stunt_again h]; exact h.isSymmSndFDerivAt (by simp) _ _
lemma Hessian (h : Eager f x) (a b : E) : stunt (stunt f a) b x=iteratedFDeriv ℝ 2 f x ![a,b] := by rw [iteratedFDeriv_two_apply,stunt_symm h a b, stunt_again h]; rfl

def sprig (u : α → E) (x : E) : (E→G) → List α → G
  | f,[] => f x
  | f,a::L => sprig u x (stunt f (u a)) L
variable (u : α→ E)
@[simp] lemma sprig_at (f : E→G) (x) : sprig u x f []=f x := rfl
lemma sprig_step (f : E→G) (x) (a) (L) : sprig u x f (a::L)=sprig u x (stunt f (u a)) L := rfl
lemma sprig_congr (h : f=ᶠ[𝓝 x] g) : sprig u x f=sprig u x g := by
   funext L; induction L generalizing f g with
   | nil => exact h.eq_of_nhds
   | cons a L ih => exact ih (f:=stunt f (u a)) (g:=stunt g (u a)) ((h.fderiv (𝕜:=ℝ)).mono (fun i e => by simp only [stunt,e]))
lemma sprig_add (h : Eager f x) (j : Eager g x) : sprig u x (f+g)=sprig u x f+sprig u x g := by
  funext L; induction L generalizing f g with
  | nil => rfl
  | cons a L ih =>
    simp_rw [sprig_step,Pi.add_apply,sprig_step]; rw [sprig_congr u (f:=stunt (f+g) (u a)) (g:=stunt f (u a)+stunt g (u a)) ?eq, ih (stunt_eager h _) (stunt_eager j _)]
    case eq => filter_upwards [h.eventually (by simp), j.eventually (by simp)] with i h j; simp only [stunt, Pi.add_apply,fderiv_add (h.differentiableAt (by simp)) (j.differentiableAt (by simp)), _root_.add_apply]
    rfl
lemma sprig_post (T : G→L[ℝ] M) (h : Eager f x) : sprig u x (T ∘ f)= T ∘ sprig u x f := by
  funext L; induction L generalizing f with
  | nil => rfl
  | cons a L ih =>
    rw [sprig_step,sprig_congr u (f:=stunt (T ∘ f) (u a)) (g:=T ∘ stunt f (u a)) ?eq, ih (stunt_eager h _)]; rfl
    case eq => filter_upwards [h.eventually (by simp)] with i j; rw [stunt,fderiv_comp _ T.differentiableAt (j.differentiableAt (by simp)), T.fderiv]; rfl
lemma sprig_smul (r : ℝ) (h : Eager f x) : sprig u x (r • f)=r • sprig u x f := sprig_post u (r • (ContinuousLinearMap.id ℝ G)) h
lemma sprig_neg (h : Eager f x) : sprig u x (-f)= - sprig u x f := by simpa using sprig_smul u (-1) h
lemma sprig_zero (x) : sprig u x (0:E→G)=0 := by funext L; induction L <;> simp_all [sprig,show stunt (0:E→G)=0 by funext a b; simp [stunt]]
lemma strokeSum {s : Finset β} {f : β→E→G} (h : ∀ i∈s,Eager (f i) x) : Eager (∑ i∈s,f i) x := by rw [show (∑ i∈s,f i)= (fun v => ∑ i∈s,f i v) from funext fun _ => by simp]; exact ContDiffAt.sum h
lemma sprig_sum (s : Finset β) (f : β→E→G) (h : ∀ i∈s,Eager (f i) x) : sprig u x (∑ i∈s,f i)=∑ i∈s,sprig u x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sprig_zero]
  | @insert i s he ih => rw [Finset.sum_insert he, Finset.sum_insert he, sprig_add u (h _ (by simp)) (strokeSum (fun j hj => h j (by simp [hj]))), ih (fun j hj => h j (by simp [hj]))]
lemma sprig_comp (T : E→L[ℝ] M) {f : M→G} (h : Eager f (T x)) : sprig u x (f ∘ T)=sprig (T ∘ u) (T x) f := by
  funext L; induction L generalizing f with
  | nil => rfl
  | cons a L ih =>
    rw [sprig_step, sprig_congr u (g:=(stunt f (T (u a))) ∘ T) ?ep, ih (stunt_eager h _)]; rfl
    case ep => filter_upwards [(T.continuous.tendsto x).eventually (h.eventually (by simp))] with i j; rw [stunt,fderiv_comp _ (j.differentiableAt (by simp)) T.differentiableAt, T.fderiv]; rfl
lemma sprig_dies (f : E→G) {a : α} (h : u a=0) (x : E) (L) : sprig u x f (a::L)=0 := by rw [sprig_step,h,show stunt f 0=0 by ext; simp [stunt],sprig_zero]; rfl
lemma sprig_agree (h : Eager f x) (a b : α) (L) : sprig u x f (a::b::L)=sprig u x f (b::a::L) := by
  simp only [sprig_step]; exact congrFun (sprig_congr u (f:=stunt (stunt f (u a)) (u b)) ((h.eventually (by simp)).mono (fun _ j => stunt_symm j (u a) (u b)))) L
end YM.MSBar.Origin

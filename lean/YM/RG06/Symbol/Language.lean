import YM.RG06.Classical.Finite
import YM.Labels.Polynomial
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
/-!
# Polynomial language for the continuum dictionary

Use independent variable +1: g (real YM interaction parameter,
not kinetic convention or RG running weight), in coefficients. We work
polynomially, then specialize for all tests. Polynomial identities detected
already at g ≠ 0. Include position variables for the local differential
calculus. Mixed ℤ grading with g:(0,-1) records the difference
`slot count - coupling power`, x:(-1,0) for formal germs. Conjugation is
coefficient only, no position reflection yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Symbols
open Connection Function Filter MvPolynomial
open scoped ContDiff Topology BigOperators
variable {α β : Type}

abbrev Chip (α:Type) := Unit ⊕ α
abbrev Joint (α:Type) := MvPolynomial (Chip α) ℂ

abbrev tap : Joint α:= X (.inl ())
abbrev ink (a:α): Joint α:= X (.inr a)

def views (t:ℝ)(v:α→ℝ) : Joint α→ₐ[ℂ]ℂ:=aeval (Sum.elim (fun _=>t:Unit→ℂ) fun i=>(v i:ℂ))
@[simp] lemma observe_tap (t:ℝ)(v:α→ℝ):views t v tap=(t:ℂ):=by simp [views,tap]
@[simp] lemma observe_ink (t:ℝ)(v:α→ℝ)(a):views t v (ink a)=(v a:ℂ):=by simp [views,ink]
@[simp] lemma observe_C (t:ℝ)(v:α→ℝ)(c:ℂ):views t v (C c)=c:=by simp [views]

theorem detects (p q:Joint α)(h:∀ t≠0,∀ v,views t v p=views t v q):p=q:=by
  classical
  let e (x:{x:ℝ // x≠0}) := (↑(x:ℝ):ℂ)
  let S:= Set.range e
  have hi:S.Infinite:=by
    let f (x:ℕ):{x:ℝ // x≠0}:=⟨x+1,by positivity⟩
    refine (show (Set.range (e ∘ f)).Infinite from ?_).mono ?_
    · refine Set.infinite_range_of_injective (fun x y he => ?_)
      apply_fun Complex.re at he; simp [e,f] at he; exact_mod_cast he
    rintro _ ⟨x,rfl⟩; exact ⟨f x,rfl⟩
  apply funext_set (fun _:Chip α=>S) (fun _=>hi)
  intro x hx; choose y hy using fun k=>hx k (Set.mem_univ k)
  let t:ℝ:=y (Sum.inl ())
  let v(i:α):ℝ:=y (Sum.inr i)
  rw [show x=Sum.elim (fun _:Unit=>(t:ℂ)) (fun i=>(v i:ℂ)) from funext fun i=>by cases i <;> exact (hy _).symm]
  exact h t (y (Sum.inl ())).property v

def install (P:α→Joint β): Joint α→ₐ[ℂ]Joint β:=aeval (Sum.elim (fun _=>tap) P)
@[simp] lemma installed_tap (P:α→Joint β):install P tap=tap:=by simp [install,tap]
@[simp] lemma installed_ink (P:α→Joint β)(a):install P (ink a)=P a:=by simp [install,ink]
@[simp] lemma installed_C (P:α→Joint β)(c:ℂ): install P (C c)=C c:=by simp [install]
lemma sight (P:α→Joint β)(t:ℝ)(u:α→ℝ)(v:β→ℝ)(h:∀ i,views t v (P i)=u i)(x:Joint α):views t v (install P x)=views t u x:=by
  have he:(views t v).comp (install P)=views t u:=by
    ext i; cases i with
    | inl=> change views t v (install P tap)=views t u tap; simp
    | inr i=> change views t v (install P (ink i))=views t u (ink i); rw [installed_ink,h,observe_ink]
  exact DFunLike.congr_fun he x

lemma observes_regular {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{u:E→α→ℂ}(n:WithTop ℕ∞)(hu:∀ i,ContDiffAt ℝ n (fun y=>u y i) x)(p:MvPolynomial α ℂ):
    ContDiffAt ℝ n (fun y=>aeval (u y) p) x:=by
  induction p using MvPolynomial.induction_on with
  | C c=> simp; exact contDiffAt_const
  | add a b ha hb=>simpa using ha.add hb
  | mul_X a i ha=>simp only [map_mul,aeval_X]; exact ha.mul (hu i)

def mirror : Joint α →+* Joint α := MvPolynomial.map (starRingEnd ℂ)
@[simp] lemma mirror_C (c:ℂ) : mirror (α:=α) (C c)=C (star c):=map_C ..
@[simp] lemma mirror_X (a:Chip α):mirror (X a)=X a:=map_X ..
lemma mirror_view (t:ℝ)(v:α→ℝ)(p:Joint α): views t v (mirror p) = star (views t v p):=by
  induction p using MvPolynomial.induction_on with
  | C c=> simp
  | add p q h i=> simp only [map_add,star_add,h,i]
  | mul_X p i h=>
    rw [map_mul,map_mul,h,map_mul,mirror_X]
    simp [views,star_mul]; cases i <;> simp [mul_comm]
@[simp] lemma mirror_mirror (p:Joint α):mirror (mirror p)=p:=detects _ _ fun t ht v=>by simp [mirror_view]

variable (W:α→ℕ)
abbrev charge : Chip α → ℤ×ℤ:=Sum.elim (fun _=>(0,-1)) (fun i=>(W i,1))
abbrev pure (p:Joint α) (d l:ℤ):= IsWeightedHomogeneous (charge W) p (d,l)
lemma graded_substitution {ι π M:Type}[AddCommMonoid M](U:ι→M)(V:π→M)(f:MvPolynomial ι ℂ→ₐ[ℂ]MvPolynomial π ℂ)(h:∀ i, IsWeightedHomogeneous V (f (X i)) (U i)){p:MvPolynomial ι ℂ}{m:M}(hp:IsWeightedHomogeneous U p m): IsWeightedHomogeneous V (f p) m :=by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero=>rw [map_zero]; exact isWeightedHomogeneous_zero ℂ V m
  | add p q hp hq he hv => rw [map_add]; exact he.add hv
  | monomial i c he=>
    have hv: f (C c)=C c:=by simp
    rw [monomial_eq,map_mul,hv,← he,Finsupp.weight_apply]; unfold Finsupp.prod Finsupp.sum; rw [map_prod]
    simp_rw [map_pow]
    apply IsWeightedHomogeneous.C_mul
    exact IsWeightedHomogeneous.prod _ _ _ fun i _=>(h i).pow _
lemma installed_grade (V:β→ℕ)(P:α→Joint β)(h:∀ i,pure V (P i) (W i) 1){p:Joint α}{d l:ℤ}(hc:pure W p d l):pure V (install P p) d l:= by
  refine graded_substitution _ _ _ (fun i=> ?_) hc; cases i with
  | inl u=> change pure V (install P tap) 0 (-1); rw [installed_tap]; exact isWeightedHomogeneous_X ℂ (charge V) (.inl ())
  | inr i=> change pure V (install P (ink i)) (W i) 1; rw [installed_ink]; exact h _
lemma tap_pure : pure W tap 0 (-1):=isWeightedHomogeneous_X ℂ (charge W) (.inl ())
lemma ink_pure (i:α): pure W (ink i) (W i) 1:=isWeightedHomogeneous_X ℂ (charge W) (.inr i)
end YM.RG06.Symbols

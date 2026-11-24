import YM.AnalyticNext.CUBIC_MATCH.Terms.Products
import Mathlib.RingTheory.PowerSeries.Basic
/-!
# Coefficient calculus for the dictionary

Real scalar parameter (includes complex and matrix/color valued curves).
Keep the factorial in the coefficient. `HasCoefficients f c` is a checkable
relation, many concrete independent c supplied elsewhere. `ω` is convenient
for reusing `YM.CubicMatch` local identities; this file gives *finite jet*
identities, does not claim convergence of any perturbative answer. Use only
with unmasked analytic germ, no assumption on inherited RG actions!
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Rules
open Function Filter CubicMatch
open scoped ContDiff Topology BigOperators
variable {E F J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup J] [NormedSpace ℝ J]
  {T : Type*} [NormedRing T] [NormedAlgebra ℝ T]

/-- Ordered Cauchy product; no commutation of the factors. -/
def bilinearCoeff (B : E →L[ℝ] F →L[ℝ] J) (c : ℕ → E) (d : ℕ → F) (k : ℕ) :=
  ∑ i∈Finset.range (k+1), B (c i) (d (k-i))
def times (c d : ℕ → T) (k : ℕ) :=
    ∑ i∈Finset.range (k+1), c i*d (k-i)

def C {I : Type*} [Zero I] (e : I) (k : ℕ) : I := if k=0 then e else 0

structure HasCoefficients (f : ℝ → E) (c : ℕ → E) : Prop where
  regular : ContDiffAt ℝ ω f 0
  get k : term k f = c k

namespace HasCoefficients
variable {f g : ℝ → E} {c d : ℕ → E} {p q : ℝ → T} {a b : ℕ → T} {l : ℝ → F} {t : ℕ → F}

theorem congr
    (hc : HasCoefficients f c) {f' c'} (hv : f=f') (hz : c=c') : HasCoefficients f' c' := hv ▸ hz ▸ hc

theorem unique (hc : HasCoefficients f c) (he : HasCoefficients g d) (h : f =ᶠ[𝓝 0] g) : c = d :=
  funext fun k => (hc.get k).symm.trans ((term_congr h).trans (he.get k))

theorem constant (x : E) : HasCoefficients (fun _=>x) (C x) := by
  refine ⟨contDiffAt_const,fun k=>?_⟩
  by_cases h:k=0 <;> simp [term,C,h,iteratedDeriv_const]

theorem linear (L : E →L[ℝ] F) (hc : HasCoefficients f c) : HasCoefficients (fun x=>L (f x)) (fun k=> L (c k)) := by
  refine ⟨L.contDiff.contDiffAt.comp (f:=f) 0 hc.regular, fun k=>?_⟩
  rw [term_linear L (hc.regular.of_le le_top),hc.get]

theorem add (hc : HasCoefficients f c) (hd : HasCoefficients g d) : HasCoefficients (fun x=> f x+g x) (fun k=> c k+d k) := by
  refine ⟨hc.regular.add hd.regular, fun k=>?_⟩
  rw [term_add (hc.regular.of_le le_top) (hd.regular.of_le le_top),hc.get,hd.get]

theorem sub (hc : HasCoefficients f c) (hd : HasCoefficients g d) : HasCoefficients (fun x=> f x-g x) (fun k=> c k-d k) := by
  refine ⟨hc.regular.sub hd.regular,fun k=>?_⟩
  rw [term_sub (hc.regular.of_le le_top) (hd.regular.of_le le_top),hc.get,hd.get]

theorem smul (z:ℝ) (hc : HasCoefficients f c) : HasCoefficients (fun x=> z • f x) (fun k=> z • c k) :=
  linear (z • ContinuousLinearMap.id ℝ E) hc

theorem neg (hc : HasCoefficients f c) : HasCoefficients (fun x=> -f x) (fun k=> -c k) := by
  simpa using hc.smul (-1)

theorem bilinear (B : E →L[ℝ] F →L[ℝ] J) (hc : HasCoefficients f c) (ht : HasCoefficients l t) :
    HasCoefficients (fun x=> B (f x) (l x)) (bilinearCoeff B c t) := by
  refine ⟨bilin_smooth B hc.regular ht.regular,fun k=> ?_⟩
  simp_rw [term_bilin B k hc.regular ht.regular,hc.get,ht.get]; rfl

theorem mul (ha : HasCoefficients p a) (hb : HasCoefficients q b) : HasCoefficients (fun x=> p x*q x) (times a b) :=
  bilinear (ContinuousLinearMap.mul ℝ T) ha hb

theorem sum {ι : Type*}{p : ι → ℝ → E}{a : ι → ℕ → E} (s : Finset ι) (h : ∀ i∈s, HasCoefficients (p i) (a i)) :
    HasCoefficients (fun x=>∑ i∈s, p i x) (fun k=> ∑ i∈s,a i k) := by
  refine ⟨ContDiffAt.sum fun i hi=> (h i hi).regular, fun k=>?_⟩
  rw [term_sum (fun i hi=> (h i hi).regular.of_le (m:=(k:WithTop ℕ∞)) le_top)]
  exact Finset.sum_congr rfl fun i hi=>(h i hi).get k

theorem head (hc : HasCoefficients f c) : f 0=c 0 := by simpa using hc.get 0
end HasCoefficients

/-- Power series interface (commutative scalar), with real differentiation. -/
abbrev HasSeries (p : ℝ → ℂ) (a : PowerSeries ℂ) := HasCoefficients p (fun k=> PowerSeries.coeff k a)
namespace HasSeries
variable {p q : ℝ → ℂ} {a b : PowerSeries ℂ}

theorem mk (c : ℕ → ℂ) (h : HasCoefficients p c) : HasSeries p (PowerSeries.mk c) := by
  unfold HasSeries; simpa only [PowerSeries.coeff_mk] using h

theorem constant (x : ℂ) : HasSeries (fun _=>x) (PowerSeries.C x) := by
  unfold HasSeries; simp only [PowerSeries.coeff_C]; exact HasCoefficients.constant x

theorem add (ha : HasSeries p a) (hb : HasSeries q b) : HasSeries (fun x=> p x+q x) (a+b) := by
  unfold HasSeries; simpa only [map_add] using! HasCoefficients.add ha hb

theorem coeff_times (k : ℕ) : (PowerSeries.coeff k) (a*b) = times (fun i=> PowerSeries.coeff i a) (fun i=> PowerSeries.coeff i b) k := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_bij (fun v (_:v∈Finset.antidiagonal k)=> v.1) ?_ ?_ ?_ ?_
  · intro ⟨x,y⟩ h; change x ∈ Finset.range (k+1)
    rw [Finset.mem_range]; have he : x+y=k := Finset.mem_antidiagonal.mp h; omega
  · rintro ⟨x,y⟩ hx ⟨u,v⟩ hu h
    have he : x+y=k:=Finset.mem_antidiagonal.mp hx
    have ht : u+v=k:=Finset.mem_antidiagonal.mp hu
    change x=u at h; rw [h,show y=v by omega]
  · intro x hx; have h:=Finset.mem_range.mp hx
    exact ⟨(x,k-x),Finset.mem_antidiagonal.mpr (show x+(k-x)=k by omega),rfl⟩
  · rintro ⟨x,y⟩ hx
    have he : x+y=k:=Finset.mem_antidiagonal.mp hx
    change ((PowerSeries.coeff x a)*PowerSeries.coeff y b)=(PowerSeries.coeff x a)*PowerSeries.coeff (k-x) b
    rw [show k-x=y by omega]

theorem mul (ha : HasSeries p a) (hb : HasSeries q b) : HasSeries (fun x=> p x * q x) (a*b) := by
  unfold HasSeries; simp only [coeff_times]; exact HasCoefficients.mul ha hb

theorem sum {ι:Type*} (s : Finset ι) {f : ι→ ℝ → ℂ}{a : ι→ PowerSeries ℂ} (h : ∀ i∈s, HasSeries (f i) (a i)) :
    HasSeries (fun x=>∑ i∈s,f i x) (∑ i∈s,a i) := by
  unfold HasSeries; simp only [map_sum]; exact HasCoefficients.sum s h

-- independent polynomial label substitutions. Includes powers, support collisions,
-- and sums without polarization.
theorem subst {ι:Type*}{f : ι→ℝ→ℂ}{a : ι→PowerSeries ℂ} (ha : ∀ i,HasSeries (f i) (a i)) (P : MvPolynomial ι ℂ) :
    HasSeries (fun r=>MvPolynomial.eval (fun i=>f i r) P)
      (MvPolynomial.eval₂Hom PowerSeries.C a P) := by
  induction P using MvPolynomial.induction_on with
  | C z=> simpa only [MvPolynomial.eval_C,MvPolynomial.eval₂Hom_C] using constant z
  | add u v h₁ h₂ => simpa only [map_add] using add h₁ h₂
  | mul_X u i uh=> simpa only [map_mul, MvPolynomial.eval_X, MvPolynomial.eval₂Hom_X'] using mul uh (ha i)
end HasSeries
end YM.RG06.Rules

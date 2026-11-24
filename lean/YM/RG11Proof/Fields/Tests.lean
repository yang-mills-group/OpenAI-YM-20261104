import YM.RG11Proof.Jets.Detector
import YM.Euclid.Test

/-!
# From all compact separated profiles to exact finite point tests

At fixed arity and finitely many free kernels one separated compact smooth
complex test realizes the finite list of readings at a given separated
configuration, **exactly** and simultaneously. Simple algebraic dual to the
fundamental lemma `YM.Test.weak_null`; need no nonquantitative mollifier
approximations. No assertion of test positivity, collar width beyond membership
in conf, or bounded test seminorms as arities/location change. In particular
cannot use this to transfer a regulator or actual comparison KNOWN on unrelated
tests; the chosen test must be in its announced finite demand & rate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Fields
open Set Function MeasureTheory Filter
open scoped BigOperators Classical ContDiff Topology
variable {n : ℕ}

theorem price_sum (s t : Test n) {F : Points n→ℂ} (hF : ContinuousOn F (conf n)) :
    (s+t).applyTo F=s.applyTo F+t.applyTo F := by
  unfold Test.applyTo; change (∫ x, (s x+t x)* F x) = _; simp_rw [add_mul]; exact integral_add (s.smearing hF) (t.smearing hF)

theorem price_scale (z : ℂ) (s : Test n) (F : Points n→ℂ) :
    (z • s).applyTo F=z • s.applyTo F := by
  unfold Test.applyTo; change (∫ x, (z * s x)* F x) = _; simp_rw [mul_assoc, ← smul_eq_mul (a:=z)] -- lemma signature
  exact integral_smul ..

variable {I : Type*}
def collect (F : I → Points n → ℂ) (h : ∀ i,ContinuousOn (F i) (conf n)): Test n →ₗ[ℂ] (I→ℂ) where
  toFun f i:= f.applyTo (F i)
  map_add' f u := funext fun i=> price_sum f u (h i)
  map_smul' c f:=funext fun _=> price_scale c f _

variable [Fintype I] [DecidableEq I]
private theorem combo (q : (I→ℂ)→ₗ[ℂ] ℂ) (v : I→ℂ): q v=∑ i,q (Pi.single i 1)*v i:=by
  trans q (∑ i,v i • Pi.single i (1:ℂ))
  · congr 1; ext x
    simp_rw [Finset.sum_apply,Pi.smul_apply]
    rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _) (fun i _ h=>by rw [Pi.single_eq_of_ne (Ne.symm h)]; simp)]
    simp
  simp [map_sum,map_smul,mul_comm]

-- Finite detector existence through all desired field and dimensional
-- components at a single location.
theorem exactTest {x : Points n} (hx : x ∈ conf n) (F : I → Points n→ℂ)
    (H : ∀ i, ContinuousOn (F i) (conf n)) : ∃ t : Test n, ∀ i, t.applyTo (F i) = F i x := by
  let W := LinearMap.range (collect F H)
  suffices (fun i=> F i x)∈ W by
    obtain ⟨t,h⟩:= this; exact ⟨t,fun i=> congrFun h i⟩
  refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).mp ?_
  intro φ hφ
  let a (i:I):=φ (Pi.single (M:=fun _:I=>ℂ) i 1)
  let L(y: Points n):=∑ i,a i*F i y
  have hL : ContinuousOn L (conf n) := continuousOn_finsetSum _ (fun i _=>continuousOn_const.mul (H _))
  have he (f : Test n): f.applyTo L=0:= by
    have h := (Submodule.mem_dualAnnihilator φ).mp hφ (collect F H f) ⟨f,rfl⟩
    rw [combo φ _] at h
    rw [←h]; unfold Test.applyTo L; simp_rw [Finset.mul_sum,mul_left_comm (f _)]
    rw [integral_finsetSum]; swap
    · exact fun i _=> (f.smearing (H i)).const_mul (a i)
    simp_rw [integral_const_mul]; rfl
  simpa only [combo (v:=fun i=>F i x),L,a,Pi.zero_apply] using (Test.weak_null hL).mp he hx
end YM.RG11.Fields

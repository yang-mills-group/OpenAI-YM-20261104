import YM.RGComparison.Core16.Insertions
import YM.RGComparison.Core16.Leading
import YM.Push.FREE_RESOLVENT.GaugeProjection
/-!
# Explicit two-insertion startup test with nonzero leading term

Two actual Wilson-energy-at-face inserts. In the arbitrary finite history and the common kernel,
conditioned at coarsest identity. This test is additional to the entire graded section family of
inserts. Aims to expose all steps at nonzero order of inserted kernels, even if some section columns
happen to evaluate to low rank for a particular choice of tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Descent
open Lattice RG Tree Wilson Precision Push.BetaTransport
open Function Filter MeasureTheory Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open PertExtension PertExtension.Series Tested Radial GaussianScore
open Work.F03
variable {G : Gauge} {n c m : Side} (d : Descent n c) (t : d.Tags) (P : ChartRatio G) (R : LocalRatio P)
    (i j : Face (Per n))

def face (G : Gauge) {n : Side} (i : Face (Per n)) (U : Config G n) := G.price (faceValue U i)

local notation "E" => Coordinates G d
lemma face_test : Testable (G := G) d (face G i) := by
  refine ⟨G.continuous_price.comp (continuous_travel ..), fun t U => ?_, ?_⟩
  · unfold face; rw [face_gauge,G.price_conj]
  simp_rw [comp_def,path_top]
  have h : ContDiffAt ℝ ∞ (fun V : Push.In G n => face G i (represent V)) (topDir d 0) := by
    rw [map_zero]; exact (Work.F03.price_smooth (A := fun v : Push.In G n => faceValue (represent v) i) (Push.writes ..)).of_le le_top
  exact h.comp (f:=topDir d) _ ((topDir d).toContinuousLinearMap.contDiff.contDiffAt)

local notation "g" i => face G i ∘ d.fine 1 ∘ d.tablePath

-- true Taylor normalization on each face, no covariance ansatz
lemma graded_face : d.grade (face G i) 2 := by
  intro x
  let f (r : ℝ) := (g i) (r • x)
  have hf (r) : f r = G.price (faceValue (represent (r • topDir d x)) i) := by
    unfold f; rw [comp_def, comp_def]; simp_rw [path_top,map_smul]; rfl
  have hi := price_limit (V:=fun r : ℝ => faceValue (represent (r • topDir d x)) i)
    (by rw [zero_smul]; exact Push.stroll_zero ..) (face_deriv ..)
  let C := ‖faceCurl i (topDir d x)‖^2 / 2; have he := hi.eventually (gt_mem_nhds (show C < C+1 by linarith))
  have h : Tested.germ ≤ 𝓝[≠] 0 := nhdsWithin_mono _ (fun r hr => ne_of_gt (show 0<r from hr))
  refine ⟨C+1,by unfold C; positivity,?_⟩
  filter_upwards [he.filter_mono h,eventually_pos] with a hv ha
  change ‖f a‖ ≤ _; rw [hf,Real.norm_of_nonneg (G.price_range _).1]; exact (lt_of_lt_of_le ((div_lt_iff₀ (pow_pos ha 2)).mp hv) le_rfl).le

lemma face_jet (x : E) : jet (face G i ∘ d.fine 1 ∘ d.tablePath) 2 x = ‖faceCurl i (topDir d x)‖^2 / 2 := by
  have hf := face_test d i (G:=G); let A := face G i ∘ d.fine 1 ∘ d.tablePath
  have H := directions hf.smooth x
  have hi := price_limit (V:=fun r : ℝ => faceValue (represent (r • topDir d x)) i)
    (by rw [zero_smul]; exact Push.stroll_zero ..) (face_deriv ..)
  have h : Tested.germ ≤ 𝓝[≠] 0 := nhdsWithin_mono _ (fun r hr => ne_of_gt (show 0<r from hr))
  have Ht : Aspiration (fun r : ℝ => r⁻¹ ^ 2 • A (r • x)) (fun j => jet A (2+j) x) := H.shift (fun j hj => H.vanish (graded_face d i x) hj)
  refine tendsto_nhds_unique Ht.tendsto_first ((hi.mono_left h).congr' ?_)
  filter_upwards with a
  unfold A
  simp_rw [comp_apply,path_top,map_smul,inv_pow, face, smul_eq_mul, div_eq_mul_inv]; ring


section positive
open Matrix FreeResolvent Exterior

-- Lift an arbitrary direction modulo interior gauge. Apply to ALL faces in the true integration
-- slice, so they have nonzero Gaussian costs even if reader picks a face different from its root.
private lemma realized (S : StepData c n) (T : Forest S.ratio) (v : Push.In G n) :
    ∃ x : T.Free → G.Color, dColor G n 1 (sliceCoord S T x) = dColor G n 1 v := by
  let u := flatten v; let w := representative S T u
  let x := profile T (w ∘ plant (G:=G) T)
  have he : flatten (sliceCoord S T x) = w := by
    have hf := projects (G:=G) T w (onto_slice T u)
    have hz : reduce G S T *ᵥ w = active T x := reduce_actual ..
    rw [hz, chart_flow] at hf; exact hf
  refine ⟨x,?_⟩
  ext i j
  change ((Exterior.d 1 n)*ᵥ parts G 1 (sliceCoord S T x) j) i = ((Exterior.d 1 n)*ᵥ parts G 1 v j) i
  rw [← component_flat, he, ← component_flat v j]
  have hp : component w j = component u j + Exterior.d 0 n *ᵥ component (potential (S:=S) T u) j := by rw [← component_mul];rfl
  rw [hp,mulVec_add, mulVec_mulVec, Exterior.closed, Matrix.zero_mulVec, add_zero]

/-- Any nonempty history ends in some full top tree slice; each rank jet of the inserted face
reads this linear subspace. -/
lemma top_full (he : d.depth ≠ 0) (v : Push.In G n) :
    ∀ (y : Push.In G c), ∃ x : Coordinates G d, dColor G n 1 (liftEnd d (y,x)) = dColor G n 1 v := by
  induction d with
  | nil => exact False.elim (he rfl)
  | @push m i S T d ih =>
    intro y
    cases d with
    | nil =>
      obtain ⟨x,hx⟩ := realized S T v; refine ⟨(Sum.elim x fun _ => 0),?_⟩; exact hx
    | push A P d =>
      specialize ih (by intro h; rw [depth] at h; omega)
      let z := ih (sliceCoord S T (G:=G) 0); refine ⟨Sum.elim (fun _=>0) z.choose,?_⟩
      exact z.choose_spec

private lemma face_pulse (h : G.Simple) (hn : 1 < n.val) : ∃ v : Push.In G n, faceCurl i v ≠ 0 := by
  haveI := h.nontrivial_color; obtain ⟨y,hy⟩ : ∃ y : G.Color, y≠0 := exists_ne _
  let a := i.2.val.1; let b := i.2.val.2; let v : Push.In G n := Pi.single (i.1,coord a) y
  refine ⟨v,?_⟩; have he : i.1 + step b ≠ i.1 := by
    haveI : NeZero n.val:= ⟨by omega⟩
    haveI : Fact (1<n.val) := ⟨hn⟩
    intro e; have hstep := add_left_cancel (e.trans (add_zero _).symm)
    have ho := congr_fun hstep b; simp at ho
  apply ne_of_eq_of_ne _ hy
  ext k
  change ((Exterior.d 1 n) *ᵥ parts G 1 v k) (i.1, plaquette i.2) = y k
  have hA : coord b ≠ coord a := fun e => (show a<b from i.2.property).ne' ((coord_iff ..).mp e)
  rw [Exterior.d_plaquettes]; change v _ k - v _ k - (v _ k - v _ k) = _
  simp only [v, a, b] at hA he ⊢; simp [he,hA]

lemma two_pulse (h : G.Simple) (hn : 1 < n.val) (he : d.depth ≠ 0) :
    ∃ x : E, 0 < jet (g i) 2 x ∧ 0 < jet (g j) 2 x := by
  have h₁ q : ∃ x : E, faceCurl q (topDir d x) ≠ 0 := by
    obtain ⟨v,hv⟩ := face_pulse q h hn
    obtain ⟨x,hx⟩ := top_full d he v 0
    exact ⟨x,fun hh => hv (by unfold faceCurl; rw [← hx];exact hh)⟩
  obtain ⟨x,hx⟩ := h₁ i; obtain ⟨y,hy⟩ := h₁ j
  have hr : ∃ x : E, faceCurl i (topDir d x) ≠0 ∧ faceCurl j (topDir d x) ≠0 := by
    by_cases h : faceCurl j (topDir d x)=0; swap;exact ⟨x,hx,h⟩
    by_cases he : faceCurl i (topDir d y)=0; swap; exact ⟨y,he,hy⟩
    have hh q : faceCurl q (topDir d (x+y))=faceCurl q (topDir d x)+faceCurl q (topDir d y):=by
      ext k; rw [map_add]; simp_rw [faceCurl,dColor, parts_add, Matrix.mulVec_add]; rfl
    refine ⟨x+y,?_,?_⟩
    · rwa [hh i,he,add_zero]
    rwa [hh j,h,zero_add]
  obtain ⟨v,hv,hB⟩ := hr
  rw [← norm_ne_zero_iff] at hv hB
  refine ⟨v,?_⟩; rw [face_jet,face_jet]; constructor <;> positivity
end positive

def sqPair (U : Config G n) := face G i U * face G j U

lemma meets : Testable d (sqPair (G:=G) i j) ∧ d.grade (sqPair (G:=G) i j) 4 := by
  have h := face_test d i (G:=G); have hf := face_test d j (G:=G)
  refine ⟨⟨h.neat.mul hf.neat, fun t U => congr_arg₂ (· * ·) (h.invariant t U) (hf.invariant t U), h.smooth.mul hf.smooth⟩, fun x => ?_⟩
  exact bill_mul (graded_face d i x) (graded_face d j x)

include R
/-- Nonzero of the order zero *after* dividing out the external coupling powers; fourth moment
of the fixed θ-independent joint conditional Gaussian. Any pair, in particular strictly separated.
-/
theorem two_positive (h : G.Simple) (hR : d.Room G) (hn : 1 < n.val) (he : d.depth ≠ 0)
    (u : ℕ → ℝ) : 0 < ranking P d u (sqPair i j) 4 := by
  obtain ⟨x,hx,hy⟩ := two_pulse d i j h hn he
  have hv (x : E) : jet (sqPair i j ∘ d.fine 1 ∘ d.tablePath) 4 x = jet (g i) 2 x * jet (g j) 2 x := head_product
    (face_test d i (G:=G)).smooth (face_test d j (G:=G)).smooth (graded_face d i) (graded_face d j) x
  obtain ⟨hh,hP⟩ := meets d i j (G:=G)
  refine ranking_positive P R hh hP u hR (fun y => ?_) (x:=x) ?_
  · rw [hv,face_jet,face_jet]; positivity
  rw [hv]; exact mul_pos hx hy
end YM.RGComparison.Core16.Descent

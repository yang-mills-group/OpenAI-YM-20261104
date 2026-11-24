import YM.OPE.Compatible.Kernel
import YM.OPE.Compatible.Haar
import YM.MultipleContact.Detector
import YM.OPE.Interpolate.Chart

/-!
# Primitive averaged projection for a finite detector horizon

Fix O(4) orbits of actual unselected-separation detectors. For each element
of the orbit keep positions *and* tensor spin components; use also real
averaging on complex field quotients. Acts on the *complete* product.
Here x is a tuple relative to its center.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov
open Function Set Filter Table MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L} {T : Table L}
variable {I J : Type} [Fintype I] [Fintype J] {d : ℕ}

abbrev Prism := MultipleContact.Detector S d
-- use Flex named notation in explicit arguments
def Nets (S : Table L) := ∀ d, MultipleContact.Detector S d

namespace Survey
variable (R : S.Rotation) (D : Prism (S:=S) (d:=d))

def gap : ℝ := (MultipleContact.detector_clearance D).choose
lemma gap_pos : 0 < gap D := (MultipleContact.detector_clearance D).choose_spec.1
lemma offsets_pay (e : D.probes) (i : Fin e.val.n) : gap D ≤ ‖bearing e.val i‖ :=
  (le_trans (by linarith only [gap_pos D] : gap D ≤ 2 * gap D)
    ((MultipleContact.detector_clearance D).choose_spec.2 e.val e.property i))

def placements (e : Exterior L) (K : Ortho) : Fin e.n → E4 :=
  Ortho.move K ∘ bearing e
def labelSet (R : S.Rotation) (e : Exterior L) (K : Ortho) : Fin e.n → S.Tag :=
  R.label K ∘ (S.classTokens ∘ e.letter)

def sized (x : I → E4) : Prop := Injective x ∧ ∀ i, ‖x i‖ < gap D
lemma openSized : IsOpen {x : I → E4 | sized D x} :=
  open_inj.inter (by
    change IsOpen {x : I → E4 | ∀ i, ‖x i‖ < gap D}
    rw [setOf_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt ((continuous_apply i).norm) continuous_const))
lemma lives {x : I → E4} (hx : sized D x) (e : D.probes) (K : Ortho) :
    Injective (beside x (placements e.val K)) := by
  have he := (beside_distinct.mp (bearing_clear e.val)).2.1
  refine beside_distinct.mpr ⟨hx.1, (Ortho.move_injective K).comp he, fun i j hp => ?_⟩
  have hi := hx.2 i
  rw [hp,show ‖placements e.val K j‖ = ‖bearing e.val j‖ from (Ortho.motion K).norm_map _] at hi
  exact not_lt.mpr (offsets_pay D e _) hi
omit [Fintype I] in
lemma sized_move (K : Ortho) {x : I → E4} (hx : sized D x) : sized D (Ortho.move K ∘ x) :=
  ⟨(Ortho.move_injective K).comp hx.1, fun i =>
    lt_of_eq_of_lt ((Ortho.motion K).norm_map _) (hx.2 i)⟩
omit [Fintype I] [Fintype J] in
lemma sized_perm (e : J ≃ I) {x : I → E4} (hx : sized D x) : sized D (x ∘ e) :=
  ⟨hx.1.comp e.injective, fun i => hx.2 (e i)⟩
lemma sized_zero : sized D (sole (0:E4)) := by
  refine ⟨injective_of_subsingleton _,?_⟩
  intro; unfold sole; simpa only [norm_zero] using gap_pos D
lemma sizedBeside {x : I → E4} {y : J → E4} (hx : sized D (beside x y)) : sized D y :=
  ⟨(beside_distinct.mp hx.1).2.1, fun i => hx.2 (.inr i)⟩

/-- Orbital averages always taken at unselected S. -/
def shot (x : I → E4) (p : I → S.Tag) (K : Ortho) : S.Field d :=
  R.act d K (D.decode fun e : D.probes =>
    kernel S (beside x (placements e.val K)) (beside p (labelSet R e.val K)))

def raw (x : I → E4) (p : I → S.Tag) : S.Field d := ∫ K, shot R D x p K ∂angles

/-- Primitive projection. At each grade the detectors have fixed unscaled
size and clearance; no attempt to fit all infinitely many detectors at one
nonzero scale. Use only in their stated separated domains. -/
def projection (ρ : S.RealSpin) (x : I → E4) (p : I → S.Tag) : S.Field d :=
  (2:ℂ)⁻¹ • (raw R D x p + S.conj ρ d (raw R D x (conjugate ρ ∘ p)))

section Smooth

-- compact parameter record, plain product of normed spaces to expose ambient derivatives
private def dE (e : Exterior L) : Fin e.n → ℕ := fun i => (e.letter i).1
private abbrev Area :=
  ((e : (↑D.probes : Type)) → Fin e.val.n → E4) ×
  ((e : (↑D.probes : Type)) → Slots S (dE e.val)) ×
  (S.Field d →L[ℝ] S.Field d)

private def tour (K : Ortho) : Area D :=
  (fun e => placements e.val K, fun e i => (labelSet R e.val K i).2,
    LinearMap.toContinuousLinearMap ((R.act d K).toLinearMap.restrictScalars ℝ))

private def evaluate (p : I → S.Tag) (xy : (I → E4) × Area D) : S.Field d :=
  xy.2.2.2 (D.decode fun e : D.probes =>
    kernel S (beside xy.1 (xy.2.1 e)) (beside p (stockTag (xy.2.2.1 e))))

variable {R} {P : DiffPlan S} {ρ : S.RealSpin}
  (H : R.Laws P ρ) (hT : S.Smooth) (p : I → S.Tag)

private lemma evaluate_tour (R : S.Rotation) (x : I → E4) (K : Ortho) :
    evaluate D p (x,tour R D K) = shot R D x p K := rfl

include hT
private lemma evaluate_smooth (y : I → E4) (z : Area D)
    (h : ∀ e : D.probes, Injective (beside y (z.1 e))) :
    ContDiffAt ℝ ∞ (evaluate D p) (y,z) := by
  let A := (I → E4) × Area D
  let B := fun (v:A) (e:D.probes) =>
    kernel S (beside v.1 (v.2.1 e)) (beside p (stockTag (v.2.2.1 e)))
  have he : ContDiffAt ℝ ∞ B (y,z) := by
    refine contDiffAt_pi.mpr ?_
    intro e
    let M := beside (fun i => (p i).fst) (dE e.val)
    let pos : A → I ⊕ (Fin e.val.n) → E4 := fun v => beside v.1 (v.2.1 e)
    let label (v : A) : Slots S M := Sum.rec (motive:=fun i => S.Field (M i))
      (fun i => (p i).2) (v.2.2.1 e)
    have hu : (fun v : A => B v e) = (fun xy => kernel S xy.1 (stockTag xy.2)) ∘
        (fun v => (pos v,label v)) := by
      ext1 v; unfold B
      apply congr_arg (kernel S (pos v))
      ext1 i; cases i <;> rfl
    -- pi projection definitionally point
    change ContDiffAt ℝ ∞ (fun v => B v e) _
    rw [hu]
    refine ContDiffAt.comp (y,z) (smooth_joint S hT _ (pos (y,z)) (h e) (label (y,z))) ?_
    refine ContDiffAt.prodMk ?_ ?_
    · refine contDiffAt_pi.mpr ?_
      rintro (i | i)
      · exact contDiffAt_pi.mp (contDiffAt_fst (𝕜:=ℝ) (n:=∞)) i
      let f : A → _ := fun v => v.2.1
      have ht : ContDiffAt ℝ ∞ f (y,z) := contDiffAt_fst.comp _ contDiffAt_snd
      exact contDiffAt_pi.mp (contDiffAt_pi.mp ht e) i
    refine contDiffAt_pi.mpr ?_
    rintro (i|i)
    · exact contDiffAt_const
    let f : A → _ := fun v => v.2.2.1
    have ht : ContDiffAt ℝ ∞ f (y,z) := contDiffAt_fst.comp _ (contDiffAt_snd.comp _ contDiffAt_snd)
    exact contDiffAt_pi.mp (contDiffAt_pi.mp ht e) i
  let F := LinearMap.toContinuousLinearMap (D.decode.restrictScalars ℝ)
  let f : A → (S.Field d →L[ℝ] S.Field d) := fun v => v.2.2.2
  have hf : ContDiffAt ℝ ∞ f (y,z) := contDiffAt_snd.comp _ (contDiffAt_snd.comp _ contDiffAt_snd)
  exact hf.clm_apply (F.contDiff.contDiffAt.comp (y,z) he)

include H
omit hT in
private lemma tour_cont : Continuous (tour R D) := by
  let v : Ortho → _ := fun K => (tour R D K).2
  have ht : Continuous v := by
    refine Continuous.prodMk ?_ (linear_orbit _ H d)
    exact continuous_pi (f:=fun K => (tour R D K).2.1) (fun e => by
      refine continuous_pi (f:=fun K => (tour R D K).2.1 e) ?_
      intro i
      exact H.spin ((e.val.letter i).1) (S.classTokens (e.val.letter i)).2)
  refine Continuous.prodMk ?_ ht
  exact continuous_pi fun e => continuous_pi fun i => continuous_orbit (bearing e.val i)
lemma shot_cont {x : I → E4} (hx : sized D x) : Continuous (shot R D x p) := by
  rw [show shot R D x p = fun K => evaluate D p (x,tour R D K) from funext fun K => (evaluate_tour ..).symm]
  apply continuous_iff_continuousAt.mpr
  intro K
  exact ((evaluate_smooth D hT p x _ (fun e => lives D hx e K)).continuousAt).comp
    (f:=fun k => (x,tour R D k)) (continuousAt_const.prodMk (tour_cont D H).continuousAt)
lemma shot_integrable {x : I → E4} (hx : sized D x) : Integrable (shot R D x p) angles :=
  (shot_cont D H hT p hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma raw_smooth {x : I → E4} (hx : sized D x) : ContDiffAt ℝ ∞ (fun y => raw R D y p) x := by
  unfold raw
  simp_rw [← evaluate_tour]
  have hh := integral_orbits (tour R D) (tour_cont D H) _ (openSized D) (evaluate D p)
    (fun y hy t => evaluate_smooth D hT p y _ (fun e => lives D hy e t))
  exact (hh x hx).contDiffAt ((openSized D).mem_nhds hx)
lemma projection_smooth {x : I → E4} (hx : sized D x) :
    ContDiffAt ℝ ∞ (fun y => projection R D ρ y p) x :=
  ((raw_smooth D H hT p hx).add
    (ContDiffAt.comp x (reflectionC ρ d).contDiff.contDiffAt
      (f:=fun y => raw R D y (conjugate ρ ∘ p)) (raw_smooth D H hT _ hx))).const_smul _ -- parentheses?
end Smooth
end Survey
end YM.OPE.Cov

import YM.Pert.Position.Frame
import YM.SchemeConversionRG11.Field.Restriction

/-!
# Operations on field frames

Uses the actual finite-dimensional free filtered field system, with its symmetries. `after`
is defined even on nonunits, so kill-unit *increments* (including scale-law derivations)
can work in the same subspace.
-/

set_option autoImplicit false
noncomputable section

namespace YM.SchemeConversionRG11.Affine

open Function Filter Submodule Pert.Position Horizon
open scoped Topology ContDiff

variable {G : Gauge} {F : Labels.Frames G} {d e : ℕ}

local notation "O" => operator F d

local notation "U" => Buffer F d

private def project (F : Labels.Frames G) (j : ℕ) : operator F j →L[ℝ] Buffer F j :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := operator F j) (F' := Buffer F j)
    (LinearMap.leftInverse (K := ℝ) (V := Buffer F j) (V' := operator F j) ((buffers F j).subtype))

private lemma project_val (v : O) (hv : v ∈ buffers F d) : (project F d v).val = v :=
  congrArg Subtype.val (LinearMap.leftInverse_apply_of_inj (buffers F d).ker_subtype (⟨v,hv⟩ : U))

def along (x y : Buffer F d) : Buffer F d := project F d (x.val * y.val)

theorem along_at (x y : U) : (along x y).val = x.val * y.val := by
  refine project_val _ ⟨?_,?_,?_,?_,?_⟩
  · change x.val (y.val _) = 0; rw [y.property.1,map_zero]
  · intro e he p hp; exact x.property.2.1 _ he _ (y.property.2.1 _ he _ hp)
  · intro p
    change (Maxwell.freeTable _).conj _ _ (x.val (y.val p)) = x.val (y.val _)
    rw [x.property.2.2.1, y.property.2.2.1]
  · intro s p
    change Extra.FD.rideO _ _ _ (x.val (y.val p)) = x.val (y.val _)
    rw [x.property.2.2.2.1, y.property.2.2.2.1]
  intro p
  change x.val (y.val (Complex.I • p)) = Complex.I • x.val (y.val p)
  rw [y.property.2.2.2.2,x.property.2.2.2.2]

def after (b c : Buffer F d) := b+c+along b c

theorem motor_injective : Injective (motor F (d := d)) :=
  fun _ _ h ↦ Subtype.ext (add_left_cancel h)

theorem after_at (x y : U) : motor F (after x y) = motor F x * motor F y := by
  unfold motor after; simp only [coe_add, along_at, mul_add, add_mul, mul_one, one_mul]; abel

@[simp] theorem motor_zero : motor F (0 : U) = 1 := by unfold motor; exact add_zero _

@[simp] theorem after_zero_left (x : U) : after 0 x = x := motor_injective (by rw [after_at, motor_zero, one_mul])

@[simp] theorem after_zero_right (x : U) : after x 0 = x := motor_injective (by rw [after_at, motor_zero, mul_one])

theorem nested (h : d ≤ e) (x y : Buffer F e) :
    restr F h (after x y) = after (restr F h x) (restr F h y) := by
  apply motor_injective; ext1 p
  apply incl_injective F h
  rw [motors, after_at, after_at]; change motor F x (motor F y (incl F _ _)) =
    incl F h (motor F _ (motor F _ _))
  rw [motors, motors]

lemma motor_regular : ContDiff ℝ ω (motor F (d := d)) :=
  contDiff_const.add (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=U) (F:=O) ((buffers F d).subtypeL : U →L[ℝ] O))

theorem after_regular : ContDiff ℝ ω (fun x : U × U ↦ after x.1 x.2) := by
  have he : ContDiff ℝ ω (fun x : U ↦ x.val) := ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=U) (F:=O) (buffers F d).subtypeL
  have hl : ContDiff ℝ ω (fun x : U × U ↦ x.1.val * x.2.val) := by
    have hf : ContDiff ℝ ω (fun x : U × U ↦ x.1.val) := he.comp contDiff_fst
    have hs : ContDiff ℝ ω (fun x : U × U ↦ x.2.val) := he.comp contDiff_snd
    exact hf.clm_comp hs
  have hq : ContDiff ℝ ω (fun x : O ↦ project F d x) := ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=O) (F:=U) (project F d)
  have hz : ContDiff ℝ ω (fun x : U × U ↦ along x.1 x.2) := hq.comp hl
  exact (contDiff_fst.add contDiff_snd).add hz

/-- This condition has open domain at each fixed horizon. -/
def Fits (A : Buffer F d) := IsUnit (motor F A)

lemma fits_zero : Fits (0 : U) := by rw [Fits,motor_zero]; exact isUnit_one

lemma Fits.surround {A : U} (hA : Fits A) : ∀ᶠ p in 𝓝 A, Fits p :=
  motor_regular.continuous.continuousAt.tendsto.eventually ((Units.isOpen (R := O)).mem_nhds (x:=motor F A) (show _ ∈ {p : O| IsUnit p} from hA))

lemma Fits.lower {A : Buffer F e} (hA : Fits A) (h : d ≤ e) : Fits (restr F h A) := by
  have hb := (ContinuousLinearMap.isUnit_iff_bijective.mp hA).1
  have he : Injective (motor F (restr F h A)) := by
    intro p q hq; apply incl_injective F h; apply hb; rw [← motors, ← motors, hq]
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨he, (LinearMap.injective_iff_surjective).1 he⟩

/-- Total off the units, only for use via theorems requiring `Fits`. -/
def undo (p : Buffer F d) := project F d (Ring.inverse (motor F p) - 1)

variable {x : Buffer F d}

private lemma stays_ok (h : Fits x) : Ring.inverse (motor F x) - 1 ∈ buffers F d := by
  let I := motor F x
  let J := Ring.inverse I
  have hb : Injective I := (ContinuousLinearMap.isUnit_iff_bijective.mp h).1
  have hl (p : E F d) : I (J p) = p := DFunLike.congr_fun (Ring.mul_inverse_cancel I h) p
  have hr (p : E F d) : J (I p) = p := DFunLike.congr_fun (Ring.inverse_mul_cancel I h) p
  refine ⟨?_,?_,?_,?_,?_⟩
  · change J _ - _ = 0
    apply sub_eq_zero.mpr
    have h' := hr ((Maxwell.freeTable F).unit d); rw [motor_unit x] at h'; exact h'
  · intro b hbd p hp; change J p - p ∈ _; apply Submodule.sub_mem _ _ hp
    rw [← incl_range F hbd.le] at hp ⊢
    obtain ⟨v, rfl⟩ := hp
    obtain ⟨w, rfl⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp (h.lower hbd.le)).2 v
    rw [motors, hr]; exact ⟨_,rfl⟩
  · intro p; change bar F d (J p - p) = J (bar F d p) - bar F d p
    rw [map_sub]; congr 1; apply hb; rw [hl]
    have hw := motor_bar x (J p); rw [← hw]; rw [hl]
  · intro s p
    change Extra.FD.rideO F s.ortho d (J p - p) = J (Extra.FD.rideO F s.ortho d p) - Extra.FD.rideO F s.ortho d p
    rw [map_sub]; congr 1; apply hb; rw [hl]; rw [← motor_spin x, hl]
  intro p; change J (Complex.I • p) - Complex.I • p = Complex.I • (J p - p)
  rw [smul_sub]; congr 1; apply hb; rw [hl, motor_mulI x, hl]

theorem undo_at (h : Fits x) : motor F (undo x) = Ring.inverse (motor F x) := by
  unfold undo; rw [motor, project_val _ (stays_ok h)]; abel

theorem fits_undo (h : Fits x) : Fits (undo x) := by
  rw [Fits,undo_at h]; exact (show IsUnit (motor F x) from h).ringInverse

theorem after_undo (h : Fits x) : after x (undo x) = 0 := motor_injective (by
  rw [after_at, undo_at h, motor_zero]; exact Ring.mul_inverse_cancel _ h)
theorem undo_after (h : Fits x) : after (undo x) x = 0 := motor_injective (by
  rw [after_at, undo_at h, motor_zero]; exact Ring.inverse_mul_cancel _ h)

theorem undo_restr (h : d ≤ e) {u : Buffer F e} (f : Fits u) : restr F h (undo u) = undo (restr F h u) := by
  have he := congrArg (restr F h) (after_undo f)
  rw [nested, map_zero] at he
  apply motor_injective
  have hk := f.lower h
  apply (show IsUnit _ from hk).mul_right_inj.mp
  rw [← after_at, ← after_at, after_undo hk, he]

theorem undo_smooth (h : Fits x) : ContDiffAt ℝ ω undo x := by
  have hM : ContDiffAt ℝ ω Ring.inverse (motor F x) := by
    obtain ⟨u, hu⟩ := h
    rw [← hu]; exact contDiffAt_ringInverse (R := O) ℝ u
  exact (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=O) (F:=U) (project F d)).contDiffAt.comp x ((hM.comp (f := motor F) x motor_regular.contDiffAt).sub contDiffAt_const)

end YM.SchemeConversionRG11.Affine

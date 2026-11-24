import YM.SchemeConversionRG11.Field.Orbit

/-!
# Field-column substitutions in reported tensors

Real multilinearity (on the underlying REAL spaces of complex fields; all evaluations there).
No assumption that real-only operations can replace the prescription laws giving complex linearity.
Operator norm (finite horizon). These theorems are on already Wick-indexed slots, so no
control on the conditioning of S.Field (or actual Gram matrices) implied.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11

open Function Pert.Position Series Orbit Affine Horizon
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {F : Labels.Frames G} {m d e n : ℕ}

/-- A correlation-type tensor on m slots through horizon d (can be assembled from mixed
  horizon placements by using the inclusions). W = coefficient output. -/
abbrev Tape (F : Labels.Frames G) (d m : ℕ) (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W] :=
  ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E F d) W

namespace Tape

section Morphism

def lifting (h : d ≤ e) : E F d →L[ℝ] E F e :=
  ((incl F h).restrictScalars ℝ).toContinuousLinearMap

end Morphism

section linear

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
local notation "T" => Tape F d m W

/-- Precomposition on all the slots. -/
def put (v : Buffer F d) : (Tape F d m W) →L[ℝ] Tape F d m W :=
  ContinuousMultilinearMap.compContinuousLinearMapL fun _ ↦ motor F v

theorem put_at (v : Buffer F d) (p : T) (q : Fin m → E F d) :
    put v p q = p (fun i ↦ motor F v (q i)) := rfl

theorem put_zero (p : T) : put (0 : Buffer F d) p = p := by
  ext1 q; rw [put_at]; simp only [motor_zero]; rfl

/-- Pullback action, so the order reverses. -/
theorem put_after (u v : Buffer F d) (p : T) :
    put (after u v) p = put v (put u p) := by
  ext1 q; rw [put_at, put_at, put_at]
  rw [after_at]; rfl

def withinHorizon (h : d ≤ e) : (Tape F e m W) →L[ℝ] Tape F d m W :=
  ContinuousMultilinearMap.compContinuousLinearMapL fun _ ↦ lifting (F:=F) h

theorem within_at (h : d ≤ e) (p : Tape F e m W) (q : Fin m → E F d) :
    withinHorizon h p q = p (fun i ↦ incl F h (q i)) := rfl

theorem put_within (h : d ≤ e) (u : Buffer F e) (p : Tape F e m W) :
    withinHorizon h (put u p) = put (restr F h u) (withinHorizon h p) := by
  ext1 q; rw [put_at, within_at, within_at, put_at]; simp_rw [motors]



section
local instance f_inst : NormedAddCommGroup (T →L[ℝ] T) :=
  ContinuousLinearMap.toNormedAddCommGroup (E:=T) (F:=T) (σ₁₂:=RingHom.id ℝ)
local instance v_inst : NormedSpace ℝ (T →L[ℝ] T) :=
  ContinuousLinearMap.toNormedSpace (E:=T) (F:=T) (σ₁₂:=RingHom.id ℝ) (𝕜':=ℝ)
/-- Smooth at each fixed arity, no bounds claimed uniform in arity. -/
theorem put_smooth : ContDiff ℝ ω (put (F:=F) (d:=d) (m:=m) (W:=W)) := by
  let L := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ (fun _ : Fin m ↦ E F d)
    (fun _ : Fin m ↦ E F d) W
  have ht : ContDiff ℝ ω (fun u : Buffer F d ↦ fun _ : Fin m ↦ motor F u) :=
    contDiff_pi.mpr (fun _ ↦ motor_regular)
  exact L.contDiff.comp ht

/-- Simultaneous frame and coefficient variation. -/
theorem placing : ContDiff ℝ ω (fun p : Buffer F d × T ↦ put p.1 p.2) := by
  have he : ContDiff ℝ ω (fun p : Buffer F d × T ↦ put (d:=d) (m:=m) (W:=W) p.1) :=
    put_smooth.comp contDiff_fst
  exact ContDiff.clm_apply (𝕜:=ℝ) (E:=Buffer F d × T) (F:=T) (G:=T) he contDiff_snd

end
/-- Pull A back in the labels, already assuming both are in the same coupling. -/
def hinge (u : Series (Buffer F d)) (A : Series (Tape F d m W)) :=
  liftJet (fun q : Buffer F d × T ↦ put q.1 q.2) (both u A)

variable {u v w : Series (Buffer F d)} {A B : Series (Tape F d m W)}

theorem tape_jet {x : ℝ → Buffer F d} {y : ℝ → T} (h : Represents n x u) (k : Represents n y A) :
    Represents n (fun t ↦ put (x t) (y t)) (hinge u A) :=
  (h.pair k).lift placing.contDiffAt

theorem tape_id : hinge 0 A = A := by
  funext i
  have h := trunc_represents A i
  have he := tape_jet (F:=F) (d:=d) (Represents_zero i) h
  exact (he.germ (Filter.Eventually.of_forall fun _ ↦ (put_zero _).symm)).unique h i le_rfl

theorem tape_join : hinge (chain u v) A = hinge v (hinge u A) := by
  funext i
  have h := trunc_represents A i
  have he := trunc_represents u i
  have hk := trunc_represents v i
  have hs := (tape_jet (chain_jet he hk) h)
  have hw := tape_jet hk (tape_jet he h)
  exact hs.unique (hw.germ (Filter.Eventually.of_forall fun _ ↦ put_after _ _ _)) i le_rfl

theorem tape_substitute {x : Series ℝ} (hx : x 0 = 0) :
    subJet (hinge u A) x = hinge (subJet u x) (subJet A x) := by
  unfold hinge; rw [← liftJet_subst placing.contDiffAt hx, ← both_subst hx]

theorem tape_through (h : Through n u v) (k : Through n A B) :
    Through n (hinge u A) (hinge v B) := (h.both k).lift placing.contDiffAt

theorem tape_restrict (h : d ≤ e) {U : Series (Buffer F e)} {Y : Series (Tape F e m W)}
    (h₁ : Through n (liftJet (restr F h) U) u) (h₂ : Through n (liftJet (withinHorizon h) Y) A) :
    Through n (liftJet (withinHorizon h) (hinge U Y)) (hinge u A) := by
  have hp : ContDiff ℝ ω (withinHorizon (W:=W) (F:=F) (m:=m) h) :=
    ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Tape F e m W) (F:=T) (withinHorizon (W:=W) (F:=F) (m:=m) h)
  have hl : ContDiff ℝ ω (restr F h) := ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Buffer F e) (F:=Buffer F d) (restr F h)
  have ht := trunc_represents U n
  have hs := trunc_represents Y n
  exact ((tape_jet ht hs).lift hp.contDiffAt).unique
    ((tape_jet ((ht.lift hl.contDiffAt).congr h₁) ((hs.lift hp.contDiffAt).congr h₂)).germ
      (Filter.Eventually.of_forall fun _ ↦ put_within h _ _))


end linear

end Tape
end YM.SchemeConversionRG11

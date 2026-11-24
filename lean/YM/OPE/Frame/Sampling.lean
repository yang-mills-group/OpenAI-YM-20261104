import YM.OPE.Frame.OnLabel
/-!
# Equivariant readouts at a single grade stage

All exteriors used by this continuum detector have positive clearance from the root and
from each other within each probe; no moving demands. Uses *complete unselected readings*.
Average over normalized Haar on Ortho, and real structure. Masks in radius, making one
common domain for all the individual grade readouts, will be applied later. Use the
original `Matrix.Norms.Frobenius` topology.
-/
set_option autoImplicit false
noncomputable section

open MeasureTheory Function Filter Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
namespace YM.OPE.Frame
open Table
open MultipleContact (Detector)
attribute [local instance] YM.Work.A15.compact_ortho
scoped instance : SecondCountableTopology Ortho := by
  haveI : SecondCountableTopology M4 := inferInstanceAs (SecondCountableTopology (Axis → Axis → ℝ))
  exact inferInstanceAs (SecondCountableTopology ↥((Matrix.unitaryGroup Axis ℝ : Set M4)))
scoped instance : MeasurableSpace Ortho := borel Ortho
scoped instance : BorelSpace Ortho := ⟨rfl⟩

private def rotations : TopologicalSpace.PositiveCompacts Ortho := ⟨⟨univ,isCompact_univ⟩,by simp⟩
def normalizedRotations : Measure Ortho := Measure.haarMeasure rotations
local notation "ν" => normalizedRotations
scoped instance : normalizedRotations.IsHaarMeasure := by unfold normalizedRotations; infer_instance
scoped instance : IsProbabilityMeasure normalizedRotations :=
  ⟨@Measure.haarMeasure_self Ortho _ _ _ _ _ rotations⟩
lemma integralable {X : Type*} [NormedAddCommGroup X] {f : Ortho → X} (h : Continuous f) :
    Integrable f normalizedRotations := h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma rotate_cont (x : E4) : Continuous fun K : Ortho => Ortho.move K x := by
  refine (PiLp.continuous_toLp 2 (fun _ : Axis => ℝ)) |>.comp (continuous_pi (fun i => ?_))
  change Continuous (fun K : Ortho => M4.move K.val x i)
  simp_rw [M4.at_coord]
  refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ continuous_const
  have hc : Continuous fun K : Ortho => (K.val : Axis → Axis → ℝ) := continuous_subtype_val
  exact (continuous_apply j).comp ((continuous_apply i).comp hc)
lemma move_plus (K : Ortho) (x y : E4) : Ortho.move K (x+y) = Ortho.move K x + Ortho.move K y := map_add (Ortho.motion K) x y
@[simp] lemma move_of_zero (K : Ortho) : Ortho.move K 0 = 0 := map_zero (Ortho.motion K)

variable {G : Gauge} {L : Register G} {S : Table L}
    {P : DiffPlan S} (X : Rotation S) (ρ : S.RealSpin) {I J : Type} [Fintype I] [Fintype J] {x : I → E4} {o : E4} {d h : ℕ}

/-- The complex-basis to realification operation. -/
def mirrorVector (b : Bool) (v : S.Field d) : S.Field d := if b then S.conj ρ d v else v

def escorts (e : Exterior L) (o : E4) (K : Ortho) (i : Fin e.n) := Ortho.move K (bearing e i) + o
def readAs (e : Exterior L) (b : Bool) (K : Ortho) (i : Fin e.n) : S.Field ((e.letter i).fst) :=
  X.act _ K (mirrorVector ρ b (S.classTokens (e.letter i)).snd)
def counted (e : Exterior L) (b : Bool) (K : Ortho) (i : Fin e.n) : S.Tag := ⟨(e.letter i).fst, readAs X ρ e b K i⟩

def answerAt (D : Detector S d) (e : D.probes) := D.decode (Pi.single e 1)
def rotatedAnswer (D : Detector S d) (e : D.probes) (b : Bool) (K : Ortho) : S.Field d :=
  X.act _ K (mirrorVector ρ b (answerAt D e))
lemma escorts_base (e : Exterior L) (o a : E4) (K : Ortho) : escorts e (o+a) K = (fun z => z+a) ∘ escorts e o K :=
  funext fun _ => (add_assoc ..).symm
lemma escorts_mul (e : Exterior L) (o : E4) (K R : Ortho) : escorts e (Ortho.move K o) (K*R) = Ortho.move K ∘ escorts e o R := by
  funext i; rw [comp_apply, escorts, escorts, Ortho.move_mul, move_plus]
lemma counted_mul (hX : X.Laws P ρ) (e : Exterior L) (b : Bool) (K R : Ortho) :
    counted X ρ e b (K*R) = X.label K ∘ counted X ρ e b R := by
  funext i; exact congrArg (fun p=> (⟨(e.letter i).fst,p⟩ : S.Tag)) (hX.group _ K R _) 
lemma counted_not (hX : X.Laws P ρ) (e : Exterior L) (b : Bool) (K : Ortho) :
    counted X ρ e (!b) K = bar ρ ∘ counted X ρ e b K := by
  funext i; refine congrArg (fun p=> (⟨(e.letter i).fst,p⟩ : S.Tag)) (show readAs X ρ e (!b) K i = S.conj ρ (e.letter i).fst (readAs X ρ e b K i) from ?_); unfold readAs; cases b <;> simp only [hX.real,mirrorVector,Bool.not_true,Bool.not_false,↓reduceIte,Bool.false_eq_true,S.reflect_star]
lemma rotated_not (hX : X.Laws P ρ) (D : Detector S d) (e : D.probes) (b : Bool) (K : Ortho) :
    rotatedAnswer X ρ D e (!b) K = S.conj ρ d (rotatedAnswer X ρ D e b K) := by
  cases b <;> simp only [rotatedAnswer,hX.real,mirrorVector,Bool.not_true,Bool.not_false,↓reduceIte,Bool.false_eq_true,S.reflect_star]

/-- Insert an orbit probe. Only used with proof of separation. -/
def inspect (e : Exterior L) (b : Bool) (x : I → E4) (A : I → S.Tag) (o : E4) (K : Ortho) :=
  sense S (beside x (escorts e o K)) (beside A (counted X ρ e b K))
def investigate (D : Detector S d) (b : Bool) (x : I → E4) (A : I → S.Tag) (o : E4) : S.Field d :=
  ∑ e : D.probes, ∫ K : Ortho, inspect X ρ e b x A o K • rotatedAnswer X ρ D e b K ∂ν
/-- `assess` is the full decoder in grade d. Only its projection onto exact weight d will be
used for the coefficient. -/
def assess (D : Detector S d) (x : I → E4) (A : I → S.Tag) (o : E4) : S.Field d :=
  (1/2 : ℂ) • (investigate X ρ D false x A o + investigate X ρ D true x A o)

lemma escorts_head (e : Exterior L) (o : E4) (K : Ortho) : Injective (beside (sole o) (escorts e o K)) := by
  rw [show beside (sole o) (escorts e o K) = (fun z => Ortho.move K z + o) ∘ beside (sole 0) (bearing e) by
    ext1 (i|i); · simp [sole]
    rfl]
  exact ((show Injective fun z => Ortho.move K z + o from fun _ _ h => Ortho.move_injective _ (add_right_cancel h)).comp (bearing_clear e))

lemma escort_cont (e : Exterior L) (o : E4) : Continuous (escorts e o) :=
  continuous_pi fun _ => (rotate_cont _).add continuous_const
lemma inspect_cont (hX : X.Laws P ρ) (h : S.Hierarchy) {e : Exterior L} {b : Bool} (A : I → S.Tag)
    (he : ∀ K, Injective (beside x (escorts e o K))) : Continuous (inspect X ρ e b x A o) := by
  refine continuous_iff_continuousAt.mpr (fun K => ?_)
  let f (K : Ortho) := ((beside x (escorts e o K)), readAs X ρ e b K)
  have hf : Continuous f := Continuous.prodMk (continuous_pi fun i => by
    rcases i with i|i; exact continuous_const; exact (rotate_cont _).add continuous_const) (continuous_pi fun i => hX.spin _ _)
  exact (sense_vary_ext_smooth A h.smooth (n := fun i => (e.letter i).fst) _ (he K)).continuousAt.comp (f:=f) hf.continuousAt
lemma inspect_live {D : Detector S d} (hX : X.Laws P ρ) (h : S.Hierarchy) {A : I → S.Tag} {e : D.probes} {b : Bool}
    (he : ∀ K, Injective (beside x (escorts e.val o K))) : Integrable (fun K => inspect X ρ e b x A o K • rotatedAnswer X ρ D e b K) ν :=
  integralable ((inspect_cont X ρ hX h A he).smul (hX.spin d _))

def admissible (D : Detector S d) (x : I → E4) (o : E4) : Prop :=
  ∀ (e : D.probes) (K : Ortho), Injective (beside x (escorts e.val o K))

variable {D : Detector S d}
lemma looks_shift (h : S.Hierarchy) (A : I → S.Tag) (z : E4) {b : Bool} (he : admissible D x o) :
    investigate X ρ D b (fun i=> x i+z) A (o+z) = investigate X ρ D b x A o := by
  have hw (e : D.probes) (K : Ortho) : inspect X ρ e b (fun i=> x i+z) A (o+z) K = inspect X ρ e b x A o K := by
    rw [inspect, escorts_base]; change sense S (beside ((fun a=>a+z) ∘ x) _) _ = _
    rw [← beside_commutes]; exact same_shift _ z h.translations (he e K)
  unfold investigate; simp_rw [hw]

lemma looks_spin (hX : X.Laws P ρ) (h : S.Hierarchy) (hc : X.Oriented S) (A : I → S.Tag) (K : Ortho) {b : Bool}
    (he : admissible D x o) : investigate X ρ D b (Ortho.move K ∘ x) (X.label K ∘ A) (Ortho.move K o) =
      X.act d K (investigate X ρ D b x A o) := by
  have hw (e : D.probes) (R : Ortho) : inspect X ρ e b (Ortho.move K ∘ x) (X.label K ∘ A) (Ortho.move K o) (K*R) =
      inspect X ρ e b x A o R := by rw [inspect, escorts_mul, counted_mul _ _ hX, ← beside_commutes, ← beside_commutes]; exact same_spin _ K hc (he e R)
  unfold investigate; rw [map_sum]; refine Finset.sum_congr rfl fun e _ => ?_
  let g (R : Ortho) := inspect X ρ (e : Exterior L) b (Ortho.move K ∘ x) (X.label K ∘ A) (Ortho.move K o) R • rotatedAnswer X ρ D e b R
  calc
    (∫ R : Ortho, g R ∂ν) = ∫ R : Ortho, g (K*R) ∂ν := ((measurePreserving_mul_left ν K).integral_comp (Homeomorph.mulLeft K).measurableEmbedding g).symm
    _ = ∫ R : Ortho, X.act d K (inspect X ρ e b x A o R • rotatedAnswer X ρ D e b R) ∂ν := by
      unfold g; simp_rw [hw,map_smul,rotatedAnswer, hX.group]
    _ = _ := (LinearMap.toContinuousLinearMap ((X.act d K).toLinearMap.restrictScalars ℝ)).integral_comp_comm (inspect_live X ρ hX h (he e))

def conjL (d : ℕ) : S.Field d →ₗ[ℝ] S.Field d where
  toFun := S.conj ρ d
  map_add' := map_add _
  map_smul' r u := by
    change S.conj ρ d (r • u) = r • S.conj ρ d u
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smulₛₗ]; simp

lemma looks_conj (hX : X.Laws P ρ) (h : S.Hierarchy) (A : I → S.Tag) (b : Bool) (he : admissible D x o) :
    investigate X ρ D (!b) x (bar ρ ∘ A) o = S.conj ρ d (investigate X ρ D b x A o) := by
  unfold investigate; rw [map_sum]; refine Finset.sum_congr rfl fun e _ => ?_
  have hw (R : Ortho) : inspect X ρ e (!b) x (bar ρ ∘ A) o R = star (inspect X ρ e b x A o R) := by
    rw [inspect,counted_not _ _ hX, ← beside_commutes]; exact same_real _ ρ ρ h.laws.toSymmetric (fun _ => le_rfl) (he e R)
  simp_rw [hw, rotated_not _ _ hX]
  apply Eq.trans (b:=∫ R : Ortho, S.conj ρ d (inspect X ρ e b x A o R • rotatedAnswer X ρ D e b R) ∂ν) ?_
    ((LinearMap.toContinuousLinearMap (conjL ρ d)).integral_comp_comm (inspect_live X ρ hX h (he e)))
  simp_rw [map_smulₛₗ]; rfl

lemma assess_shift (h : S.Hierarchy) (A : I → S.Tag) (z : E4) (he : admissible D x o) : assess X ρ D (fun i=> x i+z) A (o+z) = assess X ρ D x A o := by
  unfold assess; rw [looks_shift _ _ h _ z he, looks_shift _ _ h _ z he]
lemma assess_spin (hX : X.Laws P ρ) (h : S.Hierarchy) (hc : X.Oriented S) (A : I → S.Tag) (K : Ortho)
    (he : admissible D x o) : assess X ρ D (Ortho.move K ∘ x) (X.label K ∘ A) (Ortho.move K o) = X.act d K (assess X ρ D x A o) := by
  unfold assess; rw [map_smul,map_add, looks_spin _ _ hX h hc _ _ he, looks_spin _ _ hX h hc _ _ he]
lemma assess_conj (hX : X.Laws P ρ) (h : S.Hierarchy) (A : I → S.Tag) (he : admissible D x o) : assess X ρ D x (bar ρ ∘ A) o = S.conj ρ d (assess X ρ D x A o) := by
  unfold assess; rw [map_smulₛₗ,map_add,← looks_conj _ _ hX h _ _ he, ← looks_conj _ _ hX h _ _ he]; simp only [map_div₀,map_one,map_ofNat,Bool.not_false,Bool.not_true]; rw [add_comm]
end YM.OPE.Frame

import FormalConversion
import MSReference
import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields
import YangMills.WilsonProof.NativeSupport.MatchingNesting
import YangMills.WilsonProof.NativeSupport.ChallengeSpec

/-! Shared measurements and tested asymptotic expansions. The general formulation
at the end of this module compares one distinguished refinement. The OPE comparator
states its all-refinement requirements in `OPEMatching.Statement`. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.Matching

open Function Filter Set MeasureTheory
open scoped BigOperators Topology Distributions Classical

variable {g : GaugeGroup} {B : Maxwell.Reference g}
variable {C : WilsonFamily g} {T : Hierarchy C}

/-- The frame already includes the engineering powers of the physical length s.
On the UV tail it identifies each finite filtration with the very same fields
in the reconstructed theory. The inclusion into a higher cutoff is fixed in
physical labels before taking any scale-dependent inverses. -/
structure Measurement (B : Maxwell.Reference g) (T : Hierarchy C) where
  clock : ℝ → ℝ
  positive : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < clock s
  oneLoop : Tendsto (fun s => clock s * Real.sqrt (2 * oneLoopBeta B * Real.log s⁻¹))
    (𝓝[>] 0) (𝓝 1)
  frame (s : ℝ) (d : ℕ) : B.sector d ≃ₗ[ℂ] T.Field d
  nested (d e : ℕ) (p : B.sector d) (q : B.sector e) (eq : p.val = q.val) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, T.toLabel d (frame s d p) = T.toLabel e (frame s e q)
  /-- One physical Ward action implements the signed-axis action on the reported
  fields at every sufficiently small length, on each finite filtration. -/
  frameAxes : ∃ W : T.StressWardLaws, ∀ d, ∀ᶠ s : ℝ in 𝓝[>] 0,
    ∀ (σ : Equiv.Perm Axis) (sign : Axis → ℝ) (U : Spacetime ≃ₗᵢ[ℝ] Spacetime)
      (R : Ward.Rotation), (∀ a, sign a = 1 ∨ sign a = -1) →
      (∀ a, U (EuclideanSpace.single a 1) = sign a • EuclideanSpace.single (σ a) 1) →
      (∀ x, Matrix.toEuclideanLin R.val x = U x) → ∀ p q : B.sector d,
      RelatedByAxes B σ sign U p.val q.val → W.act d R (frame s d p) = frame s d q
  unit (d : ℕ) (p : B.sector d) (hp : p.val = 1) : ∀ᶠ s : ℝ in 𝓝[>] 0,
    ∀ (phase : Option T.Character) (n : ℕ) (a : Fin n → T.Tag) (x : Points (n+1)),
      x ∈ WilsonFamily.separated _ →
        T.correlation phase (Fin.cons ⟨d,frame s d p⟩ a) x =
        T.correlation phase a (WithLp.toLp 2 (fun i => x.ofLp i.succ))
  includeField {j h : ℕ} : j ≤ h → T.Field j →ₗ[ℂ] T.Field h
  includeLabel {j h : ℕ} (hj : j ≤ h) (v : T.Field j) :
    T.toLabel h (includeField hj v) = T.toLabel j v
  includeInsertion {j h : ℕ} (hj : j ≤ h) (v : T.Field j) (phase : Option T.Character)
      (n : ℕ) (a : Fin n → T.Tag) (x : Points (n+1)) (hx : x ∈ WilsonFamily.separated _) :
    T.correlation phase (Fin.cons ⟨h,includeField hj v⟩ a) x =
      T.correlation phase (Fin.cons ⟨j,v⟩ a) x
  multilinear (phase : Option T.Character) (n : ℕ) (d : Fin n → ℕ)
      (x : Points n) (hx : x ∈ WilsonFamily.separated n) :
    ∃ moment : MultilinearMap ℂ (fun i => T.Field (d i)) ℂ, ∀ v,
      T.correlation phase (fun i => ⟨d i,v i⟩) x = moment v
  /-- The same geometric coefficient used with fixed physical words can be
  evaluated on scale-dependent measured words by multilinear substitution. -/
  coefficientMultilinear {I : Type} [Fintype I] (d : I → ℕ) (j : ℕ) (c : T.Channel j)
      (x : I → Spacetime) (hx : Injective x) (o : Spacetime) :
    ∃ coeff : MultilinearMap ℂ (fun i => T.Field (d i)) ℂ, ∀ v,
      T.coefficient (fun i => ⟨d i, v i⟩) j c x o = coeff v

namespace Measurement
variable (H : Measurement B T)

def inputs {n : ℕ} (s : ℝ) (a : Fin n → Label B) : Fin n → T.Tag :=
  fun i => ⟨(a i).1, H.frame s (a i).1 (a i).2⟩

/-- Physical output of the original OPE through h in a fixed physical filtration.
This uses exactly the channels and coefficients tested against exterior insertions
by the existence theorem, including the unit channel. -/
def wilsonOPE {n : ℕ} (s : ℝ) (h : ℕ) (a : Fin n → Label B) (o : Spacetime) (x : Points n) :
    B.sector h :=
  (H.frame s h).symm (∑ j : Fin (h+1), ∑ i : T.Channel j.val,
    T.coefficient (H.inputs s a) j.val i (fun l => o + s • x l) o •
      H.includeField (Nat.le_of_lt_succ j.isLt) (T.actor j.val i))
end Measurement

/-- Little-o after order `N`, uniformly over a unit ball of joint smooth tests
on each separated compact. Only derivatives through `m` enter the unit ball.
Integrability guards both sides of the totalized Bochner integral. -/
def HasExpansion {n : ℕ} (m : ℕ) (clock : ℝ → ℝ) (actual : ℝ → Points n → ℂ)
    (predicted : ℕ → Points n → ℂ) : Prop :=
  (∀ (φ : WilsonFamily.SeparatedTest n) k, Integrable (fun x => φ x * predicted k x)) ∧
  ∀ (K : Set (Points n)), IsCompact K → K ⊆ WilsonFamily.separated n →
    ∀ (N : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ s : ℝ in 𝓝[>] 0,
      ∀ φ : WilsonFamily.SeparatedTest n, tsupport φ ⊆ K →
        (∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j (fun y : Points n => φ y) x‖ ≤ 1) →
        Integrable (fun x => φ x * actual s x) ∧
        ‖(∫ x, φ x * actual s x) - ∑ k : Fin (N+1),
          (clock s : ℂ)^k.val * ∫ x, φ x * predicted k.val x‖ ≤ ε * |clock s|^N

/-- All correlation and OPE tests on the same measured hierarchy. For each
arity and tuple of field horizons one finite test order works at every
perturbative order and center. Testing the entire OPE output dual reads every
positive-dimensional channel as well as the scalar output. -/
structure Compares (M : MSbar.Coefficients B) (S : Conversion B)
    (H : Measurement B T) : Prop where
  correlation (n : ℕ) (d : Fin n → ℕ) : ∃ m : ℕ,
    ∀ (phase : Option T.Character) (v : (i : Fin n) → B.sector (d i)) (o : Spacetime),
      let a : Fin n → Label B := fun i => ⟨d i, v i⟩
      HasExpansion m H.clock (fun s x => T.correlation phase (H.inputs s a)
        (WithLp.toLp 2 fun i => o + s • x i)) (fun k x => S.correlation M k a x)
  ope (n h : ℕ) (d : Fin n → ℕ) : ∃ m : ℕ,
    ∀ (v : (i : Fin n) → B.sector (d i)) (o : Spacetime) (out : B.sector h →ₗ[ℂ] ℂ),
      let a : Fin n → Label B := fun i => ⟨d i, v i⟩
      HasExpansion m H.clock (fun s x => out (H.wilsonOPE s h a o x))
        (fun k x => out (S.ope M h k a x))
  geometric : Hierarchy.SeparatedPowerLog T
  nested : Hierarchy.SeparatedNestedPowerLog T

/-- Select an existence witness at a requested volume sequence p. -/
structure Refinement (B : Maxwell.Reference g) (C : WilsonFamily g) (p : ℕ → ℕ) where
  q : ℕ → ℕ
  strictlyIncreasing : StrictMono q
  theory : Hierarchy C
  existence : theory.Properties B (p ∘ q)

abbrev ReferenceFamily := (g : GaugeGroup) → Σ B : Maxwell.Reference g, MSbar.Coefficients B

/-- A fixed position prescription can further characterize the scale measurements
on this exact hierarchy. The numerical MS array remains upstream of this predicate. -/
abbrev Appointment (reference : ReferenceFamily) :=
  (g : GaugeGroup) → (C : WilsonFamily g) → (T : Hierarchy C) →
    Measurement (reference g).1 T → Prop

/-- A scheme rule on the independent field space has no argument for a Wilson
family, physical correlation function, phase, or extraction. -/
abbrev ConversionRule (reference : ReferenceFamily) :=
  (g : GaugeGroup) → Conversion (reference g).1 → Prop

/-- A particular Wilson family must meet the volume-refinement guarantee. Its
distinguished continuum refinement must also match the prescribed formal series. -/
def OnConstruction {B : Maxwell.Reference g} (M : MSbar.Coefficients B) (S : Conversion B)
    (appointed : (C : WilsonFamily g) → (T : Hierarchy C) → Measurement B T → Prop) : Prop :=
  ∃ C : WilsonFamily g, WilsonRegularity C ∧
    ∃ choose : (p : ℕ → ℕ) → StrictMono p → Refinement B C p,
      ∃ H : Measurement B (choose id strictMono_id).theory,
        appointed C (choose id strictMono_id).theory H ∧ Compares M S H

/-- The numeric MS coefficients and their finite field and coupling conversion
are both fixed functions of the public gauge data. -/
def JointMatchingFor (reference : ReferenceFamily)
    (conversion : (g : GaugeGroup) → g.IsSimple → Conversion (reference g).1)
    (appointed : Appointment reference) : Prop :=
  ∀ (g : GaugeGroup) (hg : g.IsSimple),
    OnConstruction (reference g).2 (conversion g hg) (appointed g)

/-- Forget the matching of the distinguished continuum refinement. -/
theorem jointMatchingFor_implies_jointExistence {reference : ReferenceFamily}
    {conversion : (g : GaugeGroup) → g.IsSimple → Conversion (reference g).1}
    {appointed : Appointment reference} (h : JointMatchingFor reference conversion appointed) :
    JointExistence := by
  intro g hg
  obtain ⟨C, hC, choose, _⟩ := h g hg
  refine ⟨(reference g).1, C, hC, ?_⟩
  intro p hp
  let W := choose p hp
  exact ⟨W.q, W.strictlyIncreasing, W.theory, W.existence⟩

end YangMills.Matching

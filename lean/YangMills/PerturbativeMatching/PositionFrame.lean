import FormalConversion
import YangMills.StressTensor
import MSPositionPrescription
import MSNumericalAdjustment

/-! The measured coupling and fields come from one physical hierarchy. The
finite tests, the signed triangle and the Taylor coefficients used to adjust
the fields are supplied by the independent position prescription. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.MSbar

open Filter MeasureTheory
open scoped Topology BigOperators Classical

variable {g : GaugeGroup}

variable {B : Maxwell.Reference g} {C : WilsonFamily g} (T : Hierarchy C)

/-- The position frame is used before applying the homogeneous adjustment. -/
abbrev PositionFrames (B : Maxwell.Reference g) :=
  (s : ℝ) → (d : ℕ) → B.sector d ≃ₗ[ℂ] T.Field d

def positionMoment (J : PositionFrames T B) (s : ℝ) (d : ℕ) {n : ℕ}
    (v : Fin n → B.sector d) (x : Points n) : ℂ :=
  T.correlation none (fun i => ⟨d, J s d (v i)⟩) (s • x)

/-- Pair each actual unselected correlator with its prescribed compact
test at the physical length s. -/
def positionReport (J : PositionFrames T B) (s : ℝ) (d : ℕ) : Position.Report B d :=
  fun _ φ v => ∫ x, φ x * positionMoment T J s d v x

/-- The finite determining equations are solved on the branch tending to
free Maxwell. Near the measured frame these equations distinguish every
permitted infinitesimal field change. -/
def PositionNormalized (P : PositionPrescription B) (J : PositionFrames T B) : Prop :=
  (∀ d n (φ : SeparatedTest n) (v : Fin n → B.sector d),
    Tendsto (fun s => positionReport T J s d n φ v) (𝓝[>] 0)
      (𝓝 (Position.free B d n φ v))) ∧
  ∀ d, ∀ᶠ s : ℝ in 𝓝[>] 0,
    (∀ n (φ : SeparatedTest n) (v : Fin n → B.sector d),
      Integrable (fun x => φ x * positionMoment T J s d v x)) ∧
    (P.screen d).read (positionReport T J s d) = (P.screen d).read (Position.free B d) ∧
    ∀ Y : Module.End ℂ (B.sector d), Position.IsChange B d Y →
      ∃! X : Module.End ℂ (B.sector d), Position.IsChange B d X ∧
        (P.screen d).read (Position.variation (positionReport T J s d) X) = Y

/-- The normalized report selects the local solution of the finite equations.
A permitted change tending to zero can solve them exactly on this frame
only at the identity, eventually at each fixed cutoff. -/
def PositionLocallyUnique (P : PositionPrescription B) (J : PositionFrames T B) : Prop :=
  ∀ d (X : ℝ → Module.End ℂ (B.sector d)),
    (∀ᶠ s : ℝ in 𝓝[>] 0, Position.IsChange B d (X s)) →
    (∀ v (out : B.sector d →ₗ[ℂ] ℂ),
      Tendsto (fun s => out (X s v)) (𝓝[>] 0) (𝓝 0)) →
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      (P.screen d).read (fun n φ v =>
        positionReport T J s d n φ (fun i => v i + X s (v i))) =
          (P.screen d).read (Position.free B d) ↔ X s = 0

/-- Missing slots of a connected face carry the physical unit. -/
def PositionUnital (J : PositionFrames T B) : Prop :=
  ∀ d (u : B.sector d), u.val = 1 →
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ (n : ℕ) (a : Fin n → T.Tag) (x : Points (n+1)),
      x ∈ separated _ →
      T.correlation none (Fin.cons ⟨d, J s d u⟩ a) x =
        T.correlation none a (WithLp.toLp 2 (fun i => x.ofLp i.succ))

def PositionNested (J : PositionFrames T B) : Prop :=
  ∀ d e (v : B.sector d) (w : B.sector e), v.val = w.val →
    ∀ᶠ s : ℝ in 𝓝[>] 0, T.toLabel d (J s d v) = T.toLabel e (J s e w)

/-- Real Euclidean field labels have real unselected moments at separated
points. One tail at each cutoff works for every arity and configuration. -/
def PositionReal (J : PositionFrames T B) : Prop :=
  ∀ d, ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ (n : ℕ) (v : Fin n → B.sector d),
    (∀ i m, (MvPolynomial.coeff m (v i).val).im = 0) →
    ∀ x : Points n, x ∈ separated n →
      (T.correlation none (fun i => ⟨d, J s d (v i)⟩) x).im = 0

end YangMills.MSbar

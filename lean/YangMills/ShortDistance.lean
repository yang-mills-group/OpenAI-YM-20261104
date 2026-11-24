import YangMills.FieldMeasurements

/-! The short-distance comparison uses one field frame at every radius. A sequence
of sampling radii specifies the fixed-field alignment tests. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.ShortDistance
open Filter Set FixedFields
open scoped Topology BigOperators
variable {g : GaugeGroup} {C : WilsonFamily g} (B : Maxwell.Reference g) (T : Hierarchy C)

/-- Coordinates for the free and physical fields through each engineering dimension. -/
abbrev Frame := (d : ℕ) → B.sector d ≃ₗ[ℂ] T.Field d

structure Coordinates where
  radius : ℕ → ℝ
  positive (k : ℕ) : 0 < radius k
  decreasing : StrictAnti radius
  tendsToZero : Tendsto radius atTop (𝓝 0)
  frame : ℝ → Frame B T

/-- The same frame as a function of the sampling index. -/
abbrev Coordinates.sample {B : Maxwell.Reference g} {T : Hierarchy C} (S : Coordinates B T) (k : ℕ) :=
  S.frame (S.radius k)

/-- Compare a sequence of physical fields to a free field in one fixed norm. -/
def Aligned (frame : ℕ → Frame B T) (d : ℕ) (u : ℕ → T.Field d) (v : B.sector d) : Prop :=
  Tendsto (fun k => frame 0 d ((frame k d).symm (u k))) atTop (𝓝 (frame 0 d v))

def engineering (radius : ℕ → ℝ) (d : ℕ) (a : T.Field d) (k : ℕ) : T.Field d :=
  ((radius k ^ d : ℝ) : ℂ) • a

def Detects (radius : ℕ → ℝ) (frame : ℕ → Frame B T) : Prop :=
  ∀ d : ℕ, ∃ probes : Finset (Probe B), Separates B d probes ∧ ∀ (u : ℕ → T.Field d) (v : B.sector d),
    (∀ p ∈ probes, Tendsto (fun k => T.correlation none
      (Fin.cons (α := fun _ : Fin (p.n+1) => T.Tag) ⟨d,u k⟩
        (fun i => ⟨(p.spectators i).1,frame k _ (p.spectators i).2⟩)) (radius k • p.point))
      atTop (𝓝 (B.moment p.point (Fin.cons v.val (fun i => (p.spectators i).2.val))))) →
    Aligned B T frame d u v

/-- Phase control, operator identification and convergence of aligned insertions at the sampling radii. -/
structure FixedFieldLaws (radius : ℕ → ℝ) (frame : ℕ → Frame B T) : Prop where
  phaseBound : PhaseBound T
  phaseDerivatives (n j : ℕ) (a : Fin n → T.Tag) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
      (shrinks : Tendsto r atTop (𝓝 0)) (K : Set (Points n)) (compact : IsCompact K)
      (separated : K ⊆ YangMills.separated n) (ε : ℝ) (pos : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ s t : Option T.Character,
      ‖iteratedFDeriv ℝ j ((fun z => r k ^ (∑ i, (a i).1) • T.correlation s a (r k • z)) -
        (fun z => r k ^ (∑ i, (a i).1) • T.correlation t a (r k • z))) x‖ ≤ ε
  unit : ∃ (u : T.Field 0) (v : B.sector 0), T.toLabel 0 u = T.toLabel 4 T.unitAtFour ∧
    v.val = 1 ∧ Aligned B T frame 0 (engineering T radius 0 u) v
  stress (i j : Axis) : Aligned B T frame 4 (engineering T radius 4 (T.stress i j)) (B.stress i j)
  derivatives : ∃ W : T.StressWardLaws, ∀ (d : ℕ) (j : Axis) (a : T.Field d) (v : B.sector d),
    Aligned B T frame d (engineering T radius d a) v →
    ∃ w : B.sector (d+1), WickDerivative B j v w ∧
      Aligned B T frame (d+1) (engineering T radius (d+1) (W.derivative d j a)) w
  finiteReadings : Detects B T radius frame
  limit (n : ℕ) (d : Fin n → ℕ) (u : ℕ → (i : Fin n) → T.Field (d i)) (v : (i : Fin n) → B.sector (d i)) :
    (∀ i, Aligned B T frame (d i) (fun k => u k i) (v i)) →
    ∀ (K : Set (Points n)), IsCompact K → K ⊆ separated n → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, ∀ x ∈ K, ∀ s : Option T.Character,
        ‖T.correlation s (fun i => ⟨d i,u k i⟩) (radius k • x) - B.moment x (fun i => (v i).val)‖ ≤ ε

/-- A row ignores lower degrees if it vanishes on any representative of a
physical field already present at a lower cutoff. -/
def KillsBelow {d : ℕ} (e : ℕ) (φ : T.Field d →L[ℂ] ℂ) : Prop :=
  ∀ k < e, ∀ (u : T.Field k) (v : T.Field d), T.toLabel d v = T.toLabel k u → φ v = 0

/-- Bounds in fixed coordinates, uniform on the unit ball at each cutoff.
The forward exponent uses the first physical degree seen by the row. The
inverse exponent applies to the whole space through degree d. -/
structure FrameBounds (reference : Frame B T) (J : ℝ → Frame B T) : Prop where
  forward (d e : ℕ) (degree : e ≤ d) (φ : T.Field d →L[ℂ] ℂ) (lower : KillsBelow T e φ)
      (δ : ℝ) (pos : 0 < δ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ u : T.Field d,
        ‖φ (J r d ((reference d).symm u))‖ ≤ A * r ^ ((e : ℝ) - δ) * ‖u‖
  inverse (d : ℕ) (δ : ℝ) (pos : 0 < δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ u : T.Field d,
      ‖reference d ((J r d).symm u)‖ ≤ A * r ^ (-(d : ℝ) - δ) * ‖u‖

/-- The component in a marked slot is the same physical Ward field at every radius.
Only its engineering factor and the arguments of the correlation vary. -/
def MixedMomentBound (r : ℝ) (frame : Frame B T) {n : ℕ} (j : ℕ)
    (fields : Fin n → Σ d, B.sector d) (marked : Fin n → Bool)
    (components : Fin n → Axis × Axis) (K : Set (Points n)) (ε : ℝ)
    (phase : Option T.Character) : Prop :=
  let physical (i : Fin n) : T.Tag :=
    if marked i then
      ⟨4, ((r ^ 4 : ℝ) : ℂ) • T.stress (components i).1 (components i).2⟩
    else
      ⟨(fields i).1, frame _ (fields i).2⟩
  let wick (i : Fin n) : B.toCoordinates.Pol :=
    if marked i then (B.stress (components i).1 (components i).2).val else (fields i).2.val
  ∀ x ∈ K,
    ‖iteratedFDeriv ℝ j (fun z => T.correlation phase physical (r • z)) x -
      iteratedFDeriv ℝ j (fun z => B.moment z wick) x‖ ≤ ε

/-- The ultraviolet behavior of a single hierarchy in every vacuum sector. -/
structure MaxwellLimit (S : Coordinates B T) : Prop where
  fixedFields : FixedFieldLaws B T S.radius S.sample
  normalization : FrameBounds B T (S.frame (S.radius 0)) S.frame
  stress (a b : Axis) :
    Tendsto (fun r : ℝ => S.frame (S.radius 0) 4 ((S.frame r 4).symm (((r ^ 4 : ℝ) : ℂ) • T.stress a b)))
      (𝓝[>] 0) (𝓝 (S.frame (S.radius 0) 4 (B.stress a b)))
  mixed (n j : ℕ) (fields : Fin n → Σ d, B.sector d) (marked : Fin n → Bool)
      (components : Fin n → Axis × Axis) (K : Set (Points n)) (compact : IsCompact K)
      (separated : K ⊆ YangMills.separated n) (ε : ℝ) (positive : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s : Option T.Character,
      MixedMomentBound B T r (S.frame r) j fields marked components K ε s

end YangMills.ShortDistance

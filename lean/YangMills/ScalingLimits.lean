import YangMills.FieldMeasurements

/-! The Maxwell scaling limit, fixed-field readings and bounds on the all-radii frame. -/
set_option autoImplicit false
noncomputable section

namespace YangMills.Hierarchy
open Filter
open scoped Topology BigOperators
variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)

structure MaxwellScaling (B : Maxwell.Reference g) where
  r : ℕ → ℝ
  positive k : 0 < r k
  later : StrictAnti r
  drips : Tendsto r atTop (𝓝 0)
  frame (k d : ℕ) : B.sector d ≃ₗ[ℂ] T.Field d
  jets (n j : ℕ) (q : Fin n → Σ d, B.sector d) (marked : Fin n → Bool)
      (ab : Fin n → Axis × Axis) (K : Set (Points n)) (compact : IsCompact K)
      (separated : K ⊆ WilsonFamily.separated n) (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (fun z => T.correlation none (fun i => if marked i then
          ⟨4, ((r k ^ 4 : ℝ) : ℂ) • T.stress (ab i).1 (ab i).2⟩ else
          ⟨(q i).1, frame k _ (q i).2⟩) (r k • z)) x -
        iteratedFDeriv ℝ j (fun z => B.moment z (fun i => if marked i then
          (B.stress (ab i).1 (ab i).2).val else (q i).2.val)) x‖ ≤ ε

end YangMills.Hierarchy

namespace YangMills.FixedFields

open Filter Set Function

open scoped Topology BigOperators

variable {g : GaugeGroup} {C : WilsonFamily g} (B : Maxwell.Reference g) (T : Hierarchy C)

def Aligned (X : T.MaxwellScaling B) (d : ℕ) (u : ℕ → T.Field d) (v : B.sector d) : Prop :=
  Tendsto (fun k => X.frame 0 d ((X.frame k d).symm (u k))) atTop (𝓝 (X.frame 0 d v))

def engineering (X : T.MaxwellScaling B) (d : ℕ) (a : T.Field d) (k : ℕ) : T.Field d :=
  ((X.r k ^ d : ℝ) : ℂ) • a

def PhaseJets (X : T.MaxwellScaling B) : Prop :=
  ∀ (n j : ℕ) (q : Fin n → Σ d, B.sector d) (marked : Fin n → Bool)
    (ab : Fin n → Axis × Axis) (K : Set (Points n)), IsCompact K → K ⊆ separated n →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ K, ∀ s : Option T.Character,
      ‖iteratedFDeriv ℝ j (fun z => T.correlation s (fun i => if marked i then
          ⟨4, ((X.r k ^ 4 : ℝ) : ℂ) • T.stress (ab i).1 (ab i).2⟩ else
          ⟨(q i).1, X.frame k _ (q i).2⟩) (X.r k • z)) x -
        iteratedFDeriv ℝ j (fun z => B.moment z (fun i => if marked i then
          (B.stress (ab i).1 (ab i).2).val else (q i).2.val)) x‖ ≤ ε

def Detects (X : T.MaxwellScaling B) : Prop :=
  ∀ d : ℕ, ∃ probes : Finset (Probe B), Separates B d probes ∧ ∀ (u : ℕ → T.Field d) (v : B.sector d),
    (∀ p ∈ probes, Tendsto (fun k => T.correlation none
      (Fin.cons (α := fun _ : Fin (p.n+1) => T.Tag) ⟨d,u k⟩
        (fun i => ⟨(p.spectators i).1,X.frame k _ (p.spectators i).2⟩)) (X.r k • p.point))
      atTop (𝓝 (B.moment p.point (Fin.cons v.val (fun i => (p.spectators i).2.val))))) →
    Aligned B T X d u v

structure Laws (X : T.MaxwellScaling B) : Prop where
  allJets : PhaseJets B T X
  phaseBound : PhaseBound T
  phaseDerivatives (n j : ℕ) (a : Fin n → T.Tag) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
      (shrinks : Tendsto r atTop (𝓝 0)) (K : Set (Points n)) (compact : IsCompact K)
      (separated : K ⊆ YangMills.separated n) (ε : ℝ) (pos : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ s t : Option T.Character,
      ‖iteratedFDeriv ℝ j ((fun z => r k ^ (∑ i, (a i).1) • T.correlation s a (r k • z)) -
        (fun z => r k ^ (∑ i, (a i).1) • T.correlation t a (r k • z))) x‖ ≤ ε
  unit : ∃ (u : T.Field 0) (v : B.sector 0), T.toLabel 0 u = T.toLabel 4 T.unitAtFour ∧
    v.val = 1 ∧ Aligned B T X 0 (engineering B T X 0 u) v
  stress (i j : Axis) : Aligned B T X 4 (engineering B T X 4 (T.stress i j)) (B.stress i j)
  derivatives : ∃ W : T.StressWardLaws, ∀ (d : ℕ) (j : Axis) (a : T.Field d) (v : B.sector d),
    Aligned B T X d (engineering B T X d a) v →
    ∃ w : B.sector (d+1), WickDerivative B j v w ∧
      Aligned B T X (d+1) (engineering B T X (d+1) (W.derivative d j a)) w
  finiteReadings : Detects B T X
  limit (n : ℕ) (d : Fin n → ℕ) (u : ℕ → (i : Fin n) → T.Field (d i)) (v : (i : Fin n) → B.sector (d i)) :
    (∀ i, Aligned B T X (d i) (fun k => u k i) (v i)) →
    ∀ (K : Set (Points n)), IsCompact K → K ⊆ separated n → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, ∀ x ∈ K, ∀ s : Option T.Character,
        ‖T.correlation s (fun i => ⟨d i,u k i⟩) (X.r k • x) - B.moment x (fun i => (v i).val)‖ ≤ ε

end YangMills.FixedFields

namespace YangMills.AllRadii
open Filter Set
open scoped Topology BigOperators
variable {g : GaugeGroup} {C : WilsonFamily g} (B : Maxwell.Reference g) (T : Hierarchy C)

abbrev Frame := (d : ℕ) → B.sector d ≃ₗ[ℂ] T.Field d

/-- The component in a marked slot is the same physical Ward field at every radius.
Only its engineering factor and the arguments of the correlation vary. -/
def JetBound (r : ℝ) (J : Frame B T) {n : ℕ} (j : ℕ) (q : Fin n → Σ d, B.sector d)
    (marked : Fin n → Bool) (ab : Fin n → Axis × Axis) (K : Set (Points n)) (ε : ℝ)
    (s : Option T.Character) : Prop :=
  ∀ x ∈ K,
    ‖iteratedFDeriv ℝ j (fun z => T.correlation s (fun i => if marked i then
        ⟨4, ((r ^ 4 : ℝ) : ℂ) • T.stress (ab i).1 (ab i).2⟩ else
        ⟨(q i).1, J _ (q i).2⟩) (r • z)) x -
      iteratedFDeriv ℝ j (fun z => B.moment z (fun i => if marked i then
        (B.stress (ab i).1 (ab i).2).val else (q i).2.val)) x‖ ≤ ε

structure Laws (X : T.MaxwellScaling B) (J : ℝ → Frame B T) : Prop where
  restricts (k : ℕ) : J (X.r k) = X.frame k
  stress (i j : Axis) :
    Tendsto (fun r : ℝ => X.frame 0 4 ((J r 4).symm (((r^4 : ℝ) : ℂ) • T.stress i j)))
      (𝓝[>] 0) (𝓝 (X.frame 0 4 (B.stress i j)))
  mixed (n j : ℕ) (q : Fin n → Σ d, B.sector d) (marked : Fin n → Bool)
      (ab : Fin n → Axis × Axis) (K : Set (Points n)) (compact : IsCompact K)
      (separated : K ⊆ YangMills.separated n) (ε : ℝ) (pos : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s : Option T.Character, JetBound B T r (J r) j q marked ab K ε s

theorem Laws.selected {X : T.MaxwellScaling B} {J : ℝ → Frame B T} (h : Laws B T X J)
    (n j : ℕ) (q : Fin n → Σ d, B.sector d) (marked : Fin n → Bool)
    (ab : Fin n → Axis × Axis) (K : Set (Points n)) (compact : IsCompact K)
    (separated : K ⊆ YangMills.separated n) (ε : ℝ) (pos : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, JetBound B T r (J r) j q marked ab K ε (some T.selected) :=
  (h.mixed n j q marked ab K compact separated ε pos).mono fun _ hr => hr (some T.selected)

/-- A row ignores lower degrees if it vanishes on any representative of a
physical field already present at a lower cutoff. -/
def KillsBelow {d : ℕ} (e : ℕ) (φ : T.Field d →L[ℂ] ℂ) : Prop :=
  ∀ k < e, ∀ (u : T.Field k) (v : T.Field d), T.toLabel d v = T.toLabel k u → φ v = 0

/-- Bounds in fixed coordinates, uniform on the unit ball at each cutoff.
The forward exponent uses the first physical degree seen by the row. The
inverse exponent applies to the whole space through degree d. -/
structure FrameBounds (X : T.MaxwellScaling B) (J : ℝ → Frame B T) : Prop where
  forward (d e : ℕ) (degree : e ≤ d) (φ : T.Field d →L[ℂ] ℂ) (lower : KillsBelow T e φ)
      (δ : ℝ) (pos : 0 < δ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ u : T.Field d,
        ‖φ (J r d ((X.frame 0 d).symm u))‖ ≤ A * r ^ ((e : ℝ) - δ) * ‖u‖
  inverse (d : ℕ) (δ : ℝ) (pos : 0 < δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ u : T.Field d,
      ‖X.frame 0 d ((J r d).symm u)‖ ≤ A * r ^ (-(d : ℝ) - δ) * ‖u‖

end YangMills.AllRadii

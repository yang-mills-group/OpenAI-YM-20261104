import YM.Integration.ActualMarkedDensity
import YM.RemainderComparison.Placement.Pose

/-!
An explicit zero-activity registration extension of an already specified
representation. The radius, grade, test space and cost may vary independently
between slots. All original numerical parameters, paths, clipping, lawful
budgets and input admission are preserved. Its marked density is proved equal
to the literal insertions times the ORIGINAL representation's density.

The extended activity indexing is not identified with the original indexing.
In particular this does not transport an arbitrary Recipe.retain predicate or
prove admission of a later step of an actual trajectory.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.RegisteredPhysicalMarks

open Function Lattice RG Wilson Finset Pressure
open ConnectedActivityE6
open Push.AbsoluteSums.Animals
open RemainderComparison RemainderComparison.Typeface
open RemainderComparison.Placement
open PhysicalNext.Repeat
open scoped BigOperators Classical

variable {G : Gauge} {f c : Side} {ι : Type} [Countable ι]

/-- Every slot has a port at every site, with that slot's own radius. -/
def ports (radii : ι → ℕ) (u : Site f × ι) : RegularAddress f :=
  Tile.aperture u.1 (radii u.2)

/-- Canonically insert zero activities into the given representation. -/
def extend (R : Rep G f) (radii : ι → ℕ) : Rep G f :=
  Dove.arcadia R (ports radii) (Placement.numbers ι f)

/-- A mark's port, retaining its independent slot even at coincident sites. -/
def slot (positions : ι → Site f) (i : ι) : ℕ :=
  Dove.right (Placement.numbers ι f) (positions i, i)

theorem slot_injective (positions : ι → Site f) : Injective (slot positions) := by
  intro i j hij
  have h := (Placement.numbers ι f).symm.injective hij
  exact congr_arg Prod.snd (Sum.inr.inj h)

variable (R : Rep G f) (radii : ι → ℕ)

theorem registration (positions : ι → Site f) (i : ι) :
    (extend R radii).activities.reg (slot positions i) =
      Tile.aperture (positions i) (radii i) ∧
    (extend R radii).activities.E (slot positions i) = 0 :=
  Dove.plots R (ports radii) (Placement.numbers ι f) (positions i, i)

/-- Existing activities survive exactly, under the explicit left embedding. -/
theorem original_activities (j : ℕ) :
    (extend R radii).activities.reg (Dove.left (Placement.numbers ι f) j) =
      R.activities.reg j ∧
    (extend R radii).activities.E (Dove.left (Placement.numbers ι f) j) =
      R.activities.E j :=
  Dove.also R (ports radii) (Placement.numbers ι f) j

@[simp] theorem path_eq : (extend R radii).path = R.path := rfl
@[simp] theorem clip_eq : (extend R radii).clip = R.clip := rfl
@[simp] theorem point_eq : (extend R radii).p = R.p := rfl
@[simp] theorem beta_eq : (extend R radii).beta = R.beta := rfl
@[simp] theorem volume_eq : (extend R radii).v = R.v := rfl

theorem density_eq : (extend R radii).eval = R.eval :=
  (Dove.maths R (ports radii) (Placement.numbers ι f) 1).2

theorem exponent_eq : (extend R radii).exponent = R.exponent :=
  funext fun U => (Dove.maths R (ports radii) (Placement.numbers ι f) U).1

theorem lawful {σ C Λ δ w : ℝ} (h : R.Lawful σ C Λ δ w) :
    (extend R radii).Lawful σ C Λ δ w := by
  apply Dove.binds R (ports radii) (Placement.numbers ι f) h
  intro s z
  refine ⟨Placement.perm ι s z, fun u => ?_⟩
  exact Placement.position_covariance (radii u.2) s z u.1

theorem intake {P : Teller G} {S : StepData c f} {T : Tube G S} {x : ℝ}
    (h : Intake P T x R) : Intake P T x (extend R radii) := by
  refine ⟨h.ready, ?_, lawful R radii h.cap, h.exponent, h.height, h.sizes, h.window⟩
  obtain ⟨hp, hc, hv⟩ := h.received
  exact ⟨hp, hc, hv⟩

variable {E : ι → Type*} {orders : ι → ℕ} {costs : ι → ℝ}

/-- Literal independent portraits are constructed without separate registration
or zero-activity hypotheses, even for a countable collection of slots. -/
theorem portraits
    (D : ∀ i, Tile G (E i) (orders i) (radii i) (costs i))
    (base : ∀ i, E i) (positions : ι → Site f) (hβ : 0 < R.beta) :
    ∃ M : ∀ i, Portrait (extend R radii) (E i),
      (∀ i, (M i).wing = Lotus.Wing.logKey (slot positions i)) ∧
      (∀ i, (M i).weight = Tile.peso G (orders i) (radii i) (costs i) R.p) ∧
      ∀ tests i, ((independentPortraits M i).angle tests).ingredient =
        masked R.p.threshold (neighbors (radii i) (positions i))
          (Tile.read (D i) (positions i) (tests i)) :=
  registered_independent_portraits (extend R radii) D base positions (slot positions) hβ
    (fun i => (registration R radii positions i).1)
    (fun i => (registration R radii positions i).2)

variable [Fintype ι]

/-- All registration obligations are constructed. Independent literal stencils
and their exact prices are retained; the density on the right is that of R. -/
theorem marked_density (S : StepData c f)
    (D : ∀ i, Tile G (E i) (orders i) (radii i) (costs i))
    (base : ∀ i, E i) (positions : ι → Site f) (hβ : 0 < R.beta)
    {V : Type} [DecidableEq V] (B : Marker.Census V) (z : ι → Marker.Poly B) :
    ∃ M : ∀ i, Portrait (extend R radii) (E i),
      (∀ i, (M i).wing = Lotus.Wing.logKey (slot positions i)) ∧
      (∀ i, (M i).weight = Tile.peso G (orders i) (radii i) (costs i) R.p) ∧
      ∀ (tests : ∀ i, E i) (U : Config G f),
        Serif.TuneR (brand (independentPortraits M) tests) Set.univ (fun _ => 1) 0 z S U =
          (R.eval U : ℂ) • ∏ i, (1 +
            ((masked R.p.threshold (neighbors (radii i) (positions i))
              (Tile.read (D i) (positions i) (tests i)) U : ℝ) : ℂ) • z i) := by
  obtain ⟨M, hw, hc, hd⟩ := registered_marked_density (extend R radii) S B z
    D base positions (slot positions) (slot_injective positions) hβ
    (fun i => (registration R radii positions i).1)
    (fun i => (registration R radii positions i).2)
  refine ⟨M, hw, hc, ?_⟩
  intro tests U
  simpa only [point_eq, density_eq] using hd tests U

/-- Apply the original physical input-admission receipt once. The extension
keeps the same receipt and budgets, and has literal marked density on R. -/
theorem intake_marked_density {P : Teller G} {S : StepData c f} {T : Tube G S}
    {x : ℝ} (h : Intake P T x R)
    (D : ∀ i, Tile G (E i) (orders i) (radii i) (costs i))
    (base : ∀ i, E i) (positions : ι → Site f)
    {V : Type} [DecidableEq V] (B : Marker.Census V) (z : ι → Marker.Poly B) :
    Intake P T x (extend R radii) ∧
    ∃ M : ∀ i, Portrait (extend R radii) (E i),
      (∀ i, (M i).wing = Lotus.Wing.logKey (slot positions i)) ∧
      (∀ i, (M i).weight = Tile.peso G (orders i) (radii i) (costs i) R.p) ∧
      ∀ (tests : ∀ i, E i) (U : Config G f),
        Serif.TuneR (brand (independentPortraits M) tests) Set.univ (fun _ => 1) 0 z S U =
          (R.eval U : ℂ) • ∏ i, (1 +
            ((masked R.p.threshold (neighbors (radii i) (positions i))
              (Tile.read (D i) (positions i) (tests i)) U : ℝ) : ℂ) • z i) :=
  ⟨intake R radii h, marked_density R radii S D base positions h.positive B z⟩

end YM.Integration.RegisteredPhysicalMarks

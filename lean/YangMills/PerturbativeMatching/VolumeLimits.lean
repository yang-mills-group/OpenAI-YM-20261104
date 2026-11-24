import YangMills.FiniteVolume

/-! Smooth fixed-period limits of Wilson lattice moments, including their lattice differences. -/

set_option autoImplicit false
noncomputable section
namespace YangMills.PerturbativeMatching

open Filter MeasureTheory Set
open scoped Topology BigOperators Classical ContDiff

variable {g : GaugeGroup}

/-- Distinct insertions on the periodic box, expressed on its Euclidean cover. -/
def separatedModPeriod (period : ℕ+) (n : ℕ) : Set (Points n) :=
  {x | ∀ i j : Fin n, i ≠ j → ∃ a : Axis, ¬ ∃ k : ℤ,
    x i a - x j a = (k : ℝ) * period.val}

abbrev Grid (n : ℕ) := Fin n → Axis → ℤ

namespace Mesh

/-- A one-axis difference from `-back` to `forward`, divided by the full interval. -/
structure Step (n : ℕ) where
  slot : Fin n
  axis : Axis
  back : ℕ
  forward : ℕ
  nonempty : 0 < back + forward

def position {n : ℕ} (h : ℝ) (z : Grid n) : Points n :=
  WithLp.toLp 2 fun i => WithLp.toLp 2 fun a => h * (z i a : ℝ)

def differences {n : ℕ} (h : ℝ) : List (Step n) → (Grid n → ℂ) → Grid n → ℂ
  | [], f => f
  | s :: rest, f => fun z =>
    let e : Grid n := Pi.single s.slot (Pi.single s.axis 1)
    let u := differences h rest f
    (u (z + s.forward • e) - u (z - s.back • e)) / (((s.back + s.forward : ℕ) : ℂ) * h)

def derivatives {n : ℕ} : List (Step n) → (Points n → ℂ) → Points n → ℂ
  | [], f => f
  | s :: rest, f => fun x =>
    let e := WithLp.toLp 2 (Pi.single s.slot (EuclideanSpace.single s.axis (1 : ℝ)))
    fderiv ℝ (derivatives rest f) x e

/-- Multilinear interpolation on the mesh cell with upper corner `ceil (x / h)`. -/
def interpolate {n : ℕ} (h : ℝ) (f : Grid n → ℂ) (x : Points n) : ℂ :=
  let upper : Grid n := fun i a => ⌈x i a / h⌉
  let lowerWeight := fun (j : Fin n × Axis) => (upper j.1 j.2 : ℝ) - x j.1 j.2 / h
  ∑ lower : (Fin n × Axis) → Bool,
    (∏ j, if lower j then lowerWeight j else 1 - lowerWeight j) •
      f (fun i a => upper i a - if lower (i, a) then 1 else 0)

def moment (C : WilsonFamily g) (N p : ℕ) {n : ℕ} (v : Fin n → C.Token) (z : Grid n) : ℂ :=
  C.finiteMoment N p v (fun i a => (z i a : ZMod (C.period p * C.denominator N).val))

def smear (C : WilsonFamily g) (N p : ℕ) {n : ℕ} (t : SeparatedTest n) (f : Grid n → ℂ) : ℂ :=
  (C.mesh N : ℂ) ^ (4 * n) * ∑ z : Fin n → Site (C.period p * C.denominator N),
    t (Wilson.nodePosition C N p z) * f (fun i a => (z i a).valMinAbs)

end Mesh

/-- Every stencil converges on the full mesh sequence to the corresponding derivative
of one smooth periodic kernel. Its restriction to the period patch is the same table
used for the subsequent volume limit. The empty stencil is the original Wilson moment. -/
def SmoothMeshLimit (C : WilsonFamily g) (kernels : Wilson.PeriodPointTable C) : Prop :=
  ∀ (p n : ℕ) (v : Fin n → C.Token), ∃ f : Points n → ℂ,
    ContDiffOn ℝ ∞ f (separatedModPeriod (C.period p) n) ∧
    (∀ z : Wilson.periodPatch C p n, f z = kernels p v z) ∧
    (∀ t : SeparatedTest n, C.suitable p t →
      Tendsto (fun N => C.smear N p v t) atTop (𝓝 (∫ x, t x * f x))) ∧
    ∀ stencil : List (Mesh.Step n),
      let lattice := fun N => Mesh.differences (C.mesh N) stencil (Mesh.moment C N p v)
      let continuum := Mesh.derivatives stencil f
      ContinuousOn continuum (separatedModPeriod (C.period p) n) ∧
      (∀ x ∈ separatedModPeriod (C.period p) n, ∀ (z : ℕ → Grid n) (cutoff : ℕ → ℕ),
        Tendsto cutoff atTop atTop →
        Tendsto (fun j => Mesh.position (C.mesh (cutoff j)) (z j)) atTop (𝓝 x) →
        Tendsto (fun j => lattice (cutoff j) (z j)) atTop (𝓝 (continuum x))) ∧
      (∀ K : Set (Points n), IsCompact K → K ⊆ separatedModPeriod (C.period p) n →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ K,
          dist (Mesh.interpolate (C.mesh N) (lattice N) x) (continuum x) < ε) ∧
      (∀ t : SeparatedTest n, C.suitable p t → Integrable (fun x => t x * continuum x) ∧
        Tendsto (fun N => Mesh.smear C N p t (lattice N)) atTop (𝓝 (∫ x, t x * continuum x)))

abbrev TestTable (C : WilsonFamily g) :=
  (n : ℕ) → (Fin n → C.Token) → SeparatedTest n → ℂ

/-- At every suitable period take the full ultraviolet limit of the smeared Wilson
moment, then take the volume limit on the requested sequence of periods. -/
def HasTestLimits (C : WilsonFamily g) (periods : ℕ → ℕ) (L : TestTable C) : Prop :=
  ∀ (n : ℕ) (labels : Fin n → C.Token) (t : SeparatedTest n),
    (∀ᶠ k : ℕ in atTop, C.suitable (periods k) t) ∧ ∃ row : ℕ → ℂ,
      (∀ m, C.suitable m t →
        Tendsto (fun N => C.smear N m labels t) atTop (𝓝 (row m))) ∧
      Tendsto (fun k => row (periods k)) atTop (𝓝 (L n labels t))

/-- The hierarchy on a refinement represents every joint table that already
converges on the requested volume sequence. -/
def RepresentsTestLimits {C : WilsonFamily g} (T : Hierarchy C) (requested : ℕ → ℕ) : Prop :=
  ∀ L : TestTable C, HasTestLimits C requested L →
    ∀ (n : ℕ) (labels : Fin n → C.Token) (t : SeparatedTest n),
      L n labels t = ∫ x, t x * T.correlation none (T.project ∘ labels) x

end YangMills.PerturbativeMatching
end

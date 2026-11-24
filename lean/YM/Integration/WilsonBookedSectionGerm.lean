import YM.Integration.WilsonRunFormalMarkedStep
import YM.Integration.ActualOriginalOrbitCoefficients
import YM.XSpace.Section

/-! Relate the physical ultraviolet column and a position-scheme stencil
before the terminal Gaussian is taken. Both are tested on the original
holonomy sampler. The finite jet statement applies to separately chosen
surveys, and does not assert that their lattice cylinders coincide. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonBookedSectionGerm

open Lattice Source Source.Drops Labels Wilson PhysicalNext.Repeat.Legato
open FormalBulk08 FormalBulk08.Reef FormalBulk08.Flat FormalBulk08.Wick
open FormalBulk08.Series FormalBulk08.Jets FormalBulk08.Lava FormalBulk08.Kemp
open FormalBulk08.Pose FormalBulk08.Dawn FormalBulk08.Rial FormalBulk08.Roof
open Planned.PrimaryIntegral295 Place Film Carrier PowerSeries
open Function RG Precision Next.Free Stationary Lotus Shore
open Mesa Gorge City Cork Rift Glide Bank Wine Dove Bloch Exterior
open FormalBulk08.Orb Work.F03 Work.F05 Work.F08
open scoped ContDiff Topology Classical

variable {G : Gauge} (R : Run G) {d D : ℕ}

/-- The function which the fixed position scheme evaluates on the full
microscopic gauge configuration. -/
def surveyField (A : XSpace.Survey G R.family.params d) (v : Label G d)
    (U : CoverConfig G) : ℂ :=
  read (expand d (A.reading U)) v.val

/-- Without identifying two choices of microscopic stencils, each mixed
classical gauge jet has the same signed Taylor reading through its own
engineering horizon. This holds for every jet, not only one free direction. -/
theorem matched (A : XSpace.Survey G R.family.params d) (v : Label G d)
    (J : Jet G) (k : ℕ) (hk : k ≤ d) :
    iteratedDeriv k (fun h : ℝ => (R.family.localSection d).evaluate
      ((R.family.labels.level d).coords v) (R.family.params.links d J h)) 0 =
    iteratedDeriv k (fun h : ℝ => surveyField R A v (R.family.params.links d J h)) 0 := by
  let F := R.family.labels.level d
  obtain ⟨T, hT, _, hread⟩ := A.prepares F
  have h₁ := ((R.makes.sections d).projects (F.coords v) J).2.2 k hk
  have h₂ := (hT.projects (F.coords v) J).2.2 k hk
  have eq : (fun h : ℝ => T.evaluate (F.coords v) (R.family.params.links d J h)) =
      fun h : ℝ => surveyField R A v (R.family.params.links d J h) := by
    funext h
    exact hread _ _
  rw [← eq]
  exact h₁.trans h₂.symm

/-- All perturbative coefficients at the ultraviolet boundary of the actual
open transfer, with its prescribed scalar test and exact Laurent power. -/
theorem ultraviolet
    (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
    (a : hue G) (depth : d < D) (N per : ℕ)
    (b : Letter (R.family.labels.level d)) (f : Dawn.Studio D)
    (k : ℕ) (bound : ((R.family.labels.level d).grades (mint _ b)).2 ≤ k) :
    let F := R.family.labels.level d
    let n := R.family.side N per
    PowerSeries.X ^ (F.grades (mint F b)).2 *
      Kemp.banner k (WilsonRunFormalMarkedStep.graph R L a depth N N b f) n =
      PowerSeries.C (MvPolynomial.C (Dawn.notch (pet F b)
        ((Dawn.paper_fits (pet F b)).trans (Nat.le_trans d.le_succ depth)) f)) *
      paste (fun x : Jets.Rays (wire G n) =>
        ((R.family.localSection d).places (copy F (mint F b)) 0 (input G n x)).re) := by
  intro F n
  rw [WilsonRunFormalMarkedStep.graph, Elm.terrace_zero]
  exact WilsonFormalMarkedCubature.ultraviolet (R.family.localSection d) depth
    (CoefficientBridge.run_valuation R d) b f k bound n

end YM.Integration.WilsonBookedSectionGerm
end


import YM.Integration.FVA1Physical.Round2.PurchasedRootedField
import YM.Integration.WilsonPosteriorProjectionInletClock
import YM.Integration.FVA1Physical.Sources.Round2.PosteriorReclock

/-! Original fresh signed spatial error with the literal stencil input and
the clock reading of the independently normalized, recharted output.
All fine placements and all coarse spatial words keep their original meaning. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionRootedInlet
open Function Filter Finset Lattice RG YM.Wilson Precision RG.Supply Input Org Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PhysicalNext.Repeat.Legato Cub Circlet Graces Roost Qlocal.Schedule
open YM.Integration.FVA1Physical.Wilson Integration.FVA1Physical.Marked RGComparison.Core16 RGComparison.Core16.Spool
open MSbar MSbar.Heath MSbar.Heath.Stock MSbar.Midpoint MSbar.Cacao MSbar.CrossH MSbar.Bakery.Film MSbar.Whisk
open MSbar.Rolling MSbar.Kelvin MSbar.Lis MSbar.Bulk MSbar.Mosaic Tree Pressure Push.Uniform Exterior
open scoped Classical Topology BigOperators ContDiff
open FVA1Physical.Round2.Curvature FVA1Physical.Marked FVA1Physical.Wilson
variable {G : Gauge} {I : Type} [Fintype I] {d : ℕ}

theorem clock (J : I → RGComparison.Core16.Spool.Lamp G) (A : Issue G) (χ : ChartRatio G)
    (p : ℕ) (o : I → Site A.f) (part : Bool) :
    clockReading p A.fClock (emittedRows A χ (enterRows A (stencilInlet J o part)) p) =
      clue (renderedPolynomial (emittedRows A χ (jointFieldBank J A o part) p) p A.fClock) :=
  WilsonPosteriorProjectionInletClock.taste_input J A χ p o part

variable (a : I → CoverLabel G d)

def RootedInlet (R : PhysicalNext.Repeat.Legato.Run G) (u : G.ColorIndex)
    (p q s L radius : ℕ) (D η : ℝ) : Prop :=
  let P := p+(p+8)
  let r := fieldAuditOrder P q+2
  ∀ᶠ k : ℕ in atTop, ∀ N n, k ≤ N →
    (∃ S : Scene R.family.path.levels n r, Realized R.alloy.B.kin N n k r (Lis.sun G u) S) ∧
    ∀ (S : Scene R.family.path.levels n r) (scene : Realized R.alloy.B.kin N n k r (Lis.sun G u) S)
      (j : ℕ) (kj : k ≤ j) (jN : j < N),
      let F := (scene.step j jN kj).choose
      let v := (scene.step j jN kj).choose_spec.choose
      let A := sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
      let x := R.family.path.levels.clock.hatBeta j
      let y := R.family.path.levels.clock.hatBeta (j+1)
      S.Poly j=A.Zpost R.metals.O ∧
      ∀ (b : Site A.c) (o : I → Site A.f),
        (∀ i, separation (o i-A.S.ratio.embed b) 0 ≤ radius) →
        (∀ t : Slice (freshLamps a), separation (A.S.ratio.embed b) (legs (freshLamps a) o t).1 ≤ L*closeN y) →
        ∀ (part : Bool) (Z : List (Primary A.c G) → Positions (Primary A.c G)), (∀ l, ‖Z l‖ ≤ D) →
        let f := fun z => expect A.S A.pre (postcard G A.c A.fClock z) (fun U => look part (tally (freshLamps a) o U))
        let kernel := clockReading p A.fClock
          (emittedRows A R.metals.O (enterRows A (stencilInlet (freshLamps a) o part)) p)
        fieldDistance (Measuring.chart A.c G) b (rootedChartWidth q x) s q Z f kernel ≤ A.fClock^((p:ℝ)+1-η)

/-- A theorem about the actual uncut conditional of the named stencil. This
changes only the proven port identity of the formal output, never the source
placements, reserve, Haar denominator, or selection. -/
theorem fromOriginal (R : PhysicalNext.Repeat.Legato.Run G) (u : G.ColorIndex)
    (p q s L radius : ℕ) (D η : ℝ) (rooted : CurrentRooted a R u p q s L radius D η) :
    RootedInlet a R u p q s L radius D η := by
  simpa only [RootedInlet,CurrentRooted,clock] using rooted

end YM.Integration.WilsonPosteriorProjectionRootedInlet
end


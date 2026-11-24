import YM.Integration.WilsonFormalMarkedCubature
import YM.FormalBulk08.Elm.Mast
import YM.Integration.RunFormalChain

/-! The independently prescribed one-mark graph on the selected physical run.
At a finite horizon its normalized columns follow from the original section
and the single degree appointment at the lower end of the interval. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRunFormalMarkedStep

open FormalBulk08
open Function Filter Lattice RG Precision Next.Free Reef Flat Wilson Exterior Stationary Lotus
open Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) {d D : ℕ}
variable (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch)) (a : hue G) (depth : d < D)

private abbrev branches (i : ℕ) : (R.family.path.levels.clock.op i 0).patch.Branches R.family.path.levels.clock.kernel G :=
  (R.family.path.levels.blocks i 0).branches

/-- The microscopic section and every successive block belong to this run. -/
def graph (run : Run G) (roofs : ∀ i, Lodge ((run.alloy.B.a.clock.op i 0).patch))
    (color : hue G) (Dfit : d < D) (N i : ℕ) : Roof.Plaza (run.family.labels.level d) D := by
  exact Elm.terrace (K := run.alloy.B.a.clock.kernel) run.metals.O run.alloy.B.a roofs
    (branches run) color (run.family.labels.level d) (run.family.localSection d) Dfit N i

private abbrev vacuum (run : Run G) (roofs : ∀ i, Lodge ((run.alloy.B.a.clock.op i 0).patch))
    (color : hue G) (N i : ℕ) : Pot G := by
  exact Dove.model (K := run.alloy.B.a.clock.kernel) run.alloy.B.a roofs (branches run)
    run.metals.O color N i

/-- The formal mixing matrix uses the projection at the outgoing pivot. -/
def matrix (run : Run G) (roofs : ∀ i, Lodge ((run.alloy.B.a.clock.op i 0).patch))
    (color : hue G) (Dfit : d < D) (N i : ℕ) : Roof.Tilework (run.family.labels.level d) := by
  exact Roof.pTrain (run.family.labels.level d) run.metals.O color (destination run.alloy.B.a N i)
    (roofs i) (branches run i) (Elm.growL run.alloy.B.a i) (vacuum run roofs color N (i+1))
    (graph run roofs color Dfit N (i+1))

variable (simple : G.Simple) (origin : Loc G 1)
include simple origin

theorem normalized (N i : ℕ) (hi : i ≤ N) (trained : d ≤ R.family.path.levels.clock.J (i+1)) :
    Court origin (R.family.labels.level d) (graph R L a depth N i) := by
  induction hi using Nat.decreasingInduction with
  | self =>
    rw [graph, Elm.terrace_zero]
    exact Roof.topC origin (R.family.labels.level d) (R.family.localSection d) R.family.params
      (R.makes.sections d) (Next.Foundations.valuation G d) depth
  | of_succ i bound induction =>
    have later : d ≤ R.family.path.levels.clock.J (i+1+1) := trained.trans (R.family.path.levels.fits.mono (Nat.le_succ _))
    have income := induction later
    have next := (Dove.genu R.family.path.levels L (branches R) R.metals.O a R.alloy.B.ratio simple
      (i := i+1) (N := N) bound).toStory
    rw [graph, Elm.thickets _ _ _ _ _ _ _ _ _ _ bound]
    exact (Roof.axle (R.family.labels.level d) R.metals.O a (destination R.family.path.levels N i) (L i) (branches R i)
      (Elm.growL R.family.path.levels i) _ _ income next R.alloy.B.ratio R.family.params depth trained
      (R.family.path.levels.clock.adm i)).1

/-- The exact independently prescribed forward product, on this run at this
stop, read with all wraps into the chosen physical observing period. Every
finite numerator uses the true preimage, test pullback, stationary conditional
and the prescribed vacuum of this very history. -/
theorem measured (N i per : ℕ) (hi : i < N) (trained : d ≤ R.family.path.levels.clock.J (i+1))
    (tags : (n : Side) → (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel n).Choices)
    (b : Letter (R.family.labels.level d)) (f : Dawn.Studio D) (e r : ℕ)
    (v : chain (wire G (R.family.S.side i per)) r) :
    let n := R.family.S.side i per
    let P := destination R.family.path.levels N i
    let W := vacuum R L a N (i+1)
    let y := graph R L a depth N (i+1)
    let clock := Roof.epoch a P (L i) R.family.path.levels.clock.kernel W R.metals.O (branches R i)
    Tendsto (fun m : Side => ∑ k ∈ Finset.range (e+1),
      Wine.bill (bookH clock) (bookU clock) e k r *
        Shore.cores (Shore.tray m n)
          (rancho (WilsonFormalMarkedCubature.finiteTransfer P (L i) W R.metals.O (branches R i)
            (Elm.growL R.family.path.levels i) (y b) d (slots (R.family.labels.level d) b) f (m*n) (tags (m*n))) k r) v)
      atTop (𝓝 (rancho (Kemp.banner d ((Roof.larch (graph R L a depth N i)
        (matrix R L a depth N i)) b f) n) e r v)) := by
  intro n P W y clock
  have input := normalized R L a depth simple origin N (i+1) hi
    (trained.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
  have quiet := (Dove.genu R.family.path.levels L (branches R) R.metals.O a R.alloy.B.ratio simple
    (i := i+1) (N := N) hi).toStory
  have outgoing : graph R L a depth N i = Roof.avenue (R.family.labels.level d) R.metals.O a P (L i)
      (branches R i) (Elm.growL R.family.path.levels i) W y := Elm.thickets _ _ _ _ _ _ _ _ _ _ hi
  rw [outgoing]
  exact WilsonFormalMarkedCubature.periodized P (L i) W R.metals.O (branches R i)
    (Elm.growL R.family.path.levels i) origin y a R.family.params input quiet R.alloy.B.ratio depth trained
    (R.family.path.levels.clock.adm i) tags b f n e r v

end YM.Integration.WilsonRunFormalMarkedStep


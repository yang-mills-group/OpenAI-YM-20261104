import YM.Integration.WilsonThermometerOriginalForestReturn
import YM.Integration.WilsonThermometerPositionReceived
import YM.Integration.WilsonThermometerVertexVariation

/-! The recalibrated first nonbare coefficient on the full auxiliary copy family. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOriginalCoveredSlope
open Function Filter MeasureTheory Lattice RG Tree Wilson Exterior Precision Marker Multi Comparison.RG02
open Comparison.RG02.Assembly Comparison.RG02.Order FVA1Physical.Wilson FVA1Physical.TwoReset
open QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Earn AllOrder AllOrder.Floe PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker WilsonOriginalCopiedHistory
open scoped Classical BigOperators

variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {R:Census V} (run:Run G)
  {N i per:ℕ} (cut:i<N) {ι α:Type} {J:Passport (run.family.side (i+1) per) V}
  (M:ι→Row J R G α) (w:V→ℕ) (upper lower:Layout G) (T:Finset Age) (v:α) (p depth:ℕ)

/-- The straight pupil retains the actual copied old coefficients on every fine side. -/
def straightforward : Colors G R (run.family.side (i+1) per) :=
  fun _ tiles=>WilsonThermometerOriginalForestReturn.straight tiles M w upper lower T v p

include cut in
theorem original (live:0<p) (q:Pace.Coin) (a:ℝ) (earned:Pace.Earn q a)
    (input:Values G R (run.family.side (i+1) per))
    (agree:∀grid mult d,d≤p → ∀ y,input grid mult d y=peek mult M w upper T v d y)
    (grid:Side) (tiles:(run.family.side i per).val∣grid.val) (d:ℕ) (hd:d≤1)
    (y:Stationary.Link G grid) :
    block run cut p (receive input lower T w q earned.1 depth p) grid tiles d y=
      block run cut p (straightforward run M w upper lower T v p) grid tiles d y := by
  unfold block WilsonOriginalCoverCoefficient.read
  apply congrArg (limUnder (coverFilter run.family.path.levels.S i grid))
  funext b
  let n:=run.family.side (i+1) b.val
  let multiple:=(tiled run tiles b)
  let angle:=Stationary.arm G (run.family.side i b.val) 1 (convey (coverWin b.prop) y)
  let K:=(RunFormalChain.fromRun run).step N i b.val cut
  let F:=forest run i grid b
  let tag₀:=tag run i grid b
  have h:=WilsonThermometerOriginalForestReturn.received multiple M w upper lower T v p depth live q a earned
    input (agree n multiple) (run.family.path.levels.clock.op i b.val) K F tag₀ angle
  unfold WilsonOriginalCopiedContraction.contraction
  dsimp only
  obtain rfl|rfl : d=0 ∨ d=1 := by omega
  · exact congrArg (fun x:Poly R=>(((Pages grid (run.family.side i b.val):ℕ):ℝ)⁻¹:ℝ) • x) h.2.1
  · exact congrArg (fun x:Poly R=>(((Pages grid (run.family.side i b.val):ℕ):ℝ)⁻¹:ℝ) • x) h.2.2

end YM.Integration.WilsonThermometerOriginalCoveredSlope

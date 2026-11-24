import YM.Integration.WilsonOriginalNullWalk
import YM.QuadraticLocal.Travel

/-! Resolve the density multiplier on the numerical receiving vacuum at every group field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullResolved
open QuadraticLocal QuadraticLocal.Lanes
-- Use same M and data throughout. Countable ι handles address combinations per load.
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Mosaic RemainderComparison.Muse RemainderComparison.Sleet RemainderComparison.Serif RemainderComparison.Typeface RemainderComparison.Flues
open GridRenewal.Rain
open Marker Mallow Ovens Progress.DirectedRecipe
variable {I V : Type} [Countable I] [Fintype V] [DecidableEq V] {α : Type*}
variable {G : Gauge} {c n L : Side} {S : StepData c n} {P : Teller G}
  {Tube₀ : Tube G S} {X : Rep G n} {w x μ C : ℝ}
  {Q : YM.ConnectedActivityE6.Target G P} {ord : YM.ConnectedActivityE6.Target.Order G w}
variable (H : Cash w x μ L Q ord C Tube₀ X) {Y : Rep G c} {e f r s ν A K τ : ℝ} {k : ℕ}
variable (W : Travel.Walk H Y e f r s) (eye : Travel.Eyes H Y e ν A K k)
variable (M : I → Portrait X α) (x₀ : α) (l : I → ℝ)
variable (pledge : Motto (brand M x₀) l 0 H τ K A eye.sight)
variable (C₀ : Marker.Census V) (σ : I → Poly C₀) {radius : V → ℝ}
  (paid : Chorus C₀ radius Set.univ σ k) (site : V → Site c)
  (placed : ∀ j, Push.Corrected.Width.LocalCharge (G:=G) Y.p site (Flues.candle M x₀ S j) (fun _ => σ j))
local notation "O" => Chi.canonical
local notation "same" => (Match.staple (H:=H) («J»:=H) rfl rfl rfl)
local notation "top" => Y.p.supportExponent+1+1
local notation "Acad" => Lanes.academy H O eye.pad M x₀ l eye.bells pledge Y.p eye.block eye.pole le_rfl le_rfl
local notation "reg" => Pane.printBulbs site (Creek.theater H O M x₀ l Set.univ 0)
  Set.univ σ (Creek.Academy H O M x₀ l Set.univ 0 k) (Flues.candle M x₀ S) Acad
local notation "pre" => Lanes.layoutK H O eye.pad M x₀ l eye.bells pledge H same Y.p eye.block eye.pole
  W.entrance W.offer σ paid placed
local notation "src" => fun t => S.push X.beta (TuneR (brand M t) Set.univ l 0 σ S)
local notation "log₀" => fun t u => GridRenewal.Rain.fresh
  (∑' j, Serif.glyph (brand M t) H O Set.univ l 0 σ j u)

include W eye pledge placed paid
theorem original (forest : Tree.Forest S.ratio) (hs : 0 ≤ s)
    (law : Y.eval = S.push X.beta X.eval) (positive : ∀ U, Y.eval U ≠ 0) :
    ∃ hard : Hard α Y.p Y.activities.forced Y.activities.K site C₀,
      hard.Paid radius Y.p.B Y.p.supportExponent r ∧ ∀ t U,
      Summable (fun j => Serif.glyph (brand M t) H O Set.univ l 0 σ j U) ∧
      Summable (Fusion.Attached.packet Y.activities Y.p (hard.hard t) U) ∧
      src t U = ((Real.exp (Y.exponent U) : ℝ) : ℂ) •
        (Poly.pass (log₀ t U) * ∑' j,Fusion.Attached.packet Y.activities Y.p (hard.hard t) U j) := by
  obtain ⟨hard,bill,heard⟩ := WilsonOriginalNullWalk.original H W eye M x₀ l pledge C₀ σ paid site placed forest hs
  refine ⟨hard,bill,?_⟩
  intro t U
  have terms := (Serif.summit (brand M t) H O Set.univ l 0 eye.pad eye.bells
    (Typeface.outputs H M x₀ t l 0 pledge) σ paid Y.p eye.block eye.pole le_rfl le_rfl U).1
  obtain ⟨hsum,v,paidAt⟩ := heard t U
  have empty : (src t U).part C₀.quiet = ((Y.eval U : ℝ) : ℂ) := by
    rw [law]
    exact Lanes.tunePush H O eye.pad M x₀ t l eye.bells pledge σ paid U
  have hz : (log₀ t U).part C₀.quiet = 0 := GridRenewal.Rain.unwritten _
  rw [paidAt, Poly.part_smul, Poly.quiet_mul, Poly.pass_part _ hz, Hard.packet_of_quiet _ t U hsum,
    RG.Rep.eval, Complex.ofReal_mul, one_mul] at empty
  have hgas : ((Y.activities.gas Y.p U : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr <|
    right_ne_zero_of_mul (show Real.exp _ * Y.activities.gas Y.p U ≠ 0 from positive U)
  have he : v = ((Real.exp (Y.exponent U) : ℝ) : ℂ) := mul_right_cancel₀ hgas empty
  exact ⟨terms,hsum,he ▸ paidAt⟩

end YM.Integration.WilsonOriginalNullResolved

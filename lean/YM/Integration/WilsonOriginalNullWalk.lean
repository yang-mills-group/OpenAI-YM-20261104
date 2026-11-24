import YM.Integration.WilsonOriginalNullHouse
import YM.QuadraticLocal.Travel

/-! Two genuine original hard mergers for a roster funded on the elected house. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullWalk
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
theorem original (forest : Tree.Forest S.ratio) (hs : 0 ≤ s) :
    ∃ hard : Hard α Y.p Y.activities.forced Y.activities.K site C₀,
      hard.Paid radius Y.p.B Y.p.supportExponent r ∧
      ReadZone α Y.p Y.activities hard src log₀ := by
  have ha : 0 ≤ top := by linarith [Y.p.exponent_pos]
  have bright := Lanes.takes H O eye.pad M x₀ l eye.bells pledge H same Y.p eye.block eye.pole
    W.entrance W.offer σ paid le_rfl le_rfl (by linarith : Y.p.supportExponent ≤ top) placed forest
  have rooted := Lanes.layoutK_price H O eye.pad M x₀ l eye.bells pledge H same Y.p
    eye.block eye.pole W.entrance W.offer σ paid placed
  have lift := Kiosk.First.passes src (reg).log pre W.first paid.votes
    (Hard.mono _ rooted eye.room) (by linarith [Y.p.exponent_pos]) bright.2
  let empty := Travel.void (o:=site) G Y.p α (R:=C₀)
  have zeroFee : empty.Budget radius Y.p.B (Y.p.supportExponent + 1) s :=
    ⟨Empty.elim, fun i => Empty.elim i, fun _ => budget_finite (fun i => Empty.elim i)
      (by rw [Finset.univ_eq_empty, Finset.sum_empty]; exact hs)⟩
  refine ⟨Kiosk.Second.canopy (Kiosk.First.led pre W.first) empty W.second, ?_⟩
  apply Kiosk.Second.passes src (reg).log (Kiosk.First.led pre W.first) empty W.second paid.votes
    Y.p.exponent_pos.le lift.1 zeroFee lift.2
  · intro t u
    have gone : empty.log t u = 0 := by rw [Canopy.ShiftRows.log, tsum_empty]
    rw [gone, add_zero]
    rw [Pane.lit site _ Set.univ σ _ _ Acad placed t u paid ha, WickReps.Manor.basin,
      tsum_subtype_eq_of_support_subset]
    · exact congr_arg _ (tsum_congr fun j => Creek.stony H O M x₀ t l Set.univ 0 σ Y.p j u eye.pole)
    exact fun j hj => (show j ∈ Creek.Academy H O M x₀ l Set.univ 0 k from by_contra
      fun h => hj (Creek.onCampus H O M x₀ t l Set.univ 0 σ paid Y.p j u h))
  · intro t u; exact GridRenewal.Rain.unwritten _

end YM.Integration.WilsonOriginalNullWalk

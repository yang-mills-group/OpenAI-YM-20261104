import YM.Integration.WilsonAddressedWeakOriginalSmallAxis
import YM.Integration.WilsonThermometerWeakPanelAxes

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakOriginalSmallBill
open PhysicalNext PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Ship Next.Rank.Station Next.Rank.Spindle
open Function Filter Set Metric Source RG12 Extra.Histories RG05Readout Native Address Many Records Harvest Push.GridApprox Cells Extraction
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Tapes.West Configuration Normal Rise
open Paint Thirst Relation Perch Glimmer LiftMark Beamer Station Atlas Tariffs Ribbon
open Edition Peak Value Marker Corona Alarm Next.Rank.Glyph
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonAddressedWeakCalibration WilsonAddressedWeakReflectedHearing WilsonThermometerReflectedTrajectory
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone PhysMS
open Trace Trace.Pilot WilsonAddressedWeakCorrectedCylinder WilsonAddressedWeakPointCells WilsonAddressedWeakMaxwellPositions
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G) {d H:ℕ}
local notation "Rf" => R.family
local notation "Lev" => R.family.path.levels
local notation "cash" => WilsonThermometerOffsetLedger.cash R

open Next.Rank Read Cells

open WilsonThermometerWeakPanelBorn

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (exam:Panel H)
    (grade:d≤H) (φ:Test 2) (separated:tsupport φ⊆generic 2) (w:E4) (apart:(0:E4)≠w)
    (near:tsupport φ∈𝓝 (Extra.FD.couple 0 w)) (B:Binding Rf) (J:ChartRatio G) (O:HaarBudget G) (n:ℕ) (hn:2≤n):
    ∃ C:ℝ,0<C ∧ ∀ᶠ k:ℕ in atTop, ∀ᶠ N:ℕ in atTop, ∀ (p:ℕ) (hk:k<N),
    let F:=(Rf).labels.level d;let ξ:=exam.bag ((Lev).clock.J k)
    let tile:=Ship.yard Rf ξ.band hk.le p;let β:=(Rf).beta N p
    ∀ (b l q:ℝ) (menu:LegacyCost B J (-3) b ξ k n H O l q) (Q:Rep G ((Rf).side k p)),
      (∀ j≤d,Accent.generator G j≤b) → Actum B R.makes O J exam menu Q hk →
    ∀ (z₀:Site ((Rf).side N p)) (V:Sight Rf d p) (r:Emblems Rf d),
      Enrolled R.makes R.doors cash k N p d (digits R N p z₀) V r →
      ∀ v:F.Coeff,
      let f:=arm R r hk.le (WilsonAddressedWeakFixedChild.slide R hk.le z₀ 0) v
      Interior (tile.chamber 0) f ∧ tile.rootTest β f≤C*((2*WilsonThermometerSmallPanelRead.scaleCost (Rf) d)*F.coeffSize v):=by
  obtain ⟨C,hC,axes⟩:=WilsonAddressedWeakOriginalSmallAxis.original R simple shop S exam grade φ separated w apart near B J O
  refine ⟨C+1,by linarith only [hC],?_⟩
  have six:6≤exam.arc:=by linarith only [exam.huge,Nat.cast_nonneg (α:=ℝ) H]
  have pos:0<exam.arc:=by linarith only [six]
  filter_upwards [axes,(Ship.diminishes (Lev) n simple (by omega)).eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1)),
    (mag_rate (Lev) simple pos).eventually_ge_atTop 1] with k axes budget wide
  filter_upwards [axes] with N axes
  intro p hk;dsimp only;intro b l q menu Q funds current z₀ V r enrolled v
  obtain ⟨T,costT,price⟩:=axes p n hk hn b l q menu Q funds current z₀ V r enrolled
  let ξ:=exam.bag ((Lev).clock.J k)
  have band:ξ.band=exam.arc:=exam.factor _
  have bw:1 ≤ mag (Lev) ξ.band k:=band.symm ▸ wide
  have monitor:1≤(Lev).clock.monitor k:=Real.one_le_exp (sq_nonneg _)
  exact WilsonThermometerWeakPanelBorn.root R r hk.le (WilsonAddressedWeakFixedChild.slide R hk.le z₀ 0)
    (width (Lev) ξ.band k) (((Station.wider (Lev) ξ.band k).trans (before (Lev) ξ.band k)).trans hk.le)
    (mag (Lev) ξ.band k) bw monitor T costT v (C+1) (by linarith only [hC])
    (fun j=>⟨(price j).1,(price j).2.trans (add_le_add (le_refl C) budget)⟩)
end YM.Integration.WilsonAddressedWeakOriginalSmallBill
end

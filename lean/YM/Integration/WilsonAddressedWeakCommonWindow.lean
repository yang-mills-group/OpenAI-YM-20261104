import YM.Integration.WilsonAddressedWeakFixedRank
import YM.Integration.WilsonAddressedWeakOriginalSmallBill
import YM.Integration.WilsonAddressedWeakGenericTest
import YM.Integration.WilsonThermometerOrdinaryPanels
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakCommonWindow
open Function Filter Set Lattice RG Wilson Spec Extraction Cells
open YM.Integration.WilsonLimitConstruction
open PhysicalNext.Repeat.Legato Next.Rank Next.Rank.Tapes.West Next.Rank.East
open PhysicalNext.RankCovariance MergeProof.East Trace.Over
open scoped Topology Classical

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

variable {C:Local.Physical.Deck G} {O₀:Booked C} (M:MS_Data G O₀)

abbrev lower (exam:Panel H) (w:E4) (μ ε:ℝ) (k N p:ℕ) (hk:k<N):Prop:=
    let x₀:=Extra.FD.couple 0 w;let K:=MSDeckProbeGram.matrix M d 0 w μ 0
    let s:=clim (Lev) k;let ξ:=exam.bag ((Lev).clock.J k)
    let ρ:=gap (Lev) ξ.band k;let g:=(Rf).S.toDepth hk.le p
    ∀ (z₀:Fin 2→Site ((Rf).side N p)) (V₀:Fin 2→Sight Rf d p) (r:Fin 2→Emblems Rf d),
      (∀ i,Enrolled R.makes R.doors cash k N p d (digits R N p (z₀ i)) (V₀ i) (r i)) →
      ∃ u:Fin 2→Glyph C d→(Rf).label d,
      let y:=fun (i:Fin 2)(j:Glyph C d)=>chunk (C:=Rf) (WilsonThermometerOwnOffsetField.primaryLetter d) (u i j); (∀ i j,size (y i j)≤Perch.bill (ξ.credit-1) s) ∧
      let z:=fun i=>WilsonAddressedWeakFixedChild.slide R hk.le (z₀ i)
          (g.parent (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x₀ i))
      let A:Matrix (Glyph C d) (Glyph C d) ℂ:=fun a e=>reading R (fun _=>d) z (fun i=>y i (![a,e] i)) r hk.le full
      IsUnit A ∧ ∀a e,‖A⁻¹ a e-K⁻¹ a e‖<ε

abbrev upper (exam:Panel H) (B:ℝ) (k N p:ℕ) (hk:k<N):Prop:=
    let ξ:=exam.bag ((Lev).clock.J k);let tile:=Ship.yard (Rf) ξ.band hk.le p
    ∀ (z:Site ((Rf).side N p)) (V:Sight (Rf) d p) (r:Emblems (Rf) d),
      Enrolled R.makes R.doors cash k N p d (digits R N p z) V r → ∀ v:(Rf).label d,
      let o:=WilsonAddressedWeakFixedChild.slide R hk.le z 0
      let f:=WilsonThermometerWeakPanelBorn.arm R r hk.le o v
      Interior (tile.chamber 0) f ∧ tile.rootTest ((Rf).beta N p) f≤ B*((2*WilsonThermometerSmallPanelRead.scaleCost (Rf) d)*((Rf).labels.level d).coeffSize v)

/-- Each panel at this common preceding station tests the original physical basis on fixed own residues.
The second estimate bounds the unsubtracted positive physical cell of every enrolled numerical arm. -/
theorem original (paid:R2I.RG05Joint.AcrossPanels R.kit) (simple:G.Simple)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (V:Warehouse G) (grade:d≤H)
    (μ ε:ℝ) (positive:0<ε):
    ∃ (K:Binding (Rf)) (O:HaarBudget G) (P:Fin 3→Panel H) (δ:ℝ) (w:E4) (C₀:Fin 3→ℝ),
      K.prices=R.metals.K ∧ Checks (P 0).arc (P 1).arc (P 2).arc δ (trays H) H ∧
      (0:E4)≠w ∧ IsUnit (MSDeckProbeGram.matrix M d 0 w μ 0) ∧ (∀i,0<C₀ i) ∧
      ∀ (floor:ℕ) (η:ℝ),0<η → ∀ᶠ star:ℕ in atTop,∃ k,
      floor≤k ∧ k ≤ star ∧ (Rf).S.a k/(Rf).S.a star≤(Lev).clock.hatBeta star^η ∧
      (∃ t,Poised P K R.makes O (Next.Foundations.chart G) (trays H) (ParcelPrice G H) k t) ∧
      ∀ᶠ N:ℕ in atTop,∀p(hk:k<N) (a:Fin 3),lower (d:=d) R M (P a) w μ ε k N p hk ∧ upper (d:=d) R (P a) (C₀ a) k N p hk:=by
  obtain ⟨K,O,z,hK,_,_,bank⟩:=WilsonThermometerOrdinaryPanels.original R paid
  let J:=Next.Foundations.chart G
  obtain ⟨P,δ,together,previous⟩:=WilsonThermometerOrdinaryPanels.previous R simple bank H
  obtain ⟨w,φ,away,spread,near⟩:=WilsonAddressedWeakGenericTest.original
  have arity:2≤trays H:=by unfold trays;omega
  have low (i:Fin 3):=WilsonAddressedWeakFixedRank.coordinates R M simple shop S V
    (P i) grade φ spread 0 w away near μ ε positive K J O (trays H) arity
  choose C₀ pos upperCost using fun i=>WilsonAddressedWeakOriginalSmallBill.original R simple shop S
    (P i) grade φ spread w away near K J O (trays H) arity
  obtain ⟨threshold,atDate⟩:=eventually_atTop.mp (eventually_all.mpr fun i:Fin 3=>(low i).2.and (upperCost i))
  refine ⟨K,O,P,δ,w,C₀,hK,together,away,(low 0).1,pos,?_⟩
  intro floor η ηpos
  filter_upwards [previous (max floor threshold) η ηpos] with star access
  obtain ⟨k,minK,maxK,gap,t,course⟩:=access
  have heard:=atDate k ((le_max_right _ _).trans minK)
  refine ⟨k,(le_max_left _ _).trans minK,maxK,gap,⟨t,course⟩,?_⟩
  filter_upwards [eventually_all.mpr fun i:Fin 3=>(heard i).1.and (heard i).2] with N pay
  intro p hk i
  obtain ⟨l,q,menu,issue⟩:=course.supply i
  obtain ⟨Q,act,_⟩:=issue N p hk
  have funded(j:ℕ)(hj:j≤d):Accent.generator G j≤ParcelPrice G H:=parcelCost (G:=G) j H (hj.trans grade)
  exact ⟨(pay i).1 p hk _ l q menu Q funded act,(pay i).2 p hk _ l q menu Q funded act⟩
end YM.Integration.WilsonAddressedWeakCommonWindow
end

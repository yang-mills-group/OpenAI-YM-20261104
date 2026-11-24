import YM.Integration.WilsonThermometerWeakSeatedPortfolio
import YM.Integration.WilsonAddressedPositionStencils
import YM.Integration.WilsonThermometerWeakWardSourceBall

/-! Submit one original funded family at each real radius before imposing any
comparison tolerance, numerical tester or exterior measurement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPublishedRoster
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

open Function Filter Set Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG RG12 Labels Extra.Histories RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local
open PhysicalNext.Repeat.Legato MergeProof Accent Trace.Physical Trace.Physical.GermGraph Work.G08 Next.Rank
open RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize XSpace.Rose
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerReading
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource WilsonPositionCorrectedCap
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open scoped BigOperators Classical Topology
open Next.Extract Push PhysicalNext.RankCovariance Pert Pert.Position MS.Land MS.Menus
open RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local WilsonAddressedReportedColumns
open WilsonPositionThermometerStationNorm
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {T:Table R.family.book}
variable {D:Local.Physical.Deck G} {O:Booked D} (M:MS_Data G O)
variable (V₀:∀d,Source.SectionData (R.family.labels.level d)) (W:Mark.Weave G)
    {P₀:∀d,(ℕ×ℕ)→(R.family.label d≃ₗ[ℂ]R.family.label d)} (b:Presentation R.family)
    (house:Hearthside R.family V₀ W P₀ b (PhysicalNext.Repeat.Legato.Bandage.fly R.alloy.B.a))
variable (F:Final R.family f T) (P:ℝ→tower T) (V:Store G) {H:(Bel R.family.book).Hierarchy}
    {l:Ultrafilter (ℕ×ℕ)} {cap:ℕ} (A:ℝ→WilsonPositionThermometerCapStation.Group R.family cap)
local notation "C" => R.family
local notation "Lev" => R.family.path.levels
local notation "cash" => WilsonThermometerOffsetLedger.cash R



variable (portfolio:∀d,Mark.Portfolio R.family.params (V₀ d) (W d))

open WilsonOffsetReportingProducts
open WilsonThermometerReflectedWatch (exterior)
open WilsonCapturedPrimaryWardRetimed (reading)
open WilsonThermometerMarchTerminalWatch (upper)
open MeasureTheory Labels XSpace XSpace.Rose WilsonOffsetEquationLaw OPE.Orbits

open WilsonThermometerWeakPositionMoments (expense)


open WilsonPositionPhysicalCellTest (Sites)
open WilsonThermometerWeakExteriorOriginal (stencils)

structure Sheet {n:ℕ} (R:Run G) (d:Fin n→Fin (cap+1))(N p:ℕ) where
  Q : Sites R (N,p) n → ∀ i,Sight R.family (d i) p
  r : Sites R (N,p) n → ∀ i,Emblems R.family (d i)
  y : Sites R (N,p) n → ∀ i,Palette R.family (d i)

def paid {n N p m:ℕ}(d:Fin n→Fin (cap+1))(w:∀i,(Bel (C).book).Field (d i))
    (Z:WilsonPositionThermometerCapStation.Group (C) cap)(K:ℕ)(E:Fin (cap+1)→ℝ)(ε:ℝ)
    (hm:m≤N)(S:Sheet R d N p):Prop:=
  ∀c,(∀i,Enrolled R.makes R.doors cash m N p (d i) (digits R N p (c i)) (S.Q c i) (S.r c i) ∧
    b.step (d i) (N,p) (reading (p:=p) (S.r c i) hm (S.y c i))=
      b.step (d i) (N,p) (Z.station.wheel.atCut (N,p) (index Z (d i)) (Z.change (d i) (w i))) ∧
    size (S.y c i)≤(E (d i)*(2*(Lev).clock.hatBeta m)^ε)*(cost (C) (d i)*(‖w i‖+costHint 0))) ∧
    stencils (R:=R) b d w Z (N:=N) (m:=m) K (S.Q c) (S.r c) (S.y c)

include M V₀ W b house portfolio
theorem original {n:ℕ}(d:Fin n→Fin (cap+1)) (w:∀i,(Bel (C).book).Field (d i))
    (simple:G.Simple) (panels:R2I.RG05Joint.AcrossPanels R.kit) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (rules:Rules G) (warehouse:Warehouse G) (book:Book (f:=f) (l:=l) (H:=H) A P) (lead:Leading F P)
    (slow:WilsonWindowReportingPace.Slow R.kit) (K v:ℕ) (pos:0<v) (μ ε:ℝ) (ep:0<ε):
    ∃rad:ℕ→ℕ,∃E:Fin (cap+1)→ℝ,(∀j,0≤E j) ∧ ∀ᶠρ:ℝ in trail,
      let Z:=adjusted F P V A ρ; let m:=WilsonMeasuredWindow.stop (Lev) simple v ρ
      projects (f:=f) (Y:=l) H d w Z (WilsonPositionPrescribedFrame.positioned F P V ρ) 0 ρ ∧
      ∃report:m≤Z.station.k, ∃N₀:ℕ,∃late:∀N:ℕ,N₀≤N→Z.station.k<N,
        ∃file:∀N:ℕ,N₀≤N→(p:ℕ)→Sheet R d N p,
        (∀(N:ℕ)(hn:N₀≤N)(p:ℕ),paid b d w Z K E ε (report.trans (late N hn).le) (file N hn p)) ∧
        ∀δ:ℝ,0<δ→∀ᶠ z:ℕ×ℕ in f.fuse,∃hn:N₀≤z.1,let S:=file z.1 hn z.2
          let hm:=report.trans (late z.1 hn).le
          ∀(c:Sites R z n)(g:Site ((C).side m z.2)),expense V₀ d w Z hm
            (fun i=>c i+((C).S.toDepth hm z.2).embed g) (S.r c) (S.y c) rad δ:=by
  classical
  obtain ⟨E,en,fields⟩:=WilsonAddressedPositionStencils.original M V₀ W b house F P V A portfolio d w
    simple panels shop rules warehouse book lead slow K v pos μ ε ep
  obtain ⟨rad,_,_,threshold⟩:=WilsonThermometerWeakWardSourceBall.original R M V₀ W b portfolio house cap
    simple panels shop rules warehouse μ ε ep f H F.room.copies
  refine ⟨rad,E,en,?_⟩
  have go:Tendsto (fun ρ=>(adjusted F P V A ρ).station.k) trail atTop:=tendsto_atTop.mpr
    fun j=>(WilsonPositionCorrectedCap.mixed F P V A book lead d w j).mono fun _ e=>e.1
  have stops:=WilsonMeasuredWindow.stop_tendsto (Lev) simple v pos
  filter_upwards [fields,stops.eventually (threshold (Fin n) d),go.eventually (eventually_all.mpr (fun i=>
    WilsonThermometerReferenceStation.cutoff («C»:=R.family) (f:=f) (H:=H) simple R.makes (d i).val ε ep))]
    with ρ enrolled available upperPay
  let Z:=adjusted F P V A ρ
  let m:=WilsonMeasuredWindow.stop (Lev) simple v ρ
  obtain ⟨proj,report,income⟩:=enrolled
  obtain ⟨N₀,offered⟩:=eventually_atTop.mp income
  let late (N:ℕ)(hn:N₀≤N):Z.station.k<N:=(offered N hn).1
  have stock (N:ℕ)(hn:N₀≤N)(p:ℕ):∃D:Sheet R d N p,paid b d w Z K E ε (report.trans (late N hn).le) D:=by
    choose Q r lodged y rent rows using fun c:Sites R (N,p) n=>(offered N hn).2 p c
    refine ⟨⟨Q,r,y⟩,fun c=>⟨fun i=>⟨lodged c i,rent c i⟩,?_⟩⟩
    intro u mu un hi
    obtain ⟨q,a,bill⟩:=rows c u mu un hi
    refine ⟨q,a,fun j=>?_⟩
    convert! bill j using 6
  choose files hfile using stock
  refine ⟨proj,report,N₀,late,files,hfile,?_⟩
  intro δ positive
  let Xcap (i:Fin n):=Real.exp (Work.D01.columnLogs (Lev) Z.station.k)*
    (((Lev).clock.hatBeta Z.station.k)^ε*(cost (C) (d i)*‖Z.change (d i) (w i)‖))
  let Ycap (i:Fin n):=(E (d i)*(2*(Lev).clock.hatBeta m)^ε)*(cost (C) (d i)*(‖w i‖+costHint 0))
  filter_upwards [(upper f).eventually_ge_atTop N₀,available Xcap Ycap δ positive] with z hz budget
  obtain ⟨_,_,offers⟩:=budget
  refine ⟨hz,?_⟩
  dsimp only
  intro c g s
  let D:=files z.1 hz z.2
  let x (i:Fin n):=Z.station.wheel.atCut z (index Z (d i)) (Z.change (d i) (w i))
  let hm:=report.trans (late z.1 hz).le
  have upperBound (i:Fin n):‖x i‖≤Xcap i:=by
    have coin:‖x i‖≤((C).labels.level (d i)).coeffSize (x i):=(pi_norm_le_iff_of_nonneg
      (Work.G08.size_nonneg _ _)).mpr fun j=>Finset.single_le_sum (fun _ _=>norm_nonneg _) (Finset.mem_univ j)
    exact coin.trans (upperPay i Z.station (index Z (d i)) rfl rfl proj.2.1 (Z.change (d i) (w i)) z.1 z.2 (late z.1 hz))
  have fromR:=(hfile z.1 hz z.2 c).1
  exact offers s (fun i=>c i+((C).S.toDepth hm z.2).embed g) (fun i=>D.Q c i) (fun i=>D.r c i) (fun i=>x i) (fun i=>D.y c i)
    (fun i=>WilsonThermometerWeakShiftedWord.enrolled hm (c i) g (fromR i).1)
    (fun i=>(fromR i).2.1.symm) (fun i=>upperBound i) (fun i=>(fromR i).2.2)

end YM.Integration.WilsonThermometerWeakPublishedRoster
end

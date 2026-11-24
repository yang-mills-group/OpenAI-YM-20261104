import YM.Integration.WilsonThermometerWeakPublishedRoster
import YM.Integration.WilsonThermometerWeakOriginalShapeGeometry

/-! One cutoff family realizes all weak position moments, including arbitrary proper
faces against each fixed registered macroscopic Wilson exterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPublishedWatch
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


open WilsonThermometerWeakPublishedRoster (Sheet paid)
open WilsonPositionPhysicalCellTest (site mass)
open WilsonThermometerWeakMeasuredExterior (rate)
open WilsonThermometerWeakExteriorTest (readingAt)
open WilsonThermometerWeakOriginalShapeGeometry (fixed)
open WilsonThermometerMarchSupported (period)

structure Course {n:ℕ} (R:Run G)(d:Fin n→Fin (cap+1))(m:ℕ)(Z:WilsonPositionThermometerCapStation.Group R.family cap) where
  report : m≤Z.station.k
  start : ℕ
  late : ∀N:ℕ,start≤N→Z.station.k<N
  file : ∀N:ℕ,start≤N→(p:ℕ)→Sheet R d N p

def salary {n m:ℕ} (d:Fin n→Fin (cap+1))(w:∀i,(Bel (C).book).Field (d i))
    (Z:WilsonPositionThermometerCapStation.Group (C) cap)(K:ℕ)(E:Fin (cap+1)→ℝ)(ε:ℝ)(a:Course R d m Z):Prop:=
  ∀(N:ℕ)(hn:a.start≤N)(p:ℕ),paid b d w Z K E ε (a.report.trans (a.late N hn).le) (a.file N hn p)

def shifts {n m:ℕ} (d:Fin n→Fin (cap+1))(w:∀i,(Bel (C).book).Field (d i))
    (Z:WilsonPositionThermometerCapStation.Group (C) cap)(a:Course R d m Z)(rad:ℕ→ℕ):Prop:=
  ∀δ:ℝ,0<δ→∀ᶠ z:ℕ×ℕ in f.fuse,∃hn:a.start≤z.1,let B:=a.file z.1 hn z.2
    let hm:=a.report.trans (a.late z.1 hn).le
    ∀(c:Sites R z n)(g:Site ((C).side m z.2)),expense V₀ d w Z hm
      (fun i=>c i+((C).S.toDepth hm z.2).embed g) (B.r c) (B.y c) rad δ

def screened {n:ℕ}(d:Fin n→Fin (cap+1))(φ:Test n)(W₁:Watch (C))(ρ:ℝ)(N p:ℕ)
    (x:Sites R (N,p) n→∀i,(C).label (d i))(s:Finset (Fin n)):ℂ:=
  ∫z,φ z*(let c:=site (R:=R) ρ (N,p) z
    moment ((C).beta N p) (fun g=>(∏i:s,(C).O N p (x c i) (c i) g)*W₁.plot N p g))

def difference {n m:ℕ}(d:Fin n→Fin (cap+1))(w:∀i,(Bel (C).book).Field (d i))
    (Z:WilsonPositionThermometerCapStation.Group (C) cap)(a:Course R d m Z)(φ:Test n)(W₁:Watch (C))(ρ:ℝ)
    (s:Finset (Fin n))(z:ℕ×ℕ):ℂ:=
  if hn:a.start≤z.1 then
    let f:=a.file z.1 hn z.2;let hm:=a.report.trans (a.late z.1 hn).le
    screened d φ W₁ ρ z.1 z.2 (fun c i=>reading (p:=z.2) (f.r c i) hm (f.y c i)) s-
    screened d φ W₁ ρ z.1 z.2 (fun _ i=>Z.station.wheel.atCut z (index Z (d i)) (Z.change (d i) (w i))) s
  else 0

private theorem tested {n m:ℕ}(d:Fin n→Fin (cap+1))(w:∀i,(Bel (C).book).Field (d i))
    (Z:WilsonPositionThermometerCapStation.Group (C) cap)(a:Course R d m Z)(rad:ℕ→ℕ)
    (pay:shifts (f:=f) V₀ d w Z a rad)(room:CellHyp (C) f)(φ:Test n)(W₁:Watch (C))(ρ:ℝ)
    (N₀ p₀:ℕ)(geom:∀p:ℕ,p₀≤p→∀N:ℕ,N₀≤N→∀s:Finset (Fin n),∀k:Fin W₁.n→ℕ,(∀i,m≤k i)→
      ∀c:Sites R (N,p) n,mass φ ρ (N,p) c≠0→
      Avoids («C»:=R.family) V₀ rad (fun i:s=>(d i).val) (fun i=>c i) ∧
      (∀(i:s)(t:Fin W₁.n),(↑(((C).localSection (W₁.q t).1).footprint (fixed (R:=R) W₁.held N p t)):Set (Site ((C).side N p)))
        ⊆Mark.Outer (rad (d i)) (c i)) ∧
      WilsonThermometerWeakSeatedExterior.Seats (R:=R) (m:=m) s k c (fixed (R:=R) W₁.held N p)):
    ∀δ:ℝ,0<δ→∀ᶠ z:ℕ×ℕ in f.fuse,∀s:Finset (Fin n),
      ‖difference d w Z a φ W₁ ρ s z‖≤(∫x,‖φ x‖)*δ:=by
  classical
  let e (i:Fin W₁.n):=(W₁.q i).1
  let x (i:Fin W₁.n):(C).label (e i):=(W₁.q i).2
  obtain ⟨floor,fee,nn,issued⟩:=WilsonThermometerWeakMeasuredExterior.purchase room e
  let k (i:Fin W₁.n):=max m (floor i)
  let price:=(∏i,rate (R:=R) (e i) (k i) (fee i))*(∏i,(1+‖x i‖))
  have pos:0≤price:=mul_nonneg (Finset.prod_nonneg fun i _=>by
    dsimp only [WilsonThermometerWeakMeasuredExterior.rate];positivity [nn i,(C).S.a_pos (k i)]) (Finset.prod_nonneg fun i _=>by positivity)
  intro δ dp
  let t:=δ/(1+price)
  have tp:0<t:=by dsimp only [t];positivity
  have restore:t*price≤δ:= (mul_le_mul_of_nonneg_left (show price≤1+price by linarith) tp.le).trans_eq (div_mul_cancel₀ _ (by positivity:1+price≠0))
  filter_upwards [(upper f).eventually_ge_atTop (max N₀ W₁.t),(period f).eventually_ge_atTop p₀,
    issued k (fun i=>le_max_right _ _),pay t tp] with z late volume tickets source
  obtain ⟨fund,weights⟩:=tickets
  obtain ⟨hn,source⟩:=source
  let S:=a.file z.1 hn z.2
  let hm:=a.report.trans (a.late z.1 hn).le
  intro s
  have better:=WilsonThermometerWeakSeatedExterior.tested V₀ d w Z hm S.r S.y rad t tp.le source
    e k fund fee nn weights φ ρ s (fixed (R:=R) W₁.held z.1 z.2) x
    (geom z.2 volume z.1 ((le_max_left _ _).trans late) s k (fun i=>le_max_left _ _))
  have atWatch:fixed (R:=R) W₁.held z.1 z.2=W₁.among z.1 z.2:=funext fun i=>
    WilsonThermometerWeakOriginalShapeGeometry.installed W₁ ((le_max_right _ _).trans late) i
  dsimp only at better
  rw [atWatch] at better
  rw [difference,dif_pos hn]
  exact better.trans (mul_le_mul_of_nonneg_left restore (integral_nonneg fun _=>norm_nonneg _))

include M V₀ W b house portfolio
theorem original {n:ℕ}(d:Fin n→Fin (cap+1)) (w:∀i,(Bel (C).book).Field (d i))
    (simple:G.Simple) (panels:R2I.RG05Joint.AcrossPanels R.kit) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (rules:Rules G) (warehouse:Warehouse G) (book:Book (f:=f) (l:=l) (H:=H) A P) (lead:Leading F P)
    (slow:WilsonWindowReportingPace.Slow R.kit) (K v:ℕ) (vp:0<v) (μ ε:ℝ) (ep:0<ε):
    let Z:=adjusted F P V A;let m:=WilsonMeasuredWindow.stop (Lev) simple v
    ∃E:Fin (cap+1)→ℝ,(∀j,0≤E j) ∧ ∃use:Set ℝ, use∈trail ∧
      ∃released:∀ρ,ρ∈use → Course R d (m ρ) (Z ρ),
      (∀ρ (hρ:ρ∈use),projects (f:=f) (Y:=l) H d w (Z ρ) (WilsonPositionPrescribedFrame.positioned F P V ρ) 0 ρ ∧
        salary b d w (Z ρ) K E ε (released ρ hρ)) ∧
      ∀(φ:Test n)(W₁:Watch (C)),∀ᶠρ:ℝ in trail,∃hρ:ρ∈use,∀δ:ℝ,0<δ→∀ᶠ z:ℕ×ℕ in f.fuse,∀s:Finset (Fin n),
        ‖difference d w (Z ρ) (released ρ hρ) φ W₁ ρ s z‖≤(∫x,‖φ x‖)*δ:=by
  classical
  dsimp only
  obtain ⟨rad,E,nn,input⟩:=WilsonThermometerWeakPublishedRoster.original M V₀ W b house F P V A portfolio d w
    simple panels shop rules warehouse book lead slow K v vp μ ε ep
  let Z:=adjusted F P V A
  let m:=WilsonMeasuredWindow.stop (Lev) simple v
  let use:Set ℝ:={ρ|∃a:Course R d (m ρ) (Z ρ),projects (f:=f) (Y:=l) H d w (Z ρ) (WilsonPositionPrescribedFrame.positioned F P V ρ) 0 ρ ∧
    salary b d w (Z ρ) K E ε a ∧ shifts (f:=f) V₀ d w (Z ρ) a rad}
  have accepted:use∈trail:=input.mono fun ρ ⟨pr,r,N,late,files,hbill,htest⟩=>
    ⟨⟨r,N,late,files⟩,pr,hbill,htest⟩
  choose actual terms using fun ρ (hρ:ρ∈use)=>hρ
  refine ⟨E,nn,use,accepted,actual,fun ρ hρ=>⟨(terms ρ hρ).1,(terms ρ hρ).2.1⟩,?_⟩
  intro φ W₁
  obtain ⟨p₀,shapes⟩:=WilsonThermometerWeakOriginalShapeGeometry.original (R:=R) simple slow v vp V₀ (fun i=>(d i).val)
    (fun i=>(W₁.q i).1) rad φ W₁.held W₁.origin (generic_conf _ W₁.wild)
  filter_upwards [accepted,shapes] with ρ hρ seats
  obtain ⟨N₀,geometry⟩:=seats
  exact ⟨hρ,tested V₀ d w (Z ρ) (actual ρ hρ) rad (terms ρ hρ).2.2 F.room.copies φ W₁ ρ N₀ p₀ geometry⟩

end YM.Integration.WilsonThermometerWeakPublishedWatch
end

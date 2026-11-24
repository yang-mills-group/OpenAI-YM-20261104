import YM.Integration.WilsonThermometerWeakExteriorTest
import YM.Integration.WilsonAddressedPositionStencils
import YM.Integration.WilsonThermometerWeakWardSourceBall

/-! The corrected position source, its priced upper stencils, and every
occupied Ward-erased moment against the cleared exterior of the same Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakExteriorOriginal
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


open WilsonThermometerWeakMeasuredExterior (word posted rate)
open WilsonPositionPhysicalCellTest (Sites site mass)
open WilsonThermometerWeakExteriorTest (readingAt Housing)

def delimited {n:ℕ}{J:Type}[Fintype J](d:Fin n→Fin (cap+1))(w:∀i,(Bel (C).book).Field (d i))
    (Z:WilsonPositionThermometerCapStation.Group (C) cap) (ρ:ℝ) {N m p:ℕ} (live:m≤N)
    (r:Sites R (N,p) n→∀i,Emblems (C) (d i))(y:Sites R (N,p) n→∀i,Palette (C) (d i))
    (e:J→ℕ)(k:J→ℕ)(fund:∀i,k i≤N)(rad:ℕ→ℕ)(δ:ℝ):Prop:=
  ∀(φ:Test n)(s:Finset (Fin n))(o:J→Site ((C).side N p))(a:∀i,(C).label (e i)),
    (∀c:Sites R (N,p) n,mass φ ρ (N,p) c≠0→Housing V₀ (fun i=>(d i).val) s e rad live k fund o c) →
    let actual:=fun i=>Z.station.wheel.atCut (N,p) (index Z (d i)) (Z.change (d i) (w i))
    let filed:=fun c i=>reading (p:=p) (r c i) live (y c i)
    ‖(∫x,φ x*let c:=site ρ (N,p) x;readingAt (fun i=>(d i).val) s e (N,p) c (filed c) o a)-
      (∫x,φ x*let c:=site ρ (N,p) x;readingAt (fun i=>(d i).val) s e (N,p) c actual o a)‖ ≤
      (∫x,‖φ x‖)*(δ*∏i,(1+‖a i‖))

def stencils {n N m p:ℕ} (d:Fin n→Fin (cap+1))(w:∀i,(Bel (C).book).Field (d i))
    (Z:WilsonPositionThermometerCapStation.Group (C) cap)(K:ℕ)(Q:∀i,Sight (C) (d i) p)
    (r:∀i,Emblems (C) (d i))(y:∀i,Palette (C) (d i)) :Prop:=
  ∀(u:ℕ)(mu:m≤u)(un:u≤N),u≤WilsonInvariantActionPosition.berth R K m →
          let S:=(C).path.rep N p u
          let h:=fun i=>WilsonCapturedPrimaryWardRetimed.lift (r i) mu (y i)
          ∃q:∀i,Palette (C) (d i),
            (∀i,b.step (d i) (N,p) (WilsonCapturedPrimaryWardRetimed.reading (p:=p) (r i) un (h i))=
              b.step (d i) (N,p) (Z.station.wheel.atCut (N,p) (index Z (d i)) (Z.change (d i) (w i))) ∧
              Printed (C) (d i) S 0 (kappa (C).path u)
                (Q i u (h i)) (q i) (h i) (cash (d i) u*size (h i))) ∧
            ∀J:Finset (Fin n),(∑a:WilsonAddressedFiniteStencils.Choices R (fun i=>(d i).val) J,
                ‖∏i:J,WilsonAddressedThermometerBasis.coefficient S.p.threshold (q i.val) (a i)‖) ≤
              ∏ i:J,WilsonAddressedThermometerBasis.fee R K m (d i.val)*
                (((C).S.a m/(C).S.a u)^(d i.val).val*size (y i.val))

include M V₀ W b house portfolio
theorem original {n:ℕ}{J:Type}[Fintype J](d:Fin n→Fin (cap+1))(w:∀i,(Bel (C).book).Field (d i))
    (e:J→ℕ)(simple:G.Simple)(panels:R2I.RG05Joint.AcrossPanels R.kit)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (rules:Rules G)(warehouse:Warehouse G)(book:Book (f:=f) (l:=l) (H:=H) A P)(lead:Leading F P)
    (slow:WilsonWindowReportingPace.Slow R.kit)(K v:ℕ)(vp:0<v)(μ ε:ℝ)(ep:0<ε):
    ∃rad:ℕ→ℕ,∃E:Fin (cap+1)→ℝ,∃floor:J→ℕ,(∀i,0≤E i) ∧ ∀ᶠ ρ:ℝ in trail,
      let Z:=adjusted F P V A ρ
      let m:=WilsonMeasuredWindow.stop (Lev) simple v ρ
      projects (f:=f) (Y:=l) H d w Z (WilsonPositionPrescribedFrame.positioned F P V ρ) 0 ρ ∧
      ∃report:m≤Z.station.k,∀k:J→ℕ,(∀i,floor i≤k i)→∀δ:ℝ,0<δ→∀ᶠ np:ℕ×ℕ in f.fuse,let N:=np.1;let p:=np.2
      ∃late:Z.station.k<N,∃fund:∀i,k i≤N,
      ∃(Q:Sites R np n→∀i,Sight (C) (d i) p)(r:Sites R np n→∀i,Emblems (C) (d i))
        (y:Sites R np n→∀i,Palette (C) (d i)),
        (∀(c:Sites R np n)(i:Fin n),Enrolled R.makes R.doors cash m N p (d i) (digits R N p (c i)) (Q c i) (r c i) ∧
          b.step (d i) np (reading (p:=p) (r c i) (report.trans late.le) (y c i))=
            b.step (d i) np (Z.station.wheel.atCut np (index Z (d i)) (Z.change (d i) (w i))) ∧
          size (y c i)≤(E (d i)*(2*(Lev).clock.hatBeta m)^ε)*(cost (C) (d i)*(‖w i‖+costHint 0))) ∧
        (∀c,stencils (R:=R) b d w Z (N:=N) (m:=m) K (Q c) (r c) (y c)) ∧
        delimited V₀ d w Z ρ (report.trans late.le) r y e k fund rad δ:=by
  classical
  obtain ⟨rad,E,nonneg,forms⟩:=WilsonThermometerWeakPositionMoments.original M V₀ W b house F P V A portfolio d w
    simple panels shop rules warehouse book lead slow K v vp μ ε ep
  obtain ⟨floor,fee,nn,issued⟩:=WilsonThermometerWeakMeasuredExterior.purchase F.room.copies e
  refine ⟨rad,E,floor,nonneg,?_⟩
  filter_upwards [forms] with ρ given
  let Z:=adjusted F P V A ρ
  let m:=WilsonMeasuredWindow.stop (Lev) simple v ρ
  obtain ⟨projected,report,entry⟩:=given
  refine ⟨projected,report,?_⟩
  intro k right δ positive
  let price:=∏i,rate (R:=R) (e i) (k i) (fee i)
  have nonnegative:0≤price:=Finset.prod_nonneg fun i _=>by
    dsimp only [WilsonThermometerWeakMeasuredExterior.rate]
    positivity [nn i,(C).S.a_pos (k i)]
  let t:=δ/(1+price)
  have tp:0<t:=by dsimp only [t];positivity
  have restored:t*price≤δ:=by
    apply (mul_le_mul_of_nonneg_left (show price≤1+price by linarith) tp.le).trans_eq
    exact div_mul_cancel₀ _ (by positivity:1+price≠0)
  filter_upwards [entry t tp,issued k right] with np old science
  obtain ⟨late,printed⟩:=old
  obtain ⟨fund,tickets⟩:=science
  choose Q r logged y comparison priced available using fun c:Sites R np n=>printed c
  refine ⟨late,fund,Q,r,y,fun c i=>⟨logged c i,comparison c i⟩,?_,?_⟩
  · intro c u mu un allowed
    obtain ⟨q,literal,salary⟩:=priced c u mu un allowed
    refine ⟨q,literal,fun j=>?_⟩
    convert! salary j using 6
  intro φ s o a geometry actual fitted
  have measured:=WilsonThermometerWeakExteriorTest.tested V₀ d w Z (report.trans late.le) r y rad t tp.le available
    e k fund fee nn tickets φ ρ s o a geometry
  apply measured.trans (mul_le_mul_of_nonneg_left ?_ (integral_nonneg fun x=>norm_nonneg (φ x)))
  change t*(price*_)≤δ*_
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right restored (Finset.prod_nonneg fun i _=>by positivity)

end YM.Integration.WilsonThermometerWeakExteriorOriginal
end

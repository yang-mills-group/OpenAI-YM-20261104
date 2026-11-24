import YM.Integration.WilsonSeparatedPrefixScreenedParents
import YM.Integration.WilsonSeparatedPrefixScreenedEars
import YM.Integration.WilsonSeparatedPrefixScreenedCredit
import YM.Integration.WilsonSeparatedPrefixScreenedWord
import YM.Integration.WilsonSeparatedPrefixCellHousing
import YM.Integration.WilsonMovingForkClearance

/-! The physical N-born part of the detector hearing at every literal screened node, on the unchanged parent reporter. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixScreenedPhysical
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare

open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {z:Trace.Terrace.Arch R.family}
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS
open MS MS.Land FVA2 FVA2.Register


open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open WilsonThermometerMarchSource WilsonThermometerReflectedTrajectory WilsonMeasuredPublicEntranceHeadBoard
open WilsonAddressedAlignedColumn WilsonReflectedPublicStationFare
open WilsonThermometerOffsetCylinder WilsonThermometerOffsetTrajectory

open WilsonThermometerUnitFilingCoarse WilsonSeparatedPrefixCanonicalClearConvolution
open Lodestar
variable {E:Type}[Fintype E][DecidableEq E][Nonempty E]
open WilsonSeparatedPrefixMovingHomeEars (returned)
local notation "J₀" => Marks E
local notation "X" => Unit×(E×Bool)


open WilsonThermometerUnitFilingFlatTelescope (numerator)
omit [DecidableEq I] in
theorem original (Jr:ℝ→tower S)(Z₀:WilsonPrescription G)
    (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(quoted:∀g:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) g)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(D T h:ℕ)(d:I→Fin (D+1))
    (name:∀i,RG17.Free C (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (slip:∀s,WilsonMovingForkWindowBooks.Priced F (books s))
    (cater:Cater (C) R.doors)(bank:WilsonThermometerClusterProjectionBudget.Ready (P))
    (wage:WilsonReportLampForecast.Ready (P))(nested:WilsonPositionProgramNestedLengths.Nested R.rolls)
    (full:∀i,((P).budget i).supportExponent=100)(target:ℕ)
    (pick:E ↪ I)(L η:ℝ)(lp:0<L)(ep:0<η):
    ∃M:ℝ,1≤M ∧ ∃t≥D+3,∀base:ℕ,∀ᶠ r in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},
      (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 m
      ∃j:ℕ,base≤j ∧ ∃_fine:j+2≤f,
      ∀p N(deep:f<N),∃(V:(a:Fin (D+1))→Sight C a.val p)(u:(a:Fin (D+1))→Emblems C a.val)
        (est:∀a:Fin (D+1),Opened C a.val f p),
      (∀a,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N p a.val
        (digits R N p 0) (V a) (u a)) ∧
      ∀(branch:E→Bool)(site:E → Cover),
      let deg:=d∘pick
      let v:=fun i=>WilsonPositionHomogeneousFrame.homogeneous F Jr Z₀ (ρ (pick i)).val (deg i).val (name (pick i))
      let rows:=fun i=>(books (ρ (pick i))).rows (deg i)
      let x:=fun i=>((rows i).arm (branch i) (v i)).source (N,p)
      let y:=fun i=>offer R (x i) (est (deg i)) deep.le
      let data:=fun i=>reduce (y i)
      let roots:=snap (C) f p site
      let A:=word R (fun i=>(deg i).val) f N p deep.le site x
      let Z:=fun i=>marked R (N:=N) 0 (1,false) (roots i) (V (deg i)) (u (deg i)) (data i) f
      let B:=fun U=>∏i,((WilsonThermometerMarchSource.charge (y i):ℝ):ℂ)*(Z i).2.1 U
      (∀i,‖(C).S.gridPoint f (site i)‖≤L*outer z h r) →
      (Pairwise fun i k=>η*r≤‖(C).S.gridPoint f (site i)-(C).S.gridPoint f (site k)‖) →
      WilsonThermometerReflectedRoster.filed R (fun i=>(deg i).val) (fun _=>0) (fun _=>(1,false)) roots data
        (fun i=>V (deg i)) (fun i=>u (deg i)) J₀ deep.le t ∧
      (∀W:Config G ((C).side j p),flags ((C).path.rep N p j).p.threshold W=∅ →
        returned (R:=R) deep.le (by omega) A B W (M*((β f)^target)⁻¹)) ∧
      (∀e:ℕ,(C).ref 0≤e→∀ej:e≤j,Opened C 0 e p→∀K:ℕ,∀fk:f≤K,∀kn:K≤N,
        ‖reading R (N:=N) (credit (C) N p 0 A K kn) e (ej.trans (by omega))-
          reading R (N:=N) (numerator R N p f B) e (by omega)‖≤M*((β f)^target)⁻¹):=by
  classical
  obtain ⟨window,housing⟩:=WilsonSeparatedPrefixCellHousing.original F simple bliss slow D T h 0 d books L lp
  obtain ⟨M,one,t,degree,first,paid⟩:=WilsonSeparatedPrefixScreenedEars.original F Jr Z₀ simple bliss slow
    lead quoted shop D T h d name books slip cater bank wage nested window 1 target pick
  have clearance:=WilsonMovingForkClearance.original (I:=I) F simple bliss slow D T h books lp ep
  obtain ⟨walls,wide⟩:=eventually_atTop.mp ((hat_rate (P) simple).eventually_ge_atTop (Real.exp 3))
  obtain ⟨op,witness⟩:=eventually_atTop.mp (open_late (C) simple 0)
  refine ⟨M,one,t,degree,?_⟩
  intro base
  let wait:=max base (max first (max op walls))
  filter_upwards [paid,housing wait,clearance] with r submitted capture separated ρ band hit m f
  obtain ⟨j,before,extent,span,home⟩:=capture ρ band hit
  change j+2≤f at extent
  have firstj:first≤j:=by dsimp [wait] at before;omega
  have openj:op≤j:=by dsimp [wait] at before;omega
  have high:walls≤f:=by dsimp [wait] at before;omega
  have height:j≤f:=by omega
  have wall:Real.exp 3≤β f:=wide f high
  have heat:0<β f:=(Real.exp_pos 3).trans_le wall
  have ink:5≤((P).budget f).B:=by
    have sq:(Real.log (β f))^2≤(((P).budget f).B:ℝ):=Nat.le_ceil _
    have log3:3≤Real.log (β f):=(Real.le_log_iff_exp_le heat).mpr wall
    exact_mod_cast (show (5:ℝ)≤(((P).budget f).B:ℝ) by nlinarith)
  refine ⟨j,(le_max_left ..).trans before,extent,?_⟩
  intro p N deep
  obtain ⟨V,u,est,enroll,respond⟩:=submitted ρ band hit p N deep
  refine ⟨V,u,est,enroll,?_⟩
  intro branch site deg v rows x y data roots A Z B inside apart
  have rep:((C).path.rep N p f).p=(P).budget f:=(R.makes.wilson.represents N p f deep.le).vac
  have ample:5≤((C).path.rep N p f).p.B:=by rw [rep];exact ink
  have sep (i k:E)(dist:i≠k):((C).path.rep N p f).p.B^2+1 ≤ separation (roots i) (roots k):=by
    rw [rep]
    have fare:=separated ρ band hit (N:=N) (p:=p) deep.le site inside apart i k dist
    change ((P).budget f).B^2 < separation
      (WilsonThermometerReflectedTrajectory.point R (N:=N) 0 (1,false) (roots i) f)
      (WilsonThermometerReflectedTrajectory.point R (N:=N) 0 (1,false) (roots k) f) at fare
    rw [WilsonAddressedPublicGridRooms.position R deep.le,WilsonAddressedPublicGridRooms.position R deep.le] at fare
    exact fare
  obtain ⟨filed,clear,ear⟩:=respond branch (fun _=>(1,false)) roots j firstj height span (full f) ample sep
  let source:=fun U=>∏i∈(Stock.final E).val,(C).O N p
      (displayed R (deg i).val (x i) (1,false)) (anchorAt R (roots i) N) U
  have placed:source=A:=WilsonSeparatedPrefixScreenedWord.original R (p:=p) (fun i=>(deg i).val) deep.le site x
  have positive:2≤((P).budget j).supportExponent:=by rw [full];norm_num
  refine ⟨filed,?_,?_⟩
  · intro W ok
    have invoice:returned (R:=R) deep.le height source B W (M*((β f)^target)⁻¹):=
      clear positive W ok (Stock.final E)
    rw [placed] at invoice
    exact invoice
  · intro e early ej oe K fk kn
    have rm:8*(L*outer z h r)≤(C).S.a (j+1):=by simpa using home
    have pinned:=WilsonSeparatedPrefixScreenedParents.original R (p:=p) extent site _ inside rm
    let anchor:X:=((),(Classical.arbitrary E,false))
    let loc:=fun a:X=>WilsonOriginalNullOriginGridRoster.ancestry R p f (roots a.2.1) (j+1)
    have zloc(t:X):loc t=0:=pinned t.2.1
    have house:∀t:X,coverNumber ((C).path.rep N p (j+1)).p.B ({loc anchor,loc t}:Support _)≤1:=by
      intro t
      simpa [zloc] using WilsonThermometerUnchangedGrouping.alone ((C).path.rep N p (j+1)).p.B (0:Site ((C).side (j+1) p))
    have parent:((P).clock.op j p).ratio.parent (loc anchor)=0:=by
      rw [zloc]
      let g:=((P).clock.op j p).ratio
      change g.parent 0=0
      rw [←g.root.map_zero]
      exact g.embed_parent _
    have invoice:returned (R:=R) deep.le (ej.trans height) source B 1 (M*((β f)^target)⁻¹):=
      ear extent 1 anchor (le_refl _) house parent e early ej oe (witness j openj p) (Stock.final E)
    rw [placed] at invoice
    exact WilsonSeparatedPrefixScreenedCredit.original R deep.le kn (ej.trans height)
      (ej.trans (height.trans fk)) A (WilsonSeparatedPrefixScreenedWord.funded R (p:=p) _ deep.le site x)
      B _ invoice

end YM.Integration.WilsonSeparatedPrefixScreenedPhysical
end

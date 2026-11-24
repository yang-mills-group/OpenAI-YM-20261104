import YM.Integration.WilsonOriginalTwoFlatIRPoolFirstSignal
import YM.Integration.WilsonOriginalTwoFlatIRPoolQuadrature
import YM.Integration.WilsonOriginalTwoFlatIRPoolUnscaledField
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolFirstTest
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Shard
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOlderFreshSoftSocketRestored (stopped coin rated)
open WilsonOlderFreshSoftSocketGross (gross)
open WilsonOlderFreshSoftSocketTotal (normalized)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonOlderFreshSoftSocketFaces (fill)
open WilsonOlderFreshHybridClock (flat)
open WilsonReportingAbsoluteInletForecastBooks (mass value)
open WilsonCoeffUV.Winding
open scoped Topology BigOperators Classical

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

local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatRoseBook (group)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonOriginalMicroscopicGuardedGridSchool (Finished)
open WilsonOlderFreshSoftRoseMesh (filed)
open WilsonPositionThermometerGradedSource
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations
open WilsonReflectedPublicStationFare
open PhysMS
open MS MS.Land FVA2 FVA2.Register
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse

variable (Jr:ℝ→tower S)(Z:WilsonPrescription G)

open WilsonOriginalObservedRoseVanePurse (ages)
open WilsonOriginalObservedRoseMeshHeight (variation)
open WilsonOriginalMicroscopicGuardedPage (wrapCost)
open Extra.Histories.Motion (orbitCost orbitCost_one_le)
open WilsonOlderFreshSoftSocketStationPair (amount)
open WilsonOriginalObservedRoseMeshHeight (tilt height)
open WilsonOriginalObservedRoseScaledWallet (share)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonReceivedCanonicalVersePortfolio (weight Selection wallet)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonThermometerDeclaredSeeds
local notation "J" => Stock.census (Fin 3)

open WilsonCoeffUV.Bank.Ticket
open WilsonOlderFreshSoftSocketOptical (fixed fixed_nonneg)
open WilsonOriginalObservedRoseStoppedSalary (stop)
local notation "σ" => R.family.S.scale
local notation "g" => Pert.Asymptotics.regulatorRun R.family

open WilsonOriginalOpticalSchedule (prepared)
open WilsonOlderFreshSoftRoseCourse (seat)
open WilsonOlderFreshSoftRoseNodes (Covered)
open WilsonOlderFreshSoftRoseIncome (Stock)
universe u
variable {axis:Axis}{ε:ℝ}{schedule:WilsonOriginalAllOrderCourse.Schedule G}{crop:Campaign R}{W:Campaign.Pillars R crop}

open WilsonOriginalObservedRosePublicMesh (aperture)
open WilsonInvariantActionPosition (berth)

open WilsonOriginalObservedRosePublicGross (base)
open WilsonPositionThermometerConnected (value)
local notation "Faces" => Finset (Fin 3)

private def mark (s:Faces):(J).Mode:=⟨s,Finset.mem_univ _⟩

open WilsonOriginalObservedRosePublicConnected (cut)
open WilsonReceivedChronologicalFixedRoseFigureTerms (Account)
open WilsonOriginalTwoFlatIRSocketSale (Node)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
private def bookedFace (s:Faces):(J).Mode:=⟨s,mem_univ _⟩
open WilsonReceivedChronologicalFixedRoseVariation (cells signed)
open MeasureTheory
open WilsonReceivedChronologicalFixedRoseFittedDebit (Plan written low high)
open WilsonReceivedChronologicalFixedRoseHeldCofactor (demand)
open WilsonMovingForkOpticalBook (reporter)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonOriginalTwoFlatIRPoolOrigins (home)
open WilsonPositionThermometerGradedSource (grade)

open WilsonOriginalTwoFlatIRSocketHeardCell (incumbent)
open WilsonOriginalTwoFlatIRPoolBook (direct)
open WilsonOriginalTwoFlatIRPoolQuadrature (microscopic)
open RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
/-- Public equal-radius Rose on the honest continuum positions after removal
of the original regulator, with the true quadratic spatial and two kinetic bills. -/
theorem original (simple:G.Simple)
    (bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)(lead:Leading F Jr)
    (admitted:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(bot:∀j,1≤((P).budget j).supportExponent)
    (cap:∀j,((P).budget j).supportExponent≤100)(T h:ℕ)(x:(i:Fin 3)→RG17.Free (C) (grade i).val)
    {δ:ℝ}(books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z 6 T s.val)
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s))
    (hl:(l:Filter _)≤order.fuse)(φ:Test 3)(dp:0<δ)
    (funded:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε (prepared schedule) R crop W):
    ∃B:ℝ,0≤B ∧ ∃(physical E:ℕ)(charge:Faces→ℝ), (∀s,0≤charge s) ∧ ∀startLevel u₀:ℕ,
    Stop (C) 0 startLevel u₀ → Facilities (C) order S → ∀q:ℕ,∃A:ℝ,0≤A ∧ ∀reserve:ℕ,
    let width:=WilsonReceivedChronologicalFixedRosePublicAperture.width reserve (2*T+11+2*h)
    ∃U:Set ℝ,U∈trail ∧ ∀(target debt Q:ℕ)
    (_:cut target E debt width≤Q)(Cφ:ℝ)(_:0<Cφ)
    (D:Fin 3→ℕ)(_:∀i,ages i<D i)(X opt tol:ℝ)(_:0≤X)(_:0≤opt)(_:0<tol)
    (plan:Plan 3)(M:Fin 3→ℝ)(_:∀i,1≤M i)
    (_:plan.Affords (demand target physical) (2*E) (WilsonOriginalObservedRosePublicMesh.aperture width) 14),
    let J₀:=cut target E debt width
    ∃start:ℕ,∀ᶠv:ℕ in atTop,∃(V:Realm G (Q+1) Credit.leanC)(draw:V.draws=P),
    V.paid=R.metals.O ∧ V.y=zz P ∧ V.anchor=v ∧ Covered R D Q v start V draw opt tol ∧
    (∀s:Finset (Fin 3),s.Nonempty → Stock R D Q v start V draw opt tol s) ∧
    ∀r∈U,∀ρ:Fin 3→{s:ℝ //0<s ∧ s<δ},(∀i,(ρ i).val=r)→
    let b:=reporter F books ρ
    let L:=fun i=>home F Jr Z (books (ρ i)) (grade i) (x i)
    let K:=WilsonInvariantActionPosition.berth R reserve b
    ∃uf:u₀≤b,∀δ₀:ℝ,0<δ₀→∀ᶠpair:ℕ×ℕ in (l:Filter _),let N:=pair.1;let per:=pair.2
    ∀(c requested tag:ℕ)(bk:b≤K)(kn:K≤N),b<N →
    0<v → v≤c → c≤b → v+1≤K → σ K-σ (v-1)≤(plan.width:ℝ)*(1+Real.log (β v)) →
    let θ:=g N per v
    θ≤4*wilson z r → ∀(file:Filed R ages K),let D₀:=cells R φ r (b,per)
    ∀panel:D₀ → Panel R ages N per b K bk kn requested plan.pole tag plan.tuition,
    (∀y,(panel y).loc=y.val ∧ (panel y).M=M ∧ (panel y).slot=file.station ∧ (panel y).axis=file.A N per ∧
      (∀i,(panel y).slot i=(L i).j) ∧ (∀i,(panel y).names i=(L i).arm.source (N,per)) ∧
      ∀i,WilsonReflectedPublicOrientedFaces.displayed R (ages i) ((panel y).names i) ((panel y).turn i)=(L i).arm.source (N,per)) →
    ∀(κ:(i:Fin 3)→Knob (D i))(pt:Fin 3→Chamber)(digits:D₀→Digits (P) (Fin 3))
      (atSite:D₀→Fin 3→ Cover)(test:D₀→(s:Faces)→Pen D s→L[ℝ]ℝ),
      (∀y (s:Faces),s.Nonempty → ‖test y s‖≤X*(θ⁻¹)^debt) →
    let w:=fun y:D₀=>votes R ages (N:=N) (per:=per) file (panel y).names (panel y).turn
    let row (j:ℕ)(y:D₀)(s:Faces):=normalized R ages κ pt N per K c v (digits y) s (w y) (atSite y) (test y s) j θ
    let before:=uf.trans bk
    let source:=fun (y:D₀)(s:Faces)=>WilsonMeasuredPublicEntranceCellWords.physical R ages
      (panel y).names (panel y).turn y.val (bookedFace s) (N:=N)
    let fixed:=fun (y:D₀)(s:Faces)=>WilsonReceivedChronologicalFixedRoseTestSource.fixed R kn before (source y s)
    ∀basal first:D₀→Faces→ℂ,
    let register:=fun (y:D₀)(s:Faces)=>written R ages plan (panel y) file v c s (fixed y s) (row Q y s)
      (basal y s) (first y s)
    (∀y (s:Faces),s.Nonempty → (register y s).Paid) →
    (∀y (s:Faces),s.Nonempty → ‖basal y s‖≤low R ages plan K N per v s) →
    (∀y (s:Faces),s.Nonempty → ‖first y s‖≤high R ages plan K N per v s) →
      ‖WilsonOriginalTwoFlatIRPoolFirstSignal.smooth F Jr Z x φ r-signed R φ r (b,per) (fun y=>value (row J₀ y))‖≤
        (∫x,‖φ x‖)*(B*(wilson z r)^2+(A*(wilson z r)^q+2*θ^target))+δ₀:=by
  obtain ⟨B,bp,spatial⟩:=WilsonOriginalTwoFlatIRPoolFirstSignal.grid F Jr Z simple bliss lead admitted x φ
  obtain ⟨physical,E,charge,pos,grants⟩:=WilsonOriginalTwoFlatIRPoolUnscaledField.original
    F Jr Z simple bliss slow lead admitted shop bot cap T h x books window hl φ dp funded
  have mesh:=WilsonOriginalTwoFlatPublicMixedMesh.original F simple bliss slow 6 T h grade books
  have clk:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  obtain ⟨U₁,u₁,closed⟩:=Filter.Eventually.exists_mem (spatial.and (mesh.and (clk.positive.and
    ((clk.conforms simple).eventually (ge_mem_nhds zero_lt_one)))))
  refine ⟨B,bp,physical,E,charge,pos,?_⟩
  intro j u₀ stop fac q
  obtain ⟨A,ap,sale⟩:=grants j u₀ stop fac q
  refine ⟨A,ap,?_⟩
  intro reserve width
  obtain ⟨U,up,book⟩:=sale reserve
  refine ⟨U∩U₁,inter_mem up u₁,?_⟩
  intro target debt Q retention Cφ cp D fits X opt tol xp op tp plan M one booking J₀
  obtain ⟨start,visit⟩:=book target debt Q retention Cφ cp D fits X opt tol xp op tp plan M one booking
  refine ⟨start,?_⟩
  filter_upwards [visit] with v dated
  obtain ⟨V,draw,oil,zero,first,cover,stock,issued⟩:=dated
  refine ⟨V,draw,oil,zero,first,cover,stock,?_⟩
  intro r hr ρ same b L K
  have near:∃i,(ρ i).val=r:=⟨0,same 0⟩
  have good:=closed r hr.2
  have span:∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r:=by
    intro i
    rw [same i]
    refine ⟨le_rfl,?_⟩
    have rp:0<r:=(ρ i).property.1.trans_eq (same i)
    have gp:0<wilson z r:=good.2.2.1
    have g1:wilson z r≤1:=good.2.2.2
    have estimate:r≤r/(wilson z r)^h:=(le_div_iff₀ (pow_pos gp _)).mpr
      (mul_le_of_le_one_right rp.le (pow_le_one₀ gp.le g1))
    simpa only [outer,div_eq_mul_inv,inv_pow] using estimate
  obtain ⟨uf,probes⟩:=issued r hr.1 ρ span near
  refine ⟨uf,?_⟩
  intro δ₀ dp
  have fit:((C).S.a b/r)≤(wilson z r)^2:=(good.2.1 ρ span near).1
  have grid:=good.1 b fit
  have coords:(fun i=>homogeneous F Jr Z (ρ i).val (grade i).val (x i))=
    (fun i=>homogeneous F Jr Z r (grade i).val (x i)):=funext fun i=>by rw [same i]
  have incurred:‖WilsonOriginalTwoFlatIRPoolFirstSignal.smooth F Jr Z x φ r-
      WilsonOriginalTwoFlatIRPoolQuadrature.physical F Jr Z books x φ r ρ‖≤(∫y,‖φ y‖)*B*(wilson z r)^2:=by
    simpa only [WilsonOriginalTwoFlatIRPoolQuadrature.physical,coords] using grid
  filter_upwards [probes δ₀ dp] with pair original
  intro N per c requested tag bk kn live vp vc cb later age θ measured file D₀ panel
    filed κ pt digits sites t priced w rows before input fixed basal fresh accounts earned low₀ high₀
  have lower:=original c requested tag bk kn live vp vc cb later age measured file panel filed κ pt digits sites t priced basal fresh earned low₀ high₀
  exact (norm_sub_le_norm_sub_add_norm_sub _ (WilsonOriginalTwoFlatIRPoolQuadrature.physical F Jr Z books x φ r ρ) _).trans
    ((add_le_add incurred lower).trans_eq (by ring))

end YM.Integration.WilsonOriginalTwoFlatIRPoolFirstTest
end

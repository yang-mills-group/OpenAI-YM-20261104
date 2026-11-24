import YM.Integration.WilsonOriginalTwoFlatIRPoolOrigins
import YM.Integration.WilsonOriginalTwoFlatIRSocketOccupancy
import YM.Integration.WilsonOriginalTwoFlatIRSocketHeardCell
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolChamber
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
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS
open MS MS.Land FVA2 FVA2.Register


open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
variable (Jr:ℝ → tower S)(Z:WilsonPrescription G)

open WilsonPositionThermometerGradedSource
local notation "heads" => source (C) (Finset.univ:Finset (Fin 3))
local notation "SiteSet" => {s:Finset (Fin 3)//s.Nonempty}

open WilsonPositionThermometerCapStation (Group)
open WilsonOriginalTwoFlatRoseNominated (face)
open WilsonOriginalTwoFlatRosePhase (fields)

open WilsonOriginalTwoFlatRoseBook (group)
open WilsonThermometerAlignedCells (atOrigin)
open WilsonOriginalTwoFlatRoseNominated (face)

open WilsonOriginalTwoFlatRoseRelativePhase (nodes recenter translated)

open WilsonMovingForkOpticalBook (reporter)
open WilsonOriginalTwoFlatIRSocketHeardCell (row incumbent held)
open WilsonOriginalTwoFlatIRPoolOrigins (home)
open WilsonReceivedChronologicalFixedRoseVariation (cells)

theorem labelled {N per f:ℕ}(live:f ≤ N)(Y:(i:Fin 3)→(C).label (grade i).val)(turn:Fin 3→Motion)
    (p:WilsonCenteredPhysicalPanel.Sites R (f,per) 3)(s:Finset (Fin 3))
    (bank:(i:Fin 3)→(C).label (grade i).val)(printed:∀i,displayed R (grade i).val (Y i) (turn i)=bank i):
    row R (N:=N) Y turn p s=WilsonOriginalTwoFlatRoseSecant.field R bank
      (fun i=>((C).S.toDepth live per).embed (p i)) s:=by
  unfold WilsonOriginalTwoFlatIRSocketHeardCell.row WilsonMeasuredPublicEntranceCellWords.physical WilsonOriginalTwoFlatRoseSecant.field
  funext U
  apply Finset.prod_congr rfl
  intro i _
  rw [printed i]
  congr 1
  simp only [anchorAt,Mix.camp,dif_pos live]

def Chamber {u T h q:ℕ}{δ:ℝ}(books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z 6 T s.val)
    (x:∀i:Fin 3,RG17.Free C (grade i).val)(φ:Test 3)(r amount:ℝ):Prop :=
  ∀ρ:Fin 3→{s:ℝ //0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
  (∃i,(ρ i).val=r) → let f:=reporter F books ρ
  ∃uf:u ≤ f,∀N per:ℕ,∀_live:f<N,∀p:cells R φ r (f,per),
  ∀(Y:(i:Fin 3)→(C).label (grade i).val)(turn:Fin 3→Motion),
    (∀i,displayed R (grade i).val (Y i) (turn i) =
      (home F Jr Z (books (ρ i)) (grade i) (x i)).arm.source (N,per)) →
  ∀s:Finset (Fin 3),s.Nonempty → ∀K:ℕ,∀fk:f ≤ K,∀kn:K ≤ N,
    ‖incumbent R (N:=N) Y turn p.val s-held R kn (uf.trans fk) Y turn p.val s‖ ≤ amount*(wilson z r)^q

/-- The all-pooled finite Wilson law and the held filing of its same numerator are
tested on every cell of the physical signed profile before either regulator. -/
theorem original {J u:ℕ}(stop:Stop C 0 J u)(fac:Facilities C order S)(bliss:Bliss F l z H)
    (slow:WilsonWindowReportingPace.Slow R.kit)(lead:Leading F Jr)
    (paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d){T:ℕ}{δ:ℝ}(dp:0<δ)
    (books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z 6 T s.val)
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s))
    (x:∀i:Fin 3,RG17.Free C (grade i).val)(φ:Test 3)(h q:ℕ):
    ∃A:ℝ,0 ≤ A ∧ ∀ᶠr in trail,Chamber F Jr Z (u:=u) (h:=h) (q:=q) books x φ r A:=by
  classical
  obtain ⟨M,mp,η,ep,housed⟩:=WilsonCenteredReaderDomain.room φ
  have shape:∀x:Points 3,φ x≠0 →
      (∀i,‖x i‖ ≤ M) ∧ Pairwise fun i j=>η ≤ ‖x i-x j‖:=by
    intro x hit
    have housed₁:=housed 1 zero_lt_one x (subset_closure hit)
    exact ⟨fun i=>by simpa using housed₁.span i,fun i j ne=>by simpa using housed₁.spaced i j ne⟩
  obtain ⟨_,_,_,L⟩:=fac.costlier
  obtain ⟨fees,positive,purchased⟩:=WilsonMovingForkElectedPhase.filed F Jr Z L.toPackage stop fac bliss
    slow lead paid 6 T h grade x dp books window
  have program:=WilsonMovingForkElectedPhase.same F Jr Z 6 T h grade x books u fees positive
    (purchased h le_rfl (M+1) (η/2) (by linarith) (half_pos ep))
  let cash(s:SiteSet):ℝ:=(program q s.val s.property).choose
  have pos(s:SiteSet):0<cash s:=(program q s.val s.property).choose_spec.1
  have budgets:=Filter.eventually_all.mpr (fun s:SiteSet=>(program q s.val s.property).choose_spec.2)
  let all:SiteSet:=⟨univ,univ_nonempty⟩
  let sum:=∑s,cash s
  refine ⟨sum,sum_nonneg (fun s _=>(pos s).le),?_⟩
  have clk:=wilson_link F fac.simpleGate bliss.budgets bliss.keen bliss.lies
  have thresh:(0:ℝ)^2 < min 1 (η/4)/12:=by rw [zero_pow (by decide:2≠0)];exact div_pos (lt_min zero_lt_one (by positivity)) (by norm_num)
  have mesh:=WilsonOriginalTwoFlatPublicMixedMesh.original F fac.simpleGate bliss slow 6 T h grade books
  filter_upwards [budgets,clk.positive,(clk.conforms fac.simpleGate).eventually (ge_mem_nhds zero_lt_one),
    ((clk.conforms fac.simpleGate).pow 2).eventually (ge_mem_nhds thresh),mesh] with r table gp small thin widths
  intro ρ span near f
  have rp:0<r:=(table all).1
  have grow:r ≤ outer z h r:=by obtain ⟨i,eq⟩:=near;exact eq ▸ (span i).2
  have debt:(C).S.a f ≤ min 1 (η/4)/12*r:=(div_le_iff₀ rp).mp ((widths ρ span near).1.trans thin)
  have first:=mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) (η/4)) rp.le
  have second:=mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) (η/4)) rp.le
  have small₁:4*(3:ℝ)*(C).S.a f ≤ r:=by linarith only [debt,first]
  have small₂:4*(3:ℝ)*(C).S.a f ≤ η/4*r:=by linarith only [debt,second]
  obtain ⟨uf,_⟩:=(table all).2.2 ρ span near
  refine ⟨uf,?_⟩
  intro N per live p Y turn exactly s ne K fk kn
  obtain ⟨site,registered,licence⟩:=WilsonMeasuredPublicEntranceProfileSites.lifted R φ (per:=per) rp shape small₁ small₂
  let o:=site p.val
  obtain ⟨inside,apart⟩:=licence p.val (WilsonReceivedChronologicalFixedRoseVariation.charged R φ r (f,per) p)
  let mode:SiteSet:=⟨s,ne⟩
  obtain ⟨_,get⟩:=(table mode).2.2 ρ span near
  have house(j:↥s):‖(C).S.gridPoint f (o j)‖ ≤ (M+1)*outer z h r:=
    (inside j).trans (mul_le_mul_of_nonneg_left grow (by linarith))
  let v(i:Fin 3):=homogeneous F Jr Z (ρ i).val (grade i).val (x i)
  let bank(i:Fin 3):=((books (ρ i)).rows (grade i)).arm false (v i) |>.source (N,per)
  have labels(i:Fin 3):displayed R (grade i).val (Y i) (turn i)=bank i:=(exactly i).trans
    (congrArg (fun arm=>arm.source (N,per)) (WilsonMovingForkSlotDate.source F (books (ρ i)) (grade i) (v i)).2)
  let pins(i:Fin 3):=((C).S.toDepth live.le per).embed (snap C f per o i)
  let entire:=WilsonOriginalTwoFlatRoseSecant.field R bank pins s
  have receipt:=get N per live (fun i=>o i) house (fun i j ij=>apart (fun same=>ij (Subtype.ext same))) (fun _=>false)
  have eqn:word R (fun i:↥s=>(grade i).val) f N per live.le (fun i=>o i) (fun i=>bank i)=entire:=by
    funext U
    exact Finset.prod_coe_sort s (fun i=>(C).O N per (bank i) (pins i) U)
  have price:‖gap R N per u (uf.trans live.le) entire‖ ≤ sum*(wilson z r)^q:=by
    rw [←eqn]
    exact receipt.1.trans (mul_le_mul_of_nonneg_right (single_le_sum (fun s _=>(pos s).le) (mem_univ mode)) (pow_nonneg gp.le _))
  have row_eq:row R (N:=N) Y turn p.val s=entire:=by
    change row R (N:=N) Y turn p.val s=WilsonOriginalTwoFlatRoseSecant.field R bank
      (fun i=>((C).S.toDepth live.le per).embed ((snap C f per o) i)) s
    rw [show snap C f per o=p.val from registered p.val]
    exact labelled live.le Y turn p.val s bank labels
  have integrable:=WilsonOriginalTwoFlatRoseSecant.regular R bank pins s
  unfold WilsonOriginalTwoFlatIRSocketHeardCell.incumbent WilsonOriginalTwoFlatIRSocketHeardCell.held
  rw [row_eq]
  simpa only [WilsonOriginalTwoFlatGridScaling.gap,WilsonThermometerUnitFilingCoarse.reading,
    WilsonThermometerUnitFilingCoarse.cutoff R kn (uf.trans fk) entire integrable,gust_base] using price

end YM.Integration.WilsonOriginalTwoFlatIRPoolChamber
end

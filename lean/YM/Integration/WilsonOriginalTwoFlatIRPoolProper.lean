import YM.Integration.WilsonOriginalTwoFlatIRPoolChamber
import YM.Integration.WilsonOriginalTwoFlatIRPoolMesh
import YM.Integration.WilsonOriginalTwoFlatIRPoolPublicCost
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolProper
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

open WilsonOriginalTwoFlatRoseFaceLimits (names loc result continuous_loc separate)
open scoped ContDiff
local notation "Faces" => Finset (Fin 3)

def Capped {T h:ℕ}{δ:ℝ}(books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z 6 T s.val)
    (x:∀i:Fin 3,RG17.Free C (grade i).val)(φ:Test 3)(r bound:ℝ):Prop :=
  ∀ρ:Fin 3→{s:ℝ //0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
  (∃i,(ρ i).val=r) → let f:=reporter F books ρ
  ∀ᶠp:ℕ×ℕ in (l:Filter _),∀_live:f ≤ p.1,∀cell:cells R φ r (f,p.2),
  ∀(Y:(i:Fin 3)→(C).label (grade i).val)(turn:Fin 3→Motion),
    (∀i,displayed R (grade i).val (Y i) (turn i) =
      (home F Jr Z (books (ρ i)) (grade i) (x i)).arm.source p) →
  ∀s:Faces,‖incumbent R (N:=p.1) Y turn cell.val s‖ ≤ bound

/-- The genuine physical extraction controls all original cofactors on the
chosen pooled sources, also when different grades are reported at different homes. -/
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)(hl:(l:Filter _) ≤ order.fuse)
    {T:ℕ}{δ:ℝ}(books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z 6 T s.val)
    (x:∀i:Fin 3,RG17.Free C (grade i).val)(φ:Test 3)(h:ℕ):
    ∃E:ℕ,∃B:ℝ,1 ≤ B ∧ ∀ᶠr in trail,Capped F Jr Z (h:=h) books x φ r (B*((wilson z r)⁻¹)^E):=by
  classical
  obtain ⟨τ,positive,confined⟩:=φ.hasCompactSupport.exists_cthickening_subset_open (conf_open _) φ.tsupport_subset
  let W:=Metric.cthickening τ (tsupport (φ:Points 3→ℂ))
  have compact:IsCompact W:=φ.hasCompactSupport.cthickening
  let n(s:Faces):=Fintype.card ↥s
  let d(s:Faces)(i:Fin (n s)):ℕ:=(grade (names s i).val).val
  let near(s:Faces):=loc s '' W
  have comp(s:Faces):IsCompact (near s):=compact.image (continuous_loc s)
  have sep(s:Faces):near s ⊆ conf (n s):=by rintro _ ⟨y,hy,rfl⟩;exact separate s (confined hy)
  choose C₀ nc E rate using fun s:Faces=>WilsonOriginalTwoFlatIRPoolPublicCost.original F Jr Z simple bliss lead paid
    (d s) h (comp s) (sep s)
  let e:=∑s:Faces,E s
  let fee(s:Faces):ℝ:=C₀ s*(∏i:Fin (n s),‖x (names s i).val‖)
  have nn(s:Faces):0 ≤ fee s:=mul_nonneg (nc s) (Finset.prod_nonneg fun i _=>norm_nonneg _)
  let B:=1+∑s,fee s
  have bp:1 ≤ B:=by dsimp [B];linarith [sum_nonneg (fun s (_:s∈(univ:Finset Faces))=>nn s)]
  refine ⟨e,B,bp,?_⟩
  have hg:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have unit:(0:ℝ)^2<τ/12:=by simpa using div_pos positive (by norm_num:(0:ℝ)<12)
  have bills:=Filter.eventually_all.mpr rate
  filter_upwards [bills,WilsonOriginalTwoFlatPublicMixedMesh.original F simple bliss slow 6 T h grade books,
    hg.positive,(hg.conforms simple).eventually (ge_mem_nhds zero_lt_one),
    ((hg.conforms simple).pow 2).eventually (ge_mem_nhds unit),self_mem_nhdsWithin] with r localCap widths gp small thin (rp:0<r)
  intro ρ span anchor f
  have width:4*(3:ℝ)*(C).S.a f ≤ τ*r:=by
    have debt:(C).S.a f ≤ τ/12*r:=(div_le_iff₀ rp).mp ((widths ρ span anchor).1.trans thin)
    linarith only [debt]
  let v(i:Fin 3):=homogeneous F Jr Z (ρ i).val (grade i).val (x i)
  let arms(i:Fin 3):=(home F Jr Z (books (ρ i)) (grade i) (x i)).arm
  filter_upwards [WilsonOriginalTwoFlatIRPoolMesh.limit R F simple hl r rp v arms compact confined
    (show (0:ℝ)<1 from zero_lt_one)] with p law
  intro live cell Y turn named s
  obtain ⟨y,hy,placement⟩:=WilsonOriginalTwoFlatIRPoolMesh.pointsAt R φ rp live width cell
  have received:incumbent R (N:=p.1) Y turn cell.val s=
      WilsonOriginalTwoFlatIRPoolMesh.raw R r p (fun i=>(arms i).source p) y s:=by
    unfold WilsonOriginalTwoFlatIRSocketHeardCell.incumbent WilsonOriginalTwoFlatIRPoolMesh.raw
    rw [WilsonOriginalTwoFlatIRPoolChamber.labelled live Y turn cell.val s _ named]
    congr 1
    congr 1
    funext i
    exact (placement i).symm
  let g:=wilson z r
  have one:1 ≤ g⁻¹:=(one_le_inv₀ gp).mpr small
  have weight:0 ≤ (g⁻¹)^e:=pow_nonneg (inv_pos.mpr gp).le _
  have restr:∀i:Fin (n s),r ≤ (ρ (names s i).val).val ∧ (ρ (names s i).val).val ≤ r/g^h:=by
    intro i
    simpa only [g,outer,inv_pow,div_eq_mul_inv] using span (names s i).val
  have fitted:‖result R r v y s‖*(g^E s) ≤ fee s:=
    localCap s (fun i=>(ρ (names s i).val).val) restr (loc s y) ⟨y,hy,rfl⟩ (fun i=>x (names s i).val)
  have paid:‖result R r v y s‖ ≤ fee s*(g⁻¹)^E s:=by
    rw [inv_pow,←div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos gp _)).mpr fitted
  have direct:=law s y hy
  rw [dist_eq_norm] at direct
  have low:E s ≤ e:=single_le_sum (fun _ _=>Nat.zero_le _) (mem_univ s)
  rw [received]
  calc
    _ ≤ 1+fee s*(g⁻¹)^E s:=(norm_le_norm_sub_add _ _).trans (add_le_add direct.le paid)
    _ ≤ (g⁻¹)^e+(∑j,fee j)*(g⁻¹)^e:=add_le_add (one_le_pow₀ one)
      (mul_le_mul (single_le_sum (fun j _=>nn j) (mem_univ s)) (pow_le_pow_right₀ one low)
        (pow_nonneg (inv_pos.mpr gp).le _) (sum_nonneg (fun j _=>nn j)))
    _ = B*(g⁻¹)^e:=by dsimp [B];ring

end YM.Integration.WilsonOriginalTwoFlatIRPoolProper
end

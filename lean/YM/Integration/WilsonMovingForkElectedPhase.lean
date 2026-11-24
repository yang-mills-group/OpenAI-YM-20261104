import YM.Integration.WilsonMovingForkAbsolutePhase

/-! The same original stock and the identical, preassigned stop for all apertures. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkElectedPhase
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
variable (Jr:ℝ→tower S)(Z:WilsonPrescription G)

open WilsonMovingForkAbsolutePhase (Sampled)

theorem filed {lo wid teach}(L:Package C wid lo teach){J u:ℕ}(stop:Stop C 0 J u) (fac:Facilities C order S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    (D T h:ℕ)(d:I→Fin (D+1))(x:∀i,RG17.Free C (d i).val)
    {δ:ℝ}(dp:0<δ)
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s)) :
    ∃K:I→ℝ,(∀i,1≤K i) ∧ ∀b:ℕ,h ≤ b → ∀M η:ℝ,1≤M → 0<η →
      Sampled F Jr Z fac.simpleGate D T h b d x M η δ books u K:=by
  obtain ⟨K,e,onek,rate⟩:=WilsonMovingForkHomeIncome.original F Jr Z fac.simpleGate bliss slow lead paid D T h d x books window
  refine ⟨K,onek,?_⟩
  intro b hb M η one ep grade E nonempty
  haveI : Nonempty E:=nonempty.to_subtype
  let sum:=∑i:E,e i
  let constant:=∏i:E,K i
  have cp:0<constant:=Finset.prod_pos fun i _=>zero_lt_one.trans_le (onek i)
  have full:=WilsonOriginalTwoFlatPublicMixedRadius.selected F L (fun i:E=>i.val)
    fac.simpleGate bliss slow stop (fun i=>(d i).val) D T (2*b) (sum+2*grade) (fun i=>Nat.le_of_lt_succ (d i).isLt) one ep
  have when:=longer F fac.simpleGate bliss b
  filter_upwards [when.eventually full,WilsonOriginalTwoFlatPublicMixedSpan.original F fac.simpleGate bliss slow D T h d books,
    when.eventually ((gt_mem_nhds dp).filter_mono nhdsWithin_le_nhds),
    rate,
    WilsonOriginalTwoFlatPublicOuter.original F fac.simpleGate bliss grade,
    WilsonOriginalTwoFlatPublicOuter.original F fac.simpleGate bliss b,
    ((wilson_link F fac.simpleGate bliss.budgets bliss.keen bliss.lies).conforms fac.simpleGate).eventually (ge_mem_nhds zero_lt_one),
    (wilson_link F fac.simpleGate bliss.budgets bliss.keen bliss.lies).positive] with r all sizes below fares clock gauge low positive
  refine ⟨clock.1,below,?_⟩
  intro ρ span anchor m j
  let bk(i:I):=books (ρ i)
  have ms:=sizes ρ span anchor
  have aj:a j ≤ r:=ms.1
  have bigger:outer z h r ≤ outer z b r:=mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ ((one_le_inv₀ positive).mpr low) hb) clock.1.le
  obtain ⟨uj,read⟩:=all r (fun i=>(ρ i).val) clock.1 (fun i=>⟨(span i).1,(span i).2.trans bigger⟩) anchor (fun i=>(bk i).rows (d i))
    (fun i=>(bk i).checked) (fun i=>(bk i).active) (gauge.2.2 j aj)
  refine ⟨uj,?_⟩
  intro N p top o inside apart weak
  let value(i:E):=homogeneous F Jr Z (ρ i).val (d i).val (x i)
  have first:=read N p top o inside apart weak value
  have fare(i:E):charge F ((bk i).rows (d i)) j (weak i) (value i) ≤ K i*(β j)^(e i):=by
    let branch(k:I):=if hk:k∈E then weak ⟨k,hk⟩ else false
    have cost:=(fares ρ span anchor branch i).2.2
    simpa only [branch,dif_pos i.property,bk,value] using cost
  have beta:0<β j:=zero_lt_one.trans ((R.family.path.levels).fits.delayed j)
  have product:(∏i:E,charge F ((bk i).rows (d i)) j (weak i) (value i)) ≤ constant*(β j)^sum:=by
    calc
      _  ≤  ∏i:E,K i*(β j)^(e i):=Finset.prod_le_prod (fun i _=>zero_le_one.trans (le_max_left _ _)) (fun i _=>fare i)
      _ = _:=by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  have run:((wilson z r)⁻¹)^grade  ≤  (β j)^(2*grade):=by
    apply (mul_le_mul_iff_of_pos_left clock.1).mp
    simpa only [outer,mul_comm ((β j)^(2*grade)) r] using clock.2.2 j aj
  have convert:((β j)^(2*grade))⁻¹ ≤ (wilson z r)^grade:=by
    simpa only [←inv_pow,inv_inv] using inv_anti₀ (pow_pos (inv_pos.mpr positive) grade) run
  have invoice:(∏i:E,charge F ((bk i).rows (d i)) j (weak i) (value i))*((β j)^(sum+2*grade))⁻¹  ≤  constant*(wilson z r)^grade:=by
    calc
      _  ≤  (constant*(β j)^sum)*((β j)^(sum+2*grade))⁻¹:=mul_le_mul_of_nonneg_right product (inv_nonneg.mpr (pow_nonneg beta.le _))
      _ = constant*((β j)^(2*grade))⁻¹:=by rw [pow_add,mul_inv_rev];field_simp [ne_of_gt beta]
      _  ≤  _:=mul_le_mul_of_nonneg_left convert cp.le
  have phase:=first.trans invoice
  refine ⟨phase,WilsonOriginalTwoFlatPublicHeard.earned R fac.simpleGate (uj.trans top.le) _ ?_ phase⟩
  exact continuous_finsetProd _ fun i _=>(C).continuousO _ _ _ _ _


theorem fixed (fac:Facilities C order S)(floor:ℕ):
    ∃J u:ℕ,floor≤J ∧ J≤u ∧ Stop C 0 J u:=by
  obtain ⟨_,_,_,L⟩:=fac.costlier
  obtain ⟨J,all,upper⟩:=((RG16.Literal.forStop C fac.simpleGate L.toPackage 0).and (eventually_ge_atTop floor)).exists
  obtain ⟨u,span⟩:=all
  let stop:=span 0 le_rfl
  exact ⟨J,u,upper,stop.live.1,stop⟩

omit [DecidableEq I] [Nonempty I] in
theorem same {simple:G.Simple}(D T h:ℕ)(d:I→Fin (D+1))(x:∀i,RG17.Free C (d i).val)
    {δ M η:ℝ}(books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (u:ℕ)(k:I→ℝ)(one:∀i,1≤k i)
    (sale:Sampled F Jr Z simple D T h h d x M η δ books u k):
    WilsonOriginalTwoFlatPublicSameField.Sampled F Jr Z simple D T h d x M η δ books u:=by
  intro p E multi
  refine ⟨∏i:E,k i,Finset.prod_pos (fun i _=>zero_lt_one.trans_le (one i)),sale p E multi⟩

end YM.Integration.WilsonMovingForkElectedPhase
end

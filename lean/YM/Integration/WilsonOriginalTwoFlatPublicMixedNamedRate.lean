import YM.Integration.WilsonOriginalTwoFlatPublicMixedSpan
import YM.Integration.WilsonOriginalTwoFlatPublicNamedRate
/-! Common moving-detector price for the true named directions at their
own scales. Every face retains the book of the complete original roster. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicMixedNamedRate
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


open WilsonOriginalTwoFlatPublicNamedFare (chosen)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
variable (Jr:ℝ→tower S)(Z:WilsonPrescription G)

theorem original (fac:Facilities C order S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    (D h:ℕ)(d:I→Fin (D+1))(y:∀i,(Spin.comparator R.family.book).Field (d i).val)(x:∀i,RG17.Free C (d i).val)
    {M η:ℝ}(one:1  ≤  M)(ep:0<η):
    ∃J u T:ℕ,∃δ:ℝ,∃books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val,
      0<δ ∧ Stop C 0 J u ∧ ∀p₀:ℕ,∀E:Finset I,E.Nonempty → ∃C₀:ℝ,0<C₀ ∧
      ∀ᶠ r in trail,0<r ∧ outer z h r<δ ∧
      ∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let j:=berth R 5 m
      ∃uj:u ≤ j,∀N p:ℕ,∀top:j<N,∀o:E → Cover,(∀i,‖(C).S.gridPoint j (o i)‖ ≤ M*outer z h r) →
      (Pairwise fun i i'=>η*r ≤ ‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o i')‖) →
      ∀weak:E→Bool,
      let v(i:E):=chosen F Jr Z (ρ i).val ((books (ρ i)).V (d i)) (weak i) (y i) (x i)
      let Y:=word R (fun i:E=>(d i).val) j N p top.le o (fun i=>((books (ρ i)).rows (d i)).arm (weak i) (v i) |>.source (N,p))
      let amount:=C₀*(wilson z r)^p₀
      ‖gap R N p u (uj.trans top.le) Y‖ ≤ amount ∧ Heard R fac.simpleGate N p u Y amount:=by
  obtain ⟨_,_,_,L⟩:=fac.costlier
  obtain ⟨J,u,all⟩:=(RG16.Literal.forStop C fac.simpleGate L.toPackage 0).exists
  let stop:=all 0 le_rfl
  obtain ⟨T,δ,dp,⟨books⟩⟩:=WilsonOriginalTwoFlatPublicBooks.original F fac.simpleGate bliss D
  refine ⟨J,u,T,δ,books,dp,stop,?_⟩
  intro grade E nonempty
  haveI : Nonempty E:=nonempty.to_subtype
  choose K e onek rate using fun i:E=>WilsonOriginalTwoFlatPublicNamedFare.original F Jr Z fac.simpleGate
    bliss lead paid (d i).val T (y i) (x i)
  let H₀:=2*T+11+2*h
  let expo(i:E):=(2*T+3+H₀)*((d i).val+1)+e i
  let sum:=∑i:E,expo i
  let constant:=∏i:E,K i
  have cp:0<constant:=Finset.prod_pos fun i _=>zero_lt_one.trans_le (onek i)
  refine ⟨constant,cp,?_⟩
  have full:=WilsonOriginalTwoFlatPublicMixedRadius.selected F L.toPackage (fun i:E=>i.val)
    fac.simpleGate bliss slow stop (fun i=>(d i).val) D T (2*h) (sum+2*grade) (fun i=>Nat.le_of_lt_succ (d i).isLt) one ep
  have duties:=eventually_all.mpr rate
  obtain ⟨δ',small,applies⟩:=Metric.mem_nhdsWithin_iff.mp duties
  have when:=longer F fac.simpleGate bliss h
  filter_upwards [when.eventually full,WilsonOriginalTwoFlatPublicMixedSpan.original F fac.simpleGate bliss slow D T h d books,
    when.eventually ((gt_mem_nhds dp).filter_mono nhdsWithin_le_nhds),
    when.eventually ((gt_mem_nhds small).filter_mono nhdsWithin_le_nhds),
    WilsonOriginalTwoFlatPublicOuter.original F fac.simpleGate bliss grade,
    WilsonOriginalTwoFlatPublicOuter.original F fac.simpleGate bliss h,
    (wilson_link F fac.simpleGate bliss.budgets bliss.keen bliss.lies).positive] with r all sizes below fit clock gauge positive
  refine ⟨clock.1,below,?_⟩
  intro ρ span anchor m j
  let b(i:I):=books (ρ i)
  have ms:=sizes ρ span anchor
  have aj:a j ≤ r:=ms.1
  obtain ⟨uj,read⟩:=all r (fun i=>(ρ i).val) clock.1 span anchor (fun i=>(b i).rows (d i))
    (fun i=>(b i).checked) (fun i=>(b i).active) (gauge.2.2 j aj)
  refine ⟨uj,?_⟩
  intro N p top o inside apart weak
  let value(i:E):=chosen F Jr Z (ρ i).val ((b i).V (d i)) (weak i) (y i) (x i)
  have first:=read N p top o inside apart weak value
  have fare(i:E):charge F ((b i).rows (d i)) j (weak i) (value i) ≤ K i*(β j)^(expo i):=by
    have close:(ρ i).val∈Metric.ball (0:ℝ) δ' ∩ Set.Ioi 0:=⟨by
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (ρ i).property.1]
      exact (span i).2.trans_lt fit,(ρ i).property.1⟩
    exact applies close i ((b i).rows (d i)) (b i).checked (b i).active j H₀ (ms.2 i).1 (ms.2 i).2 (weak i)
  have beta:0<β j:=zero_lt_one.trans ((R.family.path.levels).fits.delayed j)
  have product:(∏i:E,charge F ((b i).rows (d i)) j (weak i) (value i)) ≤ constant*(β j)^sum:=by
    calc
      _  ≤  ∏i:E,K i*(β j)^(expo i):=Finset.prod_le_prod (fun i _=>zero_le_one.trans (le_max_left _ _)) (fun i _=>fare i)
      _ = _:=by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  have run:((wilson z r)⁻¹)^grade  ≤  (β j)^(2*grade):=by
    apply (mul_le_mul_iff_of_pos_left clock.1).mp
    simpa only [outer,mul_comm ((β j)^(2*grade)) r] using clock.2.2 j aj
  have convert:((β j)^(2*grade))⁻¹ ≤ (wilson z r)^grade:=by
    simpa only [←inv_pow,inv_inv] using inv_anti₀ (pow_pos (inv_pos.mpr positive) grade) run
  have invoice:(∏i:E,charge F ((b i).rows (d i)) j (weak i) (value i))*((β j)^(sum+2*grade))⁻¹  ≤  constant*(wilson z r)^grade:=by
    calc
      _  ≤  (constant*(β j)^sum)*((β j)^(sum+2*grade))⁻¹:=mul_le_mul_of_nonneg_right product (inv_nonneg.mpr (pow_nonneg beta.le _))
      _ = constant*((β j)^(2*grade))⁻¹:=by rw [pow_add,mul_inv_rev];field_simp [ne_of_gt beta]
      _  ≤  _:=mul_le_mul_of_nonneg_left convert cp.le
  have phase:=first.trans invoice
  refine ⟨phase,WilsonOriginalTwoFlatPublicHeard.earned R fac.simpleGate (uj.trans top.le) _ ?_ phase⟩
  exact continuous_finsetProd _ fun i _=>(C).continuousO _ _ _ _ _

end YM.Integration.WilsonOriginalTwoFlatPublicMixedNamedRate


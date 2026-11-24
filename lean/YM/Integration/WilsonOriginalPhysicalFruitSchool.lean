import YM.Integration.WilsonOriginalPhysicalFruitPanel
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalFruitSchool
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


open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)

open WilsonReflectedMixedMasterRegistry (Delivery Course)
open WilsonReflectedMixedLocatedSchool (Paid)


open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace

open WilsonIndependentMatchedFiledIncome (plate)
open WilsonOriginalPhysicalFruitVerse (written)
open WilsonOriginalPhysicalFruitDose (amounts)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)

def Stamped (W:Initialize G)(D T h k e u t0:ℕ)(d:I→Fin (D+1))(ex:I→ℕ){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (read:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    (M:I→ℝ)(E:I→ℕ)(C₀:I→Bool→ℝ)(ρ:I→{s:ℝ // 0<s ∧ s<δ})
    (r η roof ceiling:ℝ)(f K power target:ℕ)
    (sale:WilsonReflectedMixedSharpPanel.Purchased F D T h t0 d ex books read M ceiling η power target ρ f K):Prop:=
  ∀N per(live:K ≤ N),
      let axes:=(sale.choose_spec N per live).choose_spec.choose
      ∀(i:I)(mode weak:Bool)(s:Signed)(chi:Bool)(o:Site ((C).side f per)),
      let leg:=(books (ρ i)).rows (d i)
      let j:=station F leg weak
      let Y:=(leg.arm weak (read i (ρ i) mode weak)).source (N,per)
      ∃arm:Arm R (d i).val N per f K,arm.Y=Y ∧ arm.w=(axes i weak).symm (fitted R (d i).val j N per Y) ∧
        arm.b=chi ∧ arm.s=s ∧ arm.o=o ∧
        ∀t:ℂ,
          ((C).labels.level (d i).val).coeffSize (amounts R (d i).val K N per r t (coords R arm)) ≤
            WilsonOriginalPhysicalFruitClock.salary R (d i).val (E i) t (M i) roof *
              ((wilson z r)⁻¹)^WilsonOriginalPhysicalFruitClock.power R (d i).val (E i)*(r/a K)^η ∧
          ∀(survey:Bool)(φ:ℂ →L[ℝ] ℝ),
          WilsonOriginalPhysicalFruitPanel.Line (R:=R) W (d i).val (D+1) (d i).isLt survey k e u
            (amounts R (d i).val K N per r t (coords R arm)) φ
            (((C₀ i survey*‖φ‖)*WilsonOriginalPhysicalFruitClock.salary R (d i).val (E i) t (M i) roof)*
            ((wilson z r)⁻¹)^WilsonOriginalPhysicalFruitClock.power R (d i).val (E i)*(r/a K)^η)

def Quota (W:Initialize G)(D T h t0 k e u:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (read:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val):Prop:=
∃M:I→ℝ,∃E:I→ℕ,∃C₀:I→Bool→ℝ,(∀i,1 ≤ M i) ∧ (∀i b,0 ≤ C₀ i b) ∧
    ∀(n:ℕ)(ζ:ℝ),0<ζ → ∀(ex:I→ℕ)(pwr target:ℕ),(∀i,ex i+1 ≤ 2*pwr) →
      let τ:=depth ((2*pwr+∑i,E i)+1) (width T h) D
      ∃roof:ℝ,1 ≤ roof ∧ ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
        (∃i,(ρ i).val=r) →
        let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
        let f:=berth R 5 m
        let K:=berth R τ f
        let ceiling:=max 1 (4*∑i,M i)
        let budget:=((∑i,E i)+WilsonAddressedMixedRawTrial.power T h τ D)
        ∃sale:WilsonReflectedMixedSharpPanel.Purchased F D T h t0 d ex books read M ceiling
          (WilsonReflectedMixedSharpPanel.reserve n ζ) budget target ρ f K,
          (∀mode:Bool,Paid F D T d books (fun i s=>read i s mode) M E ρ f) ∧
          Stamped F W D T h k e u t0 d ex books read M E C₀ ρ r
            (WilsonReflectedMixedSharpPanel.reserve n ζ) roof ceiling f K budget target sale

omit [DecidableEq I] in
/-- All paid fields and both original homes of each leg share the elected
axes. Original and independently supplied surveys use the same physical dose. -/
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (W:Initialize G){D T h t0 k e u:ℕ}{d:I→Fin (D+1)}(capacity:D ≤ k){δ:ℝ}
    {books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val}
    {read:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    (school:WilsonReflectedMixedSharpSchool.Attended F D T h t0 d books read):
    Quota F W D T h t0 k e u d books read:=by
  obtain ⟨M,E,one,attend⟩:=school
  choose C₀ cpos word using fun (i:I)(survey:Bool)=> WilsonOriginalPhysicalFruitVerse.named R W survey
    (d i).val (D+1) k e u (d i).isLt ((Nat.le_of_lt_succ (d i).isLt).trans capacity)
  refine ⟨M,E,C₀,one,cpos,?_⟩
  intro n ζ room ex pwr target enough τ
  have deep:2 ≤ τ:=by dsimp [τ,WilsonReflectedOpticalRate.depth]; omega
  obtain ⟨roof,roof1,arrives⟩:=WilsonAddressedMixedOpticalMesh.original F simple bliss slow D T h τ deep d books
  refine ⟨roof,roof1,?_⟩
  have ep:=WilsonReflectedMixedSharpPanel.margin n room
  filter_upwards [attend n ζ room ex pwr target enough,arrives,
    WilsonOriginalTwoFlatPublicMixedSpan.original F simple bliss slow D T h d books] with r front optical span
  intro ρ prices nearest m f K ceiling budget
  have clock:=optical ρ prices nearest
  obtain ⟨paid,sale⟩:=front ρ prices nearest
  have earlier:= (span ρ prices nearest).1
  obtain ⟨i,ei⟩:=nearest
  have rp:0<r:= ei ▸ (ρ i).property.1
  refine ⟨sale,paid,?_⟩
  intro N per live axes
  let first:=(sale.choose_spec N per live).choose
  have sold:=(sale.choose_spec N per live).choose_spec.choose_spec
  let born:=sold.1
  let cash:=sold.2.1
  intro b mode weak s chi o leg j Y
  obtain ⟨arm,armY,armw,armChi,arms,armo,_⟩:=(born b mode weak).2.2 s chi o
  refine ⟨arm,armY,armw,armChi,arms,armo,?_⟩
  intro t
  obtain ⟨nonneg,_,fare⟩:=paid mode b weak
  have price:=WilsonOriginalPhysicalFruitClock.original R simple (first b weak) sale.choose.le live ep.1.le
    (ep.2.1.trans (by norm_num)) (axes b weak) Y (cash b weak _) arm armw r (wilson z r)
    rp clock.1 earlier t (M b) roof (zero_le_one.trans (one b)) roof1 nonneg fare clock.2.2
  refine ⟨price,?_⟩
  intro survey φ
  obtain ⟨wf,pr⟩:=word b survey (amounts R (d b).val K N per r t (coords R arm)) φ
  refine ⟨wf,fun j n hj=>(pr j n hj).more ?_⟩
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left price (norm_nonneg φ)) (cpos b survey)).trans_eq (by ring)

omit [DecidableEq I] in
theorem elected (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(wide:∀i,1 ≤ ((P).budget i).supportExponent)
    (caps:∀i,((P).budget i).supportExponent ≤ 100)(quote:OPE.Therm.Poetry (P))
    (lead:Leading F Jr)(obedient:∀g:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) g)(W:Initialize G)(D:ℕ):
    ∃t≥D+3,∃T:ℕ,∃δ:ℝ,0<δ ∧ ∃books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val,
    (∀s,WilsonMovingForkWindowBooks.Priced F (books s)) ∧ ∀(h:ℕ)(d:I→Fin (D+1))
    (y:∀i,(Spin.comparator (C).book).Field (d i).val)(x:∀i,RG17.Free C (d i).val)
    (k e u:ℕ),D ≤ k → Quota F W D T h t k e u d books (WilsonReflectedMixedMasterSchool.field F Jr Z D T d y x books):=by
  obtain ⟨t,b,T,δ,p,books,owned,school⟩:=WilsonReflectedMixedSharpSchool.elected (I:=I) F Jr Z simple bliss slow
    shop wide caps quote lead obedient D
  exact ⟨t,b,T,δ,p,books,owned,fun h d y x _ _ _ cap=>original F simple bliss slow W cap (school h d y x)⟩

end YM.Integration.WilsonOriginalPhysicalFruitSchool
end

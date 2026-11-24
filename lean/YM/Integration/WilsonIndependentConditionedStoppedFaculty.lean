import YM.Integration.WilsonIndependentConditionedStoppedPorts
import YM.Integration.WilsonIndependentConditionedBankRulerFaculty
import YM.Integration.WilsonIndependentConditionedStoppedTill
import YM.Integration.WilsonIndependentConditionedBankRulerCourse

/-! One earned Wilson cutoff, original physical basis and conditioned all-face notebook for the four complex pairings. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedStoppedFaculty
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RG.Supply Next.Foundations WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.Mosaic PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentConditionedPairProbeSemester (Home)
open WilsonIndependentConditionedPairProbes (Prices)
open WilsonIndependentConditionedPairFiledSemester (Tested)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonIndependentMatchedNamedPair (sectionAt)
open scoped BigOperators Topology Classical
variable {G:Gauge}{e k u u₀:ℕ}
local notation "J" => Fin 2
local notation "C" => Credit.leanC

open WilsonIndependentConditionedBankCorner (Bill input)
open WilsonIndependentConditionedPairFour (Assigned)
open WilsonIndependentConditionedPairProbes (Prices charge)
open WilsonIndependentConditionedPairTrialCost (roof)
open WilsonIndependentFittedPivotCash (view)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentConditionedBankPublicGram (response)
open WilsonPositionProgramTrialHomeDose (publicDose)

open WilsonIndependentConditionedBankFour (Enrolled)
open WilsonIndependentConditionedBankMatrix (sample protocol)
open WilsonIndependentConditionedBankCash (amount reserve)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentConditionedBankPublicGram (residual)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonIndependentFittedMixedCash (embed)
open WilsonOlderFreshSoftCoverScalar (clock)

open WilsonIndependentConditionedBankFittedFees (age)
open WilsonIndependentConditionedBankShellPrice (wage)
open WilsonIndependentConditionedGramPrices (profile)
open WilsonPhysicalMarkedDefect.RawProduct (belt positive)
open WilsonSeparatedPrefixMovingCalendar (epoch)

open WilsonIndependentConditionedBankReport (salary panel debit)

open WilsonIndependentConditionedBankApplied (field gram)

open GapsContact Climb PhysicalNext Extraction Table Spec Trace.Pilot Trace.Physical
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonReflectedMixedLocatedSchool (Paid)
open WilsonIndependentConditionedGramSplitPooled (marked)
open WilsonIndependentConditionedGramRawHome (fixed)
open WilsonIndependentConditionedGramSplitAward (homeLow homeHigh)
variable {R₀:Run G}{o:Extraction.Order}{RTable:Table R₀.family.book}
    (F:Final R₀.family o RTable){l:Ultrafilter (ℕ×ℕ)}{ℋ:(Bel R₀.family.book).Hierarchy}
    {Z:Trace.Terrace.Arch R₀.family}{I:Type}[Fintype I]
local notation "Bf" => R₀.family.path.levels.clock.hatBeta

open WilsonIndependentConditionedBankSeats (Resident)
open WilsonIndependentConditionedBankRulerPorts (rehome)
open WilsonIndependentNotebookConstantSeat (seat)
open WilsonIndependentConditionedBankOpening (Earned)
open WilsonReflectedPublicStationFare (station fee)
open WilsonIndependentMatchedFiledIncome (plate)


open WilsonIndependentConditionedBankRulerHearing (degrees stamps wages)
open WilsonIndependentNotebookComplexCorners (assembled reader)
open WilsonIndependentNotebookComplexQuadrant (fuse)
open Extra.Histories


open WilsonIndependentConditionedBankRulerQuartet (due capAt)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open Pert.Asymptotics


open WilsonIndependentConditionedBankRulerReport (Wallet Settled)
open WilsonReflectedMixedObservedArms (Printed)
open WilsonIndependentConditionedBankFour (Enrolled)
open Extra.Histories.Motion
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open WilsonReflectedPublicStationFare (station fee)

open WilsonIndependentConditionedBankRulerCourse (Quoted)
open WilsonIndependentConditionedBankRulerQuartet (capAt)
open WilsonIndependentConditionedGramSpatialHost (date)
open WilsonIndependentConditionedGramSpatialCourse (Page)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open WilsonReflectedMixedSharpPanel (reserve)
open WilsonReflectedOpticalRate (depth)
open WilsonInvariantActionPosition (berth)
open WilsonIndependentConditionedStoppedPorts (Sold)
open WilsonIndependentConditionedBankRulerMounted (Posted)
open WilsonThermometerUnitFilingFourPoolClock (outer)
local notation "trail" => nhdsWithin (0:ℝ) (Set.Ioi 0)

variable {D T h t:ℕ}{δ:ℝ}
variable (d:I→Fin (D+1))(books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) ℋ Z D T s.val)
variable (read:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→RTable.Field (d i).val)

open WilsonIndependentConditionedBankRulerFaculty (Opening)

def Funded (simple:G.Simple)(target τ q power:ℕ)(ζ:ℝ)(choose:J→I)(dim:J→ℕ)(fit:∀s,degrees d choose s<dim s)
    (I₀:Initialize G)(survey plain:J→Bool→Bool):Prop:=
  let S:SectionData ((primes G).F (2*D)):=(primes G).T (2*D)
  let Q:=deck (G:=G) (degrees d choose) dim fit
  let b:=2*D+2
  ∃(u u₀:ℕ)(rails:Rails (2*D) (2*D) u q)(own:∀s,Rails (degrees d choose s) D u₀ q)
    (L M:Credit)(rate:J→J→Credit)(coins:Prices)
    (A:(s:J)→Bool×Bool→Alma (R₀.family.labels.level (degrees d choose s))→ℝ),
    (∀s c i,0≤A s c i) ∧ ∀ᶠj:ℕ in atTop,
    ∃(W:ChorusLine (hol G) S (Nat.lt_succ_self (2*D)) q C C C)
      (Y:Torch (hol G) S (Nat.lt_succ_self (2*D)) rails C C C)(port:(s:J)→Home R₀ (Q s) (own s) j),
    W.arch=Y.L ∧ Y.L.V.draws=R₀.family.path.levels ∧ Y.L.V.paid=R₀.metals.O ∧
    Y.L.V.y=zz R₀.family.path.levels ∧ Y.L.V.anchor=j ∧
    FramesR (hol G) Y.L.V C C Q C ∧ HorizonP (hol G) Y.L.V C C Q ∧
    (∀s t,WilsonIndependentConditionedGramCampus.Paid Y.L.V (Q s) (Q t) D (rate s t)) ∧
    ∀old spatial width:ℕ,∀constant:ℝ,∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},
      (∀i,r≤(ρ i).val ∧ (ρ i).val≤outer Z h r) → (∃i,(ρ i).val=r) →
      let m:=date R₀ simple r
      let f:=reporter F books ρ
      let K:=berth R₀ τ f
      j ≤ m ∧ Sold (u:=u) (b:=b) (V:=Y.L.V) (port:=port) (coins:=coins) F books ρ read choose dim fit own A I₀ survey plain
        old m f K target (reserve 2 ζ) q spatial width power constant r L M

theorem joined [Nonempty I](simple:G.Simple)(bliss:Bliss F l Z ℋ)(slow:WilsonWindowReportingPace.Slow R₀.kit)
    (v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R₀.kit)(effort:I→ℕ)(M:I→ℝ)(E:I→ℕ)(big:∀i,1≤M i)
    (τ q target P:ℕ)(ζ:ℝ)(pos:0<ζ)(quarter:ζ≤1/4)
    (quotes:∀i j:I,Quoted (E i+E j) (E i+E j+max (E i) (E j))
      (2*((d i).val+(d j).val)+1) (2*T+11+2*h) τ q P ζ)
    (days:Opening (h:=h) (t:=t) F d books read simple effort M E τ target ζ)
    (choose:J→I)(dim:J→ℕ)(fit:∀s,degrees d choose s<dim s)(I₀:Initialize G)(survey plain:J→Bool→Bool):
    Funded (h:=h) F d books read simple target τ q P ζ choose dim fit I₀ survey plain:=by
  classical
  obtain ⟨u,_,rails⟩:=rail_noun (2*D) (2*D) q le_rfl 0
  let b:=2*D+2
  let u₀:=u+b+D+(D+1)+(D+1)*(D+q)+D*D
  have grade (s:J):degrees d choose s≤D:=Nat.lt_succ_iff.mp (d (choose s)).isLt
  have own (s:J):Rails (degrees d choose s) D u₀ q:=by
    have low:=grade s
    refine ⟨low,?_,?_,?_⟩
    · dsimp only [u₀];omega
    · have paid:(degrees d choose s+1)*(D+q)≤(D+1)*(D+q):=Nat.mul_le_mul_right (D+q) (Nat.succ_le_succ low)
      dsimp only [u₀];omega
    · have paid:=Nat.mul_le_mul low low
      dsimp only [u₀];omega
  have spare:u+b≤u₀:=by dsimp [u₀];omega
  have deep:2*D≤b:=by dsimp [b];omega
  have span:((∑s,degrees d choose s:ℕ):ℝ)+ζ<b:=by
    rw [Fin.sum_univ_two]
    have paid:=Nat.add_le_add (grade 0) (grade 1)
    have paid':((degrees d choose 0+degrees d choose 1:ℕ):ℝ)≤((D+D:ℕ):ℝ):=by exact_mod_cast paid
    dsimp [b];push_cast at *;linarith
  let Q:=deck (G:=G) (degrees d choose) dim fit
  obtain ⟨C₁,C₂,L,M₀,rate,coins,A,nn,opened⟩:=WilsonIndependentConditionedBankRulerSchool.original
    R₀ simple v funded (Nat.lt_succ_self (2*D)) rails (degrees d choose) dim fit own b spare deep I₀ (fun _=>Bool) survey plain
  refine ⟨u,u₀,rails,own,L,M₀,rate,coins,A,nn,?_⟩
  filter_upwards [opened] with j atDate
  obtain ⟨W,Y,port,file,trace,money,shape,anchor,frames,room,grams,source⟩:=atDate
  refine ⟨W,Y,port,file,trace,money,shape,anchor,frames,room,grams,?_⟩
  intro old spatial width constant
  let cap:=capAt R₀ d choose M A q
  have nnCap (p:J→Bool×Bool)(s:J):0≤cap p s:=by
    exact mul_nonneg (mul_nonneg (le_trans zero_le_one (big _))
      (WilsonIndependentConditionedGramRawHome.fixed_nonnegative R₀ _))
      (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _=>nn s (p s) _))
  have receipt:=WilsonIndependentConditionedStoppedTill.original (k:=D) (e:=q) F simple bliss slow d h books cap
    nnCap Q C₁ C₂ (rate 0 1) L M₀ coins (fun s=>E (choose s)) old u b τ q spatial width P ζ constant pos
    (quotes (choose 0) (choose 1)).1 (quotes (choose 0) (choose 1)).2
  filter_upwards [days j,receipt] with r now toll
  intro ρ home witness
  obtain ⟨before,page,weak,paid,bought⟩:=now ρ home witness
  refine ⟨before,?_⟩
  have sharp:=WilsonReflectedMixedSharpPanel.margin 2 pos
  apply WilsonIndependentConditionedStoppedPorts.original F books ρ read choose dim fit own A
    I₀ survey plain old effort M bought E paid C₁ C₂ (rate 0 1) L M₀ nn page.before shape q le_rfl weak
    ζ pos.le quarter sharp.1.le sharp.2.2 span spatial width P constant r (toll ρ home witness)
  intro N per up live arms host opened older
  exact (source host _ _ _ N per target opened older page.before up live (reserve 2 ζ) sharp.1.le arms).2

end YM.Integration.WilsonIndependentConditionedStoppedFaculty

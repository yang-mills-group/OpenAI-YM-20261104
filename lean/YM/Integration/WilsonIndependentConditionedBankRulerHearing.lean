import YM.Integration.WilsonIndependentConditionedBankRulerSchool
import YM.Integration.WilsonIndependentConditionedGramSplitReceiving
import YM.Integration.WilsonIndependentConditionedBankOpening

/-! The signed true two-colour hearing on its optical fine source and independently assigned older measuring ruler. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankRulerHearing
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


abbrev degrees {ι:Type*}{n:ℕ}(d:ι→Fin (n+1))(choose:J→ι)(s:J):ℕ:=(d (choose s)).val

abbrev stamps {R:Run G}{h:J→ℕ}{f K N per target:ℕ}{up:f ≤ K}{live:K ≤ N}{η:ℝ}
    (r:(s:J)→Bool→Resident R (h s) f K N per target up live η)
    (m:ℕ)(I₀:XSpace.Initialize G)(survey plain:J→Bool→Bool)(dim:J→ℕ)(fit:∀s,h s<dim s)(s:J)(i:Bool×Bool):=
  Shrine (plate (sectionAt R I₀ (survey s i.1) (h s)) (fit s)) (rehome (r s i.1) m (plain s i.1) i.2)

abbrev wages {R:Run G}{h:J→ℕ}{f K N per target:ℕ}{up:f ≤ K}{live:K ≤ N}{η:ℝ}
    (e:ℕ)(r:(s:J)→Bool→Resident R (h s) f K N per target up live η)
    (m:ℕ)(plain:J→Bool→Bool)(A:(s:J)→Bool×Bool→Alma (R.family.labels.level (h s))→ℝ)(s:J)(i:Bool×Bool):ℝ:=
  WilsonIndependentMatchedFiledIncome.charge e (rehome (r s i.1) m (plain s i.1) i.2) (A s i)

variable {D T:ℕ}{d:I→Fin (D+1)}{limit:ℝ}
variable (books:(s:{s:ℝ // 0<s ∧ s<limit})→Book F (l:=l) ℋ Z D T s.val)(ρ:I→{s:ℝ // 0<s ∧ s<limit})
variable (phys:(i:I)→{s:ℝ // 0<s ∧ s<limit}→Bool→RTable.Field (d i).val)
variable (M:I→ℝ)(E:I→ℕ)(choose:J→I)
variable (dim:J→ℕ)(fit:∀s,(degrees d choose s)<dim s)
local notation "𝒱" => Bool×Bool
variable (own:∀s,Rails (degrees d choose s) k u₀ e)
variable {V:Realm G (e+1) C}{coins:Prices}{j:ℕ}{port:∀s,Home R₀ ((deck (G:=G) (degrees d choose) dim fit) s) (own s) j}
variable {host m b K N per target:ℕ}{up:(reporter F books ρ) ≤ K}{top:K ≤ N}{η:ℝ}
variable (r:(s:J)→Bool→Resident R₀ (degrees d choose s) (reporter F books ρ) K N per target up top η)
variable (precise:(s:J)→𝒱→Alma (R₀.family.labels.level (degrees d choose s))→ℝ)
variable (I₀:XSpace.Initialize G)(survey plain:J→Bool→Bool)
variable (Y:Assigned R₀ (deck (G:=G) (degrees d choose) dim fit) own V coins j port (fun _=>𝒱)
  (stamps r m I₀ survey plain dim fit) (wages e r m plain precise) u b host m K N)

theorem original (C₁ C₂:J→Credit)(rate L₀ M₀:Credit)(enrolled:Earned Y C₁ C₂ rate L₀ M₀)
    (sale:Paid F D T d books phys M E ρ (reporter F books ρ))(nn:∀s i v,0 ≤ precise s i v)
    (α:J→Bool→ℂ)(doseP:∀s b,‖α s b‖ ≤ 1)
    (named:∀s b,let p:=choose s;let U:=(books (ρ p)).rows (d p)
      (r s b).station=station F U b ∧ (r s b).salary=fee F U b (phys p (ρ p) b) ∧ (r s b).phase=α s b)
    (opened:j ≤ host)(older:host ≤ m)(home:m ≤ (reporter F books ρ))(axes:V.y=zz R₀.family.path.levels)
    (q:ℕ)(order:q ≤ e)(g:ℝ)(weak:|g| ≤ 1)(pick:J→𝒱)(ζ:ℝ)(B:J→ℝ)(t z:ℝ)
    (pos:0 ≤ ζ)(quarter:ζ ≤ 1/4)(et:0 ≤ η)(room:2*η ≤ ζ/4)
    (span:((∑s,(degrees d choose s):ℕ):ℝ)+ζ<b)(apart:0<t)(φ:(s:J)→Rarity ((deck (G:=G) (degrees d choose) dim fit) s).D)(y:ℝ)(o:CellR)
    (cleared:∀s s',s≠s'→ClearDay (φ s) (φ s') t)(radii:∀s,radiusH (φ s) 1 y ≤ z)
    (amp:∀s,Amplitude (φ s) (B s)):
    let δ:=paceT R₀.family.path.levels.S m K
    let X:=fun s=>Y.cuts s (pick s)
    let inv:=(1+|L₀.buy (zz R₀.family.path.levels m)|)*(1+|M₀.buy (zz R₀.family.path.levels m)|)
    let c:=fun s=>((e+1:ℕ):ℝ)*∑i:(R₀.family.labels.level (degrees d choose s)).Index,precise s (pick s) (seat _ i)
    let cap:=fun s=>M (choose s)*fixed R₀ (degrees d choose s)*c s
    let S:=roof (wage (k:=k) (e:=e) R₀ (deck (G:=G) (degrees d choose) dim fit) coins u b host m K ζ (fun _=>1) (fun _=>1) B t z)
    let P:=fun s=>|field R₀ ((deck (G:=G) (degrees d choose) dim fit) s) (C₁ s) (C₂ s) host m K q 1 1|
    let Gcost:=|gram (e:=e) R₀ (deck (G:=G) (degrees d choose) dim fit) rate host K q φ B y|
    let e₀:=E (choose 0); let e₁:=E (choose 1);let n:=(degrees d choose 0)+(degrees d choose 1)
    let cash:=homeLow q S inv cap*(Bf (reporter F books ρ))^(e₀+e₁)*δ^(3*ζ/4)+
      (homeHigh q S P cap Gcost*(Bf (reporter F books ρ))^(e₀+e₁+max e₀ e₁))*(|g|^(q+1)*(δ^(2*n+1))⁻¹)
    let v:=fun s=>sample V ((deck (G:=G) (degrees d choose) dim fit) s) N m host q g (publicDose ((deck (G:=G) (degrees d choose) dim fit) s) (X s) 1)
    let row:=fun s=>input (deck (G:=G) (degrees d choose) dim fit) own C C C C X s 1 (φ s) y o
    ∀ω,‖view (X 0) host q g (row 0) (row 1) ω-
      protocol V ((deck (G:=G) (degrees d choose) dim fit) 0) ((deck (G:=G) (degrees d choose) dim fit) 1) k host m K N (φ 0) (φ 1) y o 0 ω q g (v 0) (v 1)‖ ≤
        cash*((1+∑i,‖v 0 i‖)*(1+∑i,‖v 1 i‖)):=by
  classical
  intro δ X inv c cap S P Gcost e₀ e₁ n cash v row ω
  have colour (s:J):0 ≤ c s:=mul_nonneg (by positivity) (Finset.sum_nonneg fun i _=>nn s (pick s) _)
  have invpos:0 ≤ inv:=by dsimp only [inv]; positivity
  have source (s:J):|(1:ℝ)| * (wages e r m plain precise) s (pick s) ≤
      (marked F books ρ phys (pick s).1 η (α s (pick s).1) (choose s)*c s)*δ^(-η):=by
    rw [abs_one,one_mul]
    have info:=named s (pick s).1
    apply WilsonIndependentConditionedBankRulerPorts.received (r s (pick s).1) home et
      (plain s (pick s).1) (pick s).2 e (precise s (pick s)) (nn s (pick s))
    exact WilsonIndependentConditionedBankPhysicalPorts.received F d books ρ phys (choose s) (pick s).1
      (pick s).2 η (α s (pick s).1) (r s (pick s).1) info.1 info.2.1 info.2.2 I₀ (survey s (pick s).1)
      (dim s) (fit s) (precise s (pick s)) (nn s (pick s))
  have signed:=enrolled (fun _ _=>1) q order g weak pick ζ B t z quarter span apart φ y o cleared radii amp ω
  have total:=WilsonIndependentConditionedGramSplitReceiving.original F books ρ phys M E sale
    (fun s=>(pick s).1) η (by linarith only [quarter,room]) (fun s=>α s (pick s).1)
    (fun s=>doseP s (pick s).1) choose c colour Y opened older (home.trans up) axes pick C₁ C₂ rate q inv g ζ η
    invpos pos quarter et room (fun _=>1) B t z φ y source
  have roster:=(WilsonIndependentConditionedBankShellPrice.original Y opened older axes pick ζ (fun _=>1) B t z).2
  dsimp only at total
  rw [roster] at total
  exact signed.trans <| mul_le_mul_of_nonneg_right total (by positivity)

end YM.Integration.WilsonIndependentConditionedBankRulerHearing

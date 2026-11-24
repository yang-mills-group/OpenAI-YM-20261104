import YM.Integration.WilsonIndependentConditionedBankRulerHearing
import YM.Integration.WilsonIndependentNotebookComplexCorners

/-! All weak/pooled and real/imaginary hearings share one pre-probe fitted matrix on the authentic finite trajectory. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankRulerQuartet
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


def due (R:Run G)(Q:J→SealR G)(C₁ C₂:J→Credit)(rate L M:Credit)(coins:Prices)
    (k e u b f host m K q:ℕ)(ζ:ℝ)(B:J→ℝ)(t z y g:ℝ)(E:J→ℕ)(cap:J→ℝ)(φ:(s:J)→Rarity (Q s).D):ℝ:=
  let δ:=paceT R.family.path.levels.S m K
  let inv:=(1+|L.buy (zz R.family.path.levels m)|)*(1+|M.buy (zz R.family.path.levels m)|)
  let U:=roof (wage (k:=k) (e:=e) R Q coins u b host m K ζ (fun _=>1) (fun _=>1) B t z)
  let cells:=fun s=>|field R (Q s) (C₁ s) (C₂ s) host m K q 1 1|
  let β:=R.family.path.levels.clock.hatBeta f
  homeLow q U inv cap*β^(E 0+E 1)*δ^(3*ζ/4)+
    (homeHigh q U cells cap |gram (e:=e) R Q rate host K q φ B y| *β^(E 0+E 1+max (E 0) (E 1)))*
      (|g|^(q+1)*(δ^(2*((Q 0).h+(Q 1).h)+1))⁻¹)

def capAt (R:Run G){ι:Type*}{h:ℕ}(d:ι→Fin (h+1))(choose:J→ι)(M:ι→ℝ)
    (A:(s:J)→Bool×Bool→Alma (R.family.labels.level (degrees d choose s))→ℝ)(e:ℕ)(pick:J→Bool×Bool)(s:J):ℝ:=
  let F:=R.family.labels.level (degrees d choose s)
  M (choose s)*fixed R (degrees d choose s)*(((e+1:ℕ):ℝ)*∑i:F.Index,A s (pick s) (seat F i))

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
    (opened:j ≤ host)(older:host ≤ m)(home:m ≤ reporter F books ρ)(axes:V.y=zz R₀.family.path.levels)
    (q:ℕ)(order:q ≤ e)(g:ℝ)(weak:|g| ≤ 1)(ζ:ℝ)(B:J→ℝ)(t z:ℝ)
    (pos:0 ≤ ζ)(quarter:ζ ≤ 1/4)(et:0 ≤ η)(room:2*η ≤ ζ/4)
    (span:((∑s,degrees d choose s:ℕ):ℝ)+ζ<b)(apart:0<t)
    (φ:(s:J)→Rarity ((deck (G:=G) (degrees d choose) dim fit) s).D)(y:ℝ)(o:CellR)
    (cleared:∀s s',s≠s'→ClearDay (φ s) (φ s') t)(radii:∀s,radiusH (φ s) 1 y ≤ z)
    (amp:∀s,Amplitude (φ s) (B s))(θ:J→Motion)(flag:J→Bool){ε:ℝ}(ep:0 ≤ ε):
    let Q:=deck (G:=G) (degrees d choose) dim fit
    let pick:=fun (s:J)(im:Bool)=>(flag s,im)
    let x:=assembled Y pick (fun _=>1) q g
    let v:=fun (s:J)(i:Alma (Q s).F)=>fuse (θ s) (fun c=>x s c i)
    (∀p:J→Bool×Bool,due R₀ Q C₁ C₂ rate L₀ M₀ coins k e u b (reporter F books ρ) host m K q
      ζ B t z y g (fun s=>E (choose s)) (capAt R₀ d choose M precise e p) φ ≤ ε) →
    ∀ω,let Y₀:=reader Y pick (fun _=>1) φ y o ω q g
      ‖fuse (θ 0) (fun c=>fuse (θ 1) (Y₀ c))-
        protocol V (Q 0) (Q 1) k host m K N (φ 0) (φ 1) y o 0 ω q g (v 0) (v 1)‖ ≤
        4*ε*(1+∑i,‖v 0 i‖)*(1+∑i,‖v 1 i‖):=by
  classical
  intro Q pick x v bound ω
  apply WilsonIndependentNotebookComplexCorners.original Y pick older (fun _=>1) φ y o ω q g θ ep
  intro c l
  let p:=fun s:J=>pick s (if s=0 then c else l)
  have heard:=WilsonIndependentConditionedBankRulerHearing.original F books ρ phys M E choose dim fit own r
    precise I₀ survey plain Y C₁ C₂ rate L₀ M₀ enrolled sale nn α doseP named opened older home axes q
    order g weak p ζ B t z pos quarter et room span apart φ y o cleared radii amp ω
  rw [WilsonIndependentConditionedBankMatrix.original V _ _ m K N host older
    (Y.levels 0 (pick 0 c)) (Y.reset 0 (pick 0 c)) (Y.home 0 (pick 0 c)) (Y.vacuum 0 (pick 0 c))
    (Y.levels 1 (pick 1 l)) (Y.reset 1 (pick 1 l)) (Y.home 1 (pick 1 l)) (Y.vacuum 1 (pick 1 l))
    1 1 (φ 0) (φ 1) y o 0 ω q g]
  rw [mul_assoc]
  exact heard.trans <| mul_le_mul_of_nonneg_right (bound p) (by positivity)

end YM.Integration.WilsonIndependentConditionedBankRulerQuartet

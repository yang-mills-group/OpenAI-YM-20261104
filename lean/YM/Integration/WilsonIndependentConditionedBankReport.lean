import YM.Integration.WilsonIndependentConditionedBankFrame
import YM.Integration.WilsonIndependentConditionedBankShellPrice
import YM.Integration.WilsonIndependentConditionedGramReserve

/-! The entire signed finite corner with original dated costs and one fixed aperture exponent per arm. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankReport
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
variable {G:Gauge}{h D e k u u₀:ℕ}
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
open WilsonIndependentConditionedGramCampus (Paid)
open WilsonIndependentConditionedGramPrices (profile)
open WilsonPhysicalMarkedDefect.RawProduct (belt positive)
open WilsonSeparatedPrefixMovingCalendar (epoch)

def salary (R:Run G)(Q:SealR G)(C₁ C₂:Credit)(host m K q:ℕ)(a A:ℝ):ℝ:=
  let δ:=paceT R.family.path.levels.S m K
  (Fintype.card (Alma Q.F):ℝ)*((q+1:ℕ):ℝ)*(C₁.buy (age R host m)*((δ^Q.h)⁻¹*C₂.buy (age R m K)*(|a| * A)))

def panel (R:Run G)(Q:J→SealR G)(rate:Credit)(host m K q:ℕ)
    (φ:(s:J)→Rarity (Q s).D)(B:J→ℝ)(y:ℝ):ℝ:=
  let δ:=paceT R.family.path.levels.S m K
  let A:=R.family.path.levels
  let gas:=rate.buy (zz A host+2*(A.S.scale K-A.S.scale host))
  ((q+1:ℕ):ℝ)*(gas*(δ^((Q 0).h+(Q 1).h))⁻¹*(coinMat ((Q 0).h+(Q 1).h) e*profile (φ 0) y (B 0)*profile (φ 1) y (B 1)))

def debit (q:ℕ)(g shell inverse loss₀ loss₁ gram:ℝ):ℝ:=
  (((q+1:ℕ):ℝ)*shell)*(inverse+2*|g|^(q+1)*(loss₀+loss₁))+
  3*|g|^(q+1)*(|gram| * loss₀*loss₁)

theorem original (Q:J→SealR G)(own:∀s,Rails (Q s).h k u₀ e):
    ∃C₁ C₂:J→Credit,
    ∀{R:Run G}{V:Realm G (e+1) C}{coins:Prices}{j:ℕ}{port:∀s,Home R (Q s) (own s) j}
    {ι:J→Type*}{P:(s:J)→ι s→TowerS G (Q s).D}{A:(s:J)→ι s→ℝ}{b host m K N:ℕ}
    (T:Assigned R Q own V coins j port ι P A u b host m K N)(rate L M:Credit),
    Enrolled T L M → Paid V (Q 0) (Q 1) k rate → V.anchor=j → V.y=zz R.family.path.levels →
    j  ≤  host → host  ≤  m → m  ≤  K → K  ≤  N →
    ∀(a:(s:J)→ι s→ℝ)(q:ℕ),q  ≤  e → ∀g:ℝ,|g|  ≤  1 →
    let v:=fun s i=>sample V (Q s) N m host q g (publicDose (Q s) (T.cuts s i) (a s i))
    ∀(pick:(s:J)→ι s)(ζ:ℝ)(B:J→ℝ)(t z:ℝ),ζ  ≤  1/4 → ((∑s,(Q s).h:ℕ):ℝ)+ζ < b → 0<t →
    let X:=fun s=>T.cuts s (pick s); let α:=fun s=>a s (pick s)
    let F:=fun s=>A s (pick s); let δ:=paceT R.family.path.levels.S m K
    let ε:=roof (wage (k:=k) (e:=e) R Q coins u b host m K ζ α F B t z)*δ^ζ
    let inv:=(1+|L.buy (zz R.family.path.levels m)|)*(1+|M.buy (zz R.family.path.levels m)|)
    let coarse:=fun s=>salary R (Q s) (C₁ s) (C₂ s) host m K q (α s) (F s)
    ∀(φ:(s:J)→Rarity (Q s).D)(y:ℝ)(o:CellR),
      (∀s s',s≠s'→ClearDay (φ s) (φ s') t) → (∀s,radiusH (φ s) 1 y  ≤  z) → (∀s,Amplitude (φ s) (B s)) → ∀ω,
      let row:=fun i=>input Q own C C C C X i (α i) (φ i) y o
      let G:=protocol V (Q 0) (Q 1) k host m K N (φ 0) (φ 1) y o 0 ω q g
      let E:=debit q g ε inv (coarse 0) (coarse 1) (panel (e:=e) R Q rate host m K q φ B y)
      ‖view (X 0) host q g (row 0) (row 1) ω-G (v 0 (pick 0)) (v 1 (pick 1))‖ ≤ 
        E*((1+∑i,‖v 0 (pick 0) i‖)*(1+∑i,‖v 1 (pick 1) i‖)):=by
  classical
  obtain ⟨C₁,C₂,issued⟩:=WilsonIndependentConditionedBankFittedFees.original (u:=u) Q own
  refine ⟨C₁,C₂,?_⟩
  intro R V coins j port ι P A b host m K N T rate L M income loan anchor ageV opened older cut vac a q cap g small v
    pick ζ B t z gain room ht X α F δ ε inv coarse φ y o apart sizes tests ω row G E
  let d:=fun s=>publicDose (Q s) (X s) (α s)
  let fx:=charge Q own C C C C V X coins u b host m K ζ α B t z
  let b₀:=fun s=>reserve (X s) host q (dose (X s) (α s))
  let r:=residual V (Q 0) (Q 1) k host m K N (φ 0) (φ 1) y o 0 ω q (d 0) (d 1)
  let p:=panel (e:=e) R Q rate host m K q φ B y
  have shell:roof fx=ε:=(WilsonIndependentConditionedBankShellPrice.original T opened older ageV pick ζ α B t z).2
  have clock (s:J)(D:Credit):(X s).vesselsC.cash D (X s).m=D.buy (zz R.family.path.levels m):=by
    exact congrArg D.buy (by rw [(WilsonIndependentConditionedBankFittedFees.accounts T s (pick s)).2.1,T.home])
  have hε:0 ≤ ε:=shell ▸ le_max_left .. 
  have raw:=WilsonIndependentConditionedBankFrame.original T older L M income a q cap g small
    pick ζ B t z gain room ht φ y o apart sizes tests ω
  change ‖view (X 0) host q g (row 0) (row 1) ω-G (v 0 (pick 0)) (v 1 (pick 1))‖ ≤ 
    ((((q+1:ℕ):ℝ)*roof fx)*((1+|(X 0).vesselsC.cash L (X 0).m|)*(1+|(X 1).vesselsC.cash M (X 1).m|)+
      |2*|g|^(q+1)*(b₀ 0+b₀ 1)|)+|3*|g|^(q+1)*r|)*_ at raw
  rw [shell,clock,clock] at raw
  have reserveNN (s:J):0 ≤ b₀ s:=by
    dsimp only [b₀,reserve]
    exact Finset.sum_nonneg fun _ _=>positive q _
  have sal (s:J):b₀ s ≤ coarse s:=issued T opened older s (pick s) (α s) q cap
  have rr:0 ≤ r:=by
    dsimp only [r,WilsonIndependentConditionedBankPublicGram.residual]
    exact Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>mul_nonneg
      (mul_nonneg (positive q _) (positive q _)) (positive q _)
  have levels:V.draws=R.family.path.levels:=
    (T.levels 0 (pick 0)).symm.trans (WilsonIndependentConditionedBankFittedFees.accounts T 0 (pick 0)).2.2
  have scalar:=WilsonIndependentConditionedGramReserve.original rate loan T (anchor ▸ opened) older cut vac
    pick α φ B y o tests ω q cap
  change r ≤ _ at scalar
  simp only [WilsonSeparatedPrefixMovingCalendar.epoch,ageV,levels] at scalar
  change r ≤ p*b₀ 0*b₀ 1 at scalar
  have pr:r ≤ |p| *coarse 0*coarse 1:=calc
    _  ≤  p*b₀ 0*b₀ 1:=scalar
    _  ≤  |p| *b₀ 0*b₀ 1:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (reserveNN 0)) (reserveNN 1)
    _  ≤  |p| *coarse 0*coarse 1:=mul_le_mul
      (mul_le_mul_of_nonneg_left (sal 0) (abs_nonneg p)) (sal 1)
      (reserveNN 1) (mul_nonneg (abs_nonneg _) ((reserveNN 0).trans (sal 0)))
  have good:0 ≤ |g|^(q+1):=pow_nonneg (abs_nonneg _) _
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) good) (add_nonneg (reserveNN 0) (reserveNN 1))),
      abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) good) rr)] at raw
  refine raw.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  change _ ≤ (((q+1:ℕ):ℝ)*ε)*(inv+2*|g|^(q+1)*(coarse 0+coarse 1))+3*|g|^(q+1)*(|p| *coarse 0*coarse 1)
  exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add_right
    (mul_le_mul_of_nonneg_left (add_le_add (sal 0) (sal 1)) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) good)) inv)
    (mul_nonneg (Nat.cast_nonneg (q+1)) hε)) (mul_le_mul_of_nonneg_left pr (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) good))

end YM.Integration.WilsonIndependentConditionedBankReport

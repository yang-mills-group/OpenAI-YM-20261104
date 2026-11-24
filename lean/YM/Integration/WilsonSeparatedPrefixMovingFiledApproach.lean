import YM.Integration.WilsonSeparatedPrefixMovingCorrectedField
import YM.Integration.WilsonIndependentCutJoinNativeFrames
import YM.Integration.WilsonMovingForkSharpSections

/-! First-contact wages on the actual integrated and previously fitted pupil.
All marker fees enter on their original common reported clock. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingFiledApproach
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMovingRosterAllFineSeats (Named Elected needed)
open WilsonIndependentMatchedOwnHomeProfile (scaled)
open WilsonIndependentSpoutMasterArms (basis)
open WilsonMarkedIndependentNormalizedElection (normalized)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonMovingForkSharpSections (publicFrame)
open WilsonSeparatedPrefixMovingPinnedPupil (Clear)
open WilsonIndependentMatchedOwnHomeKShell (Coins cost)
open WilsonSeparatedPrefixMovingCorrectedField (full field)
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Next.Foundations WilsonLimitConstruction XSpace
open scoped BigOperators Classical
variable {G:Gauge}{n e height seats d:ℕ}
local notation "C" => Credit.leanC
variable (Q:Fin ((n+1)+1) → SealR G)
local notation "F₀" => Q 0
local notation "Qₙ" => (fun i:Fin (n+1) => Q (Fin.succ i))

def pupil (R:Realm G (e+1) C)(m N:ℕ)(a:(∀i,Alma (Q i).F)):Herit Qₙ:=
  normalized R.draws R.paid Qₙ (fun i => WilsonIndependentSpoutMasterArms.basis Q a i.succ) m N

def purse (R:Realm G (e+1) C)(b:Herit Q)(m old N:ℕ)(a:(∀i,Alma (Q i).F)):Cost:=
  clock R.draws R.paid N m old (∏i,b i (a i))

theorem original (P:Run G)(e p ex:ℕ)(pos:0<p)(gain:2 ≤ (Q 0).h+ex)(named:∀s,Named (publicFrame P) height seats (Q s))
    (capacity:needed ((Q 0).h+capP Qₙ) 0 p ≤ seats)(reserve:capP Qₙ+(Q 0).h+ex ≤ seats):
    ∃ book : Coins, ∀(R:Realm G (e+1) C)(_stock:Elected (publicFrame P) R height seats)
    (_frames:WilsonIndependentCutJoinNativeFrames.Funded (publicFrame P) R height seats)(older t c m K N:ℕ),
    R.anchor ≤ older → older ≤ t → t ≤ c → c ≤ m → m ≤ K → K ≤ N →
    ∀(φ:Wilt Q)(b:Herit Q)(r gap farGap DF:ℝ)(B:Fin (n+1) → ℝ)(Φ:Rarity d)(y amp:ℝ)(o:CellR)(ω:Fin 0 → YForest G),
    let T:=paceT R.draws.S m t
    let ψ:=scaled (φ 0) T (pace_pos ..)
    Clear R Qₙ F₀ (fun i=>φ (Fin.succ i)) ψ older t c m r gap farGap DF B → Amplitude Φ amp →
    ∀ρ:ℝ,let bill:=fun a:(∀i,Alma (Q i).F)=>cost book (hol G) R Qₙ F₀ (pupil Q R m N a) (a 0) ψ Φ y amp older t c m K N p ex r gap farGap DF B ρ 0
    let prior:=full R Q φ b Φ y o t m c older N N ρ
    let trial:=full R Q φ b Φ y o t m c older K N ρ
    prior-trial=∑a:(∀i,Alma (Q i).F),purse Q R b m older N a*(
      field R Q φ (WilsonIndependentSpoutMasterArms.basis Q a) .upper Φ y o t m c older K N ρ ω-field R Q φ (WilsonIndependentSpoutMasterArms.basis Q a) .planted Φ y o t m c older K N ρ ω) ∧
    ∀j ≤ e, ‖coeff j (prior-trial)‖ ≤
      ∑a:(∀i,Alma (Q i).F),∑uv∈Finset.HasAntidiagonal.antidiagonal j,‖coeff uv.1 (purse Q R b m older N a)‖*bill a:=by
  obtain ⟨book,paid⟩:=WilsonSeparatedPrefixMovingOrdinarySwitch.original (d:=d) (publicFrame P) Qₙ F₀ e p ex pos gain
    (fun i=>named i.succ) (named 0) capacity reserve C
  refine ⟨book,?_⟩
  intro R stock frames older t c m K N awake old outer mid cut top φ b r gap farGap DF B Φ y amp o ω T ψ geometry money ρ bill prior trial
  obtain ⟨ahead⟩:=frames _ (named 0)
  have all:=WilsonIndependentCutJoinNativeFrames.roster frames Q named
  have source:=WilsonSeparatedPrefixMovingCorrectedField.original R Q φ b all.2 Φ y o t m c older K N ρ
    (old.trans (outer.trans mid)) (awake.trans old) (outer.trans mid) cut top ω
  refine ⟨source,?_⟩
  intro j hj
  rw [show prior-trial=_ from source,map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro a _;rw [coeff_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro uv appeared
  have deg:=Finset.HasAntidiagonal.mem_antidiagonal.mp appeared
  have rate:uv.2 ≤ e:=by omega
  have ticket:=paid R stock ahead older t c m K N awake old outer mid cut top (fun i=>φ (Fin.succ i)) ψ (pupil Q R m N a) (a 0)
    r gap farGap DF B Φ y amp o ω geometry money ρ
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (ticket.2 uv.2 rate) (norm_nonneg _)
end YM.Integration.WilsonSeparatedPrefixMovingFiledApproach
end

import YM.Integration.WilsonPositionProgramTrialSurveyRows
import YM.Integration.WilsonMaxwellThermometerSurveyThreeDraw

/-! The genuine three-site public regulator receives the physical finite coordinate on every row. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialFittedInversion
open Function Filter Finset Lattice Wilson RG RG.Supply Precision XSpace PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonMaxwellThermometerSurveyIncome (master prices)
open WilsonOriginalThermometerPalette (levels)
open WilsonMaxwellThermometerSurveyThreeInversion (surveyed)
open WilsonMaxwellThermometerSurveyThreeInversion (tender raw)
open WilsonPositionProgramInvertedStencil (packet)
open WilsonPositionProgramInversionMaterial (ceiling)
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open scoped Classical BigOperators
variable {G:Gauge}{D h k u e:ℕ}(R:Run G)(W:Initialize G)(d:Fin 3→ℕ)(fit:∀j,levels j<d j)


open WilsonPositionProgramTrialFittedSurvey (stamp)
open WilsonPositionProgramSubmittedCoordinates (submitted)
open WilsonPositionProgramInversionMaterial (dose)
open WilsonMaxwellThermometerSurveyThreeDraw (suite constant)

local notation "Q" => suite W d fit
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O

theorem original (simple:G.Simple)(s:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices s R.kit)
    (pub:prices W R.kit)(big:h<D)(rails:Rails h k u e)(cap:capP (deck (G:=G) levels d fit)≤k):
    ∀ᶠ j:ℕ in atTop,∀m K,j ≤ m → m ≤ K →
    ∀(x:(i:Fin 3)→R.family.label (levels i))(phase:Fin 3→ℂ →L[ℝ] ℝ)(φ:Wilt Q)(y:ℝ)(c:CellR)(p:Period),
      let v:Herit Q:=submitted R levels d fit x phase
      let X:=stamp L O Q m K v
      let θ:=paceT R.family.S m K
      ∀q,PowerSeries.coeff (q+ceiling R levels) (constant R W d fit φ m K X y c p)=
        ∑z∈Fintype.piFinset (fun i=>VisitsT (φ i) θ y c),(∏i,drumB (levels i) θ:ℝ) •
          PowerSeries.coeff q (surveyed R W p z (dose R levels v d fit (fun i=>wheelC θ y (z i) (φ i).ψ c))):=by
  filter_upwards [WilsonPositionProgramTrialSurveyRows.original R W levels d fit simple s funded pub big rails cap,
    WilsonMaxwellThermometerSurveyThreeDraw.original R W d fit simple s funded pub big rails cap] with j charts draws
  intro m K used before x phase φ y c p v X θ q
  have read:∀i,steep L O (Q i).ans (Q i).path K m (K-m) (PermuteLens L O (Q i) K m (X i))=v i:=
    (charts (fun _=>true) m K used before).1 v
  refine (draws m K used before X φ y c p q).trans ?_
  apply Finset.sum_congr rfl
  intro z _
  have returned (B:(i:Fin 3)→Volume (d i)):tender R d fit W X B m K=dose R levels v d fit B:=by
    exact congrArg (fun row=>dose R levels row d fit B) (funext read)
  rw [returned]

end YM.Integration.WilsonPositionProgramTrialFittedInversion

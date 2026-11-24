import YM.Integration.WilsonOriginalFoldedFiledForest

/-! The finite independent marked step on the actual torus, with its unmarked Wick denominator. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2500000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWindingVersePage
open Function Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Mosaic FormalBulk08
open Flat Reef Orb Series Jets Shore Lava Wine Gorge Lotus Mesa
open Next.Free AnalyticNext.QuarticMatch.Sheets Stationary
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open scoped BigOperators Matrix Classical
open private covariance from YM.Integration.WilsonOriginalFoldedMarkedRightColumn
open private transport from YM.Integration.WilsonOriginalFoldedFiledForest

variable {G : Gauge} (R : Run G) (N i per : ℕ)
local notation "V" => R.family.path.levels
local notation "S" => step R i per
local notation "F" => repeatF S
local notation "n" => coarse R i per
local notation "f" => fine R i per
local notation "vac" => (story V R.metals.O N (i+1)).1

def page (k : ℕ) (T : Era G ℝ) : PChart G n :=
  reed S F (upper R N i) (prediction R N i per) (ratio R) (vac f) k (T.1 f)

theorem issued (k : ℕ) (T : Era G ℝ) :
    (verseI V R.metals.O i N k T).1 n =
      Blue.mix (ratioHigh V R.metals.O N i) (page R N i per k T) := by
  apply congrArg (Blue.mix (ratioHigh V R.metals.O N i))
  exact (transport S (loose V i) (V).clock.kernel rfl rfl (predictionA V N i)
    (predictionA V N i) HEq.rfl (freeForms V N (i+1)) R.metals.O vac T.1 k).symm

theorem normalized (simple : G.Simple) (live : i < N) (tag : (S).Choices)
    (k : ℕ) (T : Era G ℝ) (legal : Auth k T) :
    let Q := (model R N i per live).covariance F tag
    let φ := shot S F (prediction R N i per) (ratio R) (vac f)
    Wick (Woods G n) Q (raiseE φ * loom (slice R N i per F) (flash (T.1 f))) =
      Wick (Woods G n) Q (raiseE φ) * flash (page R N i per k T) := by
  intro Q φ
  change Wick _ ((model R N i per live).covariance F tag) _ =
    Wick _ ((model R N i per live).covariance F tag) _ * _
  rw [covariance R N i per live F tag]
  have prior := (Bank.old V R.metals.O simple R.alloy.B.ratio N (i+1) live).basis f
  exact inside_reed S F (upper R N i) (prediction R N i per) k prior.lamp
    R.alloy.B.ratio (legal.span f) ((levels R).blocks i per).branches
    (age_sym (levels R) N (i+1) _) prior.shape (legal.pale f)

end YM.Integration.WilsonCapturedPrimaryWindingVersePage

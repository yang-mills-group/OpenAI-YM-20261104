import YM.Integration.WilsonOriginalMovingStopRawTail
import YM.Integration.WilsonOriginalTwoFlatRoseMerClock

/-! The actual deposited stencil and the normalized roster are evaluated
at the same final coupling on one original course. The shifted raw thermal
powers are paid by the original kinetic return at that order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMovingStopRawBoundary
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Shard
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOlderFreshSoftSocketRestored (stopped coin rated)
open WilsonOlderFreshSoftSocketGross (gross)
open WilsonOlderFreshSoftSocketTotal (normalized)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonOlderFreshSoftSocketFaces (fill)
open WilsonOlderFreshHybridClock (flat)
open WilsonReportingAbsoluteInletForecastBooks (mass value)
open WilsonCoeffUV.Winding
open scoped Topology BigOperators Classical

open WilsonOlderFreshSoftSocketTotal (figure cost)
open WilsonOlderFreshSoftSocketRestored (degree)
open WilsonOriginalTwoFlatRoseMerClock (Charged)
open Pert.Asymptotics (regulatorRun)
variable {G:Gauge}{I:Type}[Fintype I][LinearOrder I](R:Run G)(D d:I → ℕ)(S:Finset I)
    (κ:(i:I) → Knob (D i))(pt:I → Chamber)(N per K c v:ℕ)(cells:Digits R.family.path.levels I)
    (w:(i:I) → R.family.label (d i))(y:I → Cover)(f:Pen D S →L[ℝ]ℝ)
local notation "gv" => regulatorRun R.family N per v

theorem purchased (simple:G.Simple)(ratio:LocalRatio R.metals.O)(vc:v ≤ c)(ck:c ≤ K)(live:K ≤ N)
    (Q target maxDebt:ℕ)(debt:∀q:Selection R d S,degree R d S (fill R d S q) ≤ maxDebt)(cap:maxDebt ≤ Q)
    (charged:Charged R N per v K Q target maxDebt)(positive:0 ≤ gv)(small:gv ≤ 1)(M:ℝ)
    (raw:∀q:Selection R d S,
      mass Q (coin (stopped R d N K c v cells y S f (start R d κ pt (fill R d S q)))) ≤ M):
    ‖figure R d κ pt N per K c v cells S w y f Q gv-normalized R d κ pt N per K c v cells S w y f Q gv‖ ≤
      (∑q:Selection R d S,‖weight R d N per K w S q‖)*(gv^target*M):=by
  classical
  have edge:=WilsonOlderFreshSoftSocketTotal.original R d κ pt N per K c v cells S w y f simple ratio
    vc ck live Q (fun q=>(debt q).trans cap) positive small
  apply edge.trans
  rw [sum_mul]
  apply sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  unfold cost
  dsimp only
  apply mul_le_mul (charged _ (debt q)) (raw q) _ (pow_nonneg positive _)
  exact sum_nonneg (fun _ _=>abs_nonneg _)

theorem original (simple:G.Simple)(ratio:LocalRatio R.metals.O)(vc:v ≤ c)(ck:c ≤ K)(live:K ≤ N)
    (Q J target maxDebt:ℕ)(order:J ≤ Q)(debt:∀q:Selection R d S,degree R d S (fill R d S q) ≤ maxDebt)(cap:maxDebt ≤ Q)
    (charged:Charged R N per v K Q target maxDebt)(positive:0 ≤ gv)(small:gv ≤ 1)(M:ℝ)
    (raw:∀q:Selection R d S,
      mass Q (coin (stopped R d N K c v cells y S f (start R d κ pt (fill R d S q)))) ≤ M):
    ‖figure R d κ pt N per K c v cells S w y f Q gv-normalized R d κ pt N per K c v cells S w y f J gv‖ ≤
      (∑q:Selection R d S,‖weight R d N per K w S q‖)*((gv^target+gv^(J+1))*M):=by
  let row:=normalized R d κ pt N per K c v cells S w y f
  have boundary:=purchased R D d S κ pt N per K c v cells w y f simple ratio vc ck live Q target maxDebt debt cap
    charged positive small M raw
  have tail:‖row Q gv-row J gv‖ ≤ (∑q:Selection R d S,‖weight R d N per K w S q‖)*(gv^(J+1)*M):=by
    unfold row normalized
    rw [←sum_sub_distrib,sum_mul]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro q _
    rw [←mul_sub,norm_mul,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,rated,rated]
    exact mul_le_mul_of_nonneg_left ((WilsonOriginalMovingStopRawTail.truncated Q J order gv positive small _).trans
      (mul_le_mul_of_nonneg_left (raw q) (pow_nonneg positive _))) (norm_nonneg _)
  exact (norm_sub_le_norm_sub_add_norm_sub _ (row Q gv) (row J gv)).trans ((add_le_add boundary tail).trans_eq (by ring))

end YM.Integration.WilsonOriginalMovingStopRawBoundary

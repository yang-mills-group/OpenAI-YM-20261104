import YM.Integration.WilsonOriginalThreeForestGrades
import YM.Integration.WilsonOriginalPrimerStampedRay
import YM.Integration.WilsonOriginalJointForestRay
/-! The same registered three-color forest reads the independently filed basis terms on their genuine copied sites. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalThreePurchasedRays
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary QuadraticLocal.Affinity
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetStationaryChange WilsonOriginalPrimerReplicatedInk PhysicalForestMarkedRay PhysicalForestRay
open FreeResolvent WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonOriginalPointCompactRoster WilsonOriginalThreeCopiedCharts
open scoped Classical BigOperators ContDiff Topology
attribute [local instance] Gauge.frobInner
variable {G:Gauge} {n:Side} {I:Type} [Fintype I] {q:ℕ} {σ:ℝ}
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(l:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner l)) q σ) (A:Fin 3→Set ℂ) (charge:I→ℂ)
  (R:Run G) (N i per:ℕ) (hi:i<N) (F:Forest (step R i per).ratio) (tag:(step R i per).Choices)
  (h:n.val∣(fine R i per).val) (t:Wallet A) (L:Layout G) (tape:Finset Age)
  (Z:I→(m:Side)→Site m→PChart G m) (B:fieldDir G (coarse R i per) 1) (z:Precision.Key F G→ℝ)
local notation "M" => rows owner grades sites T A charge
local notation "J" => Stock.census (Fin 3)
local notation "Y" => copyColor h M grades (fun a=>(M a).paint t) L tape
local notation "U" => bank owner grades sites T A h t L tape
local notation "own" l:max => (T (l)).rows (home sites (owner (l))) (alone A (owner (l)))
local notation "S" => step R i per
local notation "D" => saddle R N i per F
local notation "K" => model R N i per hi

def prescribed (l:I)(j:ℕ):ℂ:=
  (((t (owner l)).val):ℂ)*Complex.ofReal (MvPolynomial.eval (Sum.elim z (flatten B)) (coeff j
    (WilsonOriginalFoldedMarkedRightColumn.before R N i per hi F (located h (sites (owner l)) (Z l (fine R i per))))))

include tag in
theorem original {w:Fin 3→ℝ}{σ₀ C:ℝ}{d seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ₀ C d seats shelf) (σpos:0<σ₀) (hs:0<σ) (bounded:∀v a,a∈A v→‖a‖≤1)
    (legal:Legal tape L) (shell:∀l m x,shellK (grades (owner l)) (Z l m x))
    (pure:∀l m x j,Pure (Z l m x j)) (matched:∀l,WilsonOriginalPrimerStampedRay.Matched (T l) (Z l))
    (s:Hot (J)) (j:ℕ) (hj:j≤q):
    readJet ((Y).power s+j) (chartMark (S) F (D) (K) B z (Y) s)=
      ∑l:I,if (J).fire (owner l)=s.val then charge l*prescribed owner sites A R N i per hi F h t Z B z l j else 0:=by
  rw [WilsonOriginalThreeForestGrades.original owner grades sites T A charge h t L tape (S) F (K) (D) B z
    tag (WilsonOriginalJointForestRay.swept R N i per hi F tag) stock σpos hs bounded legal s j]
  apply sum_congr rfl
  intro l _
  by_cases hit:(J).fire (owner l)=s.val
  · rw [if_pos hit,if_pos hit]
    apply congrArg (charge l*·)
    have cap:∀x,‖value (alone A (owner l)) x‖≤1:=fun x=>bounded _ _ (x ()).property
    have ear:=WilsonOriginalPrimerStampedRay.received (T l) (Z l) R N i per hi F h (home sites (owner l))
      (alone A (owner l)) (subject A (owner l) t) (own l) rfl rfl HEq.rfl cap hs L tape
      (shell l) (pure l) (matched l) q le_rfl B
    have base:=ear name j hj z
    rw [if_pos (show name=submitted (home sites (owner l)) from rfl)] at base
    exact base
  · rw [if_neg hit,if_neg hit]

end YM.Integration.WilsonOriginalThreePurchasedRays

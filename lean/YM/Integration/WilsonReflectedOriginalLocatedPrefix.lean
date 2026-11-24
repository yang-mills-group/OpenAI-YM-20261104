import YM.Integration.WilsonReflectedOriginalPrefixCalendar
import YM.Integration.WilsonOriginalNullOriginGridRoster
import YM.Integration.WilsonOriginalReceivedFirstMarkers
import YM.Integration.OriginalRunProfile

/-! Before-cutoff tariff on the two named cutoff sites, pulled back to K by the
actual nested maps of this very Wilson course. Its hard owner uses the actual
nonbare `Ψ_i.p` and the original reporter horizon. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedOriginalLocatedPrefix
open Filter Finset Lattice Wilson RG QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor
open Org AllOrder AllOrder.Transit AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PhysicalNext PhysicalNext.ThroughLaunch AllOrder.Transit.WheelP PhysicalNext.Repeat PhysicalNext.Repeat.Legato OriginalRunConstruction
open WilsonReflectedOriginalPrefixCalendar WilsonReflectedOriginalPrefixTariff
open WilsonOriginalNullOriginGridRoster
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "cash" => R.alloy.B.a.clock
local notation "family" => R.family

def measured (N per:ℕ)(x y:Site ((family).side N per))(i:ℕ):ℕ :=
  separation (ancestry R per N x i) (ancestry R per N y i)

include simple in
theorem salary {N per K m k a b q:ℕ}(x y:Site ((family).side N per))
    (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀i,RG.Rep G ((family).side i per))
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (source:∀i,1≤(R.alloy.B.a.budget i).supportExponent)
    (lo:m≤K)(high:K≤N)(head:1≤(cash).hatBeta K)
    (away:∃u:ℕ,reserve (cash) K a b q 2 80 ≤ (u:ℝ) ∧ u+2 ≤ measured R N per x y K) :
    ∑t∈range (N-K),Real.exp (-((Ψ (K+t)).p.supportExponent*
        (corridor (Ψ (K+t)).p.B (measured R N per x y (K+t)):ℝ)/8))*
      (cash).hatBeta (K+t)^a*(((family).S.steps K t).val:ℝ)^b ≤
      2*Real.exp (1/4)*(cash).hatBeta K^(-(q:ℤ)):=by
  let z:=fun i=>(ancestry R per N x i)
  let z':=fun i=>(ancestry R per N y i)
  let ratio:=fun i=>((cash).op i per).ratio
  have xroll (i:ℕ)(_h:K ≤ i)(live:i<K+(N-K)):(ratio i).parent (z (i+1))=z i:=
    route R per N x (by omega)
  have yroll (i:ℕ)(_h:K ≤ i)(live:i<K+(N-K)):(ratio i).parent (z' (i+1))=z' i:=
    route R per N y (by omega)
  have alpha (i:ℕ)(start:K ≤ i)(live:i<K+(N-K)):1≤(Ψ i).p.supportExponent:=by
    have actual: (Ψ i).p=R.alloy.B.a.budget i:=(course.1.walk i (lo.trans start) (by omega)).truep.point
    rw [actual];exact source i
  have wage:=WilsonReflectedOriginalPrefixCalendar.original (cash) per ratio z z' (Gauge.slopeConstant_pos simple).le
    head xroll yroll away (fun i=>(Ψ i).p.supportExponent) alpha
  apply le_trans ?_ wage
  apply le_of_eq;apply sum_congr rfl
  intro t ht
  have live:=mem_range.mp ht
  have actual: (Ψ (K+t)).p=R.alloy.B.a.budget (K+t):=
    (course.1.walk _ (by omega) (by omega)).truep.point
  change _ = Real.exp (-((Ψ (K+t)).p.supportExponent*
      (corridor ⌈(Real.log ((cash).hatBeta (K+t)))^2⌉₊ (measured R N per x y (K+t)):ℝ)/8))*
    (cash).hatBeta (K+t)^a*(((family).S.steps K t).val:ℝ)^b
  rw [show (Ψ (K+t)).p.B=⌈(Real.log ((cash).hatBeta (K+t)))^2⌉₊ from congrArg BudgetPoint.B actual]

include simple in
theorem original (profile:WithStage R.metals.p originalOrders) :
    ∀ᶠ K:ℕ in atTop,∀{N per m k a b q:ℕ},∀x y:Site ((family).side N per),
    ∀(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀i,RG.Rep G ((family).side i per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → m ≤ K → K ≤ N →
    (∃u:ℕ,reserve (cash) K a b q 2 80 ≤ (u:ℝ) ∧ u+2 ≤ measured R N per x y K) →
    ∑t∈range (N-K),Real.exp (-((Ψ (K+t)).p.supportExponent*
        (corridor (Ψ (K+t)).p.B (measured R N per x y (K+t)):ℝ)/8))*
      (cash).hatBeta (K+t)^a*(((family).S.steps K t).val:ℝ)^b ≤
      2*Real.exp (1/4)*(cash).hatBeta K^(-(q:ℤ)):=by
  have late:Tendsto (cash).hatBeta atTop atTop:=
    tendsto_atTop_add_const_left _ _ (R.alloy.B.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [late.eventually_ge_atTop 1] with K head
  intro N per m k a b q x y π Γ Ψ course lo high away
  exact salary R simple x y π Γ Ψ course (fun i=>(by norm_num:(1:ℝ)≤100).trans (budget_support R profile i)) lo high head away

end YM.Integration.WilsonReflectedOriginalLocatedPrefix

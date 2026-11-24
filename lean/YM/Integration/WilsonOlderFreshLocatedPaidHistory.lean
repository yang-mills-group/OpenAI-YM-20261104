import YM.Integration.WilsonTrueProjectedLocatedFunded
import YM.Integration.WilsonOlderFreshLocatedPayment

/-! Original basis payments on consecutive sites fund the full finite history. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOlderFreshLocatedPaidHistory
open Filter MeasureTheory Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open QuadraticLocal QuadraticLocal.Advent AllOrder AllOrder.Floe AllOrder.Transit WheelP WilsonOriginalNullCorridor
open scoped Classical Topology BigOperators

open FormalBulk08 City Pose RemainderComparison ConnectedActivityE6
open WilsonTrueProjectedPointProgram WilsonTrueProjectedPointInverse
open WilsonTrueProjectedLocatedBasis WilsonTrueProjectedLocatedHistory
open WilsonPinnedWidthTransport WilsonTrueProjectedNaturalFee WilsonTrueProjectedCourse
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G)
local notation "C₀" => R.family

open WilsonTrueProjectedLocatedFunded WilsonOlderFreshLocatedPayment

theorem original {d D : ℕ} (wood : Primer.Families R.family) (a : hue G) (depth : d<D)
    (simple : G.Simple) (loc : Stationary.Loc G 1) {U : ℕ → ℕ}
    (formal : WilsonWindowFormalPurchase.Canonical U R.kit)
    (point : WilsonNeutralPointForecast.Filed R.kit) (weakly : WilsonNeutralPointWeakForecast.Filed R.kit)
    (slow : ∀ i,(((C₀).S.block i).val:ℝ) ≤ Real.log (RG16.Lambda (C₀).path.levels i))
    (Q earned target : ℕ) (head : target+2≤earned+1) {δ ε : ℝ} (hp : 0<δ) (gap : δ<1/8) (ep : 0≤ε) :
    ∃ K : ℝ, ∃ V : ℕ, 0<K ∧ ∀ᶠ b : ℕ in Filter.atTop,
    ∀ m N p k n : ℕ, m≤b → b+n≤N → d≤(C₀).path.levels.clock.J (b+1) →
    ∀ (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (W : ∀ j,Rep G ((C₀).side j p)),
    Concourse R.alloy R.kit R.T π Γ m N p k W →
    ∀ (o : ∀ j,Site ((C₀).side j p)) (digit : ∀ j, Site ((C₀).S.block j)),
    (∀ j<n, o (b+j)=((C₀).path.levels.clock.op (b+j) p).ratio.parent (o (b+j+1))) →
    (∀ j<n, WilsonOriginalNullPlacedParallel.Joined C₀ d N p (b+j) W (o (b+j+1)) ε) →
    (∀ j<n, ((C₀).path.levels.budget (b+j)).supportExponent ≤ 100) →
    let axes := Letter ((C₀).labels.level d)
    ∀ (report : axes → ℂ) (origin fare : ℝ), 0≤origin → 0≤fare → (∀ t,‖report t‖≤origin) →
    ∀ (book : ∀ j, axes → Config G ((C₀).side j p) → ℂ)
      (_anchor : axes),
    let g := fun j => Coat.gStep (((C₀).path.rep N p j).beta)
    let prices := fun j (_ : Fin (Q+1)) (_ : axes) => fare*(g j)^(earned+1)
    let top := take R Q (lift R wood a depth digit N b g (fun l => PowerSeries.C (report l)) (b+n-b))
    let F := fun j => earnedValue R wood a depth digit N (b+n) Q g top W book (b+j)
    let bill := fun j => datedFee R wood a depth digit N (b+n) Q g top (b+j) (prices (b+j))
    let total := K*(RG16.Lambda (C₀).path.levels b)^V*origin*fare*power R target b
    Full R d wood a depth digit N p b Q (earned+1) W o book fare →
    ∃ H : Receipt R d N p b n W o F bill ε, (∑ j : Fin n,(H.u j+H.e j)) ≤ total ∧
      ∀ i≤n, (∑ j ∈ Finset.range (n-i),gain C₀ (b+i) (b+i+j)*
        ((2+4*stock C₀ (b+i+j))*bill (i+j))) ≤ total*Real.exp (δ*elapsed (C₀).S b (b+i)) := by
  obtain ⟨K,V,hK,paid⟩:=WilsonTrueProjectedLocatedFunded.original R wood a depth simple loc formal
    point weakly slow Q earned target head hp gap ep
  refine ⟨K,V,hK,?_⟩
  filter_upwards [paid] with b applyEarned
  intro m N p k n root live enrolled π Γ W history o digit route joined ceiling axes report origin wage
    ho hw affordable book anchor g prices top F bill total full
  exact applyEarned m N p k n root live enrolled π Γ W history o digit route joined ceiling report origin wage ho hw
    affordable book prices anchor (fun j lo up=>full.1 j lo (up.trans live)) (fun _ _ _ _ _=>le_refl _) <|
    fun j lo up=>full.2 j lo (up.trans_le live)

end YM.Integration.WilsonOlderFreshLocatedPaidHistory
end

import YM.Integration.WilsonReportHarvestUpperAge
import YM.Integration.WilsonReportHarvestUpperSource

/-! At the genuine upper dates, the preselected marked coordinate buys the
whole original microscopic field with a fixed pair of scale exponents. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportHarvestUpperRange
open Filter Lattice RG Source RG12 RG05Readout Address Native Harvest PhysicalNext.Repeat.Legato
open scoped Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)
def factor (S:Schedule) (D m N:ℕ):ℝ:=(S.a m/S.a N)^(D+2)

def eligible (S:Schedule)(m j n:ℕ):Prop:=S.scale n-S.scale m ≤ 2*(S.scale j-S.scale m)

theorem latest (S:Schedule) {m n:ℕ}(mn:m≤n): eligible S m n n:=by
  have noon:S.scale m ≤ S.scale n:=Real.log_le_log (inv_pos.mpr (S.a_pos m))
    (inv_anti₀ (S.a_pos n) (S.strictAnti.antitone mn))
  unfold eligible
  linarith only [noon]

include simple in
theorem original (D h:ℕ):
    ∀ᶠ m:ℕ in atTop,∀n≥m,∀j≥m,j ≤ n → eligible R.family.S m j n →
      let T:=R.family.path.levels.clock.hatBeta
      let Z:=factor R.family.S D m (n+1)
      1 ≤ Z ∧ Z ≤ (R.family.S.a m/R.family.S.a j)^(2*(D+2))*(T j)^(2*(D+2)) ∧
      ∀ b per s:ℕ, ∀ rail:Rail R.family, ∀ B:ℕ→ℕ→ℝ,
      ∀ V:Sight R.family s per, ∀ U:Emblems R.family s, Spine rail B R.makes b per s (n+1) V U →
      ∀ t:Letter s, ∀ x:R.family.label (kept t), R.family.ref (kept t) ≤ m → b ≤ m → s ≤ D →
      mass R.family (kept t) x ≤ (T m)^h →
      size (WilsonReportingUpperChartPrice.returned R.makes t x U m (n+1) per) ≤ (T m)^h*Z ∧
      Many.point U (WilsonReportingUpperChartPrice.returned R.makes t x U m (n+1) per) m (n+1) =
        chunk t (WilsonReportingFactorySingleton.upper R.makes (kept t) m (n+1) per x) := by
  filter_upwards [WilsonReportHarvestUpperAge.interval R simple,
    WilsonReportHarvestUpperSource.original R.makes D h] with m range charge n mn j mj jn chosen T Z
  have live:m ≤ n+1:=Nat.le_succ_of_le mn
  have span:1 ≤ R.family.S.a m/R.family.S.a (n+1):=
    (one_le_div (R.family.S.a_pos _)).2 (R.family.S.strictAnti.antitone live)
  refine ⟨one_le_pow₀ span,?_,?_⟩
  · have q:=pow_le_pow_left₀ (zero_le_one.trans span) (range n mn j mj jn chosen) (D+2)
    simpa only [Z,factor,mul_pow,←pow_mul] using q
  · intro b per s rail B V U spine t x dated begun small cash
    exact charge b (n+1) per s rail B V U spine t x dated begun live small cash

end YM.Integration.WilsonReportHarvestUpperRange

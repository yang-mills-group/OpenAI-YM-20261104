import YM.Integration.WilsonReportingRegisteredAction
import YM.Integration.WilsonReportingForestArea
import YM.Integration.WilsonPhysicalRegisteredForestConditional

/-! The physical forest links within each genuine registered support, its
actual complementary free assignment, and the original conditional Haar law
on the same rooted face window used by the reporting detector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingRegisteredForest
open Function Filter Finset Set MeasureTheory Metric Lattice Wilson RG Tree RG16 OPE.Therm
open MSbar.Heath PertExtension Precision PhysicalNext.Repeat.Legato
open WilsonPhysicalLocalPlaquetteForest WilsonPhysicalRegisteredForestAction WilsonReportingRegisteredAction
open scoped Topology Classical BigOperators
variable {G:Gauge} (R:Run G)
local notation "A"=>R.family.path.levels

/-- Each such link is a genuine free coordinate of the already chosen forest. -/
def wires {m per:ℕ} (T:Forest (R.family.path.levels.clock.op m per).ratio) (d:ℕ) (o:Site (R.family.side (m+1) per)) : Finset T.Free :=
  Finset.univ.filter fun e => e.val∈bonds R d o ∧ (R.family.path.levels.clock.op m per).ratio.parent e.val.1=(R.family.path.levels.clock.op m per).ratio.parent (e.val.1+step e.val.2)

def collar (m per d:ℕ) (o:Site (R.family.side (m+1) per)) :=
  WilsonAxialWindow.cells o (radius (depth R d+3) (R.family.path.levels.clock.op m per).ratio.count.val)

/-- Coordinates in both factors retain their exact submitted values. -/
theorem fixed {c f:Side} {S:StepData c f} (T:Forest S.ratio) (E:Finset T.Free)
    (v:({i:T.Free|i∉E}:Set T.Free)→G.El) (x:↥E→G.El) :
    (∀i:↥E,filled T E v x i.val.val=x i) ∧ (∀i:({i:T.Free|i∉E}:Set T.Free),filled T E v x i.val.val=v i) := by
  constructor <;> intro i <;> unfold filled <;> rw [T.off_tree]
  · exact congrFun (congrArg Prod.fst ((cut T E).apply_symm_apply (x,v))) i
  · exact congrFun (congrArg Prod.snd ((cut T E).apply_symm_apply (x,v))) i

/-- On the true reporting appointment the local proper Haar Jacobian applies
at every sufficiently late date, before all cutoffs, periods, placements and
old exterior fields. The positive Wilson vacuum occurs exactly once. -/
theorem original (simple:G.Simple) (slow:∀m,(((A).S.block m).val:ℝ)≤Real.log (Lambda (A) m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P) (d:ℕ) :
    ∀ᶠ m:ℕ in atTop,∀N,m<N→∀per (o:Site (R.family.side (m+1) per)),
    ((collar R m per d o).card:ℝ)≤(A).clock.hatBeta (m+1) ∧
    ∀(T:Forest (R.family.path.levels.clock.op m per).ratio) (V:Config G (R.family.side m per)) (H:Config G (R.family.side (m+1) per)→ℝ),
    Envelope H→GaugeInvariant H→
      let E:=wires R T d o
      let cold:=House.chilly (G:=G) (collar R m per d o) (cool (A) (m+1))
      let w:=actualConditionalDensity R.family N per m V
      actualAverage R.family (N:=N) (cold.indicator H) V=
        ∫v:({i:T.Free|i∉E}:Set T.Free)→G.El,
          (∫x in ball 0 r,Chart.jacobian P x*cold.indicator (fun U=>w U*H U)
            (filled T E v (Chart.expLinks G (↥E) x)) ∂Chart.tangent G (↥E)) ∂Measure.pi (fun _=>G.probHaar) := by
  let D:=depth R d+3
  let ε:=min J.δ (r/(2*J.C))
  have pc:=zero_lt_one.trans_le clear.cost
  have small:0<ε:=lt_min clear.dist (div_pos pr (by positivity))
  filter_upwards [WilsonReportingForestArea.dates R.family simple slow D small] with m date N live per o
  obtain ⟨physical,buy,count⟩:=date per D le_rfl
  refine ⟨count o,?_⟩
  intro T V H me invariant
  have cap:J.C*(r/(2*J.C))=r/2:=by field_simp
  apply WilsonPhysicalRegisteredForestConditional.original R live J clear P hp T (wires R T d o) o D physical (by unfold cool RG.Calendar.hatCoupling;positivity) pr sr (buy.trans (min_le_left ..)) _ _ V H me invariant
  · apply (mul_le_mul_of_nonneg_left (buy.trans (min_le_right ..)) pc.le).trans_lt
    rw [cap];exact half_lt_self pr
  · intro e he
    obtain ⟨edge,internal⟩:=(Finset.mem_filter.mp he).2
    obtain ⟨a,b⟩:=(Finset.mem_filter.mp edge).2
    exact ⟨(reaches R d o _ a).trans (Nat.le_add_right ..),(reaches R d o _ b).trans (Nat.le_add_right ..),internal⟩

end YM.Integration.WilsonReportingRegisteredForest

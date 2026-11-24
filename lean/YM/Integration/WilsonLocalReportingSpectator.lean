import YM.Integration.WilsonLocalChartAnchor
import YM.Integration.WilsonLocalInheritedDensity

/-! A signed numerical relative error for the original conditional density at
all later reporting cutoffs, on the sampled true cold field, with the
entire inherited unmarked weight retained at that field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalReportingSpectator
open Function Filter Finset Set Lattice RG Wilson Tree RG16 Precision PertExtension PertExtension.Series MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Legato WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots
open WilsonLocalConditionalResidue WilsonLocalReportingExpense WilsonLocalChartAnchor WilsonReportingRegisteredAction
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]

theorem original (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (p:ℕ) {ε:ℝ} (ep:0 < ε) :
    ∀ᶠ m:ℕ in atTop,∀N,m < N→∀per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (V:Config G (R.family.side m per)),
    let B:=incident R T d o
    let E:=moving T B
    let g:=regulatorRun R.family N per (m+1)
    let ρ:=actualConditionalDensity R.family N per m V
    ∀(v:({i:T.Free|i∉E}:Set T.Free)→G.El) (X:↥E→G.Color),admitted R J d m per o T v g X→
    ∀(A:Type) [NormedAddCommGroup A] [NormedSpace ℝ A] (marked:A),
    ‖(WilsonLocalConditionalResidue.weight P ρ T B v g X)•marked-
      (WilsonLocalInheritedDensity.model P p R N per m V T B v g X)•marked‖ ≤
      ε*g^p*‖(WilsonLocalConditionalResidue.weight P ρ T B v g X)•marked‖ := by
  obtain ⟨δ,H,W,hd,_,hH,hW,issue⟩:=WilsonLocalInheritedWeights.original P hp p
  let η:=min 1 (ε/2)
  have hη:0 < η:=lt_min zero_lt_one (by positivity)
  have rise: Tendsto (fun m:ℕ=>R.family.path.levels.clock.hatBeta (m+1)) atTop atTop :=
    (Next.Rank.Station.hat_rate R.family.path.levels simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [WilsonLocalReportingExpense.original R simple slow J clear d p hH hW hd hη,
    rise.eventually_ge_atTop 2] with m earned hot N hm per o T V
  dsimp only;intro v X good A _ _ marked
  let B:=incident R T d o
  let β:=R.family.path.β N per (m+1)
  let g:=regulatorRun R.family N per (m+1)
  let ρ:=actualConditionalDensity R.family N per m V
  have gp:0 < g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson hm))
  have bounds:=(R.makes.wilson.represents N per (m+1) (Nat.succ_le_of_lt hm)).band
  have lower:R.family.path.levels.clock.hatBeta (m+1)/2 ≤ β:=bounds.1
  have heated:2 ≤ R.family.path.levels.clock.hatBeta (m+1):=hot
  have small:g ≤ 1:=inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (show 1 ≤ β by linarith only [lower,heated]))
  obtain ⟨room,D⟩:=earned N hm per o T v X X good good
  have quote:=issue R m N per hm V T B v X 0 (fun i=>⟨(room i).1,by simpa only [Pi.zero_apply,norm_zero,mul_zero] using hd.le⟩)
  have hρ:=fun U=> (WilsonLocalInheritedRatio.positive R N per m hm V U).2
  have positive:=weight_zero P hp T B v g ρ hρ
  have rate:=increment p ((abs_nonneg _).trans quote.2.2.1) ep gp.le small ((zero_expense p hH hW gp.le X).trans D)
  rw [←WilsonLocalInheritedDensity.field P p R N per m hm V T B v g X]
  exact (WilsonLocalTerminalSpectator.signed positive quote marked).trans (mul_le_mul_of_nonneg_right rate (norm_nonneg _))

end YM.Integration.WilsonLocalReportingSpectator

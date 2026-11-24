import YM.Integration.WilsonLocalReportingChartFunctions
import YM.Integration.WilsonReportingForestPivotConditional

/-! The whole original restricted conditional is one integral in the
sampled exterior and tangent coordinates. Absolute summability follows
from the genuine product Haar Jacobian and the original bounded envelope. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalReportingChartIntegral
open Function Filter Set Finset MeasureTheory Metric Lattice Wilson RG Tree RG16 Precision PertExtension
open PhysicalNext.Repeat.Legato WilsonReportingForestPivots WilsonPhysicalRegisteredForestAction
open WilsonLocalReportingChartFunctions MSbar.Heath OPE.Therm
open scoped Classical BigOperators Matrix.Norms.Frobenius Topology
variable {G:Gauge} {c f:Side} {S:StepData c f}

abbrev Field (T:Forest S.ratio) (B:Finset T.Free) :=
  (({i:T.Free|i∉moving T B}:Set T.Free)→G.El) × (↥(moving T B)→G.Color)

def law (G:Gauge) {c f:Side} {S:StepData c f} (T:Forest S.ratio) (B:Finset T.Free) (r:ℝ) :
    Measure (Field (G:=G) T B) :=
  (Chart.physical G ({i:T.Free|i∉moving T B}:Set T.Free)).prod
    ((Chart.tangent G (↥(moving T B))).restrict (ball 0 r))

def sampled (T:Forest S.ratio) (B:Finset T.Free) (z:Field (G:=G) T B) :=
  restored T B z.1 (Chart.expLinks G (↥(moving T B)) z.2)

def entry (P:ChartRatio G) (T:Forest S.ratio) (B:Finset T.Free) (C:Set (Config G f)) (F:Config G f→ℝ)
    (z:Field (G:=G) T B) := Chart.jacobian P z.2*C.indicator F (sampled T B z)

theorem sampled_m (T:Forest S.ratio) (B:Finset T.Free) : Measurable (sampled (G:=G) T B) :=
  filled_m T (moving T B) measurable_fst ((Chart.expLinks_meas.comp measurable_snd).mul (background_m T B measurable_fst))

theorem bought (P:ChartRatio G) (hp:LocalRatio P) (ι:Type) [Fintype ι] {r:ℝ} (pr:0 < r) (sr:r < Chart.small G P) :
    Integrable (Chart.jacobian P : (ι→G.Color)→ℝ) ((Chart.tangent G ι).restrict (ball 0 r)) := by
  have h:=Integrable.fintype_prod (f:=fun _:ι=>Chart.fee P) (μ:=fun _:ι=>(volume:Measure G.Color).restrict (ball 0 r))
    (fun _=>Chart.Ratio.feeIntegrable hp sr.le)
  change Integrable (fun x:ι→G.Color=>∏i,Chart.fee P (x i)) ((Measure.pi (fun _:ι=>(volume:Measure G.Color))).restrict (ball 0 r))
  rw [ball_pi (0:ι→G.Color) pr,Measure.restrict_pi_pi]
  exact h

theorem integrable (P:ChartRatio G) (hp:LocalRatio P) (T:Forest S.ratio) (B:Finset T.Free) {C:Set (Config G f)}
    (hc:MeasurableSet C) {F:Config G f→ℝ} (ef:Envelope F) {r:ℝ} (pr:0 < r) (sr:r < Chart.small G P) :
    Integrable (entry P T B C F) (law G T B r) := by
  let E:=moving T B
  let μ:=Chart.physical G ({i:T.Free|i∉E}:Set T.Free)
  have e:Envelope (C.indicator F):=Envelope.piece hc ef (Envelope.const 0)
  obtain ⟨M,bound⟩:=e.cost
  have j:=((bought P hp (↥E) pr sr).comp_snd μ).mul_const M
  apply j.mono' (((Chart.Ratio.jacobian_meas hp).comp measurable_snd).mul (e.meas.comp (sampled_m T B))).aestronglyMeasurable
  apply ae_of_all;intro z
  change ‖Chart.jacobian P z.2*C.indicator F (sampled T B z)‖ ≤ Chart.jacobian P z.2*M
  rw [norm_mul,Real.norm_of_nonneg (Chart.jacobian_nonneg _)]
  exact mul_le_mul_of_nonneg_left (bound _) (Chart.jacobian_nonneg _)

theorem ball_ae (T:Forest S.ratio) (B:Finset T.Free) (r:ℝ) :
    ∀ᵐ z:Field (G:=G) T B ∂law G T B r,z.2∈ball 0 r :=
  Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem isOpen_ball.measurableSet)

theorem original (R:Run G) (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (J:MSbar.Heath.Voice G) (clear:MSbar.Heath.Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ}
    (pr:0 < r) (sr:r < Chart.small G P) {I:Type} [Fintype I] (d:I→ℕ) :
    ∀ᶠm:ℕ in atTop,∀N,m < N→∀per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (V:Config G (R.family.side m per))
    (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→GaugeInvariant H→
    let B:=incident R T d o
    let C:=cold R m per d o
    let ρ:=actualConditionalDensity R.family N per m V
    actualAverage R.family (N:=N) (C.indicator H) V=
      ∫z,entry P T B C (fun U=>ρ U*H U) z ∂law G T B r := by
  filter_upwards [WilsonReportingForestPivots.original R simple slow J clear P hp pr sr d] with m read N hm per o T V H eh inv
  let C:=cold R m per d o
  let B:=incident R T d o
  obtain ⟨b,hb,lo⟩:=WilsonHeldExteriorLaw.upper_floor R N per m hm
  have ρ:=(WilsonHeldExteriorLaw.regularity R N per m hm V ((R.family.path).rep N per (m+1))
    (((R.family.path).rep N per (m+1)).envelope (R.makes.wilson.represents N per (m+1) hm).good) hb lo).1
  have hc:MeasurableSet C:=MeasurableSet.iInter (fun _=>House.bath _)
  exact (read N hm per o T V H eh inv).trans (integral_prod _ (integrable P hp T B hc (ρ.mul eh) pr sr)).symm

end YM.Integration.WilsonLocalReportingChartIntegral

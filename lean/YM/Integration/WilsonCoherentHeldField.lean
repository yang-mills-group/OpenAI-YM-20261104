import YM.Integration.WilsonCoherentRetainedExperiment

/-! The retained marked integral is a measurable function of the original held coarse field. -/
noncomputable section
namespace YM.Integration.WilsonCoherentHeldField
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm
open RG16 ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open OriginalMarkedRunAction Pert.Asymptotics WilsonPhysicalRegisteredForestAction
open WilsonReportingForestPivots WilsonCoherentForestMeasure WilsonCoherentForestReadout
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {j N per:ℕ}
local notation "A" => R.family.path
local notation "stage" => R.family.path.levels.clock.op j per
local notation "f" => R.family.side (j+1) per
local notation "c" => R.family.side j per
local notation "Q" => R.family.path.rep N per (j+1)

theorem driver (hj:j<N) (P:Rep G f) (good:Measurable P.eval) :
    Measurable (fun z:Config G c × Config G f=>WilsonHeldExteriorLaw.weight R N per j z.1 P z.2) := by
  have old:=((A).rep N per j).envelope (R.makes.wilson.represents N per j hj.le).good
  exact ((((stage).density_meas ((A).levels.blocks j per).branches ((A).β N per (j+1))).comp measurable_swap).mul
    (good.comp measurable_snd)).div (old.meas.comp measurable_fst)

theorem marginal (hj:j<N) (T:Forest (stage).ratio) (B:Finset T.Free) (P:Rep G f) (good:Measurable P.eval) :
    Measurable (fun z:Config G c × (Outer T B→G.El) =>
      WilsonForestRetainedFibre.mass R (N:=N) T (moving T B) z.1 P z.2) := by
  let E:=moving T B
  let K:=Config G c × (Outer T B→G.El)
  have move : Measurable (fun z:K × (↥E→G.El)=>filled (S:=stage) T E z.1.2 z.2):=
    T.continuous_drape.measurable.comp ((cut T E).symm.measurable.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have full:= (driver R hj P good).comp ((measurable_fst.comp measurable_fst).prodMk move)
  let μ:=Chart.physical G (↥E)
  letI : IsProbabilityMeasure μ:=by dsimp [μ,Chart.physical];infer_instance
  exact (full.stronglyMeasurable.integral_prod_right' (ν:=μ)).measurable

theorem reconstructed (hj:j<N) (P:Rep G f) (ep:Measurable P.eval)
    (T:Forest (stage).ratio) (B:Finset T.Free) :
    Measurable (fun z:Config G c × Sample T B G =>
      WilsonForestRetainedFibre.corrected R (N:=N) T (moving T B) z.1 P z.2.1 (state T B z.2)) := by
  have eq:=((Q).envelope (R.makes.wilson.represents N per (j+1) hj).good).meas
  let E:=moving T B
  let toField (z:Config G c × Sample T B G):=(z.1,state T B z.2)
  let toOuter (z:Config G c × Sample T B G):=(z.1,z.2.1)
  have u:Measurable toField:=measurable_fst.prodMk ((measurable_state (G:=G) T B).comp measurable_snd)
  have v:Measurable toOuter:=measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  let w (z:Config G c × Config G f):=WilsonHeldExteriorLaw.weight R N per j z.1 P z.2
  let zp (z:Config G c × (Outer T B→G.El)):=WilsonForestRetainedFibre.mass R (N:=N) T E z.1 P z.2
  let zq (z:Config G c × (Outer T B→G.El)):=WilsonForestRetainedFibre.mass R (N:=N) T E z.1 Q z.2
  have hw:Measurable w:=driver R hj P ep
  have hp:Measurable zp:=marginal R hj T B P ep
  have hq:Measurable zq:=marginal R hj T B Q eq
  change Measurable (fun z=>(w ∘ toField) z*(zq ∘ toOuter) z/(zp ∘ toOuter) z)
  exact ((hw.comp u).mul (hq.comp v)).div (hp.comp v)

theorem joined (interior:j+1<N) (grade:ℕ) (paid:Comparison R (p:=per) interior grade)
    (T:Forest (stage).ratio) (B:Finset T.Free) :
    Measurable (fun z:Config G c × Sample T B G =>
      WilsonCoherentRetainedDriver.value R interior grade T B z.1 z.2) :=
  reconstructed R interior.le (approximation R (p:=per) interior grade)
    (OriginalMarkedRunCovariance.keep_envelope R interior paid).meas T B

private theorem finite_kernel {X:Type*} [MeasurableSpace X] (μ:Measure X) [IsFiniteMeasure μ] : SFinite μ:=inferInstance

theorem reading (interior:j+1<N) (grade:ℕ) (paid:Comparison R (p:=per) interior grade)
    (T:Forest (stage).ratio) (B:Finset T.Free) (P:ChartRatio G) (hp:LocalRatio P)
    {r:ℝ} (pr:0<r) (sr:r<Chart.small G P) (s:Set (Sample T B G)) {a:Sample T B G→ℝ} (ma:Measurable a) :
    Measurable (fun V:Config G c=>∫z in s, WilsonCoherentRetainedDriver.value R interior grade T B V z*a z ∂law P r T B) := by
  let μ:=law P r T B
  letI : IsFiniteMeasure μ:=funded P r T B hp pr sr
  let ν:=μ.restrict s
  letI : IsFiniteMeasure ν:=by dsimp only [ν];infer_instance
  letI : SFinite ν:=finite_kernel ν
  have h:Measurable (fun z:Config G c × Sample T B G=>WilsonCoherentRetainedDriver.value R interior grade T B z.1 z.2*a z.2):=
    (joined R interior grade paid T B).mul (ma.comp measurable_snd)
  exact (h.stronglyMeasurable.integral_prod_right' (ν:=ν)).measurable

end YM.Integration.WilsonCoherentHeldField

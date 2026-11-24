import YM.Integration.FVA1Physical.Sources.Round2.FieldExteriorTower
import YM.Push.BETA_TRANSPORT.Noise

/-! Exact exterior likelihood and covariance for a genuine marked posterior on
the next block. The discrete predictor tags in the fine transition stay shared. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set MeasureTheory Finset Lattice RG YM.Wilson Precision MSbar.Bulk
open Pressure Push.BetaTransport Push.BetaTransport.Gibbs
open scoped Classical Topology BigOperators
variable {G:Gauge} {c f:Side} (S:StepData c f)

def exteriorTags (β:ℝ) (I:Finset (Bond c)) (V W:Config G c) (U:Config G f) (t:S.Choices) : ℝ :=
  let q:=S.prediction U t
  Real.exp (-β*∑ e∈univ\I,(linkEnergy S (V e*(q e)⁻¹)-linkEnergy S (W e*(q e)⁻¹)))

theorem exterior_noise (β:ℝ) (I:Finset (Bond c)) (V W:Config G c) (agree:∀e∈I,V e=W e)
    (U:Config G f) (t:S.Choices) :
    S.noise β (S.prediction U t) V = S.noise β (S.prediction U t) W * exteriorTags S β I V W U t := by
  let q:=S.prediction U t
  have sumEq : noiseEnergy S q V-noiseEnergy S q W =
      ∑ e∈univ\I,(linkEnergy S (V e*(q e)⁻¹)-linkEnergy S (W e*(q e)⁻¹)) := by
    unfold noiseEnergy
    rw [←sum_sub_distrib]
    apply (sum_subset (sdiff_subset (s:=univ) (t:=I)) ?_).symm
    intro e he he'
    have keep:e∈I:=by_contra fun h=>he' (mem_sdiff.mpr ⟨he,h⟩)
    rw [agree e keep,sub_self]
  rw [noise_factor,noise_factor, exteriorTags, factor, factor, mul_assoc,←Real.exp_add]
  apply congrArg ((Next.Fluctuations.Sector.prefactor S G β) * ·)
  apply congrArg Real.exp
  change -β*noiseEnergy S q V = -β*noiseEnergy S q W+ -β*_
  rw [←sumEq]
  ring

def retainedTilt (β:ℝ) (V W:Config G c) (U:Config G f) : ℝ :=
  S.density β U V / S.density β U W

theorem retainedTilt_exterior (β:ℝ) (I:Finset (Bond c)) (V W:Config G c)
    (agree:∀e∈I,V e=W e) (U:Config G f) :
    retainedTilt S β V W U =
      (∑ t,S.likelihood U t*S.noise β (S.prediction U t) W*exteriorTags S β I V W U t) /
       (∑ t,S.likelihood U t*S.noise β (S.prediction U t) W) := by
  unfold retainedTilt StepData.density
  congr 1
  exact sum_congr rfl fun t _=>by rw [exterior_noise S β I V W agree U t,mul_assoc]

theorem retained_covariance (branch:S.patch.Branches S.kernel G) (R:Rep G f) (V W:Config G c)
    (F:Config G f → ℝ) (vpos:0 < S.push R.beta R.eval V) (wpos:0 < S.push R.beta R.eval W) :
    let tilt:=retainedTilt S R.beta V W
    let E:=expect S R W
    expect S R V F-E F = (E (tilt*F)-E tilt*E F)/E tilt := by
  intro tilt E
  have mulT (K:Config G f → ℝ): S.push R.beta (tilt*K) W=S.push R.beta K V := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro U
    change S.density R.beta U W * ((S.density R.beta U V / S.density R.beta U W)*K U)=_
    change _ = S.density R.beta U V * K U
    field_simp [(Progress.DirectedRecipe.density_strict S R.beta branch U W).ne']
  have row: E (tilt*F) = S.push R.beta (F*R.eval) V / S.push R.beta R.eval W := by
    change S.push R.beta ((tilt*F)*R.eval) W / _=_
    rw [mul_assoc,mulT]
  have vac:E tilt=S.push R.beta R.eval V/S.push R.beta R.eval W:=by
    change S.push R.beta (tilt*R.eval) W / _=_
    rw [mulT]
  rw [row,vac]
  dsimp only [E,MSbar.Bulk.expect]
  field_simp [vpos.ne',wpos.ne']

end YM.Integration.FVA1Physical.Round2.Curvature

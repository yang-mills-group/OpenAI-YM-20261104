import YM.Integration.FVA1Physical.Wilson.SparseGauge
import YM.Integration.FVA1Physical.Wilson.AngularReflection

/-! Uniform estimates for one thermal gauge window on any k physical bonds, without
requiring their positions to be near each other. The physical exceptional set has
probability below every inverse power. The gauge Haar mass has a polynomial floor. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Set MeasureTheory Lattice RG YM.Wilson Pressure MSbar.Heath.Cottage MSbar.Heath.Stock
open OPE.Therm Qlocal.Schedule Push.AbsoluteSums.Animals
open YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical BigOperators Topology
variable {G:Gauge}

private theorem shell_buffer (k:ℕ) : ∀ᶠ x:ℝ in atTop, 0<4*x⁻¹ ∧ 4*x⁻¹≤1 ∧
    sparseLoss k*angularCut x+2*(4*x⁻¹)<MSbar.Heath.Cottage.room x :=by
  filter_upwards [angular_below_thermal (2*sparseLoss k),Real.tendsto_sqrt_atTop.eventually_ge_atTop 16,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (4:ℝ)] with x below sqrt16 log1 four
  have xp:0<x:=by linarith only [four]
  have root:0<Real.sqrt x:=Real.sqrt_pos.mpr xp
  have gp:0<cue x:=inv_pos.mpr root
  have logroot:1≤Real.sqrt (Real.log x):=Real.one_le_sqrt.mpr log1
  have bound:16*x⁻¹≤cue x:=by
    change 16*x⁻¹ ≤ (Real.sqrt x)⁻¹
    rw [←div_eq_mul_inv,div_le_iff₀ xp,inv_mul_eq_div,le_div_iff₀ root]
    nlinarith only [Real.sq_sqrt xp.le,mul_le_mul_of_nonneg_right sqrt16 root.le]
  have scale:x^(-(1/2:ℝ))=cue x:=by rw [Real.rpow_neg xp.le,←Real.sqrt_eq_rpow];rfl
  have large:cue x≤MSbar.Heath.Cottage.room x:=by
    unfold MSbar.Heath.Cottage.room distance;rw [scale]
    exact (le_mul_of_one_le_right gp.le log1).trans
      (le_mul_of_one_le_right (mul_nonneg gp.le (zero_le_one.trans log1)) logroot)
  exact ⟨by positivity,by rw [←div_eq_mul_inv,div_le_one xp];exact four,by linarith only [below,bound,large]⟩

/-- On every eligible selected period and independently placed set of ≤k bonds, the
physical complement of a margin in the common gauge window costs at most the stated
inverse power. One stage delay is used for all k, K, cutoffs and periods. -/
theorem sparse_physical (R:PhysicalNext.Repeat.Legato.Run G) (simple:G.Simple)
    (gate:selectedThreshold (angularThreshold G) R.metals R.rolls R.alloy R.kit) (k K:ℕ):
    ∀ᶠ j:ℕ in atTop, ∀ (N n:ℕ) (_:j+1≤N) (B:Finset (Edge (Site (R.family.side (j+1) n)))) (_:B.card≤k),
    let x:=R.family.path.levels.clock.hatBeta (j+1);let τ:=MSbar.Heath.Cottage.room x
    let T:=House.chilly (G:=G) (sparseFaces B k) (angularCut x)
    (OPE.Therm.scene R.family.path N n (j+1)).real Tᶜ ≤ (sparseCount k:ℝ)*(x⁻¹)^K ∧
    0<4*x⁻¹ ∧ 4*x⁻¹≤1 ∧
    ∀ U∈T,∃ z:Site (R.family.side (j+1) n)→G.El,∀ e∈B,G.chord (gauge z U e)+2*(4*x⁻¹)<τ :=by
  let H:=R.family.path
  have grows: Tendsto (fun j:ℕ=>H.levels.clock.hatBeta (j+1)) atTop atTop :=
    (Multi.Wage.hat_tend simple H.levels).comp (tendsto_add_atTop_nat 1)
  filter_upwards [angular_rare_on R simple gate K,grows.eventually (shell_buffer k),
    (Work.E01.radiusB_tendsto.comp grows).eventually_ge_atTop k] with j rare shell fat
  intro N n hj B size x τ T
  haveI : IsProbabilityMeasure (OPE.Therm.scene R.family.path N n (j+1)) := probability (H:=R.family.path) (p:=n) R.T.choice hj
  have xp:1<x:=H.levels.fits.delayed _
  have natural:100*(radiusB x+1) ≤ (R.family.side (j+1) n).val:=H.levels.fits.sizeT _ _
  have pr:2*(2*k+1)<(R.family.side (j+1) n).val:=by
    change k≤radiusB x at fat;omega
  have mass:=House.cool_miss _ (rare N n hj) (sparseFaces B k)
  refine ⟨mass.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (sparse_count B k size))
    (pow_nonneg (inv_nonneg.mpr (zero_lt_one.trans xp).le) _)),shell.1,shell.2.1,?_⟩
  intro U hot
  have q0:0≤angularCut x:=by unfold angularCut cue;positivity [Real.log_pos xp]
  obtain ⟨z,edge⟩:=sparse_axial B k size pr U q0 hot
  exact ⟨z,fun e he=>(add_le_add (edge e he) le_rfl).trans_lt shell.2.2⟩

/-- The window mass is at least x^(-2 dimG k) outside the very same physical exception.
The exponent and exceptional cost have no dependence on the separation of the bonds. -/
theorem sparse_haar_floor (R:PhysicalNext.Repeat.Legato.Run G) (simple:G.Simple)
    (gate:selectedThreshold (angularThreshold G) R.metals R.rolls R.alloy R.kit) (k K:ℕ):
    ∀ᶠ j:ℕ in atTop, ∀ (N n:ℕ) (_:j+1≤N) (B:Finset (Edge (Site (R.family.side (j+1) n)))) (_:B.card≤k),
    let x:=R.family.path.levels.clock.hatBeta (j+1);let τ:=MSbar.Heath.Cottage.room x
    let μ:=Measure.pi (fun _ : Site (R.family.side (j+1) n)=>G.probHaar)
    (OPE.Therm.scene R.family.path N n (j+1)).real {U | μ.real {z | gauge z U ∈ edgeWindow B τ}
      < (x⁻¹)^(Module.finrank ℝ G.Mat*(2*k))} ≤ (sparseCount k:ℝ)*(x⁻¹)^K :=by
  filter_upwards [sparse_physical R simple gate k K] with j pay N n hj B size x τ μ
  haveI : IsProbabilityMeasure (OPE.Therm.scene R.family.path N n (j+1)) := probability (H:=R.family.path) (p:=n) R.T.choice hj
  obtain ⟨m,pos,small,fit⟩:=pay N n hj B size
  have xp:1<x:=R.family.path.levels.fits.delayed _
  apply (measureReal_mono (μ:=OPE.Therm.scene R.family.path N n (j+1)) ?_).trans m
  intro U under hot
  obtain ⟨z,fits⟩:=fit U hot
  have sz:Module.finrank ℝ G.Mat*(2*B.card)≤Module.finrank ℝ G.Mat*(2*k):=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 size)
  have cap:=finite_gauge_mass B U z pos small fits
  rw [show 4*x⁻¹/4=x⁻¹ by ring] at cap
  exact (not_lt_of_ge ((pow_le_pow_of_le_one (inv_nonneg.mpr (zero_lt_one.trans xp).le)
    (inv_le_one_of_one_le₀ xp.le) sz).trans cap)) under

end YM.Integration.FVA1Physical.Wilson

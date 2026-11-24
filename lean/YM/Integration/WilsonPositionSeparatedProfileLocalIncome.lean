import YM.Integration.WilsonPositionSeparatedProfileLocalWave

/-! Regulator-uniform income for the joint reporting wave in the original
upper probability law, with the complete shared exterior in its own L² norm. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileLocalIncome
open Function Set Finset MeasureTheory Lattice RG Wilson Source
open PhysicalNext.Repeat.Legato RGComparison.Core16.Spool RG05Readout RG05Readout.Pulse OPE.Therm
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonRegisteredWindowRestriction WilsonCoherentMeasuredStencil WilsonIncidentRegisteredMass
open WilsonCoherentReportingFrame WilsonReportingPlaquetteWindows WilsonPositionSeparatedProfileLocalWave
open private census from YM.Integration.WilsonReportingPlaquetteWindows
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} {I:Type} [Fintype I] (R:Run G)

private theorem roster (d:I→ℕ) : ∃K:ℝ,0≤K ∧ ∀k N per,k≤N→∀(y:∀i,R.family.label (d i))
    (o:I→Site (R.family.side k per)) (U:Config G (R.family.side k per)),
    ‖∏i,Push.Local.presented (R.family.localSection (d i)) (o i) (R.family.path.rep N per k).p.threshold (y i) U‖≤
      K*(R.family.path.levels.clock.hatBeta k^(reserve R d)*originalMass R d y) := by
  let K:=∑a:WilsonCoherentReportingFrame.Axis R d,wordBound (WilsonCoherentReportingFrame.roster R d a)
  have pos (a:WilsonCoherentReportingFrame.Axis R d) : 0≤wordBound (WilsonCoherentReportingFrame.roster R d a):=
    mul_nonneg (by norm_num) (encouraging _).choose_spec.1
  refine ⟨K,sum_nonneg (fun a _=>pos a),?_⟩
  intro k N per live y o U
  let θ:=(R.family.path.rep N per k).p.threshold
  rw [WilsonCoherentReportingFrame.original]
  calc
    _ ≤ ∑a:WilsonCoherentReportingFrame.Axis R d,‖WilsonCoherentReportingFrame.charge R d θ y a * tally (WilsonCoherentReportingFrame.roster R d a) o U‖ := norm_sum_le ..
    _ ≤ ∑a:WilsonCoherentReportingFrame.Axis R d,K*‖WilsonCoherentReportingFrame.charge R d θ y a‖ := by
      apply sum_le_sum;intro a _
      rw [norm_mul,mul_comm]
      exact mul_le_mul_of_nonneg_right ((word _ _ _).trans (single_le_sum (fun b _=>pos b) (mem_univ a))) (norm_nonneg _)
    _ = K*WilsonCoherentReportingPivot.mass R d θ y:= by rw [WilsonCoherentReportingPivot.mass,mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (scaled R d y per live) (sum_nonneg (fun a _=>pos a))

private theorem rms {α:Type} [MeasurableSpace α] (μ:Measure α) [IsFiniteMeasure μ]
    (H Z:α→ℝ) (eh:Envelope H) (ez:Envelope Z) {A:ℝ} (pA:0≤A) (bound:∀U,‖Z U‖≤A) :
    Real.sqrt (∫U,‖H U*Z U‖^2 ∂μ)≤A*Real.sqrt (∫U,‖H U‖^2 ∂μ) := by
  have square (F:α→ℝ) (e:Envelope F) : Integrable (fun U=>‖F U‖^2) μ := by
    have eq : (fun U=>‖F U‖^2)=(fun U=>F U*F U):=by
      funext U;rw [Real.norm_eq_abs,sq_abs,pow_two]
    rw [eq];exact (e.mul e).integrable μ
  have comp : (∫U,‖H U*Z U‖^2 ∂μ)≤∫U,A^2*‖H U‖^2 ∂μ := by
    apply integral_mono (square _ (eh.mul ez)) ((square H eh).const_mul (A^2))
    intro U;change ‖H U*Z U‖^2≤A^2*‖H U‖^2
    rw [norm_mul,mul_pow,mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (bound U) 2) (sq_nonneg _)
  calc
    _ ≤ Real.sqrt (∫U,A^2*‖H U‖^2 ∂μ) := Real.sqrt_le_sqrt comp
    _ = _ := by rw [integral_const_mul,Real.sqrt_mul (sq_nonneg A),Real.sqrt_sq pA]

variable [DecidableEq I]

theorem original (d:I→ℕ) (φ:Wave I) (compact:HasCompactSupport φ.val) (s:ℕ) :
    ∃K:ℝ,0<K ∧ ∀k N per,k≤N→∀t:ℕ,(t:ℝ)≤R.family.path.levels.clock.hatBeta k^s→
    ∀(y:∀i,R.family.label (d i)) (r:ℝ) (ξ:Cloud I) (χ:ℂ→L[ℝ]ℝ)
      (H:Config G (R.family.side k per)→ℝ),Envelope H→
    let S:=placements (V:=I) R.family k per t
    let c:=fun z:S => φ.val (fun i=>r⁻¹ • (R.family.S.place (z.val i)-ξ i))
    let Z:=fun z:S=>mark R d z.val (R.family.path.rep N per k).p.threshold y (c z) χ
    let μ:=scene R.family.path N per k
    (∑z:S,(Real.sqrt (∫U,‖H U*Z z U‖^2 ∂μ)+‖χ‖*‖c z‖*originalMass R d y*Real.sqrt (∫U,‖H U‖^2 ∂μ)))≤
      K * R.family.path.levels.clock.hatBeta k^(s*(4*Fintype.card I)+reserve R d) *
        (‖χ‖*originalMass R d y) * Real.sqrt (∫U,‖H U‖^2 ∂μ) := by
  obtain ⟨B,bp,full⟩:=roster R d
  obtain ⟨A,hA⟩:=compact.exists_bound_of_continuousOn ((show ContDiff ℝ ∞ φ.val from φ.property).continuous.continuousOn)
  let D:=max 1 A
  have dp:0<D:=zero_lt_one.trans_le (le_max_left ..)
  have wave (x:Cloud I):‖φ.val x‖≤D:=by
    by_cases live:x∈tsupport φ.val
    · exact (hA x live).trans (le_max_right ..)
    · rw [image_eq_zero_of_notMem_tsupport live,norm_zero];exact dp.le
  let C:=(3:ℝ)^(4*Fintype.card I)
  refine ⟨C*(B+1)*D,mul_pos (mul_pos (pow_pos (by norm_num) _) (by linarith)) dp,?_⟩
  intro k N per live t width y r ξ χ H eh S c Z μ
  let b:=R.family.path.levels.clock.hatBeta k
  let M:=originalMass R d y
  let X:=Real.sqrt (∫U,‖H U‖^2 ∂μ)
  have b1:1≤b:=(R.family.path.levels.fits.delayed k).le
  have pp:1≤b^(reserve R d):=one_le_pow₀ b1
  have mp:0≤M:=prod_nonneg fun _ _=>sum_nonneg (fun _ _=>norm_nonneg _)
  have xp:0≤X:=Real.sqrt_nonneg _
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson live
  have one (z:S):Real.sqrt (∫U,‖H U*Z z U‖^2 ∂μ)+‖χ‖*‖c z‖*M*X≤
      (B+1)*b^(reserve R d)*D*(‖χ‖*M)*X := by
    have cb:‖c z‖≤D:=wave _
    have bound (U):‖Z z U‖≤‖χ‖*D*(B*(b^(reserve R d)*M)):=by
      apply (χ.le_opNorm _).trans
      rw [norm_mul]
      calc
        _ ≤ ‖χ‖*(D*(B*(b^(reserve R d)*M))) := mul_le_mul_of_nonneg_left
          (mul_le_mul cb (full k N per live y z.val U) (norm_nonneg _) dp.le) (norm_nonneg _)
        _ = _ := by ring
    have amt:0≤‖χ‖*D*(B*(b^(reserve R d)*M)):=by positivity
    have h:=rms μ H (Z z) eh (legitimate R d z.val _ y (c z) χ).1 amt bound
    have spare : ‖χ‖*‖c z‖*M*X ≤ (‖χ‖*D)*M*X := by gcongr
    calc
      _ ≤ ‖χ‖*D*(B*(b^(reserve R d)*M))*X+(‖χ‖*D)*M*X := add_le_add h spare
      _ ≤ _ := by nlinarith only [mul_nonneg (sub_nonneg.mpr pp) (show 0≤D*(‖χ‖*M)*X by positivity)]
  calc
    _ ≤ ∑ _:S,(B+1)*b^(reserve R d)*D*(‖χ‖*M)*X := sum_le_sum fun z _=>one z
    _ = (Fintype.card S:ℝ)*((B+1)*b^(reserve R d)*D*(‖χ‖*M)*X) := by simp
    _ ≤ (C*b^(s*(4*Fintype.card I)))*((B+1)*b^(reserve R d)*D*(‖χ‖*M)*X) :=
      mul_le_mul_of_nonneg_right (census R.family k per t s b1 width) (by positivity)
    _ = _ := by dsimp only [b,M,X];rw [pow_add];ring

end YM.Integration.WilsonPositionSeparatedProfileLocalIncome

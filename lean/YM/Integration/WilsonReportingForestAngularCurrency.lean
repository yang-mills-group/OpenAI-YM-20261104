import YM.Integration.WilsonReportingForestTagCalendar
import YM.Integration.WilsonRegisteredPlaquetteReading
import YM.Integration.WilsonPositionSeparatedProfileReportingVariation

/-! Pay any prescribed polynomial charge on the excluded registered
plaquettes. The conditional in the conclusion propagates the whole signed
insertion under the original physical law, at every earlier date. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingForestAngularCurrency
open Filter Set Finset MeasureTheory Lattice Wilson RG RG16 OPE.Therm RG05Readout Address Native Pulse
open WilsonPositionSeparatedProfileReportingCut
open PhysicalNext.Repeat.Legato WilsonReportingForestPivots
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)
local notation "A"=>R.family.path.levels

theorem currency (simple:G.Simple) (d q:ℕ) {η:ℝ} (hp:0<η) :
    ∀ᶠ m:ℕ in atTop,∀N,m<N→∀per,let b:=(A).clock.hatBeta (m+1)
    b^d*(b⁻¹)^(d+q+1)≤η*Pert.Asymptotics.regulatorRun R.family N per (m+1)^q := by
  have grow:=(Next.Rank.Station.hat_rate (A) simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [grow.eventually_ge_atTop ((2:ℝ)^q/η)] with m high N live per
  let b:=(A).clock.hatBeta (m+1)
  let y:=R.family.path.β N per (m+1)
  let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
  have one:1≤ b:=((A).fits.delayed _).le
  have bp:0<b:=zero_lt_one.trans_le one
  have core:2^q/η≤ b:=high
  have cost:b⁻¹≤η/(2:ℝ)^q:=by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ bp).mpr (by simpa only [mul_comm η b] using (div_le_iff₀ hp).mp core)
  have trial:=(R.makes.wilson.represents N per (m+1) live).band
  have upper:y≤2*b:=trial.2
  have yp:0<y:=(half_pos bp).trans_le trial.1
  have two:0<2*b:=by positivity
  have root:Real.sqrt y≤2*b:=(Real.sqrt_le_left two.le).mpr
    (upper.trans (by nlinarith only [mul_nonneg two.le (show 0≤2*b-1 by linarith only [one])]))
  have inv:(2*b)⁻¹≤ g:=inv_anti₀ (Real.sqrt_pos.mpr yp) root
  change b^d*(b⁻¹)^(d+q+1)≤η*g^q
  calc
    _=b⁻¹*(b⁻¹)^q:=by rw [pow_succ,pow_add,inv_pow];field_simp
    _≤(η/2^q)*(b⁻¹)^q:=mul_le_mul_of_nonneg_right cost (pow_nonneg (inv_nonneg.mpr bp.le) _)
    _=η*((2*b)⁻¹)^q:=by rw [inv_pow,inv_pow,mul_pow];ring
    _≤η*g^q:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr two.le) inv q) hp.le

/-- A possibly correlated signed field need only have the named bound
on the actual rejected registered union. The weight, period, placements,
true cutoff, and stopping level can be submitted after the onset. -/
theorem tested {I:Type} [Fintype I] (simple:G.Simple)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤ Real.log (RG16.Lambda (A) m))
    (τ:ℕ→ℝ) (d q:ℕ) {η:ℝ} (hp:0<η)
    (rare:∀ᶠ m:ℕ in atTop,∀N per,m<N→∀z:Face (Per (R.family.side (m+1) per)),
      (scene R.family.path N per (m+1)).real (trigger z (τ m))≤
        (((A).clock.hatBeta (m+1))⁻¹)^(d+1+q+1)) :
    ∀ᶠ m:ℕ in atTop,∀N,m<N→∀per (o:I→Site (R.family.side (m+1) per)),
    let E:=⋃i,(House.chilly (G:=G) (tagCells R m per (o i)) (τ m))ᶜ
    let b:=(A).clock.hatBeta (m+1)
    let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
    b^d*(scene R.family.path N per (m+1)).real E≤η*g^q ∧
    ∀{k n:ℕ}(date:n+1≤ m+1)(span:k≤ n)(z:Body)(H:Config G (R.family.side (m+1) per)→ℂ)
      (c:ℝ),0≤ c→Measurable H→(∀U∈E,‖H U‖≤ c*b^d)→
      (∫ V,‖field R.family N per date span (E.indicator H) z V‖
        ∂scene R.family.path N per k)≤ c*(η*g^q) := by
  let n:ℝ:=Fintype.card I
  have n0:0≤ n:=Nat.cast_nonneg _
  have budget:0<η/(n+1):=div_pos hp (by linarith)
  filter_upwards [rare,tag_dates R simple slow,currency R simple (d+1) q budget] with m law cells spend N live per o
  let E:=⋃i,(House.chilly (G:=G) (tagCells R m per (o i)) (τ m))ᶜ
  let b:=(A).clock.hatBeta (m+1)
  let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
  let μ:=scene R.family.path N per (m+1)
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson live
  let a:=(b⁻¹)^(d+1+q+1)
  have bp:0<b:=zero_lt_one.trans ((A).fits.delayed _)
  have a0:0≤ a:=pow_nonneg (inv_nonneg.mpr bp.le) _
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos bp).trans_le (R.makes.wilson.represents N per (m+1) live).band.1))
  have me:MeasurableSet E:=MeasurableSet.iUnion (fun _=>(House.bath (G:=G) _).compl)
  have each (i:I):μ.real ((House.chilly (tagCells R m per (o i)) (τ m))ᶜ)≤ b*a:=
    (House.cool_miss a (law N per live) _).trans (mul_le_mul_of_nonneg_right ((cells per).2 (o i)) a0)
  have total:μ.real E≤ n*(b*a):=calc
    _≤∑i,μ.real ((House.chilly (tagCells R m per (o i)) (τ m))ᶜ):=measureReal_iUnion_fintype_le _
    _≤∑_i:I,b*a:=sum_le_sum (fun i _=>each i)
    _=n*(b*a):=by simp [n,nsmul_eq_mul]
  have invoice:b^d*μ.real E≤η*g^q:=calc
    _≤ b^d*(n*(b*a)):=mul_le_mul_of_nonneg_left total (pow_nonneg bp.le _)
    _=n*(b^(d+1)*a):=by rw [pow_succ];ring
    _≤ n*((η/(n+1))*g^q):=mul_le_mul_of_nonneg_left (spend N live per) n0
    _≤(n+1)*((η/(n+1))*g^q):=mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _=η*g^q:=by field_simp
  refine ⟨invoice,?_⟩
  intro k n date span z H c cp mh bound
  have major (U):‖E.indicator H U‖≤ E.indicator (fun _=>c*b^d) U:=by
    by_cases u:U∈E
    · simpa only [Set.indicator_of_mem u] using bound U u
    · simp [u]
  have global (U):‖E.indicator H U‖≤ c*b^d:=(major U).trans (by
    by_cases u:U∈E
    · simp [u]
    · simpa only [Set.indicator_of_notMem u] using mul_nonneg cp (pow_nonneg bp.le d))
  have fi:Integrable (E.indicator H) μ:=Integrable.of_bound
    (mh.indicator me).aestronglyMeasurable (c*b^d) (ae_of_all _ global)
  have weighted:=actualTransport_weighted_integrable R.family R.makes live
    ((mh.indicator me).aestronglyMeasurable (μ:=prior G _)) global le_rfl
  rw [actualTransport_base R.family R.makes live] at weighted
  have hi:Integrable (E.indicator (fun _=>c*b^d)) μ:=(integrable_const _).indicator me
  exact (WilsonPositionSeparatedProfileReportingVariation.original R.family R.makes N per live date span _ weighted z).trans (calc
    _≤∫U,E.indicator (fun _=>c*b^d) U ∂μ:=integral_mono fi.norm hi major
    _=c*(b^d*μ.real E):=by rw [integral_indicator me,setIntegral_const,smul_eq_mul];ring
    _≤ c*(η*g^q):=mul_le_mul_of_nonneg_left invoice cp)

end YM.Integration.WilsonReportingForestAngularCurrency

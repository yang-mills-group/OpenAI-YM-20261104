import YM.Integration.WilsonOriginalRadialRaySpring
import YM.Work.E09.Scales

/-! The original Wilson spring at its funded radial interpolation fields.
The opening is common to both regulators and every node of the finite panel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalRadialDecoderSpring
open Finset Filter RG Wilson Lattice Labels Source Push.Local Pressure
open PhysicalNext PhysicalNext.Repeat.Legato Pert.Asymptotics WilsonCapturedPrimaryAngles
open WilsonCapturedPrimaryCollar WilsonCapturedPrimaryPaid WilsonFirstReceivedRadialStencil
open WilsonOriginalRadialRaySpring
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "spring" => R.family.path.levels.clock.kernel.penalty

private def quote (T:ℕ):ℝ:=6*((T:ℝ)+1)+3

private theorem crop (b:BudgetPoint) (T:ℕ){g:ℝ}(gp:0<g)(gc:g≤1)
    (fee:1 ≤ b.supportExponent)(cash:Real.log g⁻¹ ≤ b.B):
    1+(radius b (cutoff b g T):ℝ) ≤ quote T*(b.B:ℝ)^2:=by
  let B:ℝ:=b.B
  have one:1 ≤ B:=by change (1:ℝ)≤(b.B:ℝ);exact_mod_cast (show 1≤b.B from b.B_pos)
  have pp:0 ≤ B:=zero_le_one.trans one
  have square:B≤B^2:=le_self_pow₀ one (by decide)
  have two:1≤B^2:=one.trans square
  have l:0≤Real.log g⁻¹:=Real.log_nonneg (one_le_inv_iff₀.mpr ⟨gp,gc⟩)
  have rhs:(cutoff b g T:ℝ)≤((T:ℝ)+1)*B:=by
    have ident:-Real.log (g^T)=(T:ℝ)*Real.log g⁻¹:=by rw [Real.log_pow,Real.log_inv];ring
    have nl:0≤(T:ℝ)*Real.log g⁻¹:=mul_nonneg (Nat.cast_nonneg _) l
    have ns:0≤(T:ℝ)*Real.log g⁻¹/b.supportExponent:=div_nonneg nl b.exponent_pos.le
    change (Nat.ceil (-Real.log (g^T)/b.supportExponent):ℝ)≤_
    rw [ident]
    calc _≤(T:ℝ)*Real.log g⁻¹/b.supportExponent+1:=(Nat.ceil_lt_add_one ns).le
         _≤(T:ℝ)*B+B:=add_le_add ((div_le_self nl fee).trans
           (mul_le_mul_of_nonneg_left cash (Nat.cast_nonneg T))) one
         _=_:=by ring
  have Bpos:0≤(T:ℝ)+1:=by positivity
  have wpos:0≤4*B+2:=by positivity
  have upper:4*B+2≤6*B:=by linarith only [one]
  change 1+((cutoff b g T*(4*b.B+2)+2*b.B:ℕ):ℝ)≤_
  push_cast
  change 1+((cutoff b g T:ℝ)*(4*B+2)+2*B)≤quote T*B^2
  calc _ ≤ 1+((((T:ℝ)+1)*B)*(6*B)+2*B):=by
             gcongr
       _ ≤ B^2+((((T:ℝ)+1)*B)*(6*B)+2*B^2):=by gcongr
       _ = _:=by unfold quote;ring

theorem original (simple:G.Simple)(d target:ℕ):
    ∀ᶠ i in atTop,∀{N per D:ℕ}(_live:i<N),
      1≤(R.family.path.levels.budget i).supportExponent →
      ∀ a∈tests (R.family.labels.level d),∀j≤D,
      let W:=WilsonCapturedPrimaryWeakTrialRadial.field R d N per i target D a j
      (Real.exp (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op i per)
        (R.family.path.β N per (i+1)) W))^2 ≤ 2:=by
  obtain ⟨C,δ,cp,dp,lip⟩:=WilsonPhysicalMarkedDefect.PlaquetteChart.slope G
  let T:=grade target d 1
  let n:=d+6
  let F:ℝ:=∑ a∈tests (R.family.labels.level d),fare R.family.params a
  have wages:(∀a:Probe G d,0≤fare R.family.params a):=fun a=>by unfold fare;positivity
  have fp:0≤F:=sum_nonneg (fun a _=>wages a)
  have qq:0≤quote T:=by unfold quote;positivity
  let expCost:ℝ:=4*spring*(64*C)
  have sp:0<spring:=R.family.path.levels.clock.kernel.penalty_pos
  have ec:0<expCost:=by dsimp only [expCost];positivity
  have logtwo:0<Real.log 2:=Real.log_pos (by norm_num)
  let ε:=min δ (Real.log 2/expCost)
  have ep:0<ε:=lt_min dp (div_pos logtwo ec)
  have rise:=Next.Rank.Station.hat_rate R.family.path.levels simple
  have decay:Tendsto (fun i:ℕ=>(F*(quote T)^n)*((radiusB (H i):ℝ)^(2*n)*temp (H i))) atTop (𝓝 0):=by
    simpa only [mul_zero,Function.comp_apply] using (((Work.E09.radiusB_temp (2*n)).comp rise).const_mul (F*(quote T)^n))
  have small:=decay.eventually (gt_mem_nhds ep)
  filter_upwards [small,RG01.Vacuum.Flat.nextComparable R.family.path.levels simple,
    rise.eventually_ge_atTop (Real.exp 1),rise.eventually_ge_atTop 4] with i low near lg hi
  intro N per D live paid a ha j hj W
  let b:=R.family.path.levels.budget i
  let β:=R.family.path.β N per (i+1)
  let g:=regulatorRun R.family N per (i+1)
  let r:=radius b (cutoff b g T)
  let z:=g^gap target 1*node D j
  have gp:0<g:=RG16.Literal.g_pos R.makes live
  have bp:0<β:=Overlay.beta_positive R.makes.wilson live
  have band:= (R.makes.wilson.represents N per (i+1) live).band
  change H (i+1)/2≤β ∧ β≤2*H (i+1) at band
  have hp:0<H i:=by linarith only [hi]
  have hm:H i ≤ H (i+1):=WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le (Nat.le_succ i)
  have bg:1≤β:=by linarith only [band.1,hm,hi]
  have bs:β≤4*(H i):=by linarith only [band.2,near]
  have gc:g≤1:=by
    change (Real.sqrt β)⁻¹≤1
    exact inv_le_one_of_one_le₀ ((Real.one_le_sqrt).2 bg)
  have inv:g⁻¹≤H i:=by
    change ((Real.sqrt β)⁻¹)⁻¹≤_
    rw [inv_inv,Real.sqrt_le_iff]
    exact ⟨hp.le,bs.trans (by nlinarith only [mul_nonneg hp.le (sub_nonneg.mpr hi)])⟩
  have cash:Real.log g⁻¹ ≤ b.B:=by
    have large:1≤Real.log (H i):=(Real.le_log_iff_exp_le hp).mpr lg
    exact (Real.log_le_log (inv_pos.mpr gp) inv).trans ((le_self_pow₀ large (by decide:2≠0)).trans (Nat.le_ceil ((Real.log (H i))^2)))
  have u:1+(r:ℝ)≤quote T*(b.B:ℝ)^2:=crop b T gp gc paid cash
  have u0:0≤1+(r:ℝ):=by positivity
  have doses:fare R.family.params a≤F:=single_le_sum (fun a _=>wages a) ha
  have billed:b.threshold*fare R.family.params a*(1+(r:ℝ))^n≤ε:=by
    calc _≤b.threshold*F*(quote T*(b.B:ℝ)^2)^n:=mul_le_mul
           (mul_le_mul_of_nonneg_left doses b.threshold_pos.le) (pow_le_pow_left₀ u0 u _)
           (pow_nonneg u0 _) (mul_nonneg b.threshold_pos.le fp)
         _=(F*(quote T)^n)*((radiusB (H i):ℝ)^(2*n)*temp (H i)):=by
           change (temp (H i))*F*(quote T*(radiusB (H i):ℝ)^2)^n=_
           rw [mul_pow,←pow_mul];ring
         _ ≤ _:=le_of_lt low
  have nodep:=node_mem hj
  have z0:0≤z:=mul_nonneg (pow_nonneg gp.le _) nodep.1
  have zs:|z|≤g^2:=by
    rw [abs_of_nonneg z0]
    exact (mul_le_of_le_one_right (pow_nonneg gp.le _) nodep.2).trans (pow_le_pow_of_le_one gp.le gc (by unfold gap;omega))
  have rate:β*g^2=1:=by
    change β*((Real.sqrt β)⁻¹)^2=1
    rw [inv_pow,Real.sq_sqrt bp.le,mul_inv_cancel₀ bp.ne']
  have balance:β*|z|≤1:=(mul_le_mul_of_nonneg_left zs bp.le).trans_eq rate
  have unit:|z|≤1:=zs.trans (pow_le_one₀ gp.le gc)
  have result:=bound (n:=R.family.side i per) R.family.params b 0 r a gp unit bp.le balance cp.le lip (billed.trans (min_le_left ..))
  change β*(∑ e:Bond (R.family.side i per),G.chord (W e)) ≤ 64*C*(b.threshold*fare R.family.params a*(1+(r:ℝ))^n) at result
  let bill:=WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op i per) β W
  have last:2*bill≤Real.log 2:=by
    change 2*(|β| *(2*spring*∑ e:Bond (R.family.side i per),G.chord (W e)))≤_
    rw [abs_of_pos bp]
    calc _ = (4*spring)*(β*∑ e:Bond (R.family.side i per),G.chord (W e)):=by ring
         _ ≤ (4*spring)*(64*C*(b.threshold*fare R.family.params a*(1+(r:ℝ))^n)):=mul_le_mul_of_nonneg_left result (by positivity)
         _ = (b.threshold*fare R.family.params a*(1+(r:ℝ))^n)*expCost:=by dsimp [expCost];ring
         _ ≤ _:=(le_div_iff₀ ec).mp (billed.trans (min_le_right ..))
  change (Real.exp bill)^2≤2
  rw [←Real.exp_nat_mul,←Real.exp_log (by norm_num:0<(2:ℝ))]
  exact Real.exp_le_exp.mpr last

end YM.Integration.WilsonOriginalRadialDecoderSpring

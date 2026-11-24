import YM.Integration.WilsonVacuumPreResetFiniteHeatScale
import YM.Integration.WilsonMarkedIndependentNormalizedSeam

/-! A single physical-period reserve for a marked finite update. Its exponent
absorbs the accrued powers of the fine side without another loss at later dates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentNormalizedScale
open Filter Lattice RG Wilson Precision WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Bank WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open ActualRunAdmissionScales ActualRunAdmissionClock Next.Foundations PhysicalNext.Repeat.Legato
open scoped Topology
variable {G:Gauge}

def rate (A:Levels G)(m p:ℕ):ℝ:=Real.exp (-((A.S.side m p).val:ℝ)/(4096*zz A m))

theorem original (A:Levels G)(simple:G.Simple)(D:ℕ):
    ∀ᶠj:ℕ in atTop,∀p:ℕ,
      let n:ℝ:=(A.S.side j p).val
      let f:ℝ:=(A.S.side (j+1) p).val
      (zz A j*(1+f)^4)^D*(rate A (j+1) p+Real.exp (-n/(512*zz A j)))≤rate A j p:=by
  filter_upwards [WilsonVacuumPreResetFiniteHeatScale.clock A simple,
    OriginalPeriodWindingPrice.period_power A 1,(WardBin.bell A simple).eventually_ge_atTop 2,
    FundedMarkedPeriodPowers.absorb A simple ((9*D+1)*16)] with j clock covered beta receipt p
  let n:ℝ:=(A.S.side j p).val
  let f:ℝ:=(A.S.side (j+1) p).val
  let z:=zz A j
  let z':=zz A (j+1)
  have zn:1≤z:=clock.1
  have hp:0<z:=by linarith
  have hp':0<z':=clock.2.1
  have ratio:z'≤2*z:=clock.2.2
  have hbeta:A.clock.hatBeta j≤n:=by simpa [n] using covered p
  have hn:2≤n:=beta.trans hbeta
  have hf:3*n≤f:=by
    have hL : (3:ℝ)≤(A.S.block j).val := by exact_mod_cast A.S.block_large j
    have size:f=n*((A.S.block j).val:ℝ):=by dsimp [f,n];exact_mod_cast (A.S.oneStep j p).exact_size
    rw [size,mul_comm n];exact mul_le_mul_of_nonneg_right hL (by linarith)
  have hz:z≤f:=by
    have b:1<A.clock.hatBeta j:=by linarith
    have h:z≤A.clock.hatBeta j:=by
      change 1+Real.log (Real.log (A.clock.hatBeta j))≤_
      rw [add_comm]
      exact (Real.add_one_le_exp _).trans ((Real.exp_log (Real.log_pos b)).le.trans
        (Real.log_le_self (by linarith)))
    linarith
  have bill:2*(z*(1+f)^4)^D≤f^(9*D+1):=
    (WilsonVacuumPreResetFiniteHeatScale.power _ _ _ (0:ℝ) (by linarith) hp.le hz le_rfl (by linarith) D rfl).1
  have pay:=(receipt p z⁻¹ (inv_pos.mpr hp) (by simp [z])).2
  have he:f^((9*D+1)*16)≤Real.exp (n/(1024*z)):=calc
    _=(f^((9*D+1)*16)*Real.exp (-(z⁻¹/512)*n))*Real.exp ((z⁻¹/512)*n):=by
      rw [mul_assoc, ←Real.exp_add];simp [neg_mul]
    _≤Real.exp (-((z⁻¹/2)/512)*n)*Real.exp ((z⁻¹/512)*n):=mul_le_mul_of_nonneg_right pay (Real.exp_pos _).le
    _=_:=by rw [←Real.exp_add];congr 1;field_simp;ring
  have small:f^(9*D+1)≤Real.exp (n/(16384*z)):=by
    by_contra! large
    have bad:=pow_lt_pow_left₀ large (Real.exp_pos _).le (show (16:ℕ)≠0 from by decide)
    rw [←pow_mul, ←Real.exp_nat_mul] at bad
    norm_num at bad
    rw [show 16*(n/(16384*z))=n/(1024*z) by field_simp;ring] at bad
    exact (not_lt_of_ge he) bad
  have hOld:n/(16384*z)+ -f/(4096*z')≤ -n/(4096*z):=by
    apply (le_div_iff₀ (by positivity:0<4096*z)).mpr
    field_simp [hp.ne',hp'.ne']
    nlinarith only [mul_le_mul_of_nonneg_left ratio (show 0≤n by linarith),
      mul_le_mul_of_nonneg_left hf hp.le,mul_nonneg (show 0≤n by linarith) hp.le]
  have hNew:n/(16384*z)+ -n/(512*z)≤ -n/(4096*z):=by
    apply (le_div_iff₀ (by positivity:0<4096*z)).mpr
    field_simp [hp.ne'];linarith
  have bound(t:ℝ)(h:n/(16384*z)+t≤ -n/(4096*z)):
      2*((z*(1+f)^4)^D*Real.exp t)≤Real.exp (-n/(4096*z)):=calc
    _≤Real.exp (n/(16384*z))*Real.exp t:=by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right (bill.trans small) (Real.exp_pos _).le
    _≤_:=by rw [←Real.exp_add];exact Real.exp_le_exp.mpr h
  change (z*(1+f)^4)^D*(Real.exp (-f/(4096*z'))+Real.exp (-n/(512*z)))≤Real.exp (-n/(4096*z))
  rw [mul_add]
  linarith only [bound _ hOld,bound _ hNew]

/-- Only a fixed power of the fine side is needed for the normalized cover
singleton's dated charge, uniformly in the UV cutoff and the period. -/
theorem age (W:Credit)(S:Schedule)(m j p:ℕ)(mj:m≤j){z:ℝ}(hz:1≤z):
    W.buy (z+snowP S m j)≤W.buy z*(1+((S.side j p).val:ℝ))^W.d:=by
  have s0:0≤S.scale m:=by simpa only [S.scale_zero] using scales S (Nat.zero_le m)
  have den:((S.denominator j).val:ℝ)≤((S.side j p).val:ℝ):=by
    exact_mod_cast Nat.le_mul_of_pos_left (S.denominator j).val (S.period p).pos
  have hs:S.scale j≤((S.side j p).val:ℝ):=by
    change Real.log (((((S.denominator j).val:ℝ))⁻¹)⁻¹)≤_
    rw [inv_inv];exact (Real.log_le_self (Nat.cast_nonneg _)).trans den
  have positive:0≤z+snowP S m j:=add_nonneg (zero_le_one.trans hz) (sub_nonneg.mpr (scales S mj))
  have arg:z+snowP S m j≤z*(1+((S.side j p).val:ℝ)):=by
    change z+(S.scale j-S.scale m)≤_
    nlinarith only [s0,hs,mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg (S.side j p).val (α:=ℝ))]
  unfold Credit.buy
  rw [mul_assoc,←mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ positive arg _) (zero_le_one.trans W.good)
end YM.Integration.WilsonMarkedIndependentNormalizedScale
end

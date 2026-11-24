import YM.Integration.WilsonMaxwellThermometerPublicFiling
import YM.Integration.WilsonReflectedPhysicalRate
import YM.Integration.WilsonThermometerMarchReference

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedFilingRate
open Filter RG RG17 Lattice Wilson PhysicalNext.Repeat.Legato OPE Trace Trace.Pilot PhysMS
open scoped Topology Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit) (v:ℕ) (wide:0<v)
local notation "k!"=>WilsonReflectedPhysicalRate.launch R simple v
local notation "β!"=>R.family.path.levels.clock.hatBeta
local notation "g!"=>WilsonPositionThermometerSevenFaceRate.temperature (R:=R) simple (B:=v)
local notation "fee!"=>WilsonThermometerMarchReference.fee R.family Finset.univ
include slow wide

/-- A fixed polynomial in the clock at the real launch costs less than any
reserve of this physical collar. All constants precede its regulator. -/
theorem clock (n:ℕ) (D η:ℝ) (D₀:0≤D) (η₀:0<η):
    ∀ᶠr:ℝ in trail,D*(β! (k! r))^n*r^(1/32:ℝ)≤η:=by
  let A:=R.family.path.levels
  let C:=|A.clock.bar|+2*G.slopeConstant
  have sp:0<G.slopeConstant:=Gauge.slopeConstant_pos simple
  have reach:=(WilsonReflectedPhysicalRate.dates R simple slow v wide).2.pace.eventually
    (gt_mem_nhds (show (1:ℝ)<2 by norm_num))
  have flat:=((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n:ℝ) (1/32) (by norm_num)).comp
    PhysMS.to_log_zoom).const_mul (D*C^n)
  have fee:=flat.eventually (gt_mem_nhds (show D*C^n*0<η by simpa using η₀))
  filter_upwards [reach,fee,PhysMS.to_log_zoom.eventually_ge_atTop 1,
    self_mem_nhdsWithin (s:=Set.Ioi (0:ℝ))] with r short cheap large rp
  have rp':0<r:=rp
  have Lpos:0<LogV r:=by linarith
  change R.family.S.scale (k! r)/LogV r<2 at short
  have hi: R.family.S.scale (k! r) ≤ 2*LogV r := ((div_lt_iff₀ Lpos).mp short).le
  have hx:0≤β! (k! r):=le_trans zero_le_one (R.family.path.levels.fits.delayed _).le
  have ha:A.clock.bar≤|A.clock.bar| * LogV r :=(le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) large)
  have hcap:β! (k! r)≤C*LogV r:=by
    change A.clock.bar+G.slopeConstant*R.family.S.scale (k! r) ≤ _
    dsimp [C]; linarith only [ha,mul_le_mul_of_nonneg_left hi sp.le]
  have shape:r^(1/32:ℝ)=Real.exp (-(1/32:ℝ)*LogV r):=by
    rw [Real.rpow_def_of_pos rp']; unfold LogV; rw [Real.log_inv]; congr 1;ring
  change D*C^n*((LogV r)^(n:ℝ)*Real.exp (-(1/32:ℝ)*LogV r))<η at cheap
  rw [Real.rpow_natCast,←shape] at cheap
  calc
    _≤D*(C*LogV r)^n*r^(1/32:ℝ):=by gcongr
    _=D*C^n*((LogV r)^n*r^(1/32:ℝ)):=by rw [mul_pow];ring
    _≤_:=cheap.le

omit wide slow in
private theorem income (E ε:ℝ) (ep:0≤E) (one:ε≤1) (s:Finset (Fin 3)) (k:ℕ):
    let B:=1+2*E*(∑i:Fin 3,|fee! i|)
    (∏i∈s,(1+E*(2*β! k)^ε*fee! i))≤(B*β! k)^3:=by
  intro B
  have hx:1≤β! k:=(R.family.path.levels.fits.delayed _).le
  have hp:1≤2*β! k:=by linarith
  have hb:1≤B:=by
    dsimp [B]; linarith only [mul_nonneg (mul_nonneg zero_le_two ep) (Finset.sum_nonneg (s:=(Finset.univ:Finset (Fin 3))) (fun i _=>abs_nonneg (fee! i)))]
  have hh:1≤B*β! k:=one_le_mul_of_one_le_of_one_le hb hx
  refine (le_abs_self _).trans ?_
  rw [Finset.abs_prod]
  calc
    _≤∏_i∈s,(B*β! k):=by
      apply Finset.prod_le_prod
      · exact fun i _=>abs_nonneg _
      · intro i _
        have rent: |fee! i| ≤ ∑a:Fin 3,|fee! a|:=Finset.single_le_sum (fun a _=>abs_nonneg (fee! a)) (Finset.mem_univ i)
        have powC: (2*β! k)^ε≤2*β! k:=by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hp one
        calc
          |1+E*(2*β! k)^ε*fee! i| ≤ |(1:ℝ)| + |E*(2*β! k)^ε*fee! i|:=abs_add_le _ _
          _=1+E*(2*β! k)^ε* |fee! i|:=by rw [abs_one,abs_mul,abs_mul,abs_of_nonneg ep,
              abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
          _≤1+E*(2*β! k)*(∑a:Fin 3,|fee! a|):=by gcongr
          _≤B*β! k:=by dsimp [B];nlinarith only [hx]
    _=(B*β! k)^s.card:=by simp
    _≤_:=pow_le_pow_right₀ hh (by simpa using Finset.card_le_univ s)

theorem original (h q:ℕ) (E K ε δ:ℝ) (ep:0≤E) (one:ε≤1) (kp:0≤K) (dp:0<δ):
    ∀ᶠr:ℝ in trail,∀N p:ℕ,k! r≤N→∀s:Finset (Fin 3),
      ((∏i∈s,(1+E*(2*β! (k! r))^ε*fee! i))*2^(3-s.card))*(K*r^((h:ℝ)+1/32)) ≤
        δ*|g! r (N,p)|^q*r^(h:ℝ):=by
  let B:=1+2*E*(∑i:Fin 3,|fee! i|)
  let D:=8*K*B^3*2^q
  have bp:1≤B:=by
    dsimp [B]; linarith only [mul_nonneg (mul_nonneg zero_le_two ep) (Finset.sum_nonneg (s:=(Finset.univ:Finset (Fin 3))) (fun i _=>abs_nonneg (fee! i)))]
  have Dp:0≤D:=by dsimp [D];positivity
  filter_upwards [clock R simple slow v wide (q+3) D δ Dp dp,
    self_mem_nhdsWithin (s:=Set.Ioi (0:ℝ))] with r bill rp
  intro N p admissible s
  let x:=β! (k! r)
  let g:=|g! r (N,p)|
  have hx:1≤x:=(R.family.path.levels.fits.delayed _).le
  have xp:0<x:=by linarith
  have gp:0≤g:=abs_nonneg _
  have band:=(WilsonMaxwellThermometerPublicFiling.band R simple v r N p admissible).2
  have scaled:1≤(2*x)*g:=by
    change (Real.sqrt x)⁻¹≤2*g at band
    have sx:Real.sqrt x≤x:=(Real.sqrt_le_iff).mpr ⟨xp.le,by nlinarith [sq_nonneg (x-1)]⟩
    calc
      1=Real.sqrt x*(Real.sqrt x)⁻¹:=(mul_inv_cancel₀ (Real.sqrt_pos.mpr xp).ne').symm
      _≤Real.sqrt x*(2*g):=mul_le_mul_of_nonneg_left band (Real.sqrt_nonneg _)
      _≤(2*x)*g:=by nlinarith [mul_le_mul_of_nonneg_right sx gp]
  have Pp:0≤(B*x)^3:=by positivity
  have marker: ((∏i∈s,(1+E*(2*x)^ε*fee! i))*2^(3-s.card)) ≤ 8*(B*x)^3:=by
    calc
      _≤(B*x)^3*2^(3-s.card):=mul_le_mul_of_nonneg_right (income R E ε ep one s _) (by positivity)
      _≤(B*x)^3*2^3:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)) Pp
      _=8*(B*x)^3:=by ring
  have rp':0<r:=rp
  have fr:0≤r^(1/32:ℝ):=Real.rpow_nonneg rp'.le _
  have hr:0≤r^(h:ℝ):=Real.rpow_nonneg rp'.le _
  change D*x^(q+3)*r^(1/32:ℝ) ≤ δ at bill
  have extra:=mul_le_mul_of_nonneg_left (one_le_pow₀ scaled (n:=q))
    (show 0≤8*(B*x)^3*(K*r^(1/32:ℝ))*r^(h:ℝ) by positivity)
  rw [Real.rpow_add rp']
  calc
    _≤8*(B*x)^3*(K*(r^(h:ℝ)*r^(1/32:ℝ))):=mul_le_mul_of_nonneg_right marker (by positivity)
    _=(8*(B*x)^3*(K*r^(1/32:ℝ))*r^(h:ℝ))*1:=by ring
    _≤(8*(B*x)^3*(K*r^(1/32:ℝ))*r^(h:ℝ))*((2*x)*g)^q:=extra
    _=(D*x^(q+3)*r^(1/32:ℝ))*g^q*r^(h:ℝ):=by
      dsimp [D]; rw [pow_add]; simp only [mul_pow];ring
    _≤δ*g^q*r^(h:ℝ):=by gcongr
end YM.Integration.WilsonMaxwellThermometerNominatedFilingRate

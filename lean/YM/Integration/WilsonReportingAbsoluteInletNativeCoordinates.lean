import YM.Integration.WilsonReportingAbsoluteInletNativeDates
import YM.RGComparison.Core16.Savings
import YM.RGComparison.Core16.Trajectory
import YM.Pert.Asymptotics.RawAxis

/-! Measured native regulator and the filed finite inverse product at the
actual inlet. Every forecast in this module is evaluated on its original
list of dates at the actual N, per. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonReportingAbsoluteInletNativeCoordinates
open Function Filter Finset Real Lattice RG Wilson
open PhysicalNext.Repeat.Legato Pert.Asymptotics RGComparison.Core16
open WilsonReportingAbsoluteInletNativeDates
open scoped Classical Topology BigOperators
variable {G:Gauge}

def shifts (R : Run G) (p k N : ℕ) (i : ℕ) :=
  line R.family.path p k N i-R.family.path.β N p N

theorem temperature (R : Run G) (p k N : ℕ) :
    Descent.offset (shifts R p k N) (regulatorRun R.family N p N)=line R.family.path p k N := by
  funext i
  have bp:0<R.family.path.β N p N:=(half_pos (zero_lt_one.trans (R.family.path.levels.fits.delayed N))).trans_le (R.makes.wilson.represents N p N le_rfl).band.1
  change ((Real.sqrt (R.family.path.β N p N))⁻¹)⁻¹^2+
    (line R.family.path p k N i-R.family.path.β N p N)=_
  rw [inv_inv,Real.sq_sqrt bp.le]
  ring


def finite (R:Run G) (N per t:ℕ) (h:ℕ→ℝ) (l:ℕ):ℝ :=
  R.family.path.β N per N*((∏j∈range (N-(t+l)),h (t+l+j))^2-1)

theorem measured (R:Run G) {t N per:ℕ} (T:Slices R.family.path.levels per) (live:t≤N)
    (h:ℕ→ℝ):
    let x:=shifts R per t N
    let v:=finite R N per t h
    let d:=traversal T live
    let g:=regulatorRun R.family N per N
    (Descent.offset v g+(x-v)=line R.family.path per t N) ∧ (x-v) d.depth=0 := by
  intro x v d g
  have tail:t+d.depth=N:=by change t+(traversal T live).depth=N;rw [traversal_depth];omega
  constructor
  · rw [←temperature R per t N]
    funext l
    change g⁻¹^2+v l+(x l-v l)=g⁻¹^2+x l
    ring
  · have a:x d.depth=0:=by
      change R.family.path.β N per (t+d.depth)-R.family.path.β N per N=0
      rw [tail,sub_self]
    have b:v d.depth=0:=by dsimp only [v,finite];rw [tail];simp
    change x d.depth-v d.depth=0
    rw [a,b,sub_self]

def inverseTemperature (x:ℝ):ℝ:=(Real.sqrt x)⁻¹

theorem squared {x y:ℝ}(x0:0 < x)(y0:0 < y):
    x=y*(inverseTemperature y/inverseTemperature x)^2 ∧ x*(inverseTemperature x)^2=1:=by
  change x=y*((sqrt y)⁻¹/(sqrt x)⁻¹)^2 ∧ x*((sqrt x)⁻¹)^2=1
  simp only [div_inv_eq_mul,mul_pow,inv_pow,sq_sqrt x0.le,sq_sqrt y0.le,←mul_assoc,
    mul_inv_cancel₀ x0.ne',mul_inv_cancel₀ y0.ne',one_mul,and_self]

theorem centered_price (p:ℕ){ε x y g r H:ℝ}(ep:0 < ε)(y0:0 < y)(g0:0 ≤ g)(g1:g ≤ 1)
    (r0:0 < r)(r3:r ≤ 3)(shape:x=y*r^2)(base:x*g^2=1)(band:y ≤ 8*x)
    (book:|r-H| ≤ (min ε 1/64)*g^(p+2)):
    |x-y-y*(H^2-1)| ≤ ε*g^p:=by
  let δ:=min ε 1/64
  have d0:0 ≤ δ:=(div_pos (lt_min ep zero_lt_one) (by norm_num)).le
  have d1:δ ≤ 1:=by dsimp [δ];linarith only [min_le_right ε 1]
  have pow1:g^(p+2) ≤ 1:=pow_le_one₀ g0 g1
  have close:|r-H| ≤ 1:=book.trans ((mul_le_mul_of_nonneg_left pow1 d0).trans (by simpa only [mul_one] using d1))
  have sides:=abs_le.mp close
  have join:|r+H| ≤ 7:=abs_le.mpr ⟨by linarith only [sides.2,r0],by linarith only [sides.1,r3]⟩
  have money:y*g^2 ≤ 8:=by
    calc _ ≤ (8*x)*g^2:=mul_le_mul_of_nonneg_right band (sq_nonneg g)
         _ = 8:=by rw [mul_assoc,base,mul_one]
  have bill : 8*δ*7 ≤ ε:=by dsimp [δ];linarith only [min_le_left ε 1,le_of_lt ep]
  have identity:x-y-y*(H^2-1)=y*(r-H)*(r+H):=by rw [shape];ring
  calc |x-y-y*(H^2-1)| = (y*|r-H|)*|r+H|:=by rw [identity,abs_mul,abs_mul,abs_of_pos y0]
       _ ≤ (y*(δ*g^(p+2)))*7:=mul_le_mul (mul_le_mul_of_nonneg_left book y0.le) join (abs_nonneg _) (by positivity)
       _ = ((y*g^2)*δ*7)*g^p:=by rw [pow_add];ring
       _ ≤ ε*g^p:=mul_le_mul_of_nonneg_right
         (((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right money d0) (by norm_num : (0:ℝ)≤7))).trans bill)
         (pow_nonneg g0 _)

theorem comparable {x y b t:ℝ}(hot:2  ≤  x)(entry:x/2  ≤  b)(endp:0 < t)(exit:t  ≤  2*y)(range:y  ≤  2*x):
    0 < inverseTemperature b ∧ inverseTemperature b  ≤  1 ∧ 0 < inverseTemperature t ∧ inverseTemperature b/inverseTemperature t  ≤  3:=by
  have b1:1  ≤  b:=by linarith only [hot,entry]
  have bp:0 < b:=zero_lt_one.trans_le b1
  have sb:=Real.sqrt_pos.2 bp;have st:=Real.sqrt_pos.2 endp
  have ss:1  ≤  sqrt b:=by simpa only [Real.sqrt_one] using sqrt_le_sqrt b1
  have sq: sqrt t  ≤  3*sqrt b:=by
    have a:=sq_sqrt endp.le;have c:=sq_sqrt bp.le
    have ratio:t  ≤  8*b:=by linarith only [entry,exit,range]
    nlinarith only [a,c,ratio,bp,sb,st]
  refine ⟨inv_pos.mpr sb,?_,inv_pos.mpr st,?_⟩
  · exact (inv_le_one₀ sb).2 ss
  · change (sqrt b)⁻¹/(sqrt t)⁻¹  ≤  3
    rw [div_inv_eq_mul,mul_comm,←div_eq_mul_inv]
    exact (div_le_iff₀ sb).2 sq

variable (R:Run G) (simple:G.Simple)
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "σ" => R.family.S.scale

private theorem eventually_log (c:ℝ) (hc:0≤c):∀ᶠ x:ℝ in atTop,c*Real.log x≤x/2:=by
  have e:0<1/(2*(1+c)):=by positivity
  filter_upwards [Real.isLittleO_log_id_atTop.def e,eventually_ge_atTop (1:ℝ)] with x small hx
  have xp:0≤x:=zero_le_one.trans hx
  have ln:0≤Real.log x:=Real.log_nonneg hx
  have bound:Real.log x≤x/(2*(1+c)):=by
    simpa [Real.norm_eq_abs,abs_of_nonneg ln,abs_of_nonneg xp,div_eq_mul_inv,mul_comm] using small
  have upper:=(le_div_iff₀ (by positivity:0<2*(1+c))).mp bound
  linarith

include simple in
theorem clocks (W:ℕ):∀ᶠ m:ℕ in atTop,∀{N:ℕ},m≤N→σ N-σ m≤W*Real.log (β N) → β N≤2*β m:=by
  have pos:0≤G.slopeConstant:=(Gauge.slopeConstant_pos simple).le
  obtain ⟨k,late⟩:=eventually_atTop.mp ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually
    (eventually_log (G.slopeConstant*(W:ℝ)) (mul_nonneg pos (Nat.cast_nonneg _))))
  filter_upwards [eventually_ge_atTop k] with m km
  intro N mn window
  have reserve:=late N (km.trans mn)
  have change:β N-β m=G.slopeConstant*(σ N-σ m):=by
    change (_+_*(σ N))-(_+_*(σ m))=_
    ring
  have upper:=mul_le_mul_of_nonneg_left window pos
  rw [←mul_assoc] at upper
  linarith

end YM.Integration.WilsonReportingAbsoluteInletNativeCoordinates

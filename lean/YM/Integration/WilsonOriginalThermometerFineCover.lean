import YM.Integration.WilsonOriginalThermometerFineCells
import YM.Pressure.Seeds

/-! Before the ultraviolet cutoff, every occupied cell of the thermometer
pays an adjustable true cover at each finer mesh. Its logarithmic size prices
the fine-date source radii and the transfer back to the reporting date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalThermometerFineCover
open Filter Set Lattice Wilson RG Source Pressure Extraction PhysicalNext.Repeat.Legato
open WilsonSeparatedOriginalThermometerCells
open scoped Topology BigOperators Classical ContDiff

variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "S" => R.family.S

def gap (m i:ℕ) : ℝ := R.family.S.scale i - R.family.S.scale m
def depth (A:ℝ) (m i:ℕ) : ℕ := ⌈(A+1)*(1+Real.log (β i)+gap R m i)⌉₊

private theorem exponent (m i:ℕ) :
    R.family.S.a i * Real.exp (gap R m i)=R.family.S.a m := by
  unfold gap Schedule.scale
  rw [Real.exp_sub,Real.exp_log (inv_pos.mpr (R.family.S.a_pos i)),Real.exp_log (inv_pos.mpr (R.family.S.a_pos m))]
  field_simp [(R.family.S.a_pos i).ne',(R.family.S.a_pos m).ne']

private theorem ordered {m i:ℕ} (hi:m ≤ i) : 0≤gap R m i := by
  apply sub_nonneg.mpr
  apply Real.log_le_log (inv_pos.mpr (R.family.S.a_pos m))
  exact (inv_le_inv₀ (R.family.S.a_pos m) (R.family.S.a_pos i)).mpr (R.family.S.strictAnti.antitone hi)

private theorem log_advance (simple:G.Simple) {m i:ℕ} (hi:m ≤ i) :
    Real.log (β i) ≤ Real.log (β m)+G.slopeConstant*gap R m i := by
  have pos : 1≤β m := (R.family.path.levels.fits.delayed m).le
  have height:0≤gap R m i := ordered R hi
  have asset:0≤G.slopeConstant*gap R m i := mul_nonneg (Gauge.slopeConstant_pos simple).le height
  have diff:β i=β m+G.slopeConstant*gap R m i := by unfold Calendar.hatBeta gap; ring
  calc
    _ ≤ Real.log (β m*(1+G.slopeConstant*gap R m i)) := by
      apply Real.log_le_log (zero_lt_one.trans (R.family.path.levels.fits.delayed i))
      rw [diff,mul_add,mul_one]
      linarith only [le_mul_of_one_le_left asset pos]
    _ ≤ _ := by
      rw [Real.log_mul (zero_lt_one.trans_le pos).ne' (by positivity : 0<1+G.slopeConstant*gap R m i).ne']
      linarith only [Real.log_le_sub_one_of_pos (show 0<1+G.slopeConstant*gap R m i by linarith)]

private theorem cubic {x:ℝ} (hx:0≤x) : (1+x)^3≤27*Real.exp x := by
  have one:1+x≤3*Real.exp (x/3) := by linarith only [Real.add_one_le_exp (x/3)]
  have p:=pow_le_pow_left₀ (show 0≤1+x by positivity) one 3
  rw [mul_pow,← Real.exp_nat_mul] at p
  convert p using 1 <;> norm_num <;> first | ring | rfl

theorem raw (simple:G.Simple) {A:ℝ} (ap:0≤A) {m i:ℕ} (hi:m ≤ i) :
    let b := radiusB (β i)
    (depth R A m i*(4*b+2)+2*b+2:ℕ) ≤
      20*(A+2)*((2+G.slopeConstant)*(1+Real.log (β m))*(1+gap R m i))^3 := by
  let t:=gap R m i
  let u:=1+Real.log (β m)
  let g:=2+G.slopeConstant
  let X:=g*u*(1+t)
  have tp:0≤t := ordered R hi
  have hp:0≤G.slopeConstant := (Gauge.slopeConstant_pos simple).le
  have gp:1≤g := by dsimp [g]; linarith
  have up:1≤u := by dsimp [u]; linarith [Real.log_nonneg (R.family.path.levels.fits.delayed m).le]
  have vp:1≤1+t := by linarith
  have xp:1≤X := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le gp up) vp
  have lip:=log_advance R simple hi
  have big : 1+Real.log (β i)+t ≤ X := by
    change 1+Real.log (β i)+t ≤ g*u*(1+t)
    change Real.log (β i)≤Real.log (β m)+G.slopeConstant*t at lip
    have bound:1+Real.log (β i)+t≤u+(1+G.slopeConstant)*t := by dsimp [u]; linarith
    apply bound.trans
    have base:u≤g*u := le_mul_of_one_le_left (zero_le_one.trans up) gp
    have slope:1+G.slopeConstant ≤g*u :=
      (show 1+G.slopeConstant≤g by dsimp [g];linarith).trans (le_mul_of_one_le_right (zero_le_one.trans gp) up)
    nlinarith only [base,mul_le_mul_of_nonneg_right slope tp]
  have li:0≤Real.log (β i) := Real.log_nonneg (R.family.path.levels.fits.delayed i).le
  have bx : (radiusB (β i):ℝ) ≤2*X^2 := by
    have ce:=Nat.ceil_lt_add_one (sq_nonneg (Real.log (β i)))
    have mix := pow_le_pow_left₀ li (show Real.log (β i)≤X by linarith only [big,tp]) 2
    change (⌈Real.log (β i)^2⌉₊:ℝ)≤2*X^2
    nlinarith only [ce,mix,(one_le_pow₀ xp : 1≤X^2)]
  have dx : (depth R A m i:ℝ) ≤ (A+2)*X := by
    have ce:=Nat.ceil_lt_add_one (show 0≤(A+1)*(1+Real.log (β i)+t) by positivity)
    change (⌈(A+1)*(1+Real.log (β i)+t)⌉₊:ℝ)≤(A+2)*X
    nlinarith only [ce,mul_le_mul_of_nonneg_left big (show 0≤A+1 by positivity), xp]
  have x3:X^2≤X^3 := by simpa only [pow_succ] using (le_mul_of_one_le_right (sq_nonneg X) xp : X^2≤X^2*X)
  have b2:4*(radiusB (β i):ℝ)+2≤10*X^2 := by linarith only [bx,(one_le_pow₀ xp : 1≤X^2)]
  have cover:(depth R A m i:ℝ)*(4*(radiusB (β i):ℝ)+2)+2*(radiusB (β i):ℝ)+2 ≤20*(A+2)*X^3 := by
    have priced:=mul_le_mul dx b2 (by positivity) (by positivity :
      0≤(A+2)*X)
    nlinarith only [priced,bx,x3,(one_le_pow₀ xp : 1≤X^3),mul_nonneg ap (pow_nonneg (zero_le_one.trans xp) 3)]
  intro b
  push_cast
  exact cover

theorem span (simple:G.Simple) {A:ℝ} (ap:0≤A) {m i:ℕ} (hi:m ≤ i) :
    let b := radiusB (β i)
    R.family.S.a i*(depth R A m i*(4*b+2)+2*b+2:ℕ) ≤
      (20*27*(A+2)*(2+G.slopeConstant)^3)*R.family.S.a m*(1+Real.log (β m))^3 := by
  let t:=gap R m i
  let u:=1+Real.log (β m)
  let g:=2+G.slopeConstant
  let X:=g*u*(1+t)
  have tp:0≤t := ordered R hi
  have hp:0≤G.slopeConstant := (Gauge.slopeConstant_pos simple).le
  have gp:1≤g := by dsimp [g]; linarith
  have up:1≤u := by dsimp [u]; linarith [Real.log_nonneg (R.family.path.levels.fits.delayed m).le]
  have vp:1≤1+t := by linarith
  intro b
  have cover:=raw R simple ap hi
  apply (mul_le_mul_of_nonneg_left cover (R.family.S.a_pos i).le).trans
  have total:=mul_le_mul_of_nonneg_left (cubic tp)
    (show 0≤R.family.S.a i*(20*(A+2)*g^3*u^3) by have ha := R.family.S.a_pos i; have hg := zero_le_one.trans gp; have hu := zero_le_one.trans up; positivity)
  calc
    _ = R.family.S.a i*(20*(A+2)*g^3*u^3)*(1+t)^3 := by ring
    _ ≤ _ := total
    _ = _ := by 
      calc
        _ = (20*27*(A+2)*g^3)*(R.family.S.a i*Real.exp t)*u^3 := by ring
        _ = _ := by rw [show R.family.S.a i*Real.exp t=R.family.S.a m from exponent R m i]

theorem price (simple:G.Simple) (k h q:ℕ) {m i:ℕ} (hi:m ≤ i) {a:ℝ} (paid:8≤a) :
    (β i)^k * Real.exp ((h:ℝ)*gap R m i) *
      Real.exp (-(a/8)*(depth R (k+h+q+2:ℕ) m i)) ≤
      ((β m)^q)⁻¹*Real.exp (-gap R m i) := by
  let t:=gap R m i
  let A:ℝ:=((k+h+q+2:ℕ):ℝ)
  let d:=depth R A m i
  have tp:0≤t:=ordered R hi
  have hv:0≤Real.log (β i) := Real.log_nonneg (R.family.path.levels.fits.delayed i).le
  have bmon : β m ≤ β i := by
    have gapEq:β i-β m=G.slopeConstant*t := by dsimp [t,gap,Calendar.hatBeta];ring
    nlinarith only [gapEq,mul_nonneg (Gauge.slopeConstant_pos simple).le tp]
  have logs := Real.log_le_log (zero_lt_one.trans (R.family.path.levels.fits.delayed m)) bmon
  have target : (A+1)*(1+Real.log (β i)+t) ≤ (d:ℝ) := Nat.le_ceil _
  have upper : (k:ℝ)*Real.log (β i)+h*t+q*Real.log (β m)+t ≤ (d:ℝ) := by
    apply LE.le.trans _ target
    change _≤(((k+h+q+2:ℕ):ℝ)+1)*(1+Real.log (β i)+t)
    push_cast
    have x:0≤(k:ℝ):=by positivity
    have y:0≤(h:ℝ):=by positivity
    have w:0≤(q:ℝ):=by positivity
    nlinarith only [hv,tp,x,y,w,mul_nonneg y hv,mul_nonneg x tp,mul_nonneg w tp,mul_le_mul_of_nonneg_left logs w]
  have wd:(d:ℝ)≤(a/8)*d:=le_mul_of_one_le_left (by positivity) (by linarith)
  change (β i)^k*Real.exp ((h:ℝ)*t)*Real.exp (-(a/8)*(d:ℝ))≤_
  calc
    _ = Real.exp ((k:ℝ)*Real.log (β i)+(h:ℝ)*t+(-(a/8))*(d:ℝ)) := by
      simp only [Real.exp_add,Real.exp_nat_mul,Real.exp_log (zero_lt_one.trans (R.family.path.levels.fits.delayed i))]
    _ ≤ Real.exp (-((q:ℝ)*Real.log (β m)) + -t) := by
      apply Real.exp_le_exp.mpr; linarith only [upper,wd]
    _ = _ := by rw [Real.exp_add,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (zero_lt_one.trans (R.family.path.levels.fits.delayed m))]

theorem cells (simple:G.Simple) (φ:Test 3) (legal:tsupport φ⊆conf 3) (A:ℝ) (ap:0≤A) :
    ∃p₀:ℕ,∀ᶠ m:ℕ in atTop,∀ p ≥ p₀,∀ (N i:ℕ) (_ : m ≤ i) (top:i≤N) (r:ℝ), 0<r → r≤1 →
    R.family.S.a m*(RG16.Lambda R.family.path.levels m)^4 ≤ r →
    ∀ z:Fin 3→Site (R.family.side N p),
      weight φ (positions (R:=R) r (N,p)) z≠0 → ∀v w,v≠w →
      depth R A m i*(4*radiusB (β i)+2)+2*radiusB (β i) ≤
        separation ((R.family.S.toDepth top p).parent (z v)) ((R.family.S.toDepth top p).parent (z w)) := by
  obtain ⟨c,cp,posted⟩:=WilsonOriginalThermometerFineCells.actual R φ legal
  let K:=20*27*(A+2)*(2+G.slopeConstant)^3
  have sp:0≤G.slopeConstant :=(Gauge.slopeConstant_pos simple).le
  have kp:0≤K:=by dsimp [K];positivity
  have grow:=Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate R.family.path.levels simple)
  obtain ⟨p₀,accepted⟩:=eventually_atTop.1 posted
  refine ⟨p₀,?_⟩
  filter_upwards [grow.eventually_ge_atTop (K/c)] with m big p large N i hi top r rp cap mesh z live v w off
  have scored:=accepted p large
  apply scored N i top r rp cap z live v w off
  have native:=span R simple ap hi
  let L:=Real.log (β m)
  have lp:0≤L := Real.log_nonneg (R.family.path.levels.fits.delayed m).le
  have enlarge:(1+L)^3≤(2+L)^3 :=pow_le_pow_left₀ (by positivity) (by linarith) 3
  have cm:K≤c*(2+L) := by
    have val:K≤L*c :=(div_le_iff₀ cp).mp big
    linarith only [cp,val]
  have target:K*(1+L)^3≤c*(2+L)^4 := calc
    _ ≤ K*(2+L)^3 := mul_le_mul_of_nonneg_left enlarge kp
    _ ≤ (c*(2+L))*(2+L)^3 := mul_le_mul_of_nonneg_right cm (by positivity)
    _ = _ := by ring
  have fold := mul_le_mul_of_nonneg_left target (R.family.S.a_pos m).le
  have tail := mul_le_mul_of_nonneg_right mesh cp.le
  have finer:= R.family.S.strictAnti.antitone top
  push_cast at native ⊢
  change R.family.S.a m*(2+L)^4≤r at mesh
  change R.family.S.a m*(2+L)^4*c≤r*c at tail
  change _≤K*R.family.S.a m*(1+L)^3 at native
  nlinarith only [native,fold,tail,finer]

end YM.Integration.WilsonOriginalThermometerFineCover
end

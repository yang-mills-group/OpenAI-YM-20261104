import YangMills.WilsonProof.GraphOperands
import YM.MS.Train.Profile
import Mathlib.NumberTheory.Harmonic.GammaDeriv
/-!
 # Coordinates in the supplied MS-bar prescription

 The formal-to-formal comparison uses `MS.Land.MS_Data`, including its ε convention and
 restoration factors. **Lengths and ν**: the real subtraction parameter
 `v` (sometimes `μ` in `YM/MS`, sometimes `ν` in `YM/FVA2`) differs from the MS mass μ.
 It is LOG ν, where ν=exp(γ_E/2) μ / √(4π), μ the *MS mass* in our physical
 units. Use `Teller.logNu`; in particular for EXACT μ=1
 use `logNu 1`. Here are precise checks on complex-parameter normalization `tenorK`
 in the $\epsilon = -z$ prescription and integer-dimensional momentum Wick operators.
 This is not a comparison to a different DR prescription or a claim of
 uniqueness of analytic continuation by specializing to integer dimensions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Teller
open Set Filter Function Finset MeasureTheory Metric Real
open MS MS.Arc MS.Plane MS.Koszul MS.Heat MS.Plane.Flux MS.Landau MS.Arts MS.Plane.Wire MS.Rock MS.Rock.Path MS.Plum MS.Alps MS.Garment MS.Color MS.Shine MS.Hem MS.Hem.Mell MS.Pearl MS.Train
open scoped Topology ContDiff Interval

/-- The corresponding ν for the given (positive) MS mass μ. -/
def nuOf (μ:ℝ):ℝ:= Real.exp (Real.eulerMascheroniConstant/2) * μ / Real.sqrt (4*Real.pi)

lemma transported (μ:ℝ)(H:0<μ): logNu μ=Real.log (nuOf μ):= by
 rw [logNu,nuOf,Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity:(Real.exp (Real.eulerMascheroniConstant/2))≠0) H.ne', Real.log_exp,Real.log_sqrt (by positivity)]; ring
lemma logged (μ t:ℝ)(H:0<μ): logNu (Real.exp (-t)*μ)=logNu μ -t:= by
 rw [logNu,Real.log_mul (by positivity) (by positivity),Real.log_exp, logNu]; ring
-- use positive real base avoiding branch changes.
def dim (ε:ℂ):ℂ:= 4-2*ε
def zeta : ℝ:= Real.exp Real.eulerMascheroniConstant / (4*Real.pi)
def factor (μ:ℝ)(ε:ℂ) : ℂ:= ((↑(zeta*μ^2):ℂ)^ε)/( ( (2*Real.pi:ℝ ):ℂ )^(dim ε))
-- the def integrated multiplicative is
lemma units (μ:ℝ)(H:0<μ)(z:ℂ): tenorK z (logNu μ)= factor μ (-z)*( (π:ℂ)^z/(Complex.Gamma (z+1)) ):= by
 rw [ Train.restore_tape, factor ]; let a:= zeta*μ^2; let b:=2*π; have ha:0<a:=by unfold a zeta; positivity
 have hb:0<b:= by unfold b; positivity
 have he : (room:ℂ)=Complex.exp ( ( -4:ℂ )*( Real.log b:ℂ ) ):= by
    rw [← Complex.ofReal_ofNat (n:=4), ← Complex.ofReal_neg, ← Complex.ofReal_mul,←Complex.ofReal_exp]; congr 1
    rw [neg_mul,Real.exp_neg]
    have hx: Real.exp (4*Real.log b)=b^4:= by simpa [Real.exp_log hb] using Real.exp_nat_mul (Real.log b) 4
    rw [hx]; rfl
 have ht: Real.log a=2* logNu μ:= by unfold a zeta logNu; rw [Real.log_mul (by positivity) (by positivity),Real.log_div (by positivity) (by positivity), Real.log_exp,Real.log_pow]; push_cast; ring
 unfold Train.feeD; change (room:ℂ)* Complex.exp (_ *(( Real.log π-2*Real.log b:ℝ ):ℂ)) / _ * _ = ((a:ℂ)^(-z)/(b:ℂ)^(dim (-z)))*_
 rw [ he, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'), Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne'), Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr pi_pos.ne'), ← Complex.ofReal_log ha.le, ← Complex.ofReal_log hb.le, ← Complex.ofReal_log pi_pos.le, ht]; push_cast
 unfold dim; rw [div_eq_mul_inv, div_eq_mul_inv,div_eq_mul_inv, ← Complex.exp_neg ]; rw [mul_right_comm _ ( (Complex.Gamma (z+1))⁻¹ )]; rw [ ← mul_assoc ]; simp only [← Complex.exp_add]; congr 2; ring
lemma calibration : logNu 1= (Real.eulerMascheroniConstant - Real.log (4*Real.pi))/2:= by rw [logNu,Real.log_one,zero_add]

-- At every positive auxiliary integer count & at zero, restores the concrete momentum-integration weight. No spectator traces on an output.
lemma pitch (μ:ℝ)(H:0<μ)(n:ℕ): tenorK n (logNu μ)* ( MS.Arc.pitch n :ℂ )=factor μ (-( n:ℂ )):= by
 rw [units μ H, Arc.pitch,Complex.Gamma_nat_eq_factorial,Complex.cpow_natCast, inv_pow]; push_cast; have H: ( ( Nat.factorial n:ℕ ):ℂ )≠0:= by exact_mod_cast Nat.factorial_ne_zero _
 have h: (π:ℂ) ^ n ≠0:= pow_ne_zero _ (by exact_mod_cast pi_pos.ne'); field_simp
variable {G:Gauge}{U:Rip G}{F:Mob G}{m n:ℕ}
lemma momentum (μ:ℝ)(HM:0<μ)(h:Knot false U)(hp:Form0 false F)(he:m≤n)(l:Legs (Shore G m)): unitC n (logNu μ) U F m l= factor μ (-(n:ℂ)) * Ccy (U n) (F n) (Px n) (Arts.lift he l):= by
 rw [unitC, LinearMap.smul_apply, Wave.port_spec (Town_nat n) _ h hp]; change tenorK n (logNu μ)*_=_; rw [ Path.reg_proj hp.price h.price hp.token h.token he l,Complex.real_smul, ← mul_assoc,pitch μ HM]
end YM.FVA2.Teller

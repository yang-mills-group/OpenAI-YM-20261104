import YM.FVA2.Recall.Splitting
/-!
 # Every unscaled analytic cost insertion, per letter or Wilson term.
 Action pre-change with full Haar/chart and witness. (No change to the specified trajectory.)
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Recall.Move
open Function Set Filter Finset MeasureTheory FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open StationaryMarks MultiGauge.Stack PowerSeries MarkovChain Warp Splice OpenSlots
open Paint Euler PertExtension PertExtension.Series Radial GaussianScore FVA2.Facade
open Tested OpenSlots.Quadratic -- ensure χ cost
open scoped Classical Topology BigOperators ContDiff
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (m:Move)
def weight (w:PowerSeries ℝ): PowerSeries ℝ:= m.sponsor w * m.q^2
lemma pace (w:PowerSeries ℝ): constantCoeff (m.sponsor w)=constantCoeff w:= by
 have he:Through 0 w (C (constantCoeff w)):= by intro i hi; obtain rfl:i=0:= (by omega); simp
 have hx:= m.sponsor_neat he 0 le_rfl; simpa using hx
lemma lead (w:PowerSeries ℝ): term (m.weight w) 0=term w 0:= by
 unfold weight term; rw [ coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply ];
 rw [map_mul,pace,map_pow, m.initial,one_pow,mul_one]

variable (w:PowerSeries ℝ)(f:E→ℝ)
local notation "ℚ₀"=> OpenSlots.Quadratic.genesis w f
local notation "Q"=> OpenSlots.Quadratic.P (ℚ₀)
local notation "ξ"=> Move.weight m w
local notation "Ψ"=> Move.walk m E
omit [FiniteDimensional ℝ E] in
lemma tenure : Q=(OpenSlots.Quadratic.genesis (m.weight w) f).P:= by
 apply records (genesis w f); intro x; rw [OpenSlots.Quadratic.native,OpenSlots.Quadratic.native,m.lead] -- args
lemma heat_start (x:E): (fuel Q).val x=term w 0 * (coeff 2 (Stack.rise f)).val x:= by unfold rise; rw [heat, show Q x x=(ℚ₀).flourish x from rfl,native,coeff_mk]; change _=term w 0 * jet f 2 x; ring
lemma fuel_cost : (fuel Q)= (term w 0) • coeff 2 (Stack.rise f):= by
 apply Subtype.ext; funext x; exact heat_start ..
variable (h:Stationary f)
include h
lemma upstream : X^2 *OpenSlots.pay w f= -(carry w * Stack.rise f)+ X^2 * C (fuel Q):= by
 apply Stack.into; intro x; simp_rw [_root_.map_add,_root_.map_mul,map_pow,map_neg,map_mul,show Stack.read x X=X from PowerSeries.map_X .., rayPrice f h, load,show Stack.read x (C (fuel Q))= C ((fuel Q).val x) from PowerSeries.map_C ..,heat_start,← Stack.reading_term,read_rise ]; rw [mul_add,mul_neg,mul_left_comm,naturalRise f h x]
lemma downstairs : OpenSlots.pay (m.weight w) f= Ψ (OpenSlots.pay w f)+ carry m.drift * C (fuel Q) := by
 apply PowerSeries.X_pow_mul_cancel (k:=2); obtain hu := congr_arg (Ψ) (upstream w f h); rw [upstream (m.weight w) f h,← tenure, mul_add]; simp_rw [map_add,map_mul,map_neg,map_pow,m.walk_c,m.walk_x] at hu
 rw [ map_mul,carries, service_value _ _ (homo_fuel Q), any_rise,mul_pow] at hu
 unfold Move.weight Move.drift; simp_rw [ _root_.map_mul, _root_.map_pow, map_sub, map_one, _root_.map_pow ]
 let p:= carry (E:=E) m.p; let q:=carry (E:=E) m.q; have hx:p*q=1:= by unfold p q; rw [←map_mul carry,m.old,map_one];
 let z:=OpenSlots.pay w f; let s:= carry (E:=E) (m.sponsor w); let Y:= Ψ z; let r:= rise f; let C':= C (fuel Q);
 change X^2 *p^2 *Y = -(s * r)+ X^2 * p^2 * (q^2*C') at hu
 have htq:p^2*q^2=1:= by rw [←mul_pow, hx,one_pow]
 rw [ show X^2 * p^2 * (q^2*C')=X^2*C' from (?_ : _) ] at hu; swap; · rw [mul_assoc (X^2), ← mul_assoc (p^2), htq,one_mul]
 change -(s*q^2*r)+ X^2*C' =X^2*Y + X^2*((1-q^2)*C')
 -- ring modulo htq
 linear_combination q^2 * -hu + ( X^2 * Y ) * htq -- check sign

lemma renew : chip (m.weight w) f= adjust m Q * Ψ (chip w f):= by
 unfold chip; rw [m.downstairs w f h,compose_two _ _ ( m.constantLead _|>.trans (OpenSlots.stipend w f h) ) (zero_rise ..), exponent_p _ _ (OpenSlots.stipend w f h), mul_comm (adjust m Q)]; rfl

section cloth
variable {G:Gauge} (J:Precision.ChartRatio G)(I:Type)[Fintype I]
omit h
lemma light : m.walk (I→G.Color) (tissue J I)= tissue J I:= by unfold tissue; rw [map_mul,m.fix,m.any_rise]
end cloth
end YM.FVA2.Recall.Move

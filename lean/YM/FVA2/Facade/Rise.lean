import YM.FVA2.Facade.Holding
import YM.RGComparison.Core16.Therm.Pulse
/-!
 # Ray action accounting, including higher formal coupling entries

 Evaluate weights in a genuine common coupling parameter. Keep exact
 correspondence to the explicit exponent and Hessian, not solving coefficients
 by an outside analytic-stage assumption. Taking an arbitrary finite (or full)
 Taylor alignment of coupling entries suffices up through that order. These are
 all ordinary unmarked prices; any shared cylinders are multiplied *before*
 applying the eventual conditional contractions.
 -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.FVA2.Facade
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter MeasureTheory PertExtension Precision Lattice GaussianScore PowerSeries Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic RGComparison.Core16
open PertExtension.Series Tested Radial
open scoped Classical Topology BigOperators ContDiff ENNReal
variable {M E F:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup M][NormedSpace ℝ M] [NormedAddCommGroup F][NormedSpace ℝ F]
variable [FiniteDimensional ℝ E][FiniteDimensional ℝ M] [FiniteDimensional ℝ F]
section
variable (V: M→ℝ) (h: Stationary V) (W:PowerSeries ℝ)(x:M)
local notation "π"=> Stack.read x (Stack.rise V)

lemma takeDrop (n:ℕ) (u: Ticket M) (x:M) : Stack.read x (Stack.drop n u)= Stack.drop n (Stack.read x u):= PowerSeries.ext fun i=>by rw [reading_term,Stack.drop,Stack.drop,coeff_mk,coeff_mk,reading_term] -- inspect drop
lemma negdrop {R:Type}[CommRing R](n:ℕ)(u:PowerSeries R): Stack.drop n (-u)=-(Stack.drop n u):=PowerSeries.ext fun i=> by unfold Stack.drop; rw [map_neg, coeff_mk, coeff_mk, map_neg]
lemma driveTerm : Stack.read x (advancing V)= -(Stack.drop 2 π)+ PowerSeries.C (jet V 2 x) :=by
 unfold advancing; rw [map_add,takeDrop,map_neg,negdrop]; congr 1; unfold Stack.read; rw [PowerSeries.map_C]; unfold Stack.rise; rw [coeff_mk]; rfl
include h
lemma naturalRise : X^2 * Stack.drop 2 π=π:= Stack.recover 2 π (fun i hi=> by rw [read_rise]; interval_cases i; exact (jet_zero ..|>.trans h.base0); exact h.base1 _)
lemma oneMore : Stack.drop 1 π= X * Stack.drop 2 π:= by
 conv_lhs=>rw [← naturalRise V h x]
 rw [show X^2*Stack.drop 2 π= X^1*(X*Stack.drop 2 π) by ring, Stack.drop_mul]
omit h in
lemma splitRate : W= PowerSeries.C (term W 0)+ X * Stack.drop 1 W:= by
 apply PowerSeries.ext; intro i; rw [map_add]; cases i with
 | zero=> simp [Stack.drop,Tested.term]
 | succ i=> rw [coeff_C, if_neg (by simp), zero_add,← pow_one (X (R:=ℝ)), coeff_X_pow_mul', if_pos (by omega), Stack.drop, coeff_mk, Nat.add_comm]; rw [show (1+i-1)=i by omega]
lemma rayPrice : Stack.read x (pay W V)= -(W* Stack.drop 2 π)+ PowerSeries.C (term W 0 * jet V 2 x):= by
 unfold pay; rw [map_add,map_mul,map_mul,rollThrough,load,takeDrop,oneMore V h x,driveTerm]; unfold Tracks.shadow; change _+(-Stack.drop 1 W)*(X*Stack.drop 2 π)=_; nth_rw 3 [splitRate W]; rw [map_mul (PowerSeries.C : ℝ→+* PowerSeries ℝ)]; ring
end

section spectrum
variable {ι:Type}[Fintype ι] (g:ι→E×F→ℝ)(w:ι→ℝ→ℝ)(y:F) (d:E)
variable (hp:∀ i,Stationary (g i)) (hg:∀ i,ContDiffAt ℝ ω (g i) 0) (hw:∀ i,ContDiffAt ℝ ω (w i) 0)
local notation "A"=> LinearMap.fst ℝ ℝ E
 def flank (y:F): ℝ × E→ₗ[ℝ] E×F := (LinearMap.snd ℝ ℝ E).prod ((LinearMap.id (R:=ℝ) (M:=ℝ)).smulRight y ∘ₗ LinearMap.fst ℝ ℝ E)
local notation "T"=> flank (E:=E) y
 def prime (i:ι): ℝ × E→ ℝ:= (w i ∘ A) * (g i ∘ (flank y))
 def raise : ℝ × E→ℝ := Therm.pedal + ∑ i, prime g w y i
 def amount (W:ℝ→ℝ): PowerSeries ℝ:= Stack.read (1:ℝ) (Stack.rise W)

include hw hg
lemma hotter (i:ι) : ContDiffAt ℝ ω (prime g w y i) 0:= (leaned A (hw i)).mul (leaned T (hg i))
lemma hotter_all : ContDiffAt ℝ ω (Facade.raise g w y) 0:= by
 refine Therm.pedal_smooth.contDiffAt.add ?_; rw [show ∑ i,prime g w y i=fun x=>∑ i,prime g w y i x from funext fun x=>Finset.sum_apply ..]; exact ContDiffAt.sum (fun i _=>hotter g w y hg hw i)
@[simp] lemma atRate (s:ℝ)(i) : Stack.read (s,d) (Stack.rise (prime g w y i))= Stack.read s (Stack.rise (w i))* Stack.read (T (s,d)) (Stack.rise (g i)):= by
 rw [prime,rise_mul ((leaned A (hw i)).of_le le_top) ((leaned T (hg i)).of_le le_top),map_mul,←Vault.climbing A ((hw i).of_le le_top), ←Vault.climbing T ((hg i).of_le le_top), caught,caught]; rfl

lemma para (s:ℝ)(k:ℕ) : jet (raise g w y) k (s,d)= jet Therm.pedal k (s,d)+∑ i,jet (prime g w y i) k (s,d):= by
 let p:= prime g w y
 unfold Facade.raise; rw [Inherit.plus k Therm.pedal_smooth.contDiffAt (show ContDiffAt ℝ ω (∑ i,p i) 0 from by rw [show ∑ i,p i=fun x=> ∑ i,p i x from funext fun _=>Finset.sum_apply ..]; exact ContDiffAt.sum (fun i _=>hotter g w y hg hw i))];
 simpa only [one_smul, one_mul] using congr_arg (jet Therm.pedal k (s,d)+·) (jetSum Finset.univ (fun _=>1) p (hotter g w y hg hw) k (s,d))

-- determine the fixed ambient Hessian. `Steep` supplied later using native costs
variable (p:ι→PowerSeries ℝ)(N:ℕ)(h:∀i, Through N (amount (w i)) (p i))
include hp
private lemma prior (s:ℝ)(i:ι) : let W:= Stack.read s (Stack.rise (w i)); let V:= Stack.read (s,d) (Stack.rise (prime g w y i)); let v: PowerSeries ℝ:= Stack.read (T (s,d)) (Stack.rise (g i)); V=X^2 * (W * Stack.drop 2 v):= by
 dsimp only; rw [← mul_left_comm (Stack.read _ _), naturalRise (g i) (hp i), atRate g w y d hg hw]
private lemma base2 (i:ι) (s:ℝ): jet (prime g w y i) 2 (s,d)= term (amount (w i)) 0 * jet (g i) 2 (T (s,d)) := by
 rw [←read_rise, prior g w y d hp hg hw, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
 -- interpret coefficient 0
 simp_rw [coeff_zero_eq_constantCoeff_apply, map_mul]
 unfold amount term; rw [← coeff_zero_eq_constantCoeff_apply (Stack.read _ _), ←coeff_zero_eq_constantCoeff_apply (Stack.drop _ _),read_rise,Stack.drop, coeff_mk,read_rise, Nat.add_zero, read_rise]; simp
lemma steadies : Stationary (Facade.raise g w y):= by
 refine ⟨(hotter_all g w y hg hw).of_le le_top,?_, fun ⟨s,x⟩=>?_⟩
 · unfold raise; simp [Pi.add_apply,Finset.sum_apply,prime,Function.comp_apply,(hp _).base0,Therm.pedal]
 rw [para g w y x hg hw s,(Therm.double Therm.pedal_smooth.contDiffAt (s,x) (fun t=>by unfold Therm.pedal; simp; ring)).1,zero_add]; apply Finset.sum_eq_zero; intro i _; rw [←read_rise,prior g w y x hp hg hw, coeff_X_pow_mul', if_neg (by norm_num)]

include h
lemma initialQ (s:ℝ) : jet (Facade.raise g w y) 2 (s,d)= s^2+(totalPrice (fun i=> Quadratic.genesis (p i) (g i))).flourish (T (s,d))/2 := by
 rw [para g w y d hg hw s,(Therm.double Therm.pedal_smooth.contDiffAt (s,d) (fun t=>by unfold Therm.pedal; simp; ring)).2]; change s^2 + _= _; rw [bought,Finset.sum_div]; congr 1;
 apply Finset.sum_congr rfl; intro i _; rw [base2 g w y d hp hg hw, Quadratic.native, show term (amount (w i)) 0= term (p i) 0 from h i 0 (Nat.zero_le _)]; ring
omit h
omit hp hg hw in
private lemma pedalSquare (s:ℝ): Stack.read (s,d) (Stack.rise Therm.pedal)= PowerSeries.C (s^2)*X^2:= by
 let f:= Therm.pedal (E:=E)
 have hh(t:ℝ): f (t • (s,d))= t^2 • (s^2):= by unfold f Therm.pedal; simp; ring
 have hp := directions (f:=f) (Therm.pedal_smooth.contDiffAt.of_le le_top) (s,d); simp_rw [hh] at hp
 have h:=hp.unique (Aspiration.single (s^2) 2)
 apply PowerSeries.ext; intro i; rw [read_rise,coeff_C_mul,coeff_X_pow]
 have ht:=congr_fun h i; by_cases he: i=2<;>simpa [he, ne_comm] using ht

omit hp hg hw in
lemma flank_one : T (1,d)= (d,y):= by simp [flank]
lemma focused (i:ι): Stack.read ((1:ℝ),d) (advancing (prime g w y i)) = Stack.read (d,y) (pay (amount (w i)) (g i)):= by
 rw [driveTerm,prior g w y d hp hg hw,base2 g w y d hp hg hw, Stack.drop_mul, rayPrice (g i) (hp i),flank_one]; rfl
lemma concentrated : Stack.read ((1:ℝ),d) (advancing (raise g w y))= Stack.read (d,y) (∑ i,pay (amount (w i)) (g i)):= by
 apply PowerSeries.ext; intro i;
 rw [map_sum,map_sum,levels]; unfold Radial.layers; by_cases h:i=0
 · simp_rw [h]; simp [Warp.wrap (stipend _ _ (hp _)) _]
 rw [if_neg h]; simp_rw [←focused g w y d hp hg hw,levels,Radial.layers,if_neg h];
 rw [para g w y d hg hw 1 (i+2), ←read_rise, pedalSquare, coeff_C_mul, coeff_X_pow, if_neg (by omega),mul_zero,zero_add]; simp_rw [add_zero,Finset.sum_neg_distrib]

end spectrum
end YM.FVA2.Facade

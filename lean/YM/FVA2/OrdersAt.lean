import YM.FormalOPE.RG10.OpenSlots.Passenger
import YM.RGComparison.Core16.Silk.Roll

/-!
# Root normalization on an open coarse configuration versus `Fk.read`

Germ-algebra theorem. No bounds on a `Steady`, no claim a cutoff estimate is
uniform. Ray test is taken *at exactly the same y*, not y=0 or Π at a root.
No chart choice induced by the observable. `Bk.OrdersAt` can be applied both
to analytic first Wilson kernel and to the Gaussian/interaction integrals
used to apply the rule later (appropriate post-square perturbative
weight must still be supplied at those later steps).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Bk
open Filter Topology Function Finset MeasureTheory
open FormalOPE.RG10 FormalOPE.RG10.MarkovChain OpenSlots
open RGComparison.Core16 RGComparison.Core16.Lumen Lumen.Planet
open PertExtension Precision Inherit Push.Loops PertExtension.Chart Lattice RG
    PertExtension.GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
    Papers Warp Line Roof Router Quadratic
open scoped Classical Topology ContDiff BigOperators InnerProductSpace
variable {G:Gauge} {I D : Type}[Fintype I]
local notation "E"=> Direction G I
local notation "X"=> ℝ× E
variable {Y : Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y]

def sideChange (y:Y) : ℝ × E →ₗ[ℝ] E × Y where
   toFun a:= (a.2, a.1 • y)
   map_add' _ _:= Prod.ext rfl (add_smul ..)
   map_smul' _ _ := Prod.ext rfl (mul_smul ..)


variable (y:Y) (J: ChartRatio G) (H : LocalRatio J) (S : Direction G I × Y → ℝ) (hS:ContDiffAt ℝ ω S 0)
local notation "Q"=> genesis (1:PowerSeries ℝ) S
local notation "μ"=> tangent G I

section squares
-- quadratic Fk onscreen
variable {K K' : Type}[NormedAddCommGroup K][NormedSpace ℝ K][NormedAddCommGroup K'][NormedSpace ℝ K']
variable (u:Quadratic (K×K')) [FiniteDimensional ℝ K](h:(core u).RespectsPrice)
lemma annul (x:K)(z:K'): u.P (skew u h z,z) (x,0)=0:= by
   rw [show (skew u h z,z) = (skew u h z,0)+(0,z) by simp, map_add, LinearMap.add_apply ];
   change (core u).P (-(h.inner.inverse (changing u z))) x +changing u z x=_
   rw [show (core u).P=h.inner.P from Exists.choose_spec h, map_neg]; simp [Law.applies]
lemma saddle_sum (x:K)(z:K') : u.flourish (Quadratic.center u h (x,z))= (Quadratic.recordQ h.inner).flourish x + (Quadratic.reduced u h).flourish z:= by
   rw [Quadratic.centering, show (x+ _,z)=(x,0)+(skew u h z,z) by simp only [Prod.mk_add_mk,zero_add], biplus,u.side (x,0), annul,mul_zero, add_zero];
   change (core u).flourish x+_= (recordQ h.inner).flourish x+u.flourish (skew u h z,z); unfold Quadratic.flourish; rw [show (core u).P=h.inner.P from Exists.choose_spec h]; rfl
end squares
-- exact y and S; the assumption Q can also be supplied from full inherited precision
variable (U:Quadratic ((Direction G I)×Y)) (hU:∀ a,U.flourish a=2*jet S 2 a) (h:(Quadratic.core U).RespectsPrice)
local notation "SaddleΓ" => h.inner

abbrev phasePad (w:X) : ℝ:= w.1 ^ 2
lemma pad_j (i:ℕ)(x:X) : jet phasePad i x= if i=2 then phasePad x else 0:= by
   have hx:= directions (show ContDiffAt ℝ ∞ phasePad (0:X) from contDiffAt_fst.pow 2) x;
   have he (t:ℝ) : phasePad (t • x)= t^2 • phasePad x:= mul_pow ..
   simp_rw [he] at hx; exact congr_fun (hx.unique (Aspiration.single (phasePad x) 2)) i

abbrev mount (v:X):= phasePad v+ S (sideChange y v)
local notation "T"=> (mount y S)
include hS
omit [FiniteDimensional ℝ Y] in
lemma side_s : ContDiffAt ℝ ω (S ∘ sideChange y) 0:= (show ContDiffAt ℝ ω S (sideChange y 0) from (sideChange y).map_zero.symm ▸ hS).comp 0 ((LinearMap.toContinuousLinearMap (sideChange (I:=I) (G:=G) y)).contDiff.contDiffAt) -- unused hS?
include hS
lemma montant (i:ℕ) (a:X) : jet T i a=(if i=2 then phasePad a else 0) + jet S i (sideChange y a):= by
   rw [show T=(phasePad+S ∘ sideChange y) from rfl, Inherit.plus i (show ContDiffAt ℝ ω phasePad (0:X) from contDiffAt_fst.pow 2) (side_s y S hS),pad_j,← read_rise,← read_rise (sideChange y a), ←Vault.climbing _ (hS.of_le le_top), caught ]; -- infty naming
lemma paid_advance (x:E) : Stack.read (1,x) (exponential (advancing T))= Stack.read (x,y) (exponential (advancing S)):= by
   apply PowerSeries.ext; intro i;
   have he: boost (sideChange y) (advancing S)=advancing T:= by
     apply Stack.into; intro a; apply PowerSeries.ext; intro i; rw [caught,levels,levels];
     unfold Radial.layers; simp_rw [montant y S hS]; by_cases he:i=0
     · simp [he]
     simp [he]
   rw [← he, ← boost_exp, caught,show sideChange y ((1:ℝ),x)=(x,y) from Prod.ext rfl (one_smul ..)]

-- y-scale volume and denominator
omit hS
abbrev ambient (y:Y) (U:Quadratic (E×Y))(h:(core U).RespectsPrice):= Real.exp (-1-(reduced U h).flourish y / 2) * ((∫ t, h.inner.kern t ∂(tangent G I))* jacobian J (0:E))
include H
omit [FiniteDimensional ℝ Y] in
lemma positive_amount : 0 < ambient J y U h:= by
    have ht:0< overhead J I:= official H
    apply mul_pos (Real.exp_pos _); refine mul_pos (integral_exp_pos ?_) ht
    have hz:=h.inner.integrable_entry (A:=1) μ (Zone.Invoice.const (1:ℝ)) continuous_const; rwa [one_mul] at hz

abbrev rayBlock : Ticket (Direction G I × Y):= boost (LinearMap.fst ℝ (Direction G I) Y) (tissue J I) * exponential (advancing S)
lemma rayStart : incline (rayBlock J S):= pool (preserve_boost _ (awake H)) (Stack.initial _)

include H hS hU
lemma assigned (O:E × Y → ℝ) (hp: ContDiffAt ℝ ω O 0) (i:ℕ) :
    Therm.stamp μ ((jacobian J (U:=I) ∘ Prod.snd)*(O ∘ sideChange y)) T 1 i =
    ambient J y U h * coeff i (Stack.read y (uptake U μ h (rayBlock J S * Stack.rise O))) := by
    let W:= rayBlock J S; let A:=W * Stack.rise O; let S':= SaddleΓ; let D:=skew U h y; let B:= jacobian J (0:E); let p:= Real.exp (-1-(reduced U h).flourish y/2)
    let O':X→ℝ:= (jacobian J (U:=I) ∘ Prod.snd)*(O∘sideChange y)
    have hA : 0 < B:= (official (I:=I) H)
    have he(x:E): integrandSeries T O' i (1,x)= B*coeff i (Stack.read (x,y) A):=by
       change _=B * coeff i (Stack.read (x,y) (rayBlock J S*Stack.rise O)); symm;
       rw [← coeff_C_mul];
       have hM : Stack.read (1,x) (Stack.rise O')*Stack.read (1,x) (exponential (advancing T)) = PowerSeries.C B * Stack.read (x,y) A:=by
           unfold A W rayBlock O';
           have h1 : ContDiffAt ℝ ∞ ((jacobian J (U:=I)) ∘ Prod.snd) (0:X):=ContDiffAt.comp (0:X) (g:=jacobian J) (f:=Prod.snd) ((PertExtension.Chart.Ratio.jacobian_smooth H).of_le le_top) contDiffAt_snd
           rw [map_mul,map_mul,caught,tissue,map_mul,rollThrough,rise_mul h1 ((side_s y _ hp).of_le le_top),map_mul,←Vault.climbing _ (hp.of_le le_top),paid_advance y S hS,caught]
           rw [show sideChange y (1,x)=(x,y) from Prod.ext rfl (one_smul ..), show Stack.read ((1:ℝ),x) (Stack.rise (jacobian J ∘ Prod.snd)) = Stack.read x (Stack.rise (jacobian J)) from ?_]; swap
           · rw [← show boost (LinearMap.snd ℝ ℝ E) (Stack.rise (jacobian J))=Stack.rise (jacobian J ∘ Prod.snd) from Vault.climbing (LinearMap.snd ℝ ℝ E) (Chart.Ratio.jacobian_smooth H |>.of_le le_top), caught]; rfl
           rw [show jacobian J (0:E)= B from rfl,← mul_assoc,← mul_assoc,← mul_assoc, ← map_mul, mul_inv_cancel₀ hA.ne',map_one,one_mul]; rw [mul_assoc, mul_assoc, mul_comm (Stack.read _ (rise O))]; rfl
       rw [show rayBlock J S*Stack.rise O=A from rfl, ← hM,coeff_mul]; simp_rw [read_rise,business]; rfl
    have hc(x:E) : kernel T (1,x+D)= p * S'.kern x:= by
       unfold kernel; rw [montant y S hS]; unfold p S' Law.kern; rw [← Real.exp_add]; apply congr_arg; change -( (if (2:ℕ)=2 then ((1:ℝ)^2) else 0)+ _)= _; rw [if_pos rfl,one_pow]; have hE:= (hU (sideChange y ((1:ℝ),x+D))).trans _root_.rfl -- simplify
       have hP:= saddle_sum U h x y; rw [show Quadratic.center U h (x,y)=sideChange y (1,x+D) from Prod.ext rfl (one_smul ..).symm] at hP; rw [hP] at hE; change h.inner.P x x+(U.reduced h).flourish y= _ at hE; linarith
    rw [Therm.stamp_moment]; let cook(x:E):= normTerm O' T i (1,x);
    change ∫ x,cook x ∂μ= _* coeff i (Stack.read y _); rw [← integral_add_right_eq_self cook D, Stack.reading_term];
    have hdX : (coeff i (uptake U μ h A)).val y = (integrateP U μ h (coeff i A)).val y:= by unfold uptake throughPrice; simp_rw [AddMonoidHom.coe_mk, ZeroHom.coe_mk,coeff_mk]; rfl
    have hd: (∫ x,S'.kern x∂μ)≠0:=by have ha:= positive_amount y J H U h; intro hh; unfold ambient at ha; change 0<p*((∫ x,S'.kern x∂μ)*B) at ha; rw [hh,zero_mul,mul_zero] at ha; exact lt_irrefl _ ha
    change _= _ * ((coeff i (uptake U μ h A)).val y); rw [hdX, integrateP_display U μ h];
    have hh (x:E): cook (x+D)= (p*B)*((coeff i A).val (x+D,y) * S'.kern x):=by
        unfold cook normTerm; rw [hc,he,Stack.reading_term]; ring
    simp_rw [hh,integral_const_mul]; unfold Law.average; change _= p*((∫ x,S'.kern x∂μ)*B) *((∫ x,(coeff i A).val (x+D,y)* S'.kern x∂μ)/(∫ x,S'.kern x∂μ)); field_simp

variable {n : Side} {A k L R T' : Type}[Fintype k] [Fintype L] [Fintype R]
variable {Ξ:Shelf G A L} {P : Planet Ξ n I k T'} (hP : Fk.rise P =ᶠ[𝓝 0] mount y S)
local notation "ℶ"=> ambient J y U h

include hP
lemma valued (O:E × Y→ℝ)(hp:ContDiffAt ℝ ω O 0)(p:Stuff G I R)(ψ:(R→G.Color)→ℝ)
    (he:ψ ∘ Fk.scene p =ᶠ[𝓝 0] O ∘ sideChange y) : PowerSeries.mk (Fk.harvest P J p ψ) =
    PowerSeries.C ℶ * Stack.read y (uptake U μ h (rayBlock J S * Stack.rise O)):= by
    apply PowerSeries.ext; intro i; rw [coeff_mk, coeff_C_mul]; unfold Fk.harvest; rw [show Fk.cap J p ψ=(jacobian J ∘ Prod.snd) * (ψ∘ Fk.scene p) from rfl,Therm.stamp_protect μ _ _ (f':=mount y S) (K':=(jacobian J ∘ Prod.snd)*(O∘ sideChange y)) (EventuallyEq.mul (EventuallyEq.refl _ _) he) hP]; exact assigned y J H S hS U hU h O hp i
lemma savings_y : PowerSeries.mk (Fk.birth P J) = PowerSeries.C ℶ * Stack.read y (uptake U μ h (rayBlock J S)) := by
   have he:= valued y J H S hS U hU h hP (1:E×Y→ℝ) contDiffAt_const Fk.vacant (fun (_:Empty→G.Color)=>1) (EventuallyEq.refl _ _); rw [rise_one,mul_one] at he; exact he
theorem OrdersAt (O:E × Y→ℝ)(hp:ContDiffAt ℝ ω O 0)(p:Stuff G I R)(ψ:(R→G.Color)→ℝ)
    (he:ψ ∘ Fk.scene p =ᶠ[𝓝 0] O ∘ sideChange y) (r:ℕ) :
    PowerSeries.mk (Fk.read P J p ψ r)= Stack.drop r (Stack.read y (fit U μ h (Stack.rise O) (rayBlock J S))):= by
   let Z:=PowerSeries.mk (Fk.birth P J); let W:=rayBlock J S; let X':=Stack.read y (fit U μ h (Stack.rise O) W)
   have ht:PowerSeries.mk (Fk.harvest P J p ψ)=Z*X':= by
       unfold Z X'; rw [valued y J H S hS U hU h hP O hp p ψ he,savings_y y J H S hS U hU h hP,mul_assoc (PowerSeries.C ℶ) , ← map_mul, fit_eq _ _ _ _ _ (rayStart J H S)]
   have hC : constantCoeff Z≠0:=by
       unfold Z; rw [savings_y y J H S hS U hU h hP,map_mul,constantCoeff_C, ←coeff_zero_eq_constantCoeff_apply, reading_term, coeff_zero_eq_constantCoeff_apply, show constantCoeff (uptake U μ h (rayBlock J S)) = 1 from Quadratic.upright U μ h (rayStart J H S)]; change ℶ*1≠0; rw [mul_one]; exact (positive_amount y J H U h|>.ne')
   have heV i: Fk.valuation P J p ψ i= coeff i X':= by unfold Fk.valuation Tested.divide term; rw [ht]; change coeff i (Z*X'*Z⁻¹)=_; rw [mul_right_comm,PowerSeries.mul_inv_cancel _ hC,one_mul]
   apply PowerSeries.ext; intro i; rw [coeff_mk,Stack.drop,coeff_mk]; exact heV _
end YM.FVA2.Bk

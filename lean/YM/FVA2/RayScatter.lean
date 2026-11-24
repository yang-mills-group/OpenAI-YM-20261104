import YM.FVA2.PriceTower
import YM.RGComparison.Core16.Therm.Scroll
import YM.FormalOPE.RG10.Sync.Layout
import YM.FormalOPE.RG10.MultiGauge.Membership
/-!
# Fk Therm cost on an open X-bearing vs RG10 Splice/Quadratic.fit and Route.Bulk

Coarse field full y. At each y and order. Haar has not been frozen before doing
this evaluation; applies to `jacobian × O` priced term and to common conditional
denominator. Distinguish coarse Hessian cost (Boltzmann factor), which depends
on y and has to cancel before identifying centered answers. `absolute` proves a
formula for it. `digital_ink` gives direct view *with* the covariance Law and
mean from `Bank.score`; state from x first then Point V. no uniform premise.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.RayScatter
open Filter Topology Function PowerSeries Lattice MeasureTheory FormalOPE.RG10
open FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice
open FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router
open FormalOPE.RG10.OpenSlots
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested
open GaussianScore RGComparison.Core16.Therm
open scoped Topology ContDiff Classical BigOperators
variable {E F: Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]

-- angled.Beard with artificial pure t² `b` restoring below
abbrev tax (b:ℝ)(x:ℝ× E):= b*x.1^2
def recover (y:F) : ℝ × E →L[ℝ] E × F := (ContinuousLinearMap.snd ℝ ℝ E).prod ((ContinuousLinearMap.fst ℝ ℝ E).smulRight y)
def charge (p:E×F→ℝ)(b:ℝ)(y:F): ℝ × E→ℝ:= tax b+p ∘ recover y
omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] in
lemma charge_hot (b:ℝ)(y:F){p:E×F→ℝ}(h:ContDiffAt ℝ ω p 0): ContDiffAt ℝ ω (charge p b y) 0:= ContDiffAt.add (contDiffAt_const.mul (contDiffAt_fst.pow 2)) (( (map_zero (recover y (E:=E))).symm ▸ h : ContDiffAt ℝ ω p ((recover y) 0)).comp _ (recover y (E:=E)|>.contDiff.contDiffAt))

lemma tax_free (b:ℝ)(i:ℕ)(x:E) : jet (tax b) i (1,x) = if i=2 then b else 0:= by
    have he: Aspiration (fun t:ℝ=> tax b (t • ((1:ℝ),x))) (fun i=>if i=2 then b else 0):=by
        convert Aspiration.single b 2 using 1; funext v; change b*(v*1)^2= _; rw [mul_one]; exact mul_comm .. 
    exact congr_fun ( (directions (f:=tax b) (ContDiffAt.mul contDiffAt_const (contDiffAt_fst.pow 2)) (1,x)).unique he ) i
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma recovery (y:F)(u:E): recover y ((1:ℝ),u)=(u,y):= by simp [recover]
omit [FiniteDimensional ℝ F] in
lemma cost_law {p:E×F→ℝ}(b:ℝ)(h: ContDiffAt ℝ ω p 0)(y:F)(i:ℕ)(x:E) : jet (charge p b y) i (1,x)=(if i=2 then b else 0)+jet p i (x,y):= by
    unfold charge; rw [ Inherit.plus (a:=tax b) _ ( contDiffAt_const.mul (contDiffAt_fst.pow 2)) (( (map_zero (recover y (E:=E))).symm ▸ h : ContDiffAt ℝ ω p ((recover y) 0)).comp _ (recover y (E:=E)|>.contDiff.contDiffAt)), tax_free,GermLaplace.jet_pull (recover y) _ (h.of_le le_top), recovery ]
omit [FiniteDimensional ℝ F] in
lemma layers_push {p:E×F→ℝ}(b:ℝ)(h: ContDiffAt ℝ ω p 0)(y:F)(i:ℕ)(x:E): layers (charge p b y) i (1,x)=layers p i (x,y):= by
    unfold Radial.layers; by_cases he:i=0; · subst i; simp
    rw [if_neg he,if_neg he,cost_law b h]; split; omega; simp
omit [FiniteDimensional ℝ F] in
lemma expquota {p:E×F→ℝ}(b:ℝ)(h: ContDiffAt ℝ ω p 0)(y:F)(i:ℕ)(x:E): expsum (layers (charge p b y)) i i (1,x)= expsum (layers p) i i (x,y):= by
    unfold expsum; apply Finset.sum_congr rfl; intro j hj; congr 1; clear hj; induction j generalizing i with | zero=> simp [Zone.TaylorPow]| succ j ih=> unfold Zone.TaylorPow Zone.mul; exact Finset.sum_congr rfl (fun t ht=> congr_arg₂ (·*·) (ih t.1) (layers_push b h y t.2 x))
variable (p:E×F→ℝ)(W:Quadratic (E×F))
namespace square
variable (hp:(Quadratic.core W).RespectsPrice)(y:F)
-- block Hessian.V charge (W not assumed nondegenerate on full). need exact drag laws.
local notation "Λ"=>Quadratic.RespectsPrice.inner hp
local notation "σ"=> W.skew hp y
local notation "Ω"=> W.reduced hp
omit [FiniteDimensional ℝ F] in
lemma cross_zero (x:E): W.P (σ,y) (x,0)=0:= by
     rw [show (σ,y)=(σ,0)+ (0,y) from by simp,map_add]; let v:= W.changing y
     change (Quadratic.core W).P (W.skew hp y) x+v x=0
     rw [ show (Quadratic.core W).P=(Λ).P from hp.choose_spec ]; change (Λ).P (- (Λ).inverse v) x + _ = _; rw [map_neg, LinearMap.neg_apply,(Λ).applies]; simp
omit [FiniteDimensional ℝ F] in
lemma size_inner (x:E): W.flourish (Quadratic.center W hp (x,y))=(Λ).P x x+(Ω).flourish y:= by
     rw [Quadratic.centering, show (x+σ,y)=(x,0)+(σ,y) from by simp,Quadratic.biplus, W.side (x,0), cross_zero W hp y, mul_zero, add_zero]; change (Quadratic.core W).P x x+(W.flourish (σ,y))= _; rw [show (Quadratic.core W).P=(Λ).P from hp.choose_spec]; rfl
end square

variable {p} (b:ℝ)(h:ContDiffAt ℝ ω p 0)(Q: Quadratic (E×F))(hy:∀ v,Q.flourish v=2*jet p 2 v)(hp:(Quadratic.core Q).RespectsPrice)
variable (y:F) [MeasurableSpace E][BorelSpace E](μ: Measure E)[Measure.IsAddHaarMeasure μ]
local notation "L"=> Quadratic.RespectsPrice.inner hp
local notation "ξ"=> Q.skew hp y
local notation "Φ"=> expneg -- test macro

def basePower (b:ℝ) := Real.exp (-b - (Q.reduced hp|>.flourish y)/2)*ExactTower.capital L μ
omit [FiniteDimensional ℝ F] in
lemma base_power_pos : 0<basePower Q hp y μ b:= mul_pos (Real.exp_pos _) ( ExactTower.venture L μ )
-- keep coeff convolution ordinary
variable (k:E × F→ℝ)(hk:ContDiffAt ℝ ω k 0)
include h hy hk
theorem absolute : PowerSeries.mk ( RGComparison.Core16.Therm.stamp μ (k ∘ recover y) (charge p b y) 1 ) = C (basePower Q hp y μ b)* Stack.read y (Q.uptake μ hp (Stack.rise k*Stack.exponential (Stack.advancing p))) := by
    let A := Stack.rise k*Stack.exponential (Stack.advancing p); let s:= Real.exp (-b-(Q.reduced hp|>.flourish y)/2); apply PowerSeries.ext; intro i
    let r:= coeff i A; let c:= basePower Q hp y μ b; have he(x:E): integrandSeries (charge p b y) (k∘ recover y) i (1,x)= r.val (x,y):= by
        rw [ ← show coeff i (Stack.read (x,y) A)= _ from Stack.reading_term A i _, show A= _ from (rfl:A=Stack.rise k*Stack.exponential (Stack.advancing p)), _root_.map_mul (Stack.read _), coeff_mul, integrandSeries, Zone.mul]; exact Finset.sum_congr rfl (fun j _=> by rw [ Stack.read_rise, GermLaplace.jet_pull (recover y) _ (hk.of_le le_top), Stack.business, recovery,expquota b h ])
    rw [coeff_mk,stamp_moment, coeff_C_mul,Stack.reading_term]; change _= c * (coeff i (Q.uptake μ hp A)).val y; unfold Quadratic.uptake throughPrice; simp only [ AddMonoidHom.coe_mk, ZeroHom.coe_mk, coeff_mk,LinearMap.toAddMonoidHom_coe ]; rw [Quadratic.integrateP_display]; change _=c * (L).average μ (fun x=>r.val (x+ξ,y)); simp_rw [normTerm,he]; rw [ ← MeasureTheory.integral_add_right_eq_self (f:=fun x:E=> r.val (x,y)* kernel (charge p b y) (1,x)) (g:=ξ) ]; have ht(x:E): kernel (charge p b y) (1,x+ξ) = s * (L).kern x:= by
         have he:= square.size_inner Q hp y x; rw [ Quadratic.centering,hy ] at he; unfold s kernel Law.kern; rw [ ← Real.exp_add,cost_law b h,if_pos rfl ]; congr 1; linarith
    have hx:= ( ExactTower.venture L μ ).ne'; unfold Law.average; simp_rw [ht, mul_left_comm (r.val _),integral_const_mul,Pi.mul_apply]; change _ = (s*ExactTower.capital L μ) * (_ / (ExactTower.capital L μ)); field_simp

omit h hy hk
section digital
open Route Sync
variable {I K:Type}[Fintype I][Fintype K] (T:Ticket (E×F))(L1: Layout I E)(L2: Layout K F)
local notation "ℓ"=> across L1 L2
local notation "q"=> Sync.matrix (B:=K) (Γ:=hp.inner) L1 LinearMap.id
-- generic real post to actual route, income.Open 
omit [FiniteDimensional ℝ F] in
lemma moving : digital L2 (Q.uptake μ hp T)= Bulk.move ( Sync.matrix (Γ:=hp.inner) L1 LinearMap.id ) ( digital (across L1 L2) (boost (Q.center hp) T)):= by
    let W:= (boost (Q.center hp) T); rw [ Sync.moving hp.inner L1 L2 LinearMap.id μ, show boost (accompany (LinearMap.id (R:=ℝ) (M:=E))) W = W from ?_]; swap; · apply Stack.into; rintro ⟨x,y⟩; rw [caught]; rfl
    apply congr_arg; apply PowerSeries.ext; intro i; unfold W Quadratic.uptake simpleMean boost throughPrice; simp only [ AddMonoidHom.coe_mk,ZeroHom.coe_mk, coeff_mk,PowerSeries.coeff_map ]; rfl

def logarithm : Channel (I⊕K):= digital ℓ (decant (boost (Q.center hp) T))
omit [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E] in
lemma root0 : coeff 0 (logarithm Q hp T L1 L2)=0:=by unfold logarithm digital; rw [ PowerSeries.coeff_map, coeff_zero_eq_constantCoeff_apply, onceBlank, map_zero ]
omit [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E] in
lemma exp_log (Ht: incline T): advance (logarithm Q hp T L1 L2)=digital ℓ (boost (Q.center hp) T) := by unfold logarithm; rw [ ← authority,soluble (preserve_boost _ Ht)]
omit [FiniteDimensional ℝ F] in
lemma generates (Ht: incline T): Bulk.income ( Sync.matrix (Γ:=hp.inner) L1 ( d:=LinearMap.id ) ) ( logarithm Q hp T L1 L2 )=digital L2 (Q.uptake μ hp T):= by rw [moving Q hp μ T L1 L2,Route.Bulk.income,exp_log Q hp T L1 L2 Ht]
-- use *same covariance matrix* on all tickets.
omit [FiniteDimensional ℝ F] in
theorem digital_ink (A:Ticket (E×F))(hT: incline T):
    digital L2 ( Q.fit μ hp A T )= Bulk.transfer (Sync.matrix (Γ:=hp.inner) L1 LinearMap.id) ( digital ℓ (boost (Q.center hp) A)) (logarithm Q hp T L1 L2) := by
    unfold Quadratic.fit Bulk.transfer; rw [generates Q hp μ T L1 L2 hT, exp_log Q hp T L1 L2 hT,←map_mul (digital ℓ),← map_mul (boost _),← moving Q hp μ (T * A) L1 L2, map_mul]; congr 1
    let S:=Q.uptake μ hp T; have hs : incline S:= Quadratic.upright Q μ hp hT; change digital L2 (Return S)=_
    apply ((worth hs).map (digital L2)).mul_left_cancel; rw [←map_mul (digital L2),spend_it hs,map_one,PowerSeries.mul_invOfUnit]
    unfold digital; rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,coeff_zero_eq_constantCoeff_apply,hs,map_one]; rfl
end digital
end YM.FVA2.RayScatter

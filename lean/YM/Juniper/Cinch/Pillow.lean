import YM.Juniper.Cinch.Twill
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Cinch
open Function Filter Metric Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Averaging
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G: Gauge}{c:Side}{X:Support c}{W:BudgetPoint}
open Quotes Finset Ovens Ovens.Pipes Progress.DirectedRecipe Payments Further.LogJets Pressure
open Extra.Iteration Song
set_option quotPrecheck false
variable (X:Pipes G c){A B:Tap G c}{b δ v w τ σ : ℝ}(T:Pylon W c)

abbrev Gains (c:Side):= ℕ⊕Seat c
def badge (c:Side): ℕ≃ Gains c := numbering _
local notation "N"=> badge c
abbrev spread {Y:Type}(f:ℕ→ Y) (g:Seat c→ Y):= Sum.elim f g

def adobe : Pipes G c:= ⟨spread X.reg T.map ∘ N,X.kernel,spread X.softer (fun i=> (T.map i).support) ∘ N, fun i=> (by change (Sum.elim X.softer (fun i=> (T.map i).support) (N i)).Nonempty; cases N i; exact X.sites _; exact ⟨_,(T.map _).anchor⟩)⟩
def flint (t:ℝ) (E:Tap G c):Tap G c:= ⟨spread E.regular (Pylon.gap t) ∘ N, E.forced, spread E.logarithm (Pylon.graft T t) ∘ N⟩
def jam (k:Equiv.Perm ℕ) (v:Signed)(t:Site c): Equiv.Perm ℕ:= (N).trans ((Equiv.sumCongr k (Seat.move (n:=c) v t)).trans (N).symm)
lemma jam_works (k:Equiv.Perm ℕ)(v:Signed)(t:Site c)(i:ℕ): N (jam k v t i)=Equiv.sumCongr k (Seat.move v t) (N i):= (N).apply_symm_apply _
local notation "Y"=> adobe X T
variable (t:ℝ)
local notation "E"=> flint T t A
variable (h: Payments.Fittings A X W)
local notation "F₀"=> (X.pours A)
local notation "f"=> spread X.reg T.map
local notation "q"=> spread A.regular (Pylon.gap t)
local notation "s₀"=> spread X.softer (fun i=> (T.map i).support)
local notation "ρ"=> spread A.logarithm (Pylon.graft T t)
include h
lemma charges : ((Y).pours E).RegularFamily W:= by
    have he(i : Gains c): W.Regular (f i).support (q i) ∧ q i 1=0 ∧ (Nonwrapping (f i).support (f i).site → ∀ x y, IsAffineDirection (f i).site x → IsAffineDirection (f i).site y → logHessian (q i) x y=0):= by
       rcases i with i|i; exact ⟨h.regular.smooth i,h.regular.at_flat i,h.regular.vanish i⟩; exact ⟨Pylon.charger T i,Pylon.origin _,fun ht=> (T.high (i.unwrapped ht)).elim⟩
    exact ⟨fun i=> (he (N i)).1,fun i=> (he (N i)).2.1,fun i=> (he (N i)).2.2⟩
lemma gliss (s:Signed)(b:Site c): Nonempty (((Y).pours E).Moves s b) := by
    obtain ⟨u⟩:= h.moves s b; let F:= jam u.ep s b
    have he(i:ℕ): (f (N (F i))).site=affine s b (f (N i)).site ∧ (f (N (F i))).support=image (affine s b) (f (N i)).support ∧ q (N (F i))=(q (N i)) ∘ pull s b := by
       unfold F; rw [jam_works]; cases N i
       · exact ⟨u.reg_site _,u.reg_support _,funext (u.valuesE _)⟩
       next i=> exact ⟨(T.pays b s i t (G:=G)).1,(T.pays b s i t (G:=G)).2.1,(T.pays b s i t (G:=G)).2.2.1⟩
    exact ⟨F,u.kp,fun i=>(he i).1,fun i=>(he i).2.1,u.forced_support,u.forced_inventory,u.forced_tests,fun i U=> congr_fun ((he i).2.2) U,u.valuesK⟩ -- nested record nonempty?
lemma gates : Payments.Fittings E Y W:= by
    have he(i:Gains c): Trio.Tidy W (s₀ i) (ρ i) ∧ ∀ V, ρ i V≠0 → ¬ Healthy W.threshold (s₀ i) V := by cases i; exact ⟨⟨h.looks _,h.reads _,h.steady _⟩,h.visits _⟩; exact Pylon.tender T _ _
    refine ⟨charges X T t h,⟨h.support.sym,h.support.symtest,h.support.meas,h.support.meas_test,h.support.reads,h.support.reads_test,h.support.permit⟩,gliss X T t h,fun i=> (he (N i)).2,fun i=> (he (N i)).1.invariant,fun i=> (he (N i)).1.uses,fun i=> (he (N i)).1.borel,fun s b=>?_⟩
    obtain ⟨η,hη,he'⟩:= h.carries s b; let F:=jam η s b
    have hξ(i:ℕ): s₀ (N (F i))=image (affine s b) (s₀ (N i)) ∧ ρ (N (F i))=ρ (N i) ∘ pull s b := by
       unfold F; rw [jam_works]; cases N i; exact ⟨hη _, funext (fun i=> he' i _)⟩; next i=> exact ⟨(T.pays b s i t (G:=G)).2.1,(T.pays b s i t (G:=G)).2.2.2⟩
    exact ⟨F,fun i=>(hξ i).1, fun U i=> congr_fun (hξ i|>.2) U⟩
-- exactly +1 exponent. ticket both some expenses even δ=0.
def forecastW (G:Gauge)(c:Side)(P:BudgetPoint)(u:ℝ):ℝ:= (Fintype.card (Seat c):ℝ)*(Pylon.droop G P u*Real.exp ((P.supportExponent+1)*(turnB P c+81:ℕ)))
local notation "ψ"=> Pylon.droop G W t
local notation "g"=> forecastW G c W t
omit h in
lemma wings {r: Seat c→ℝ}(he : ∀ i, 0 ≤ r i ∧ r i ≤ ψ * Real.exp ((W.supportExponent+1)*coverNumber W.B (T.map i).support)): SumBudget r g:= by
    have hp:= Pylon.vessel T (G:=G) t (1,0); apply budget_finite fun i=> (he i).1; apply le_trans (Finset.sum_le_sum («g»:=fun i=> ψ * Real.exp ((W.supportExponent+1)*(turnB W c+81:ℕ))) (fun i _=>?_)); · rw [sum_const,card_univ,nsmul_eq_mul]; rfl
    have hz:= W.exponent_pos; exact (he i).2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (by change ((coverNumber W.B (Seat.spread i T.corner)):ℕ) ≤ _; rw [Seat.visit_count]; exact T.short)) (by linarith))) hp.1.1)
omit h in
lemma fledged (he: (F₀).EBound W b) : ((Y).pours E).EBound W (b+g):= by
   obtain ⟨k,hk,h⟩:= he; let r:=spread k (fun _:Seat c=> ψ); have hp(i:Gains c): W.supBounds (f i).site (f i).support (q i) (r i):= by cases i; exact hk _; exact (Pylon.vessel T t _).1
   refine ⟨r∘ N,fun i=> hp (N i),fun i=> Cost.equiv («f»:=fun j:Gains c=> if (f j).site=i then W.mass (f j).support (r j) else 0) (N) ?_⟩; refine Cost.sum («f»:=fun j:Gains c=> if (f j).site=i then W.mass (f j).support (r j) else 0) (h i) (wings T t ?_); intro j; split
   · refine ⟨le_trans (hp (.inr j)|>.1) (W.loMass (T.map j).support _ (hp (.inr j)|>.1)),?_⟩
     unfold BudgetPoint.mass; rw [mul_comm]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith only [] : W.supportExponent ≤ W.supportExponent+1) (Nat.cast_nonneg _))) (hp (.inr j)|>.1)
   · have hx:= (hp (.inr j)).1; exact ⟨le_rfl,mul_nonneg hx (Real.exp_nonneg _)⟩
omit h in
lemma soften (k:ℕ→ℝ) (he:softCost W X k b): softCost W (Y) (spread k (fun _:Seat c=> ψ) ∘ N) (b+g):= by
   let u:= spread k (fun _:Seat c=> ψ); have hk(j:Seat c):0≤ ψ := (Pylon.vessel (G:=G) T t j|>.1).1; refine ⟨fun i=> ?_, fun i=> Cost.equiv («f»:=fun j:Gains c=> if i∈ s₀ j then u j * Real.exp ((W.supportExponent+1)*coverNumber W.B (s₀ j)) else 0) (N) ?_⟩; · change 0 ≤ u _; cases N i; exact he.1 _; exact hk (1,0) 
   apply Cost.sum («f»:=fun j:Gains c=> if i∈ s₀ j then u j * Real.exp ((W.supportExponent+1)*coverNumber W.B (s₀ j)) else 0) (he.2 i); apply wings T t; intro j; split
   · exact ⟨mul_nonneg (hk j) (Real.exp_nonneg _), le_rfl⟩
   · exact ⟨le_rfl,mul_nonneg (hk j) (Real.exp_nonneg _)⟩
end YM.Juniper.Cinch

import YM.AllOrder.Burn.Camp
import YM.AllOrder.Burn.Open
import YM.AllOrder.Burn.Cooling
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Burn
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Floe Floe.Pace Floe.Aero Floe.StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω α:ℝ}{k r m n N l:ℕ}{j:Side}
open Till Tilt Floe.Step Floe.Step.PlanV Plateau
-- L=1 for receipts on either.Housing z support paid. R.Space β recognition. factor 2*sqrt or 4..
variable (p:BudgetPoint)(A:Activities G j)(s:Locale G)
local notation "V"=> (s j)
local notation "U₀"=> Site j ⊕ ℕ
local notation "I"=>Site j
open Till Tilt
abbrev spine (p:BudgetPoint)(i:Site j):RegularAddress j:= ⟨i,court i p.B,halo_subset _ _ (mem_singleton_self _)⟩
-- Countable address generator. For output may use non-this letter frame if prove canonical bills. auxiliary uses simple
noncomputable def keys (n:Side): ℕ ≃ Site n ⊕ ℕ := Extra.Iteration.numbering _ -- path
noncomputable def pivot (n:Side): Site n ↪ ℕ:= ⟨fun i=>(keys n).symm (.inl i),fun _ _ h=>Sum.inl_injective ((keys n).symm.injective h)⟩
def press : Activities G j:={A with reg:=Sum.elim (spine p) A.reg ∘ keys j,E:=Sum.elim V A.E ∘ keys j}
local notation "R"=>press p A s
local notation "K'"=> keys j
local notation "Z"=> Set.range (pivot j)
lemma rolled (i:ℕ) : i∈Z↔∃ x:Site j,K' i= .inl x:= by constructor <;> rintro ⟨x,hx⟩; exact ⟨x,hx ▸ (K').apply_symm_apply _⟩; exact ⟨x,(K').injective ((K').apply_symm_apply .. |>.trans hx.symm)⟩
lemma rights (i:Site j) : keys j (pivot j i)=.inl i:= (keys j).apply_symm_apply _
lemma earns (x:I): (R).reg (pivot j x)= spine p x∧(R).E (pivot j x)= (s j x):= by simp [press,rights]
lemma shell (i:I): coverNumber p.B (court i p.B)≤ 1:= (Corona.list_cost _ (show covers p.B (court i p.B) {i} from ⟨subset_refl _, Corona.ship_halo _ (by intro a ha b hb; rw [mem_singleton] at ha hb; subst a b; exact .refl)⟩)).trans_eq (card_singleton _) -- ship connectivity
variable (h: A.Valid p C Ω) {τ Δ Cp:ℝ}(hp:∀ i:Site j, Fairness p i (court i p.B) (s j i) τ)(hx : PhysicalNext.Repeat.Trio.Mirrors (s j))
include h hp hx
lemma remit : (R).Valid p (Real.exp p.supportExponent * τ+C) Ω ∧ Candor p R Z (Real.exp p.supportExponent * τ) C:= by
 obtain ⟨F,hF,hC⟩:= h.boundE; let f:= Sum.elim (fun _ : I => τ) F; let u :ℕ→ℝ:= f ∘ K'; let b:= Real.exp p.supportExponent*τ; have H: ∀ i,p.Regular (((R).reg i).support) ((R).E i) ∧ p.supBounds (((R).reg i).site) (((R).reg i).support) ((R).E i) (u i) ∧ ((R).E i) 1=0 ∧ (Nonwrapping (((R).reg i).support) (((R).reg i).site) → ∀ x y,IsAffineDirection (((R).reg i).site) x→IsAffineDirection (((R).reg i).site) y→logHessian ((R).E i) x y=0):= by
    intro i; simp only [press,u,Function.comp_apply]; cases K' i with
    | inl x => exact ⟨(hp x).ready,(hp x).cap,(hp x).one,(hp x).nth⟩
    | inr i => exact ⟨h.regular.smooth i,hF i,h.regular.at_flat i,h.regular.vanish i⟩
 have hv: ∀ (n:Signed)(p':Site j), ∃ t:(R).Moves n p',∀ i,t.ep i∈Z↔ i∈Z:= by
   intro t x; obtain ⟨X⟩:= h.moves t x; let l:=Push.Local.turnSites t x; let p₀:=Equiv.sumCongr l X.ep; let e':=(K').trans (p₀.trans (K').symm); have he i : K' (e' i)= p₀ (K' i):=(K').apply_symm_apply _
   have hM i: let f:=Sum.elim (spine p) A.reg; let g:=Sum.elim V A.E; (f (p₀ i)).support=(f i).support.image (affine t x)∧ (f (p₀ i)).site= affine t x (f i).site∧ g (p₀ i)= g i∘pull t x:= by
      rcases i with i|i; · refine ⟨?_, rfl, funext fun U=> (hx ..).symm⟩; change halo p.B {l i}= _; rw [← Finset.image_singleton]; exact Push.Local.halo_map l (Push.Local.turn_sep t x) ..
      exact ⟨X.reg_support i,X.reg_site i,funext (X.valuesE i)⟩
   refine ⟨⟨e',X.kp,fun i=> ?_,fun i=> ?_,X.forced_support,X.forced_inventory,X.forced_tests,fun i U=> ?_,X.valuesK⟩,fun i=>?_⟩
   all_goals first | (simp only [press,Function.comp_apply,he]; exact (hM _).1) | (simp only [press,Function.comp_apply,he]; exact (hM _).2.1)| (simp only [press,Function.comp_apply,he]; exact congr_fun (hM _).2.2 _) | (change (e' i)∈Z↔_; rw [rolled,rolled,he]; cases K' i <;> simp [p₀])
 have hz: Candor p R Z b C:= by
    refine ⟨⟨u,fun i=>(H i).2.1,fun i=>?_⟩,hv⟩
    let V₀:I →ℝ:=fun x=> if x=i then p.mass (court i p.B) τ else 0; let w0 :I ⊕ℕ→ℝ:=Sum.elim V₀ 0; let w1:I⊕ℕ→ℝ:=Sum.elim (fun _=>0) (wallet p A F i)
    have hy : SumBudget V₀ b:= by refine budget_finite (fun x=>(by unfold V₀; split; exact mul_nonneg (Real.exp_pos _).le (hp i).cap.1; rfl)) ?_; simp only [V₀,Finset.sum_ite_eq',Finset.mem_univ,if_true]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_of_le_one_right p.exponent_pos.le (by exact_mod_cast shell p i))) (hp i).cap.1
    have hh (x:ℕ) : (if x∈Z then wallet p (R) u i x else 0)= w0 (K' x)∧(if x∈Z then 0 else wallet p R u i x)=w1 (K' x):= by
        simp only [rolled,wallet,press,Function.comp_apply,u]; cases K' x with
        | inl a=> by_cases ht:a=i <;> simp [V₀,spine,ht,w0,w1,wallet,f]
        | inr a=> simp [w0,w1,V₀,wallet,f]
    have changex {f g:ℕ→ℝ}{b:ℝ}(he:f=g)(h:SumBudget f b):SumBudget g b:=he ▸ h
    constructor; exact changex (show (fun x=> w0 (K' x)) = _ from funext fun x => by convert! (hh x).1.symm using 2) (Extra.Iteration.Cost.equiv (K') ((by simpa only [add_zero] using! Extra.Iteration.Cost.sum (f:=w0) hy (show SumBudget (fun _ : ℕ=> 0) 0 from ⟨fun _=>le_rfl, summable_zero,(by simp)⟩))))
    exact changex (show (fun x=>w1 (K' x))=_ from funext fun x=> by convert! (hh x).2.symm using 2) (Extra.Iteration.Cost.equiv (K') (by simpa only [zero_add] using! Extra.Iteration.Cost.sum (f:=w1) (show SumBudget (fun _ : I=>0) 0 from ⟨fun _=>le_rfl,Summable.of_finite,(by simp)⟩) (hC i)))
 have hg {T: Activities G j}(M:Set ℕ)(hV : Candor p T M b C) : T.EBound p (b+C):=by obtain ⟨u,hV,hE⟩:= hV.sale; refine ⟨u,hV,fun i=>?_⟩; have he(x:ℕ): wallet p T u i x=(if x∈M then wallet p T u i x else 0)+(if x∈M then 0 else wallet p T u i x):=(by split<;> simp); change SumBudget (wallet p T u i) (b+C); rw [funext he]; exact budget_plus (hE i|>.1) (hE i|>.2)
 exact ⟨⟨⟨fun i=>(H i).1,fun i=>(H i).2.2.1,fun i=>(H i).2.2.2⟩,⟨h.forced.sym,h.forced.symtest,h.forced.meas,h.forced.meas_test,h.forced.reads,h.forced.reads_test,h.forced.permit⟩,fun i j=> ⟨(hv i j).choose⟩,hg Z hz,h.boundK⟩,hz⟩
end YM.AllOrder.Burn

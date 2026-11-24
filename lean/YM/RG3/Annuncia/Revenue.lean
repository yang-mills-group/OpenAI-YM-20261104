import YM.RG3.Annuncia.Magic
import YM.RG3.Riding.Jaw
/-!
# Quantitative transport with l1 test-question decal. NO census dimension
 factor and allows any declared grade in actuator upper. P downstream.O.Meta
 receives at original support headers exactly. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Annuncia.Replica
open Function Filter Finset YM.Marker Lattice RG Wilson MergeProof MergeProof.Accent
  RG3.Script RG3.Held RG3.Press RG3.Forms Push.AbsoluteSums Ac Riding Push.GridApprox.Nil
open scoped Matrix.Norms.Frobenius ContDiff BigOperators Topology Classical
variable {V W:Type*}[DecidableEq V][Fintype W][DecidableEq W]{u:W→V}(R:Census V){γ:W→ℂ}
local notation "S"=> Replica u R
variable (u)
lemma coverage {U:Set V}{a:Poly S}(ht:Scoped (Set.preimage u U) a)(z:R.Mode)(hz:¬ (z.val:Set V)⊆ U): (mouth u R γ a).part z=0:=by
 rw [quota]; apply sum_eq_zero; intro b _; split
 next he=>
    refine mul_eq_zero_of_right _ (ht b (fun h=>?_))
    apply hz; rw [← he]; intro v hv;obtain ⟨j,hj,rfl⟩:= mem_image.mp (show v∈b.val.image u from hv); exact h hj
 exact rfl

variable (γ)
lemma born {n:Side}{G:Gauge}(o:V→Site n){P:Support n}{t:ℝ}{f:Config G n→Poly S}(h:Borne (o ∘ u) P f t): Borne o P (mouth u R γ∘f) t:=by -- composition proof R unsupplied order.
 refine ⟨fun a b hx hk=>congrArg (mouth u R γ) (h.home _ _ hx hk),fun x U=>congrArg (mouth u R γ) (h.turns x U),fun i=>?_,fun U=> coverage u R (h.scope U)⟩
 unfold comp; simp_rw [quota]
 exact Finset.measurable_sum _ fun j _=> by split; exact measurable_const.mul (h.me j); exact measurable_const
lemma gem {n:Side}{G:Gauge}(o:V→Site n){P:Support n}{t:ℝ}{f:Config G n→Poly S}(h:Burns (o ∘ u) P f t): Burns o P (mouth u R γ∘f) t:= ⟨born u R γ o h.toBorne,fun U H=>h.permits U (fun hi=>H ((congrArg _ hi).trans (_root_.map_zero (mouth u R γ)))),fun U=>(quiet u R γ _).trans (h.sil U)⟩
lemma cash {n:Side}{G:Gauge}(o:V→Site n){P:Box n}{t:ℝ}{f:Config G n→Poly S}(h:Flow (o ∘ u) P f t): Flow o P (mouth u R γ∘f) t:= ⟨born u R γ o h.toBorne,fun U H=>h.permits U (fun hi=>H ((congrArg _ hi).trans (_root_.map_zero (mouth u R γ))))⟩

-- every query has norm bound α on current sensor space, choose at Supply.
variable (w:V→ℝ)(a:W→ℝ)(hw:∀i,0≤w i)(hA:∀i,‖γ i‖≤ a i)
-- sum estimate across all sensor colors per thermal mode

def amount (g:(S).Mode→ℝ)(i:R.Mode):= ∑ j: (S).Mode, if bill u R j=i then (∏ k∈j.val,a k)*g j else 0
-- Q sign factor.Many.Names multiplexer(moving with β honors). Keep exposure on aggregated not postulating κ.
include hA
lemma paid (g:(S).Mode→ℝ){x:Poly S}(h:∀i, ‖x.part i‖ ≤ g i)(i:R.Mode): ‖(mouth u R γ x).part i‖≤amount u R a g i:=by
 rw [quota]; apply (norm_sum_le _ _).trans; apply sum_le_sum; intro j _; split
 next _=> rw [norm_mul,show ‖sign u R γ j‖=∏ q∈j.val,‖γ q‖ from norm_prod ..]; exact mul_le_mul (prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>hA i)) (h _) (norm_nonneg _) (prod_nonneg fun i _=>(norm_nonneg _).trans (hA i))
 next _=> simp
omit hA in
lemma exactPrice (g:(S).Mode→ℝ): Riding.unitPrice R w (amount u R a g)= wordsPrice (fun i=>a i*w (u i)) g:=by
 unfold Riding.unitPrice wordsPrice amount; simp_rw [mul_sum]; rw [sum_comm]; refine sum_congr rfl fun i _=>?_ ; rw [sum_eq_single_of_mem (bill u R i) (mem_univ _),if_pos rfl]; swap;· intro b _ hb; rw [if_neg (Ne.symm hb),mul_zero]
 unfold Poly.toll bill; rw [prod_image (fun _ he _ hh ht=>(admit u R i).separate he hh ht),prod_mul_distrib]; ring

variable {Ω:Type*} (g₁:Ω→W→ℂ)(h1:∀i v,‖g₁ i v‖ ≤ a v)
omit hA
 include hw h1
lemma save {Y I:Type*}{n:Side}{X:I→Support n}{f:I→Y→Poly S}{b:ℕ}{e d:ℝ}(ha:∀i,0≤a i)(h : Towed (fun i=>a i*w (u i)) X f b e d) : ∃ c:I→R.Mode→ℝ, Summable (fun i=>unitPrice R w (c i))∧ Hit X b (fun i=>unitPrice R w (c i)) e d∧∀i,0≤c i∧∀z U j, ‖(mouth u R (g₁ z) (f i U)).part j‖≤ c i j:=by
 -- derive summable by charged envelope. Need hw. Section h1.
 obtain ⟨D,hD,hZ,hh⟩:=h
 choose p pp hp he using hh
 let c(i:I):= amount u R a (p i)
 have hC(i)(j:R.Mode):0 ≤ c i j:=by unfold c amount; exact sum_nonneg fun j _=>by split;exact mul_nonneg (prod_nonneg fun k _=>ha k) (pp i j);rfl
 have hv(i): unitPrice R w (c i)≤D i:=by rw [show c i=amount u R a (p i) from rfl,exactPrice]; exact he i
 have ht(i):0 ≤ unitPrice R w (c i):=by unfold unitPrice Poly.toll; exact sum_nonneg fun j _=>mul_nonneg (prod_nonneg fun k _=>hw k) (hC i _)
 refine ⟨c,hD.of_nonneg_of_le ht hv,fun i=>budget_mono (hZ i) (fun j=>?_) (fun j=>?_),fun i=>⟨hC i,fun z U j=>?_⟩⟩
 · split; exact mul_nonneg (ht _) (Real.exp_pos _).le; rfl
 · split; exact mul_le_mul_of_nonneg_right (hv _) (Real.exp_pos _).le;rfl
 exact paid u R (g₁ _) a (h1 z) _ (hp _ U) _

variable {n:Side}{G:Gauge}(P:RG.Rep G n){H:Box n→ Config G n→Poly (Replica u R)}{t e:ℝ}
include h1 hw
lemma review (ha:∀i,0≤a i)(_h0:Towed (fun i=>a i*w (u i)) Prod.fst H P.p.B e t):∃ c,Riding.Review P (w:=w) (fun z p U=>mouth u R (g₁ z) (H p U)) c e t:=by
 obtain ⟨c,-,hh,hC⟩:= YM.RG3.Annuncia.Replica.save u R w a hw g₁ h1 ha _h0
 exact ⟨c, fun i=> (hC i).1,fun z i U j=> (hC i).2 z U j,hh⟩
end YM.RG3.Annuncia.Replica

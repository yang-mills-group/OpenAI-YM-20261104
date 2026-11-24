import YM.Qlocal.Versal.Sandy
import YM.Qlocal.Quipu.Tempo
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Frame
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet
open Function Filter Lattice Laurent RG Wilson Stationary Lasso Zora Work.F02 Metric
open Marker Multi Finset
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
open ConnectedActivityE6.Blaze ConnectedActivityE6
variable {V:Type}[DecidableEq V] {ι E:Type} {G:Gauge}{k n j r i:ℕ} {c:Side} {d t a v u C:ℝ}{R:Census V}
variable (l:Lattice.Order){s:Senses R}(A:Album ι s G n)(x:Site c)(W:Config G c)(o:Site c)(p:BudgetPoint)
set_option quotPrecheck false
local notation "θ"=> p.threshold
local notation "t₀"=> p.supportExponent
open Extra.Iteration
namespace Album
open SelectedOrderedKernels
lemma proposal : Weather (increment W) (0:Directions G c):= fun i=> by unfold increment; change ContDiffAt ℝ ω (fun x:Directions G c=> G.mat (G.lieExp (x i))*G.mat (W i)) 0; exact (G.exp_jet.contDiffAt.comp 0 (f:=fun x:Directions G c=> x i) ((ContinuousLinearMap.proj (φ:=(fun _ : Edge (Site c)=> G.Color)) (R:=ℝ) i).contDiff.contDiffAt)).mul contDiffAt_const
variable (P:ι→Prop)(h:A.Health a C)(ha:0<a)
local notation "K"=> realize P A x r
local notation "F"=> A.readout P x r
local notation "E!"=> increment W
include h ha
lemma Maya (u:Fin k→ Directions G c) : HasSum (fun i=> leftDerivs (F i) (List.ofFn u) W) (leftDerivs (K) (List.ofFn u) W):= by
 have he:=proposal W; obtain ⟨d,hd⟩:= habitat (increment W) he k
 simp_rw [expand (j:=k) ((A.winter P x r h ha (E!) he).of_le le_top) u,show ∀ i:ι, _ from fun i=> expand (j:=k) ((A.jobs P x r h ha (E!) he i).of_le le_top) u]
 apply hasSum_sum; intro i hi; exact ContinuousMultilinearMap.hasSum_eval (A.printing P x r h ha (E!) he hd i.length_le) _
lemma Arrival (u:List (Directions G c)) : HasSum (fun i=> leftDerivs (F i) u W) (leftDerivs (K) u W):=by simpa only [List.ofFn_get] using Maya A x W P h ha (r:=r) u.get
variable {X:Support c}{b w:ℕ}
lemma regular (hm:∀ i, P i → (A i).cone l x ⊆ X): p.Regular X (realize P A x r):= by
 have hX: LocalOn ↑X (K):= by intro U V he; change (∑' i,_)=(∑' i,_); apply tsum_congr; intro i; unfold readout; split; exact (A i).located l x r U V (agrees_mono he (show ↑((A i).cone l x) ⊆ ↑X from Finset.coe_subset.mpr (hm i ‹_›))); rfl -- elaboration
 have hv(W:Config G c): ContDiffAt ℝ (↑p.order) ((realize P A x r) ∘ increment W) 0 := (winter P A x r h ha (increment W) (proposal W)).of_le le_top -- order of args?
 exact ⟨hX,(A.aperture_mark P x r h ha).measurable, A.safe P x r,fun U _=> hv U,fun i _ a l hl=>Next.Foundations.left_has a hl (hv i)⟩
omit h ha
lemma chilly (hs:A.Health (d+a+v) C)(ht' : t/p.B≤d)(hc:0≤t)(H:∀ i,P i→ Vase.Carrier l (A i) x b w p.B X) (hv:0≤v) (z:ℕ) (hz:∀ i,P i→z ≤ (A i).momentum) (r:ℕ) (ha:0<a) : SumBudget (fun i=> if P i then Vase.Sus (A i) p r w else 0) (θ^n*Vase.humid G p.power p.order n r w b t a * C * Real.exp (-(t*coverNumber p.B X + v*z))) := by
 let μ:= θ^n*Vase.humid G p.power p.order n r w b t a; let y:=t*coverNumber p.B X+v*z; have hy:0≤Real.exp (-y):=Real.exp_nonneg _; let α:=d+a+v; have ht:0≤μ:=mul_nonneg (pow_nonneg p.threshold_pos.le n) (Vase.humid_nn _ _ _ _ _ _ _ _ ha) -- ellipsis fail
 have h₀:0≤μ:=ht; let f(i):=if P i then Vase.Sus (A i) p r w else 0
 have hf(i:ι):0≤f i:=by unfold f; split; exact (Vase.Suspend l (A i) x p (H i ‹_›) r).1;rfl
 have hb(i:ι) : f i ≤ (μ*Real.exp (-y))*(A i).fare α := by
    by_cases h:P i; swap; · rw [show f i=0 from if_neg h]; exact mul_nonneg (mul_nonneg h₀ hy) (hs.1 i)
    have he : f i * Real.exp y ≤ μ*(A i).fare α:= by apply le_trans ?_ (Vase.economical (u:=v) l (A i) x p (H i h) r ha hc ht'); rw [show Vase.Sus _ _ _ _=f i from (if_pos h).symm]; apply mul_le_mul_of_nonneg_left _ (hf i); refine Real.exp_le_exp.mpr (add_le_add_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hz i h) hv) _) -- argument orientation
    apply le_of_mul_le_mul_right ?_ (Real.exp_pos y); exact (by rw [mul_right_comm μ, mul_assoc _ (Real.exp (-y)), ← Real.exp_add, neg_add_cancel,Real.exp_zero,mul_one]; exact he)
 have hp:Summable (fun i=> (μ*Real.exp (-y))*(A i).fare α):= hs.2.1.mul_left _; have hh:= hp.of_nonneg_of_le hf hb; exact ⟨hf,hh,(hh.tsum_le_tsum hb hp).trans (by rw [tsum_mul_left]; rw [mul_right_comm μ]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs.2.2 h₀) hy)⟩
-- easier combine cold carrier→regular real full costs.
lemma money (H:∀ i,P i→ Vase.Carrier l (A i) x b w p.B X)(hv:SumBudget (fun i=> if P i then Vase.Sus (A i) p r w else 0) t)(hp: A.Health a C)(ha:0<a) : p.Regular X (K) ∧ ∀ o∈X,p.supBounds o X (K) t := by
 refine ⟨A.regular l x p P hp ha (fun i hi=>(H i hi).complete),fun o ho=>⟨(tsum_nonneg (g:=fun i=> if P i then Vase.Sus (A i) p r w else 0) hv.1).trans hv.2.2, fun U hU l' hℓ hz'=>?_⟩⟩
 have hh : HasSum (fun i=>leftDerivs (F i) l' U) (leftDerivs (K) l' U):= Arrival A x U P hp ha l'
 have hx(i): ‖leftDerivs (F i) l' U‖≤ if P i then Vase.Sus (A i) p r w else 0:= by unfold readout; split; exact ((Vase.Suspend l (A i) x p (H i ‹_›) r).2.2 _ ho).2 U hU l' hℓ hz'; change ‖leftDerivs (fun _=>(0:ℝ)) _ _‖≤0; rw [Work.G07.left_const,ite_self,norm_zero] -- rewrite with lemma
 rw [← hh.tsum_eq]; have ht:= hv.2.1.of_nonneg_of_le (fun i=> norm_nonneg _) hx; exact (norm_tsum_le_tsum_norm ht).trans ((ht.tsum_le_tsum hx hv.2.1).trans hv.2.2)
end Album
end YM.Qlocal.Quipu.Sonnet

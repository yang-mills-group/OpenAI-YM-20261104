import YM.AllOrder.Catch.Vane
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Catch
open Function Filter Matrix Metric MeasureTheory ProbabilityTheory Finset
open ConnectedActivityE6 Blaze Brush Poll Local Vote Clock
open PositionX.Jet PhysicalNext Repeat Lantern
open Laplace Laplace.SigmaP PertExtension PertExtension.Series Radial Tested
open scoped Topology ENNReal BigOperators Classical ContDiff Polynomial
variable {ι:Type*} {T:Clock ι} {X Y:ι→Type}[∀ i,NormedAddCommGroup (X i)][∀ i,NormedSpace ℝ (X i)][∀ i,FiniteDimensional ℝ (X i)][∀ i,Fintype (Y i)][∀ i,DecidableEq (Y i)]
variable (V:∀ i:ι,ℝ×(X i × Body (Y i))→ℝ) (W:∀i,X i)
    {A B:∀i,X i× Body (Y i)→ℝ}{M:∀i,X i→ Matrix (Y i) (Y i) ℝ}{ρ:∀ i,X i→Body (Y i)}
-- Morph to EVERY Y filter allowed. require growth Flow for given tableau.N.Incr order exact same Hess (paid.Octane). Need n+3 derivatives on Venue + Lift.Enough requested. Choose Holder proof rewriting.N=H+3. Good.
variable (D u v b p:ι→ℝ) {s z₁:ℝ}{k j:ℕ}
local notation "Ω" x=> X x × Body (Y x)
local notation "Γ"=> fun i=> grace (A i) (B i) (ρ i) (M i)
variable {W b V D u p} (U:Vaccine (k+3) D u p T A B ρ M)(N:North W b u T) (S:Flood V T (k+3))
local notation "F"=> fun i=> course (W i)
local notation "Pt"=> Clock.tier (fun i=>Body (Y i)) T
local notation "Ph"=> T.book (fun i=> closedBall (0:Body (Y i)) (D i))
variable {η:Type*}
local notation "H₀"=> T.Meter
local notation "N₀"=> (k+3)
local notation "ℍ"=> T.book (fun i:ι=>closedBall (0:ℝ) (b i))
variable {v} (ht:∀ᶠ i in T.rail,|v i| ≤ b i)
include N ht
lemma part_small : ∀ᶠ i in T.rail, ‖F i (v i)‖ < u i ∧ |v i| < u i:= by
 filter_upwards [ht,N.early] with i hi hv; refine ⟨?_, hi.trans_lt hv.2.2⟩; rw [course,norm_smul]; exact (mul_le_mul_of_nonneg_right hi (norm_nonneg _)).trans_lt hv.2.1
include U
lemma chilled {f:∀ i,X i}(hv:∀ᶠ i in T.rail, ‖f i‖ < u i)(hq:H₀ (fun i=> ‖f i‖) (-(1/2:ℝ))): H₀ (fun i=> ‖ρ i (f i)‖) (-(1/2)):= by
 apply (U.price.unitPay le_rfl hq).smaller; filter_upwards [hv,U.D_live] with i hi hp; obtain ⟨he,hx⟩:= hp; let E:= ball (0:X i) (u i); have hc:= (convex_ball (0:X i) (u i)).norm_image_sub_le_of_norm_fderiv_le (f:=ρ i) (fun i hi=> (he.curve i (mem_ball_zero_iff.mp hi)).smooth.differentiableAt (by simp)) (C:=p i) (fun x hx=>by rw [← norm_iteratedFDeriv_one]; exact (Brush.offer.1 (he.curve x (mem_ball_zero_iff.mp hx))).inside _ (by omega)) (mem_ball_self he.pos) (mem_ball_zero_iff.mpr hi); rw [hx.steer.map0,sub_zero,sub_zero] at hc; rw [abs_of_nonneg (norm_nonneg _)]; exact hc.trans (le_abs_self _)
variable (z:∀ i,Body (Y i))(hv:∀ᶠ i in T.rail, ‖z i‖ ≤ D i)
local notation "jV"=> fun i=> plunge (V i) (W i) (z i) (ρ:=ρ i)
local notation "Q"=> fun i=>uplift (course (W i)) (ρ i) (z i)
include hv
lemma alert : Cover T (N₀) 0 (fun _=>1) (fun i=>uplift (F i) (ρ i) (z i)) v ∧ ∀ᶠ i in T.rail,‖Q i (v i)‖ <1:=by
 let q t:= (z t); let ℓ(i:ι) := ContinuousLinearMap.toSpanSingleton ℝ (W i); let ξ(i:ι) := ContinuousLinearMap.toSpanSingleton ℝ (z i)
 have hz: H₀ (fun i=> ‖z i‖) 0:= U.rate.width.smaller (hv.mono fun i hi=> le_trans ((abs_of_nonneg (norm_nonneg _)).trans_le hi) (le_abs_self _)); let r:=(-(1/2:ℝ)); have ha:=pole N ht; have hW:=N.W_age; have hG : H₀ (fun i=>‖F i (v i)‖) r:= by simp_rw [course,norm_smul]; exact ((ha.ab.mul hW).weak (by simp [r]));
 let f i:(ℝ→Body (Y i)):= ρ i ∘ course (W i); have hm:H₀ (fun i=>‖f i (v i)‖) r:= chilled U N ht ((part_small N ht).mono fun _ hi=>hi.1) hG
 have hr: r<0:=(by norm_num [r]); have hh:H₀ (fun i=> ‖ξ i (v i)‖) r:=by simp_rw [ξ,ContinuousLinearMap.toSpanSingleton_apply,norm_smul]; exact ((ha.ab.mul hz).weak (by simp [r]));
 constructor
 · have he:Cover T (N₀) 0 (fun _=>1) (fun i=>F i) v:= (ray W le_rfl (ha.weak hr.le) hW).weak (by simp);
   have hV:Cover T (N₀) 0 (fun _=>1) (fun i=>f i) v:= by refine (Cover.comp le_rfl he (u:=ρ) (x:=v) (Cover.has U.price ?_)).weak (by simp) ; exact ((part_small N ht).and U.D_live).mono (fun i hi=>(hi.2.1.curve _ hi.1.1).smaller (by omega))
   exact Cover.join (Cover.exponent (V:=fun _=> ℝ) le_rfl (ha.ab.weak hr.le)) (he.join (Cover.add hV ((ray z le_rfl (ha.weak hr.le) hz).weak (by simp))))
 filter_upwards [hm.low hr (show 0<(1/2:ℝ) by norm_num),hh.low hr (show 0 < (1/2:ℝ) by norm_num), ha.low hr zero_lt_one,hG.low hr zero_lt_one] with i hp he hm hh; refine max_lt hm (max_lt ((le_abs_self _).trans_lt hh) ?_); change ‖f i (v i)+ (ξ i) (v i)‖<1; linarith only [hp,he,norm_add_le (f i (v i)) (ξ i (v i)), norm_nonneg (ξ i (v i)),le_abs_self ‖f i (v i)‖,le_abs_self ‖ξ i (v i)‖]
include S
lemma pluck : Cover T (N₀) 0 (fun _=>1) (jV) v:= by
 let Fq:= Q; obtain ⟨hl,h⟩:= alert U N ht z hv; apply Cover.weak (Cover.comp (a:=0) (b:=0) (u:=V) (f:=Fq) le_rfl hl ?_) (by simp); intro e he; exact ((S.ticket e he).and h).mono fun i hi=>hi.1 _ hi.2
local notation "U₁"=> fun i=> warmP (A i) (B i) (M i) (ρ i) (V i) (W i) (z i)
local notation "ξ"=> unroll -- parser
omit ht
lemma dreamP : TaylorCap T k b (fun i=> U₁ i (b i)) (fun i=> someJ (U₁ i)):= by
 have hζ(i:Σ i:ι,{r:ℝ//r∈ Metric.closedBall 0 (b i)}):|(i.2:ℝ)| ≤ b i.1:= mem_closedBall_zero_iff.mp i.2.2; let Q' (i:Σ i:ι,{r:ℝ//r∈ Metric.closedBall 0 (b i)}):=i.1; let tf:= T.liftF Q';
 let hk:∀ᶠ i in T.rail, 0<b i:= N.early.mono fun i hi=> hi.1; let f i t:=Γ i (z i) (t,F i t); have hx:TaylorCap T k b (fun i=> f i (b i)) (fun i=> someJ (f i)):= TaylorCap.paintT N.high hk (by omega : k < k+3) (filming (v:=fun i=>(i.2:ℝ)) (U.reposition Q' tf) (N.way Q' tf) _ (Eventually.of_forall hζ) (tf.tends.eventually hv)); -- z specify
 let hs:= jV; let L i:= climb2 ((hs) i); have hg:TaylorCap T (k+2) b (fun i=>hs i (b i)) (fun i=>someJ (hs i)):= TaylorCap.paintT N.high hk (by omega : k+2 < k+3) (pluck (T:=ℍ) (v:=fun i=> i.2) (U.reposition _ tf) (N.way _ tf) (S.paint Q' tf) (Eventually.of_forall hζ) (fun i=> z i.1) (tf.tends.eventually hv));
 have hC:= U.D_live.and S.rise; have hU:TaylorCap T k b (fun i=> L i (b i)) (fun i=>someJ (L i)):= by
    refine TaylorCap.shiftT N.low hk ?_ (TaylorCap.shiftT N.low hk ?_ hg); · filter_upwards [hC] with i hi; let d:=sign (V i) (W i) hi.1.2 hi.2 (z i); exact ⟨(by rw [Laplace.SigmaP.shift,dslope_same]; exact d.2.1), shifty d.2.2.2⟩
    exact hC.mono fun i hi=>let d:=sign _ _ hi.1.2 hi.2 (z i); ⟨d.1,d.2.2.2⟩
 apply TaylorCap.fit (hx.less hU) (EventuallyEq.refl ..); intro i hi; exact hC.mono fun j hj=> let ht:=sign _ (W j) hj.1.2 hj.2 (z j); (congr_fun (some_sub (worth hj.1.2 hj.2 _) (shifty (shifty ht.2.2.2))) i).symm
lemma dream : TaylorCap T k b (fun i=> Real.exp (U₁ i (b i))) (fun i=> someJ (Real.exp ∘ U₁ i)) := by
 let A':= U₁; let hp:= dreamP U N S z hv; let t:= U.D_live.and S.rise; have h:Tendsto (fun i=>someJ (A' i) 0) T.rail (𝓝 0):= tendsto_const_nhds.congr' (t.mono fun i hi=>by dsimp only; rw [someJ_zero]; exact (initial hi.1.2 hi.2 (z i) (W:=W i)).symm);
 apply TaylorCap.fit (TaylorCap.process Real.exp Real.contDiff_exp.contDiffAt hp h N.high (N.early.mono fun i hi=> hi.1)) (EventuallyEq.refl ..); intro j hj; exact t.mono fun i hi=> (congr_fun (conviction (fee hi.1.2 hi.2 (z i) (W:=W i))) j).symm
end YM.AllOrder.Catch

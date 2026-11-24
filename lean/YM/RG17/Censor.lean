import YM.RG17.Workbox
import YM.OPE.Polar.Supervise
/-!
 # Physical proxy on one R. RAD with reserve. Adapted from OPE.Polar.Supervise. No change to CYMB. Retain all position dependence; crossing worlds not used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits OPE.Log Polar Extraction Word Table Metric
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U:Spec.Final C f S) {K I J L: Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] {Y:Filter L}{r:L→ℝ} (v₁:J→Exterior C.book) (hr:Tendsto r Y home){η M:ℝ} {d:I→ℕ}{x:L→I→E4}
set_option quotPrecheck false
local notation "T"=> (fun i=>OPE.run (r i))
local notation "P"=> (fun i=>r i/T i)
private def inputP (I:Type)[Fintype I] : (I→E4)→L[ℝ] Points (Fintype.card I):=
    { toFun:= fun x=> points (x ∘ runNames I), map_add':= fun _ _=> by ext; rfl, map_smul':=fun _ _=> by ext; rfl, cont:= by unfold points; fun_prop }
include U
private lemma meetAt (c:I→E4) (a:I→ C.book.Token)(h: Injective c): ContDiffAt ℝ ∞ (fun z=> observe S z a) c:=by
    unfold observe worded; simp only [S.readAt]; have hg: inputP _ c∈conf _:=runs_conf.mpr h; exact ContDiffAt.comp (f:=inputP _) c ((S.smooth_read U.room.kernel.smooth _) _ hg|>.contDiffAt ((conf_open _).mem_nhds hg)) (inputP I).contDiff.contDiffAt
variable (hr₀:0<η)
include hr hr₀
lemma meetSum {v:L→ Labels S d} {R:J→ L→ℂ}(h:∀ᶠ i in Y, WithinRoom (r i) M η (x i) 0): ∀ᶠ i in Y,∀ w∈ closedBall (0:I→ E4) 1,DifferentiableAt ℝ (fun w=>∑ j:J,R j i * whole S (centered x r i w) (v i) (bearing (v₁ j)) (fields S (v₁ j))) w:=by
    let y(i)(t:I→E4):=centered x r i t
    let S₀:= Finset.univ.image v₁; filter_upwards [within_centered hr hr₀ h, (loglife hr).pos, frames_safe (I:=I) (M:=M+η) hr S₀ (half_pos hr₀)] with i hi hr hS w hw
    simp_rw [whole_observed]; refine DifferentiableAt.fun_sum (fun j _=>differentiableAt_const _|>.mul ?_)
    let X(w):=beside (y i w) (bearing (v₁ j)); have hz:ContDiff ℝ ∞ X:=by apply contDiff_pi.mpr; intro i; rcases i with i|i; unfold X y centered; simp [beside]; fun_prop; exact contDiff_const
    exact ((meetAt U (X w) _ (hS _ (hi w (mem_closedBall_zero_iff.mp hw)) _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))|>.coin (by positivity))).comp w hz.contDiffAt).differentiableAt (by simp)
set_option maxHeartbeats 550000 in
lemma arcsW {V:J→ Labels S d} {F:J→ L→ℂ} (hf:∀ j,∃ c,RateLE Y T (F j) c) (hx:∀ᶠ i in Y, WithinRoom (r i) M η (x i) 0) (a:Axis) (p:I) : ∀ᶠ i in Y,∀ z:I→E4,‖z‖≤1 → ∃ k:Ortho, ‖(forwards k).val-basis a‖<knobSize I ∧ Radiates (fun z=>∑ j:J,F j i * whole S (centered x r i z) (V j) (bearing (v₁ j)) (fields S (v₁ j))) z (ray p k) (Real.exp (T i^2)):=by
    let S':=Finset.univ.image v₁; let K'(j:J):= I⊕ Fin (v₁ j).n
    letI(x:J): Fintype (K' x):= inferInstanceAs (Fintype (I⊕_)); letI(x:J): DecidableEq (K' x):= Classical.decEq _
    obtain ⟨Z,u,hu,hU,hZ⟩:= chooseTilt K' a (knobSize I) knob_pos
    let C' i:= ∑ e:J, ‖F e i‖; let y(e:J):I⊕ Fin (v₁ e).n→ C.book.Token:=beside (names (V e)) (names (fields S _)); let X:= centered x r
    let p':= P; let T'':= T; have hT':= run_towards hr; have hz:RateIs Y T'' p' (-1):=((loglife hr).div (Wallet.clock hT')).swap (by ring)
    have hr':=hz.tends neg_one_lt_zero hT';
    have hu': ∀ᶠ i in Y, 3* p' i ≤ u * (η/2/2*r i):=by
       filter_upwards [hz.pos,(tendsto_inv_atTop_zero.comp hT').eventually (ge_mem_nhds (show 0<u*η/16 from by positivity)),(loglife hr).pos] with i _ hP hr; have hW: r i/run (r i)≤ r i*(u*η/16):= by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hP hr.le
       unfold p'; nlinarith only [mul_pos hu (mul_pos hr₀ hr),hW]
    have hC:∀ᶠ i in Y, C' i ≤ Real.exp (T'' i^2/2):=by
       choose c hc using hf; let A:= (∑ j:J,max 0 (c j)); have hh: RateLE Y T'' C' A:=RateLE.sum hT' fun j _=> (hc j).norm.mono ((le_max_right 0 _).trans (Finset.single_le_sum (fun i _=> le_max_left 0 (c i)) (Finset.mem_univ j)))
       filter_upwards [hh (A+1) (by linarith),hT'.eventually_ge_atTop (2*(A+1)),hT'.eventually_ge_atTop 0] with i hi hv hx; exact ( (Real.le_norm_self _).trans hi).trans (Real.exp_monotone (by nlinarith only [mul_le_mul_of_nonneg_right (show 2*_≤T'' i from hv) (show 0≤T'' i from hx)]))
    have hTilt:= eventually_all.mpr (fun i=> tilted_radius U (y i) Z hT' (δ:=1) hz (hr'.eventually (ge_mem_nhds zero_lt_one)))
    filter_upwards [within_centered hr hr₀ hx, frames_safe (I:=I) (M:=M+η) hr S' (half_pos hr₀), hz.pos,(loglife hr).pos, hC, hTilt,hu'] with i ht he hp hv hh hT hΦ z hz
    let A:= X i z; let B(e:J):= beside A (bearing (v₁ e)); let W(e:J)(u: K' e):= B e u; let d:= η/2/2*r i; have hd : 0< d:= by unfold d; positivity
    have he(e:J): Apart d (B e):= he _ (ht z hz) (v₁ e) (Finset.mem_image_of_mem _ (Finset.mem_univ e))
    obtain ⟨K,hK,hV⟩:= hZ W fun e=> (he e).coin hd.le
    refine ⟨K,hU _ hK,?_⟩; let g (e:J)(z:I→E4):=F e i * whole S (X i z) (V e) (bearing (v₁ e)) (fields S (v₁ e)); let a:= Real.exp (T'' i^2/2); let C₀ (e:J):= ‖F e i‖*a
    have hx: Radiates (fun z=> ∑ i:J,g i z) z (ray p K) (∑ i:J, C₀ i):=by
       apply Radiates.sum g; intro e hh; let t:=B e; let v':= ray p K; let u(i'):ℝ:= if i' = p then p' i else 0; let q:=beside u (fun _ : Fin (v₁ e).n => (0:ℝ));
       have hp' : Reserve K (B e) q (p' i):= sep_power _ _ hu hd (he e) K (hV e) (fun j=> by rcases j with j|j; change |u j|≤_; exact (by by_cases h:j=p <;> simp [hp.le,abs_of_nonneg hp.le,u,h]); exact (abs_zero.trans_le hp.le)) hΦ
       obtain ⟨F₀,hf,hF,hc⟩:= hT e K hK (B e) q hp'
       unfold g; apply Radiates.smul _; refine ⟨F₀,hf,fun y hy=> ?_,hc⟩
       obtain ⟨hx,hf⟩:=hF y hy; let V':= z+y • v'; have he: beside (X i V') (bearing (v₁ e))=along (B e) K q y:=by
           funext j; rcases j with j|j
           · by_cases h:j=p; subst j
             · simp [V',v',ray,B,A,X,q,u,along,centered, smul_add, smul_smul, ← add_assoc, p']; rw [mul_comm y]
             simp [V',v',ray,X,B,A,centered,q,u,along,h]
           simp [B,q,along]
       rw [whole_observed,(show z + y • ray p K=V' from rfl),he]; exact hf
    apply hx.mono; unfold C₀; rw [← Finset.sum_mul]; exact (mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le).trans_eq (by rw [← Real.exp_add]; unfold T''; congr 1; ring)
lemma listRates (v:L→ Labels S d) (hf:∀ j:I,∃ u, RateLE Y T (fun i=> v i j) u) (F:J→L→ℂ)(he:∀ j:J,∃ u,RateLE Y T (F j) u)(hx:∀ᶠ i in Y,WithinRoom (r i) M η (x i) 0) : ∀ᶠ i in Y,∀ z:I→ E4,‖z‖ ≤ 1→∀ (j:I)(a:Axis), ∃ k: Ortho, ‖(forwards k).val-basis a‖ < knobSize I ∧ Radiates (fun z => ∑ j:J, F j i * whole S (centered x r i z) (v i) (bearing (v₁ j)) (fields S (v₁ j))) z (ray j k) (Real.exp (T i^2)):=by
    let R:=(j:I)→ Fin (Module.finrank ℂ (S.Field (d j))); letI:Fintype R:=inferInstanceAs (Fintype ((j:I)→ Fin _)); letI: DecidableEq R:= Classical.decEq _
    let B j:= Module.finBasis ℂ (S.Field (d j)); let c(j:J×R)(i:L):ℂ:= ∏ s:I,(B s).coord (j.2 s) (v i s); let G(j:J×R)(i:L):=F j.fst i*c j i; let V(j:J×R): Labels S d:= fun i=>B i (j.2 i)
    choose C hC using hf; choose w hW using he; have hR (j:J×R): RateLE Y T (G j) (w j.1+∑ i:I,C i):= (hW _).mul (RateLE.prod (f:=fun i t=>(B i).coord (j.2 i) (v t i)) (run_towards hr) (fun i _=> pay_fixed (run_towards hr) (((B i).coord (j.2 i)).restrictScalars ℝ) (hC i)))
    let v':J×R→ Exterior _:= fun j=> v₁ j.1
    have hF(i:L): (fun a:I→E4=> ∑ j:J, F j i* whole S (centered x r i a) (v i) (bearing (v₁ j)) (fields S (v₁ j)))=(fun x₁:I→ E4=> ∑ j:J×R, G j i * whole S (centered x r i x₁) (V j) (bearing (v' j)) (fields S (v' j))) :=by
       funext z; simp only [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro j _; let f:MultilinearMap ℂ (fun j:I=> S.Field (d j)) ℂ := sectionLabels (d:=Sum.elim d _) (fields S (v₁ j)) (m:=Orbits.moment S (beside (centered x r i z) (bearing (v₁ j))))
       have hh (u:Labels S d): whole S (centered x r i z) u (bearing (v₁ j)) (fields S _)= f u:= (sectionLabels_apply ..).symm
       change F j i*whole S (centered x r i z) _ _ _=_
       rw [hh]; have he:f (v i) = ∑ p:R,c (j,p) i • f (V (j,p)):=by
           have h'(w:Labels S d):w=fun j:I=>∑ p, ((B j).coord p (w j)) • B j p:=funext fun j=>Eq.symm ((B j).sum_repr _)
           conv_lhs=> rw [h' (v i)]
           rw [MultilinearMap.map_sum]; exact Finset.sum_congr rfl fun j _=>f.map_smul_univ ..
       rw [he, Finset.mul_sum]; refine Finset.sum_congr rfl fun a _=>?_ ; unfold G v'; rw [mul_assoc]; change F j i * _ = F j i*(c (j,a) i * _); rw [hh]; rfl
    simp_rw [show ∀ i:L,(fun z => ∑ j:J, F j i * whole S (centered x r i z) (v i) (bearing (v₁ j)) (fields S (v₁ j)))=_ from hF]
    filter_upwards [eventually_all.mpr (fun i:I=>eventually_all.mpr (fun j:Axis=>arcsW (F:=G) (V:=V) U v' hr hr₀ (fun j=>⟨_,hR j⟩) hx j i))] with i hi z hz j a using hi j a z hz
end YM.RG17

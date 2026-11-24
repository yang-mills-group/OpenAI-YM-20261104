import YM.OPE.Polar.Selection
import YM.OPE.Polar.Penalized
import YM.OPE.Exchange.Coherence
import YM.OPE.Exchange.Regime
/-!
# One-radius interpolation charge: panels from all detector placements
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Polar
open Function Set Filter MeasureTheory Metric Boundary Table
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U:Spec.Final C f S)
variable {P:Prescription U.sector.derivatives} {I J L : Type}[Fintype I][DecidableEq I][Fintype J] {T b r A: L→ℝ}{X:L→ I→ E4}(p:I→ C.book.Token){l:Filter L}
    (w:Mode U.sector.derivatives) (a:Axis)(v:I) (hr:Tendsto r l (𝓝[>] 0)){η M ξ:ℝ}
local notation "D"=>closedBall (0:I→E4) 1
local notation "f!"=>fun i=> P.ope w (X i) p 0
set_option quotPrecheck false
local notation "T'"=> (fun i=> run (r i))
def centered (X:L→ I→ E4)(r:L→ℝ)(i:L)(z:I→ E4) := X i+(r i/run (r i)) • z
private lemma near {x y:I→E4}(h:‖x-y‖ ≤ η)(j:I): ‖x j-y j‖ ≤ η:= (norm_le_pi_norm (x-y) j).trans h
lemma WithinRoom.extends {x x':I→ E4}{r : ℝ}(hr:0< r)(h:WithinRoom r M η x 0) (he: η>0) (hf: ‖x'-x‖ ≤ η /4*r) : WithinRoom r (M+η) (η/2) x' 0:= by
    have hv(j):= near hf j
    constructor
    · intro i; linarith only [c_dist_point (x' i) (x i) 0,h.span i,hv i, mul_pos hr he]
    intro i j hi; linarith only [h.spaced i j hi,c_dist_point (x i) (x' i) (x j), c_dist_point (x' i) (x' j) (x j), hv i,hv j,norm_sub_rev (x i) (x' i)]

include hr
lemma within_centered (hη:0<η)(h:∀ᶠ i in l, WithinRoom (r i) M η (X i) 0): ∀ᶠ i in l,∀ z : I→ E4, ‖z‖≤1 → WithinRoom (r i) (M+η) (η/2) (centered X r i z) 0:=by
    have hT:=run_towards hr; filter_upwards [h,hT.eventually_gt_atTop 0, (tendsto_inv_atTop_zero.comp hT).eventually (ge_mem_nhds (show 0 < η/4 by linarith)),(loglife hr).pos] with i hi ht hh hp z hz; apply WithinRoom.extends hp hi hη; rw [centered,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (div_pos hp ht).le]; exact (mul_le_of_le_one_right (div_pos hp ht).le hz).trans (show r i/run (r i) ≤ _ from by rw [div_eq_mul_inv,mul_comm]; exact mul_le_mul_of_nonneg_right hh hp.le)

lemma frames_safe (s:Finset (Exterior C.book))(hη:0<η): ∀ᶠ i in l,∀ z:I→ E4, WithinRoom (r i) M η z 0 → ∀ u∈ s, Apart (η/2 * r i) (beside z (bearing u)):=by
    -- most by finite then apply
    have hh:∀ u∈s, ∀ᶠ i in l,∀ z:I→E4,WithinRoom (r i) M η z 0→ Apart (η/2*r i) (beside z (bearing u)):=by
       intro u hu; have hU:= bearing_clear u; obtain ⟨hv,hV,hY⟩:= beside_distinct.mp hU
       have hT:=tendsto_nhds_of_tendsto_nhdsWithin hr; let f(a:ℝ)(i:L):= a*r i; have hA(a): Tendsto (f a) l (𝓝 0):= by simpa only [mul_zero] using! (hT.const_mul a)
       have hx(i): 0 < ‖(0:E4)-bearing u i‖:= norm_pos_iff.mpr (sub_ne_zero.mpr (hY () i)); have he:∀ᶠ i in l, Apart (f (η/2) i) (bearing u):=eventually_all.mpr fun i=> eventually_all.mpr fun j=> eventually_all.mpr fun h=> (hA _).eventually (gt_mem_nhds (norm_pos_iff.mpr (sub_ne_zero.mpr (hV.ne h))))
       filter_upwards [eventually_all.mpr (fun i=> (hA (η/2+M)).eventually (gt_mem_nhds (hx i))),he, (loglife hr).pos] with i hv he hr z hz; refine Apart.seams ?_ he ?_
       · intro j k h; exact lt_of_lt_of_le (mul_lt_mul_of_pos_right (show η/2<η by linarith only [hη]) hr) (hz.spaced j k h)
       intro j k; linarith only [show (η/2+M)*r i < ‖(0:E4)-bearing u k‖ from hv k,c_dist_point (0:E4) (z j) (bearing u k),hz.span j,norm_sub_rev (z j) 0] -- f needs unfold
    filter_upwards [(eventually_all_finset s).2 hh] with i hi z hz u hu using hi u hu z hz

omit hr [Fintype J] in
lemma Radiates.sum {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X] (f:J→X→ℂ){x v:X}{s:Finset J}{P:J→ℝ}(h:∀ i∈s,Radiates (f i) x v (P i)): Radiates (fun x=>∑ i∈s,f i x) x v (∑ i∈s,P i):=by
    induction s using Finset.induction with
    | empty => simp only [Finset.sum_empty]; exact ⟨fun _=>0,fun x _=>differentiableAt_const _,fun _ _=>rfl,fun _ _=>(norm_zero (E:=ℂ)).le⟩
    | insert j s hj ih=> simpa only [Finset.sum_insert hj] using (h j (Finset.mem_insert_self ..)).add (ih fun i hi=>h i (Finset.mem_insert_of_mem hi))
-- no Fintype J actually omit! use finset Exterior.

include U hr p
local notation "D'"=> (fun i=> r i/run (r i))
set_option maxHeartbeats 400000 in
lemma turnways (hη:0<η)(h:∀ᶠ i in l, WithinRoom (r i) M η (X i) 0) : ∀ᶠ i in l,∀ z:I→E4, ‖z‖≤1 → ∃ K:Ortho, ‖(forwards K).val-basis a‖<knobSize I ∧ Radiates (fun z=> P.ope w (centered X r i z) p 0) z (ray v K) (Real.exp (run (r i)^2*(3/4))) :=by
    let Q:= (P.sheet w).support; let K'(x:(Q: Set (Exterior C.book))):= I⊕ Fin x.val.n
    letI(x:(Q:Set (Exterior C.book))): Fintype (K' x):= inferInstanceAs (Fintype (I⊕Fin x.val.n)); letI(x:(Q:Set (Exterior C.book))): DecidableEq (K' x):= Classical.decEq _
    -- BEWARE DecidableEq K' vs standard; use implicit equations if `∀ᶠ hTilt...`
    obtain ⟨Z,u,hu,hU,hZ⟩:= chooseTilt (K:=K') a (knobSize I) knob_pos -- syntax
    let C' := ∑ e∈Q, ‖(P.sheet w) e‖; let y(e:Exterior C.book) : I⊕Fin e.n→ C.book.Token:= beside p e.letter; let x:= centered X r
    let p':= D'; let T'':= T'; have hT':= run_towards hr; have hz:RateIs l T'' p' (-1):=((loglife hr).div (Wallet.clock hT')).swap (by ring)
    have hr':=hz.tends neg_one_lt_zero hT';
    have hu': ∀ᶠ i in l, 3* p' i ≤ u * (η/2/2*r i):=by
       filter_upwards [hz.pos,(tendsto_inv_atTop_zero.comp hT').eventually (ge_mem_nhds (show 0<u*η/16 from by positivity)),(loglife hr).pos] with i _ hP hr; have hW: r i/run (r i)≤ r i*(u*η/16):= by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hP hr.le
       unfold p'; nlinarith only [mul_pos hu (mul_pos hη hr),hW]
    have hC:∀ᶠ i in l, C' ≤ Real.exp (T'' i^2/4):=by
       filter_upwards [(Real.tendsto_exp_atTop.comp hT').eventually_ge_atTop C',hT'.eventually_ge_atTop 4] with i hi hv using le_trans hi (Real.exp_monotone (by nlinarith only [show 4 ≤ T'' i from hv]))
    have hTilt:= (eventually_all_finset Q).mpr (fun i hi=> tilted_radius U (y i) Z hT' (δ:=1) hz (hr'.eventually (ge_mem_nhds zero_lt_one))) -- Lean argument stick?
    filter_upwards [within_centered hr hη h, frames_safe (I:=I) (M:=M+η) hr Q (half_pos hη), hz.pos,(loglife hr).pos, hC, hTilt,hu'] with i ht he hp hv hh hT hΦ z hz
    let A:= x i z; let B(e: Exterior C.book):= beside A (bearing e); let s:= Q; let W(e:(Q:Set (Exterior C.book))) (u: K' e):= B e.val u; let d:= η/2/2*r i; have hd : 0< d:= by unfold d; positivity
    obtain ⟨K,hK,hV⟩:= hZ W fun e=> (he _ (ht z hz) e.val e.property).coin hd.le
    refine ⟨K,hU _ hK,?_⟩; let g (e: Exterior C.book)(z:I→E4):=(P.sheet w) e* Prescription.reading S (x i z) p 0 e; let a:= Real.exp (T'' i^2/2); let C₀ (e: Exterior C.book):= ‖(P.sheet w) e‖*a
    have hx: Radiates (fun z=> P.ope w (x i z) p 0) z (ray v K) (∑ i∈s, C₀ i):=by
       apply Radiates.sum g; intro e hh; let t:=B e; let v':= ray v K; let u(i'):ℝ:= if i' = v then p' i else 0; let q:=beside u (fun _ : Fin e.n => (0:ℝ));
       have hp' : Reserve K (B e) q (p' i):= sep_power _ _ hu hd (he _ (ht z hz) e hh) K (hV ⟨e,hh⟩) (fun j=> by rcases j with j|j; change |u j|≤_; exact (by by_cases h:j=v <;> simp [hp.le,abs_of_nonneg hp.le,u,h]); exact (abs_zero.trans_le hp.le)) hΦ
       obtain ⟨F,hf,hF,hc⟩:= hT e hh K hK (B e) q hp'
       apply Radiates.smul _ (f:=fun z=> Prescription.reading S (x i z) p 0 e); refine ⟨F,hf,fun y hy=> ?_,hc⟩
       obtain ⟨hx,hf⟩:=hF y hy; let V':= z+y • v'; have he: beside (centered X r i V') (bearing e)=along (B e) K q y:=by
           funext j; rcases j with j|j
           · by_cases h:j=v; subst j
             · simp [V',v',ray,B,A,x,q,u,along,centered, smul_add, smul_smul, ← add_assoc, p']; rw [mul_comm y]
             simp [V',v',ray,x,B,A,centered,q,u,along,h]
           simp [B,q,along]
       have hi:hx=hx:=rfl; unfold Prescription.reading; simp only [sub_zero]; change F _ = if Injective (beside (centered X r i V') (bearing e)) then _ else _; rw [if_pos (he.symm ▸ hx),he]; exact hf
    apply hx.mono; unfold C₀; rw [← Finset.sum_mul]; exact (mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le).trans_eq (by rw [← Real.exp_add]; unfold T''; congr 1; ring)
end YM.OPE.Polar

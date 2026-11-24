import YM.FVAAlt2.Rocket.Lodge
/-!
# Paying the `Atlas.orders` and `Atlas.readiness` from pre and post window
    and converting thermal-to-measuring tests of the frame.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Lodge.Track
open Function Set Filter MeasureTheory Topology Real Finset Lattice RG Precision Gauge
open Oracle Epoch Calibration Rocket Uniform Binding Diagram Ledger Taping Atlas
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X:Type}(T:Track X){G:Gauge}
def ticketT : Epoch.Marked T.entire :={l:= T.depth,Z:= T.fill,gap:= fun i=> T.surface i.volW, cap:=fun _=> (Real.exp_pos _).le,live:= T.ht_live,steps:=T.moved, distant:=fun k=> le_trans (by norm_num: (2:ℝ)≤3) (T.surf_min _) }
set_option quotPrecheck false
local notation "Q"=> T.ticketT
local notation "L"=> T.lumber
local notation:max "P_" x:max=>Page.opening T.entire x
lemma credit_for(i:Page T.entire): T.fill i.bindW ≤ (Q).credit i:=by unfold Epoch.Marked.credit; change T.fill i.bindW ≤ 1+T.fill i.bindW+_; linarith [abs_nonneg ((Q).peak i)]
lemma life_for(i:Page T.entire): (L).val i.bindW ≤ (Q).age_t.val i:= ENNReal.ofReal_le_ofReal (T.credit_for i)
lemma structural : (Q).Structural:=by
    refine ⟨ (Poly.roof _).mono fun i=> (ENNReal.ofReal_le_ofReal (T.length_pay i.volW)).trans (T.life_for i.prev), (Poly.roof _).mono fun i=> (ENNReal.ofReal_le_ofReal (T.length_pay i.volW)).trans (T.life_for i.next) ⟩
variable {K:KernelChoices}(Y:Oracle.Program K)(Z:∀ P:Patch,P.Branches K G) {u p:ℕ}
-- anticipatory post-price bound. fixed before choosing polynomial payer window, no time dependent costs assumed.
open Atlas
abbrev bills (G:Gauge){K:KernelChoices}(Y:Oracle.Program K)(J Lbar:ℕ) (Z:∀ P:Patch,P.Branches K G)(p u:ℕ):ℝ≥0∞:= if h:4 ≤ J ∧ 3 ≤ Lbar ∧ Odd Lbar then
    glowF G Y Z p u ⟨ ⟨Lbar,by have hL:= h.2.1; omega⟩,J,h.1,h.2.1,h.2.2 ⟩ + glowPage G Y u J else 0
lemma bills_f (J L':ℕ): bills G Y J L' Z p u≠⊤:=by
    unfold bills; split; exact ENNReal.add_ne_top.mpr ⟨ gf_f G Y Z _, gpage_f G Y _⟩; exact ENNReal.zero_ne_top
lemma pays (i:Flap T.entire):
   bills G Y (T.J i.volW) (T.L i.volW).val Z p u = glowF G Y Z p u (T.desk.pactP i)+ glowPage G Y u (T.J i.volW) := by unfold bills; rw [dif_pos (show _ ∧ _ from ⟨ le_trans (Nat.le_add_right 4 1) (T.issued _),T.stands _,T.owns _⟩)];rfl
local notation "ζ"=> (1/2:ℝ)
variable (hh:∀ w,bills G Y (T.J w) (T.L w).val Z p u ≤ ENNReal.ofReal (T.fill w))
include hh
lemma top_off (x:X):glowPage G Y u (T.J x)≤ (L).val x:=by
    let i:Flap T.entire:=⟨x,0,by unfold entire long; have h:=T.life x; positivity⟩
    have he:= hh i.volW; rw [pays T Y Z i] at he; exact le_add_self.trans he
lemma field_p (hp:p+2≤u)(hk:3≤u)(hv:∀ w, orders G Y p u (T.J w) ζ (by norm_num) (by norm_num) ≤ (T.L w).val): SatisfiesQ G Y T.desk Z Q p u ζ:=by
    refine ⟨fun _=>rfl,T.structural,hk,hp, (Poly.roof _).mono fun x=>?_,(Poly.roof _).mono fun x=>(T.top_off Y Z hh x.bindW).trans (T.life_for _),by norm_num,by norm_num, fun i=>T.issued _,fun i=>hv _⟩
    have he:= hh x.volW; rw [pays T Y Z x] at he; exact le_self_add.trans (he.trans (T.life_for x.prev))
omit hh
lemma peak_point(x:X):(Q).peak (P_ x)=0:= by rw [Marked.peak,show (Q).l _=1 from pow_zero _,log_one]
include Y G Z
lemma credits : OfAge Q L:=by
    let F:Tent T.entire := fun _=> Calibration.dawn
    refine co_age T.desk G Y Z (D:=native T.entire) ?_ F
    refine ⟨fun _=>rfl,T.opens,?_ ,?_,?_⟩
    · exact ((Poly.oneQ _).add (Poly.roof _)).mono fun i=> by change ENNReal.ofReal (1+T.fill i)≤ 1 + ENNReal.ofReal (T.fill i); simpa using! (ENNReal.ofReal_add_le : ENNReal.ofReal (1 + T.fill i) ≤ _) -- lhs etc
    · let A:=T.lumber; let v:=2*log 8; apply Poly.mono (g:=fun i=>ENNReal.ofReal (log 8)+2*(A.val i)*(A.val i)) ?_ (fun i=>?_) 
      · exact (Poly.standard _ ENNReal.ofReal_ne_top).add (((Poly.standard _ (by finiteness : (2:ℝ≥0∞)≠⊤)).mul (Poly.roof _)).mul (Poly.roof _))
      rw [T.thick]; apply ENNReal.ofReal_add_le.trans (add_le_add_right _ _); change ENNReal.ofReal (_* _ )≤2* ENNReal.ofReal (T.fill i) * ENNReal.ofReal (T.fill i) 
      apply le_trans (b:= ENNReal.ofReal (2*T.fill i*T.fill i)) _ _
      · apply ENNReal.ofReal_le_ofReal; have hx:=T.above i; have H:1 ≤ T.fill i:= T.filled i; have hT:1≤ T.Θ i:=T.space_hi _; exact mul_le_mul (mul_le_mul_of_nonneg_left ((T.hallL i).trans hx) (by norm_num)) hx (zero_le_one.trans hT) (by positivity)
      rw [ENNReal.ofReal_mul (by have h:=T.filled i; positivity),ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤ 2)]; simp
    simpa only [T.opens,log_one,neg_zero,ENNReal.ofReal_zero] using! (Poly.standard (L) (u:=0) ENNReal.zero_ne_top)
end YM.RegulatorIR.FVAAlt2.Lodge.Track

import YM.RegulatorIR.Cluster.Zodiac

/-! Telescoping of products from the top mesh. Estimates also cover positive
ranks, wrapped and unwrapped fields after relevant composition. Uses coarse
precost Ward inequality only on cover. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Function Set Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Uniform Gradient Step Diagram Ledger Ledger.Sky Ledger.Sky.Accounts Collapsed
open scoped ENNReal NNReal Topology BigOperators Classical
variable {W I Z: Type}{M:W→ℕ} {X Y:Page M→Type} {S: Sky X Y}{T:S.Accounts}
  {p e u r H b n q:ℕ}{L:Meter W}{J:Composite I}{A:I→(w:Page M)→ Orders (X w)}
  {v:I→Page M→ℝ≥0∞}{D:I→ W→Set Room}{d:W→ℝ}{m:I→ℕ}{t:W→ℝ≥0∞}
  {c:Flap M→ℝ≥0∞}{x:W→Room}

structure Corporate (S:Sky X Y)(T:S.Accounts)(A:I→(w:Page M)→Orders (X w))(R: (w:Page M)→Orders (X w))(p:ℕ) (m:I→ℕ)(J:Composite I): Prop where
  gather : ∀ w,R (Page.opening M w)=chargeC J A (Page.opening M w)
  lift : ∀ w,(S.frames w).each (J.accounts m) (T.bulk w.prev) (R w.prev)= R w.next
  consent : ∀ w i,i≤p → (S.sight w).Way (R w.prev) i
variable (G:Milieu S T q p L)
include G in
private lemma space_prices (w): CostRow (S.sight w).space p:=by
 intro i hi
 obtain ⟨c,hc,H⟩:= G.core.prices 0 (Nat.zero_le _) i hi
 refine ⟨c w,hc.cost w,fun x y=>le_trans ?_ (H w x)⟩
 exact le_trans (mul_one _).ge (le_trans (mul_le_mul_right ((show _ from ((Premium.rooted (native _ (S.high w) 0) _).uses _)).width_unit y) _) (term_le ..))
private lemma straight_prices (B:S.Lead u c)(w): CostRow (S.sight w).straight p:=by
 intro i hi; let C:=c w
 have H:Layer.height (S.sight w).pole (c w):= fun x y=> row_to_sup (B.down w) y x
 refine ⟨C,ne_top_of_le_ne_top ENNReal.one_ne_top (B.cap w),fun x z=>?_⟩
 change ‖Step.inert _ _ _ _ _ _‖ₑ ≤ C
 unfold Step.inert; split_ifs; exact H ..; rw [enorm_zero]; exact bot_le

variable (J : Composite I) {R:(w:Page M)→Orders (X w)} (Y₀:Zodiac L S v D J d H t x)
 (B:Crown L S T A p (u+u+b) D v d m J)
 (V₀: Corporate S T A R p m J)
 (L': S.Lead u c)
 (ha: H≤ b)(hu: u+u+b≤q)
include B G Y₀ hu
include ha in
lemma forced (i) (hi:i≤p) r : Claim (flapL M L) (fun w=> S.coverQ x u w.next) (fun w=>t w.volW) (fun w=> (S.frames w).each (J.accounts m) (T.bulk w.prev) (chargeC J A w.prev) i r - chargeC J A w.next i r) := by
 have hp:= any_joins S.lifts (Vac S T) (G.fund hu) (G.solid (show u+u ≤ q by omega)) _ B.folded
 let R (w:Flap M):= drop S.lifts (Vac S T) J m (fun i w=> A i w.prev) w
 have hv: Folds p (flapL M L) (estate S.high (Exit S.lifts) (fun i=> area J D i.volW) (u+u)) (fun w=> t w.volW) R:=fun e hi j=>Carry.charge (hp e hi j) (Y₀.salary ha)
 have hh:= Y₀.final_width B R hv i hi r
 convert hh using 1; ext1 w; unfold R drop; rw [B.continuity_at w]; rfl

include V₀
lemma rawStorage (w): Bill (R w) p:=by
 have hv : ∀ (w:W) i,i ≤ p → ∀ r,0<r→ markQ (S.coverQ x u (Page.opening _ w)) (R (Page.opening _ w) i r)≠⊤:=by
    intro w i hi r _
    rw [V₀.gather]
    have hx:= S.hl (Page.opening M w)
    apply Claim.cost (Y₀.each_width B i hi r)
    apply ENNReal.mul_ne_top _ (Y₀.stays w)
    apply ENNReal.inv_ne_top.mpr; unfold heightP; exact pow_ne_zero _ ((ENNReal.ofReal_pos.mpr hx).ne')
 have ht:= S.preserves (p:=p) (x:=x) T R G.core G.sky hv (show u ≤ q by omega) (J.accounts m) (fun w i _ r _=>by unfold reportOut; rw [V₀.lift w,sub_self]; exact ne_top_of_le_ne_top ENNReal.zero_ne_top (quota_zero _).le)
 intro i hi r; exact ne_top_of_le_ne_top (ht w i hi r) (quota_mono _ (fun z=> (S.coverQ x u w).width_unit z))

def exceed (A:I→(w:Page M)→Orders (X w)) (R:(w:Page M)→ Orders (X w))(w):= R w-chargeC J A w
omit G Y₀ B hu in
lemma initiates (w:W): exceed J A R (Page.opening M w)=0:=by unfold exceed;rw [V₀.gather, sub_self]
omit Y₀ in
lemma potential : ∀ w,Ranks (J.accounts m) (R w):= by
 refine Page.proves (fun w=> ?_) (fun i h=>?_)
 · rw [V₀.gather]; exact (B.shape.graded _).1
 rw [← V₀.lift i];exact GridStep.each_shape _ ( (G.fund hu).vac i) (J.accounts m) h
omit B Y₀ V₀ G hu in
lemma ticket_price (w:Page M): ticket 1 t w=t w.bindW:=by unfold ticket; simp
include L'
omit G Y₀ B hu V₀ in
lemma small_gain : S.Softness u L c 1 1:= ⟨L',by simp, by simp,fun w=>by simpa using L'.cap w,by simpa using! Poly.oneQ _,fun _=>le_rfl⟩
include ha
-- full result through p; point estimates for each composite before k (this walk)
lemma imprint : S.Imprints T (exceed J A R) u p (J.accounts m) x 1 t 1 L := by
 let P:= chargeC J A
 have ht: ∀ w,CostRow (S.sight w).space p:=space_prices G
 have hh: ∀ w,CostRow (S.sight w).straight p:= straight_prices L'
 have hv w i (hi:i ≤ p): (S.sight w).Way (exceed J A R w.prev) i:= by
    unfold Strip.Way exceed
    rw [sub_shot _ (hh w) (rawStorage G J Y₀ B V₀ hu _) (B.product_price _) hi,sub_shot _ (ht w) (rawStorage G J Y₀ B V₀ hu _) (B.product_price _) hi,B.ways hh ht _ _ hi, V₀.consent w i hi]
 refine ⟨?_, ?_, hv,?_,by grind,Y₀.stays⟩
 · intro i hi r hr; convert Claim.zeroQ using 1; ext1 w; rw [initiates J V₀ w]; rfl
 · intro i hi r; convert forced G J Y₀ B ha hu i hi r using 1
   · ext1 w; exact ticket_price w.prev
   ext1 w
   unfold reportOut; unfold exceed; rw [← V₀.lift w]
   have hM:= each_minus (n:=J.accounts m) (w:=w) (A:=fun w=>R w.prev) (B:=fun w=>P w.prev) S.lifts (Vac S T) (G.fund hu) (G.solid hu) (rawStorage G J Y₀ B V₀ hu _) (B.product_price _) hi
   change ((S.lifts.grid w).each (J.accounts m) (Vac S T w) (R w.prev) i r - P w.next i r) - (S.lifts.grid w).each (J.accounts m) (Vac S T w) (R w.prev-P w.prev) i r= _
   rw [hM,Pi.sub_apply]; change _= (S.lifts.grid w).each (J.accounts m) (Vac S T w) (P w.prev) i r-P w.next i r; abel
 intro w e _ i he; by_cases hx:R w e i=0
 · exact (B.shape.graded w).1 e i (fun hv=> he (by unfold exceed;change R w e i- J.product (fun j=>A j w) e i=0; rw [hx,hv,sub_self]))
 exact potential G J B V₀ hu w e i hx

lemma gapClaim (e) (he : e ≤ p) r: Claim (coverL M L) (S.coverQ x u) (fun w=> t w.bindW) fun w=>exceed J A R w e r:=by
 have ht:= imprint G J Y₀ B V₀ L' ha hu
 have hh:= small_gain (L:=L) L'
 cases r with
 | zero=>
   apply Carry.mono (Carry.charge (S.till T _ G.core G.sky hh ht (by omega) he) (Carry.mono (Carry.unit ..) (fun w=>by rw [show ticket _ _ _=t _ from ticket_price (Page.opening M w.bindW)];exact le_rfl)))
   intro w; dsimp only; rw [quotaNote, initiates J V₀]
   simp [note]
 | succ r=>
    convert S.glides T _ G.core G.sky hh ht (by omega) e he _ (show 0<r+1 by omega) using 1; ext1 w; exact (ticket_price w).symm

/-- Normalized full product at every page of the fine era, conditional on the
single columns. -/
theorem settled : Folds p (coverL M L) (S.coverQ x u) (fun w=> (heightP S.l H w)⁻¹*t w.bindW) R:=by
 intro i he r; have hp: Claim (coverL M L) (S.coverQ x u) (fun w=>(heightP S.l H w)⁻¹*t w.bindW) (fun w=> exceed J A R w i r):= by
    apply Carry.charge (gapClaim G J Y₀ B V₀ L' ha hu i he r) (Carry.mono (Carry.unit ..) (fun w=> (one_mul _).ge.trans (mul_le_mul_left (Y₀.grows_height w) _)))
 convert hp.add (Y₀.each_width B i he r) using 1; ext1 w;change _=R w i r-_+_; rw [sub_add_cancel]
end YM.RegulatorIR.Cluster

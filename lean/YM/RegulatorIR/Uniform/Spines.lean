import YM.RegulatorIR.Uniform.RelaxMark

/-! Pulling out (exactly, before bounding) the same-rank non-strict
contribution. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Uniform
open Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Diagram Function Finset
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W Z:Type} {X Y : W→Type} {r:ℕ}

lemma first_payment {I: Type}(F:ℕ→Orders I)(n:ℕ→ℕ)(e j:ℕ) : heated n F e j=F 0 e j+∑ i∈range (n e),F (i+1) e j:=by unfold heated; rw [Finset.sum_range_succ',add_comm]

lemma crop_plus {I J:Type} (f:I↪J) (T S:Packet J r): crop f (T+S)=crop f T+crop f S:=rfl
lemma crop_diff {I J:Type}(f:I↪J)(T S:Packet J r): crop f (T-S)=crop f T-crop f S:=rfl
lemma offer_diff {I J:Type}(f:I↪J)(T S:Packet I r): offer f (T-S)=offer f T-offer f S:=by
 have ht:= Diagram.offer_sum' f (T-S) S;rw [sub_add_cancel] at ht; rw [ht,add_sub_cancel_right]
lemma draft_diff {I:Type}(K:Layer I I)(T S:Packet I r)[Fintype I]: draft K (T-S)=draft K T - draft K S:=by rw [← add_left_inj (draft K S),← Diagram.draft_add];rw [sub_add_cancel,sub_add_cancel]

section Split
variable {I:Type}
lemma ray_split (K:Layer I I)(T S:Packet I r) {A:Tariff I}(B:Premium A) {c:ℝ≥0∞} (h:row (swap K) A id id c)(ht:markQ B T≠⊤)(hs:markQ B S≠⊤)(hc:c≠⊤)(i:Fin r):
       ray i (T+S) K = ray i T K + ray i S K := by
 have H (T:Packet I r)(q:markQ B T≠⊤) : Summable (Function.uncurry (swivel i T K)):=
    quota_summable (w:=fun v=>B.width v.1) (fun x=> B.width_unit _) (ne_top_of_le_ne_top (by exact ENNReal.mul_ne_top q hc) (ray_charge i T h))
 funext y
 change (∑' z,swivel i (T+S) K y z) = _+_
 unfold ray; simp_rw [swivel,Pi.add_apply,mul_add]
 exact Summable.tsum_add ((H T ht).comp_injective (show Injective fun z:I=> (y,z) from fun _ _ h=>congr_arg Prod.snd h) : Summable (swivel i T K y)) ((H S hs).comp_injective (show Injective fun z:I=>(y,z) from fun _ _ h=>congr_arg Prod.snd h) : Summable (swivel i S K y))
lemma draft_split (K:Layer I I)(T S:Packet I r) {A:Tariff I}(B:Premium A) {c:ℝ≥0∞} (h:row (swap K) A id id c)(ht:markQ B T≠⊤)(hs:markQ B S≠⊤)(hc:c≠⊤): draft K (T+S)= draft K T + draft K S:= by
 have H (x:List (Fin r)): drawing (T+S) K x=drawing T K x+drawing S K x:= by
   induction x with
   | nil=>rfl
   | cons i s ih=>
      rw [drawing,drawing,drawing,ih]; apply ray_split _ _ _ B h _ _ hc
      exact ne_top_of_le_ne_top (by finiteness) (mark_draw (B:=B) h _ _); exact ne_top_of_le_ne_top (by finiteness) (mark_draw (B:=B) h _ _)
 unfold draft; rw [H,symmetry_sum']
end Split

section Assemble
-- any stage gauge orbit. l arbitrary positive.
variable (P : Post X Y){L:Meter W}{u b:ℕ} {D:(w:W)→Layer (X w) (X w)} (h:∀ w,Layer.Sym (P.deck w) (P.deck w) (D w))(hk:Beam L (P.cone u) D)
include h hk
variable [∀ w,Fintype (Y w)]
lemma rolls {U:(w:W)→ℕ→Orders (X w)}{F:(w:W)→ℕ→Orders (Y w)} (e j:ℕ)(n:ℕ→ℕ) (hr:∀ i,Workday L (P.cone u) (fun w=>U w i e j))(he:∀ w i,(P.deck w).Ready (U w i e j))
   (H:∀ i,0 < i → Claim L (P.pear u) 1 (P.vgap (fun w=>U w i e j) (fun w=> F w i e j))):
  Claim L (P.pear u) 1 (fun w=>
        draft (P.wrapK D w) (heated n (F w) e j)- (P.deck w).deckSum (draft (D w) (heated n (U w) e j))-
        draft (P.wrapK D w) (P.vgap (fun w=>U w 0 e j) (fun w=>F w 0 e j) w)):=by
 let A:= fun w=>∑ i∈range (n e), U w (i+1) e j; let B:= fun w=>∑ i∈range (n e), F w (i+1) e j
 have hl: Workday L (P.cone u) A:= Workday.sum (fun i w=>U w (i+1) e j) _ (fun _ _=>hr _)
 have hp :Claim L (P.pear u) 1 (P.vgap A B) := Post.gap_sum _ (fun i (_:i∈range (n e))=> H (i+1) (by omega)) (fun i _=>hr (i+1))
 convert P.draft_budget_mark hk h hp using 1
 ext1 w
 let K:= D w; let K':= P.wrapK D w
 obtain ⟨k,hk,H⟩:= hk
 have hP:= Workday.sum (fun i w=>U w i e j) (range (n e+1)) (fun i _=>hr i)
 obtain ⟨c,hc,hP⟩:=hP
 have he': (P.deck w).Ready (heated n (U w) e j):= Deck.ready_sum _ _ (fun i _=>he w _)
 rw [Packet.draft_per _ (h w) he' (H w).1 (H w).2 (show localQ (P.cone u w) _ _ from hP w) (hk.cost w) (hc.cost w)]
 obtain ⟨a,ha,H⟩:=hr 0;obtain ⟨b,hb,G⟩:=hl
 simp_rw [first_payment (U w),first_payment (F w), Post.vgap]; rw [Deck.desk_sup (P.deck w) (H w) (ha.cost w) (G w) (hb.cost w)]
 change draft K' ( _+ _) - draft K' (_+_)- _ = _; rw [draft_add,draft_add,draft_diff,draft_diff]; abel

-- mark scalar zero extension should preserve entirely. For k=0,j=0, no mark norm assumptions from other tasks, but all scalars finite. Incoming source estimates may omit all scalar bounds.
variable {x: W→Room}{v t:W→ℝ≥0∞}
lemma rolls_mark {U:(w:W)→ℕ→Orders (X w)}{F:(w:W)→ℕ→Orders (Y w)} (e j:ℕ)(n:ℕ→ℕ) (hr:∀ i,j+i>0→ Claim L (P.rooted x u) t fun w=>U w i e j)(ht:∀ w,t w≠⊤)
   (H:∀ i,0 < i → Claim L (P.anchored x u) v (P.agap (fun w=>U w i e j) (fun w=>F w i e j))):
  Claim L (P.anchored x u) v (fun w=> draft (P.wrapK D w) (heated n (F w) e j)-(P.deck w).scroll (draft (D w) (heated n (U w) e j))-draft (P.wrapK D w) (P.agap (fun w=>U w 0 e j) (fun w=>F w 0 e j) w)):=by
 let A:= fun w=>∑ i∈range (n e), U w (i+1) e j; let B:= fun w=>∑ i∈range (n e), F w (i+1) e j
 have hl: Claim L (P.rooted x u) t A:= Claim.sum (fun i w=>U w (i+1) e j) _ (fun _ _=>hr _ (by omega))
 have hp : Claim L (P.anchored x u) v (P.agap A B) := Post.gap_range _ (fun i (_:i∈range (n e))=> H (i+1) (by omega)) (fun i _=>hr (i+1) (by omega)) ht
 convert P.draft_budget_mark hk h hp using 1
 ext1 w
 let K':= P.wrapK D w
 obtain ⟨k,hk,H⟩:=hk
 have hu : markQ (P.rooted x u w) (U w 0 e j)≠⊤:=by
    cases j with
    | zero=>
       let T:=U w 0 e 0; let X:= (P.rooted x u w)
       have hX (y:Tuple _ 0): X.width y=1:=by simp [Premium.width,Tariff.diameter];
       change quota T X.width≠⊤; unfold quota; simp_rw [hX,mul_one]; simp
    | succ l=>exact Claim.cost (hr 0 (by omega)) w (ht w)
 let X:= (P.rooted x u w)
 have hz : markQ X (A w) ≠ ⊤:= Claim.cost hl w (ht w)
 have hT: markQ X (heated n (U w) e j) ≠ ⊤:= by rw [first_payment]; exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hu,hz⟩) (quota_add ..)
 rw [Packet.draft_scroll _ (h w) hT (H w).1 (H w).2 (hk.cost w)]
 have h₁ := ne_top_of_le_ne_top hu (quota_mono (U w 0 e j) (w:=1) fun y=> X.width_unit y)
 have h₂ := ne_top_of_le_ne_top hz (quota_mono (A w) (w:=1) fun y=> X.width_unit y)
 simp_rw [first_payment (U w),first_payment (F w), Post.agap];rw [Deck.scroll_sup (P.deck w) h₁ h₂]
 change draft K' (_+_)-draft K' (_+_)-_=_; rw [draft_add,draft_add,draft_diff,draft_diff]; abel
end Assemble
end YM.RegulatorIR.Uniform

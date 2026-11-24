import YM.RegulatorIR.Uniform.Claim

/-! At a step use a common radius for one account; restrict budget parameters
separately between steps. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Uniform
open Function Budget Spatial Motion Budget.Packet Budget.Tuple Diagram Budget.Layer Budget.Deck Budget.Tariff
open scoped ENNReal Topology BigOperators Classical
variable {W:Type}{I J: W→ Type}{r : ℕ}

structure Post (I J : W→Type) where
 period : W→ℝ
 positive : ∀ w, 0<period w
 length : W→ℝ
 spacing : ∀ w, 0<length w
 deck : ∀ w, Deck (period w) (I w) (J w)
namespace Post
variable (A:Post I J)

def cone (k:ℕ) w := (native (A.length w) (A.spacing w) k).uses (A.deck w).pos
def per (k:ℕ)(w) := (onFold _ (A.positive w) _ (A.spacing w) k).uses (A.deck w).atO
def pear (k:ℕ) (w) : Premium (A.per k w) := (Premium.remnant _ (A.positive w) _ (A.spacing w) k).uses (A.deck w).atO

def wrapK (K:(w:W)→Layer (I w) (I w))(w:W):Layer (J w) (J w):= wrapL (A.deck w) (A.deck w) (K w)

variable {L:Meter W} {K:(w:W)→Layer (I w) (I w)} {h k:ℕ}
lemma descent (H:Beam L (A.cone h) K)(hh : k ≤ h):Beam L (A.cone k) K:=by
 obtain ⟨f,hf,H⟩:=H
 have hz w (x y:I w): (A.cone k w).road x y ≤ (A.cone h w).road x y:= moment_mono (A.spacing ..) hh dist_nonneg
 exact ⟨_,hf,fun w=>⟨Layer.row_mono (hz w) (H w).1,Layer.row_mono (hz w) (H w).2⟩⟩
lemma writes {T:(w:W)→Packet (I w) r}(H: Workday L (A.cone h) T)(ht:k≤h): Workday L (A.cone k) T:=by
 obtain ⟨f,hf,H⟩:=H
 have hh w (x:Tuple (I w) r): (A.cone k w).diameter x ≤ (A.cone h w).diameter x:=Tariff.diam_mono (fun (i j:I w)=>moment_mono (A.spacing w) ht (dist_nonneg (x:=(A.deck w).pos i) (y:=(A.deck w).pos j))) _
 exact ⟨_,hf,fun w i x=>(quota_mono (fun z:Hold i x=>T w z.val) (fun z=> hh w z.val)).trans (H w i x)⟩
lemma wrap_beam (H:Beam L (A.cone h) K)(hK: ∀ w,Layer.Sym (A.deck w) (A.deck w) (K w)):Beam L (A.per h) (A.wrapK K):=by
 obtain ⟨f,hf,H⟩:=H; refine ⟨_,hf,fun w=>⟨(row_cost _ _ _ (A.positive w) (A.spacing w) h (H w).1),?_⟩⟩
 rw [show swap (A.wrapK K w)=wrapL (A.deck w) (A.deck w) (swap (K w)) from funext fun x=>funext fun y=>other _ _ _ (hK w) y x]; exact row_cost _ _ _ (A.positive w) (A.spacing w) h (H w).2
lemma draft_budget_mark {T:(w:W)→Packet (J w) r}{B:(w:W)→ Premium (A.per h w)}{v}(H:Beam L (A.cone h) K)(hK:∀ w,Layer.Sym (A.deck w) (A.deck w) (K w))(ht:Claim L B v T): Claim L B v (fun w=>Packet.draft (A.wrapK K w) (T w)):= Claim.draft_budget ht (A.wrap_beam H hK)
lemma deck_work {T:(w:W)→Packet (I w) r}(H: Workday L (A.cone h) T)(ht:∀ w,(A.deck w).Ready (T w)) : Workday L (A.per h) (fun w=>(A.deck w).deckSum (T w)) :=by
 obtain ⟨f,hf,H⟩:=H; exact ⟨_,hf,fun w=> deck_local (A.deck w) (A.positive w) (A.spacing w) h _ (ht w) (H w)⟩

-- needs room n count (proved on labels in applications)
def weight (b:ℕ) (w: W) := ∑' j, (amount (A.length w) b (Spatial.singular (A.period w) ((A.deck w).atO j)))⁻¹

variable {u b:ℕ}
lemma forged {T:(w:W)→Packet (I w) (r+2)}(HH:Workday L (A.cone ((u+b)+(u+b))) T)(Hb:Beam L (A.cone (u+b)) K)(hr:∀ w,(A.deck w).Ready (T w))(hk:∀ w,Layer.Sym (A.deck w) (A.deck w) (K w))(hC:Poly L (A.weight b))(x:Fin r) :
    Claim L (A.pear u) 1 (fun w=> loop ((A.deck w).deckSum (T w)) (wrapK A K w) - (A.deck w).deckSum (loop (T w) (K w))):=by
 obtain ⟨f,hf,H⟩:=HH; obtain ⟨g,hg,G⟩:=Hb
 exact Carry.regular (Poly.mono ((hg.mul hf).mul hC) fun w=> loop_error_cost (A.deck w) (A.positive w) (A.spacing w) u b (hk w) (hr w) (G w).1 (hg.cost w) (H w) (hf.cost w) x)

-- Mark target budget; permit rescale between fine and coarse lengths separately

def rooted (x:W→Room)(u:ℕ)(w) : Premium (A.cone u w) := (Premium.rooted (native _ (A.spacing w) u) (x w)).uses (A.deck w).pos
def anchored (x:W→Room)(u:ℕ)(w) : Premium (A.per u w):= (Premium.rooted (onFold _ (A.positive w) _ (A.spacing w) u) (x w)).uses (A.deck w).atO
-- gain explicitly in physical distance

def toll (x:W→Room) (u:ℕ) w := amount (A.length w) u (Spatial.singular (A.period w) (x w))
lemma toll_top (x:W→Room) (u w) : A.toll x u w ≠ ⊤:=by unfold toll amount; finiteness
lemma toll_pos (x:W→Room) (u w) : 0 < A.toll x u w:= zero_lt_one.trans_le (amount_unit (A.spacing w) u (singular_nonneg ..))
lemma toll_divide {x:W→Room}{f: W→ℝ≥0∞}{v: W→ℝ≥0∞}(h: Carry L v (fun w=> f w * A.toll x u w)): Carry L (fun w=>v w*(A.toll x u w)⁻¹) f :=by
 apply Carry.mono (Carry.scale (w:=fun w=>(A.toll x u w)⁻¹) h)
 intro w; exact (show f w * _ * _ = f w by rw [mul_assoc,ENNReal.mul_inv_cancel (A.toll_pos x u w).ne' (A.toll_top x u w), mul_one]).ge
lemma folded_claim (x:W→Room){v}{T:(w:W)→Packet (I w) r}(h:Claim L (A.rooted x u) v T): Claim L (A.anchored x u) v (fun w=>(A.deck w).scroll (T w)) := Carry.mono h fun w=> scroll_bound (A.deck w) (A.positive w) (A.spacing w) u (x w) (T w)
lemma narrower (x:W→Room){v:W→ℝ≥0∞}{T:(w:W)→Packet (I w) r}(h:Claim L (A.rooted x b) v T)(hh:u≤b): Claim L (A.rooted x u) v T := Carry.mono h (fun w=> quota_mono _ fun _=>Premium.prem_mono (fun a b=>amount_sp w hh a b) (fun _=>moment_mono (A.spacing ..) hh dist_nonneg) _)
where
 amount_sp w (h : u≤b) (i j : I w) :(A.cone u w).road i j ≤ (A.cone b w).road i j:= moment_mono (A.spacing ..) h dist_nonneg
lemma loop_marked (x:W→Room) {t:W→ℝ≥0∞}{T:(w:W)→Packet (I w) (r+2)}(H:Beam L (A.cone b) K)(hT:Claim L (A.rooted x ((u+b)+b)) t T)(ht:∀ w,t w≠⊤)(hk:∀ w,Layer.Sym (A.deck w) (A.deck w) (K w)) :
 Claim L (A.anchored x u) (fun w=> t w*(A.toll x b w)⁻¹) (fun w=>loop ((A.deck w).scroll (T w)) (wrapK A K w) - (A.deck w).scroll (loop (T w) (K w))) :=by
 apply A.toll_divide; obtain ⟨f,hf,F⟩:= H
 exact Carry.mono (Carry.mul_left hf hT) (fun w => loop_source_cost (A.deck w) (A.positive w) (A.spacing w) u b (hk w) (F w).1 (hf.cost w) _ le_rfl (Claim.cost hT w (ht w)))

lemma cross_claim {s:ℕ}(x:W→Room) {D:(w:W)→Layer (J w) (J w)} {T:(w:W)→Packet (J w) (r+1)} {U:(w:W)→Packet (J w) (s+1)}{t:W→ℝ≥0∞}
      (H:Beam L (A.per (u+b)) D) (hx:Claim L (A.anchored x (u+b)) t T)(ht:Claim L (A.pear (u+b)) 1 U):
    Claim L (A.anchored x u) (fun w=> t w * (A.toll x b w)⁻¹) (fun w=>knot (D w) (T w) (U w)):=by
 obtain ⟨f,hf,F⟩:= H; apply A.toll_divide
 exact Carry.mono (Carry.mul_right hx ((Carry.admit ht (Poly.oneQ ..)).mul hf)) (fun w=> Budget.crossed_mark _ (A.positive w) _ (A.spacing w) (A.deck w).atO (x w) u b (T w) (U w) (D w) (F w).2)
end Post
end YM.RegulatorIR.Uniform

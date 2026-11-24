import YM.RG01Estimate.FurrowFlags
/-! # Wrapped-gather budget committed before fus. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Censor.Fresco
open Function Filter Set Lattice Wilson RG Progress.DirectedRecipe AnalyticBridge VerifiedReset Collection Averaging Ovens Ovens.Pipes
   Payments Extra.Iteration Pilgrim
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}{p:BudgetPoint}{hn:20<n.val}(Q:Pilgrim p n hn)
   {L:Pipes G n}{d c b : Tap G n} {δ w A C H V Δ ε γ u δ' : ℝ}

-- both wraps (regular and soft) on this step; throw and prices. expose actual τ hyper.
def intake (p:BudgetPoint)(hn:20<n.val)(T:ℝ) := Fintype.card (Seat n)*(T*Real.exp ((p.supportExponent+1)*((coin p n hn :ℝ)+81)))
def priceWrap (G:Gauge)(p:BudgetPoint)(Δ:ℝ)(hn:20<n.val):= intake p hn ((1+turnFee p)*toll G Δ p)
lemma wrap_nn (G:Gauge)(p:BudgetPoint)(Δ:ℝ)(hn:20<n.val): 0 ≤ priceWrap G p Δ hn:=by
   have hp:= toll_nn G p Δ; have ht:= turnFee_pos p; unfold priceWrap intake; positivity
lemma addons :
   let q:=priceWrap G p Δ hn
   let t (_:Seat n):= turnFee p*toll G Δ p
   let h (_:Seat n):= toll G Δ p
   (∀ i,p.supBounds i.snd (Seat.spread i Q.X) (Pilgrim.tea G Δ i) (t i)) ∧
     (Quotes.anchored p (fun x:Seat n=> x.reg Q.X Q.anchored) t q)∧ Ac.Hit (fun x:Seat n=> x.spread Q.X) p.B h (p.supportExponent+1) q:=by
   intro q t h
   have hp := toll_nn G p Δ; have hX:= p.exponent_pos; have ht:=turnFee_pos p
   have hg i:coverNumber p.B (Seat.spread i Q.X)≤ coin p n hn+81:= (Seat.visit_count i Q.X).trans_le Q.pays
   let s:ℝ:=(1+turnFee p)*toll G Δ p*Real.exp ((p.supportExponent+1)*((coin p n hn:ℝ)+81)); have hs:0 ≤ s := by unfold s; positivity
   refine ⟨fun i=> Q.tea_pays .. |>.2.2.2,fun o=> ?_,fun o=> ?_⟩
   · refine Push.AbsoluteSums.budget_mono (Cost.finite _ hs) (fun i=>?_) (fun (i : Seat n)=>?_)
     · split <;> first| exact le_rfl|exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg ht.le hp)
     split
     · change Real.exp _ * (turnFee p*toll G Δ p) ≤ s; unfold s
       rw [mul_comm]; refine mul_le_mul ?_ ?_ (Real.exp_nonneg _) (mul_nonneg (by positivity) hp)
       · exact mul_le_mul_of_nonneg_right (by linarith) hp
       apply Real.exp_monotone; apply mul_le_mul (by linarith : p.supportExponent ≤ p.supportExponent+1) _ (Nat.cast_nonneg _) (by linarith); exact_mod_cast hg i
     exact hs
   refine Push.AbsoluteSums.budget_mono (Cost.finite _ hs) (fun i=>?_) (fun (i:Seat n)=>?_)
   · split <;> first|exact le_rfl|exact mul_nonneg hp (Real.exp_nonneg _)
   split
   · change toll G _ _ * _ ≤ s; apply mul_le_mul (le_mul_of_one_le_left hp (by linarith)) ?_ (Real.exp_nonneg _) (mul_nonneg (by positivity) hp)
     apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ (by linarith); exact_mod_cast hg i
   exact hs

-- payments for regular error sector *alone*, post-budget mask. Main numbering retained for Eq.
def excess (n:Side) : Set ℕ:= fun i=> (numbering (Main n) i).isRight -- booleans
lemma logistics {ε γ: ℝ} (hd:(L.pours d).EBound p ε)(he:(L.pours c).EBound p γ):
   let X:= ((combine Q L).pours (pour Q Δ d c b))
   X.EBound p (ε+(γ+priceWrap G p Δ hn)) ∧
     Activities.EBound {X with E:=fun i=> if i∈excess n then X.E i else 0} p (γ+priceWrap G p Δ hn):=by
   intro X; obtain ⟨x,hx,hP⟩:= hd; obtain ⟨y,hy,hK⟩:=he; let h : Seat n→ℝ:= fun _ => turnFee p*toll G Δ p
   let q:= priceWrap G p Δ hn
   obtain ⟨hf,hS,hT⟩:= addons (G:=G) (Δ:=Δ) Q; let u:= Sum.elim x (Sum.elim y h);let N:= numbering (Main n)
   constructor
   · refine ⟨u ∘ N,fun i=> ?_,fun i=> ?_⟩
     · change p.supBounds (allot L.reg L.reg Q.X _ (N i)).site (allot L.reg L.reg Q.X _ (N i)).support (ink d.regular c.regular _ (N i)) (u (N i))
       rcases N i with i|i|i; exact hx _; exact hy _; exact hf i
     exact Cost.equiv (f:=fun k=> let H:=allot L.reg L.reg Q.X Q.anchored k; if H.site=i then p.mass H.support (u k) else 0) (numbering (Main n)) (Cost.sum (hP i) (Cost.sum (hK i) (hS i))) -- name f
   let t:= Sum.elim (0:ℕ→ℝ) (Sum.elim y h)
   refine ⟨t ∘ N,fun i=>?_, fun i=>?_⟩
   · change p.supBounds (allot L.reg L.reg Q.X _ (N i)).site (allot L.reg L.reg Q.X _ (N i)).support (if i∈excess n then ink d.regular c.regular (tea G Δ) (N i) else 0) (t (N i))
     cases he:N i
     next u=>
       rw [if_neg (show ¬ i∈excess n from by change ¬ (N i).isRight; rw [he]; simp)]; exact sup_le (sup_const 0) (by simp [t])
     next v=>
       rw [if_pos (show i∈excess n from by change (N i).isRight=true; rw [he]; rfl)]
       rcases v with i|i; exact hy i; exact hf i
   suffices H : SumBudget (fun k=>let Z:= allot L.reg L.reg Q.X Q.anchored k; if Z.site=i then p.mass Z.support (t k) else 0) (0+(γ+q)) from
       Cost.equiv (numbering (Main n)) (by rw [zero_add] at H; exact H)
   apply Cost.sum _ (Cost.sum (hK i) (hS i)); simp [SumBudget,t,BudgetPoint.mass]

variable {f w':ℕ→ℝ}
lemma budgets (hv : softCost p L f V) -- insert var
    (_hh:hardCost p L w' w) (hx:Payments.rooted b w' f):
    ∃ s :ℕ→ℝ,softCost p (combine Q L) s (V+priceWrap G p Δ hn) ∧ Payments.rooted (pour Q Δ d c b) w' s:=by
   let z:= Sum.elim f (fun _:Seat n=> toll G Δ p); let Y:= iced Q Δ b; let M:=numbering (Soft n)
   have h0 i:0 ≤ z i:= by rcases i with i|i; exact hv.1 i; exact toll_nn ..
   have hL i U : ‖Y i U‖ ≤ z i:= by rcases i with i|i; exact (hx i U).2; exact ((Q.contract ..).2.2.2 U).1
   refine ⟨z ∘ M,⟨fun i=> h0 (M i),fun x=> ?_⟩,fun i U=>⟨(hx i U).1,hL ..⟩⟩
   let g : Soft n → ℝ:= fun i=> if x∈ loaf L Q.X i then z i*Real.exp ((p.supportExponent+1)*coverNumber p.B (loaf L Q.X i))else 0
   exact Cost.equiv (f:=g) M (Cost.sum (hv.2 x) ((addons Q).2.2 x))

lemma finances (hd:Fittings d L p)(hc:Fittings c L p)(hb:Fittings b L p)(hD:(L.pours d).EBound p ε)(he:(L.pours c).EBound p γ)
    (hv : softCost p L f V)(hh:hardCost p L w' w) (hx:Payments.rooted b w' f) (hR: Rates p.B A w (V+priceWrap G p Δ hn) u)(hF : ε+(γ+priceWrap G p Δ hn) ≤ δ):
    Ingredients (combine Q L) (pour Q Δ d c b) p δ A:=by
    obtain ⟨s,hs,hY⟩:= budgets (Q:=Q) (Δ:=Δ) hv hh hx
    exact Payments.tender (mixes Q hd hc hb Δ) (Time.E_rises (logistics Q hD he).1 hF) hh hs hY hR
end YM.RG01Estimate.Censor.Fresco

import YM.RegulatorIR.Epoch.Banking

/-! Costs generating K matrices (α pre.L scalar).
Amounts in Ly. quorum F structural explicit. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Epoch
open Function Set Filter Finset Lattice RG Gauge Budget Budget.Packet Budget.Tuple Budget.Layer Geometry Momentum Oracle Uniform YM.RegulatorIR.Ledger Step Taping ENNReal Exterior Laurent Bloch
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X:Type}{M:X→ℕ}{k:ℕ}{G : Gauge}{n:Page M→Side}
namespace League
-- common cohort can meet monotonic lengths. Mark R uses sign.E etc.

def stampE (S:Oracle.Circuit M n)(Z:X→ℝ)(h:∀ w,0≤ Z w): Marked M where
 l:=S.l
 gap i:= (S.sizeL i).val
 Z:=Z
 cap:=h
 live:=S.l_p
 steps:= S.width_s
 distant i:= by exact_mod_cast (le_trans (by decide:2 ≤ 3) (S.holds i))

variable {K : KernelChoices}(S:Circuit M n) (Y:Program K)
lemma minted_calc (i: Flap M)(R:List Axis)(h:R.length ≤ S.J i.prev-2): (Precision.advanceC (S.sizeL i) (S.tells Y i) R).strip (Y.receipt.α (S.J i.prev)) (Y.receipt.Ω (S.J i.prev)/((S.sizeL i).val:ℝ)^(1+R.length)):=by
 let j:=S.J i.prev; let m:=S.J i.next; let P:=S.crew i
 have hp:= S.honored Y i.prev;have hz:= S.honored Y i.next
 have hm:Next.Free.Mag j m:= ⟨S.week _,S.week _,by have he:m≤ j:= S.shakes _;have h:j≤ m+1:= S.slow _;omega⟩
 have hx: Next.Free.HopQuote K j m (Y.fees j) (Y.fees m) _ _ _ _:= Y.hailed.hop j m hm
 exact ((hx P).1 R h).1
lemma discount_p (G:Gauge)(i:Flap M)(p k:ℕ)(h:p≤ S.J i.prev-2): let j:=S.J i.prev; PriceW (ruling (S.pactP i) G (S.tells Y i)) (S.sizeL i).val k p (pack_c G k (Y.receipt.α j) (Y.receipt.Ω j)):=by
 intro j; let a:= S.honored Y i.prev; exact grant G _ a.card.pos a.card.paid fun l hl=> minted_calc S Y i l (hl.trans h)
end League
namespace Reserve
variable (S:Marked M)
def maskA (i:Page M)(θ:ℝ):ℝ≥0∞ := ENNReal.ofReal (Real.exp ((S.peak (Page.opening M i.bindW)-S.peak i)*θ))
def peak_M (θ) := fun i:Page M=> maskA S i θ
def maskB (θ:ℝ) (i:Page M):ℝ≥0∞:= ENNReal.ofReal (Real.exp ((S.peak (Page.opening M i.bindW)- min (S.peak i) 0)*θ))
lemma both (θ:ℝ)(i:Page M): maskA S i θ= -- change
 ENNReal.ofReal ((S.l (Page.opening M i.bindW)/S.l i)^θ):=by
 unfold maskA; rw [Real.rpow_def_of_pos (div_pos (S.live _) (S.live _)), Real.log_div (S.live _).ne' (S.live _).ne'];rfl
lemma mask_live (i:Page M)(θ): maskB S θ i≠⊤:= ENNReal.ofReal_ne_top
lemma meets (i) {θ:ℝ}(ht:0≤θ):maskA S i θ ≤ maskB S θ i:=by
 apply ENNReal.ofReal_le_ofReal; apply Real.exp_monotone;gcongr; exact min_le_left ..
lemma tactics (θ): S.More (peak_M S θ) θ:= by
 intro i; apply le_of_eq; change _=ENNReal.ofReal _*ENNReal.ofReal _;rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]; unfold peak_M maskA; rw [← Real.exp_add, S.mark_P]; congr 2; have h:i.next.bindW=i.prev.bindW:=rfl;rw [h];ring
lemma shadow {θ:ℝ}(ht:0≤ θ): S.More (maskB S θ) θ:=by
 intro i; change _≤ ENNReal.ofReal _* ENNReal.ofReal _;rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]; unfold maskB; rw [← Real.exp_add]; apply ENNReal.ofReal_le_ofReal; apply Real.exp_monotone; rw [← add_mul,show i.next.bindW=i.prev.bindW from rfl]; gcongr; by_cases h:S.peak i.prev≤0
 · have he:min (S.peak i.next) 0≤ S.peak i.prev + S.slope i:= min_le_left .. |>.trans_eq (S.mark_P i)
   rw [min_eq_left h]; linarith
 rw [min_eq_right (lt_of_not_ge h).le]; linarith [min_le_right (S.peak i.next) 0,S.rise i]
lemma medium (D:Choice M)(h:∀ w,S.peak (D.choose w)=0)(θ:ℝ)(ht:0≤θ): Marked.Balancer D (maskB S θ):=by
 constructor
 · intro i hv; unfold maskB;rw [min_eq_left (S.debit D h _ hv),min_eq_left (S.debit D h _ (le_trans (show i.prev.downW≤_ from Nat.le_succ _) hv)),S.mark_P, show i.next.bindW=i.prev.bindW from rfl];gcongr; have ht:= S.rise i; linarith
 intro i hv; unfold maskB; rw [min_eq_right (S.credit_p D h _ hv), min_eq_right (S.credit_p D h i.next (le_trans hv (show i.prev.downW ≤ i.next.downW from Nat.le_succ _))),show i.next.bindW=i.prev.bindW from rfl]
end Reserve
end YM.RegulatorIR.Epoch

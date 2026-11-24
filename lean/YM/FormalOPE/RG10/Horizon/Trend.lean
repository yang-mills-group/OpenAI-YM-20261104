import YM.FormalOPE.RG10.Horizon.Deposit

/-! # One-sided formal coefficient estimates

Keeping fixed shape information, NO claims of cost uniform over nearby shapes. Distinct weight
proxies, usable for padded near and when throwing away one or more high grades. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Clearing
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD Panel Panel.Consumer InversionTop
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle Arrangements Apertures Transit Route Capture Weave Film
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Ledger Rates
variable {G:Gauge}{F:Frames G}{R:Rails F}{P:Plan F}{Y:Drivers}{Z:Patience P Y}{r m d h n:ℕ}
namespace Limits
variable {α β γ s t:ℝ} {p q : ℕ} {x y:ℝ→fps} {F' G': ℝ→ℝ} {I:Type*}
/-- A size, with log length tending to infinity, so ordinary-power precision ξ, fixed budget. -/
def Maintains (α:ℝ) (f : ℝ→ℝ) := ∃ (b:ℕ)(C:ℝ),0≤ C ∧ ∀ᶠ t in atTop, f t≤ cash t C b α

local notation "κ" => Real.exp
lemma jackets {f g v :ℝ→ℝ} (hf : Maintains α f) (hx : Maintains α g) (hk : ∀ t,v t ≤ f t+g t): Maintains α v:=by
 obtain ⟨b,B,hB,hf⟩:=hf; obtain ⟨a,A,hA,hx⟩:=hx
 refine ⟨max b a,A+B,by positivity,?_⟩
 filter_upwards [hf,hx] with t ht hb; apply (le_trans (hk t) (le_trans (add_le_add ht hb) ?_)); simp_rw [cash, legUp]; rw [← add_mul, add_mul (a:=A),add_comm (A* _)]
 apply mul_le_mul_of_nonneg_right _ tilt_pos.le
 apply add_le_add <;> gcongr <;> (first|exact Position.Grade.Polys.rise t|simp)
lemma balanced {f g h' : ℝ→ℝ} (hf: Maintains α f)(hx: Maintains β g) (hk : ∀ s, 0 ≤ f s) (ht : ∀ s, h' s ≤ f s*g s): Maintains (α+β) h':= by
 obtain ⟨b,B,hB,hf⟩:=hf; obtain ⟨a,A,hA,hx⟩:=hx
 refine ⟨b+a,A*B,by positivity,?_⟩
 filter_upwards [hf,hx] with t h h'; apply ((ht t).trans (mul_le_mul_of_nonneg_left h' (hk t))).trans
 apply (mul_le_mul_of_nonneg_right h (cash_nn hA ..)).trans_eq
 simp_rw [cash,legUp, tilted,pow_add]; ring
lemma recline {f g:ℝ→ℝ} (hf: Maintains β f) (hx :∀ᶠ t in atTop,g t ≤ f t) (he:α≤β) : Maintains α g:= by
 obtain ⟨b,B,hB,hf⟩:=hf; refine ⟨b,B,hB,?_⟩; filter_upwards [hf,hx,eventually_ge_atTop 0] with t ht hx hs; exact hx.trans (ht.trans (mul_le_mul_of_nonneg_left (shade he hs) (leg_nn _ _ _ hB)))

lemma previous (h : Polys F') : Maintains 0 fun x=> ‖F' x‖ := by obtain ⟨d,C,hc,h0⟩:=h; exact ⟨d,C,hc,Eventually.of_forall fun x=> by simp [cash,no_tilt]; exact h0 x⟩
lemma history (f:I→ℝ→ℝ) (S:Finset I) (h : ∀ i∈S, Maintains α (f i)): Maintains α (fun t=> ∑ i∈S,f i t) := by induction S using Finset.induction_on with
 | empty=> exact ⟨0,0,le_rfl, Eventually.of_forall (fun _=>by simp [cash,legUp])⟩
 | insert i S hi ih=> simp_rw [sum_insert hi]; exact jackets (h i (mem_insert_self ..)) (ih fun i hi=> h i (mem_insert_of_mem hi)) (fun _=>le_rfl)

-- exposed costs, polynomial growth, one-sided, *charge before applying to a theory*
def Salaried (r:ℕ) (α:ℝ) (f:ℝ→fps) := Maintains α fun s=> coin r (f s)
namespace Salaried

lemma le (hx: Salaried r β x) (he : α≤β): Salaried r α x:= recline hx (Eventually.of_forall (fun _=> le_rfl)) he
lemma of_eq (hx : Salaried r α x) (hz:∀ᶠ t in atTop, Through r (x t) (y t)): Salaried r α y := recline hx (hz.mono fun _ he=> he.fare.symm.le) le_rfl
lemma inside {q:ℕ}(h:q≤r) (hx:Salaried r α x): Salaried q α x:= recline hx (Eventually.of_forall (fun s=>by
 rw [cstate,cstate]; exact sum_le_sum_of_subset_of_nonneg (range_mono (Nat.add_le_add_right h 1)) (fun _ _ _=>norm_nonneg _))) le_rfl
lemma added (hx: Salaried r α x)(hy:Salaried r α y): Salaried r α (x+y):= jackets hx hy fun _=> coin_add ..
lemma multiplied (hx:Salaried r α x) (hy:Salaried r β y) : Salaried r (α+β) (x*y):= balanced hx hy (fun _=>coined _) fun _=> coin_mul ..
lemma neg (hx: Salaried r α x): Salaried r α (-x):= recline hx (Eventually.of_forall fun _=> (coin_neg _).le) le_rfl
lemma diff (hx: Salaried r α x)(hy: Salaried r α y): Salaried r α (x-y):= by rw [sub_eq_add_neg]; exact added hx hy.neg
lemma warp (T:Tuned R Z) (hx: Salaried r α x) : Salaried r α (fun s=>R.flow.warp s (x s)):= by
 let H (n m) (s:ℝ):=‖coeff m (x s) * coeff n (R.flow.psi s ^ m)‖; let G (n:ℕ) (s:ℝ):= ‖coeff n (x s)‖
 have hG i (hi:i≤r) : Maintains α (G i):= recline hx (Eventually.of_forall fun _=> rstate _ hi) le_rfl
 have he (i j:ℕ) (hi:j≤r) : Maintains α (H i j) := (add_zero α) ▸ balanced (hG _ hi) (previous (R.ok.wheels T.smooth j i)) (fun _=> norm_nonneg _) fun _=> (norm_mul ..).le
 let S:=Finset.range (r+1)
 have hv i (hu:i∈S) : Maintains α (fun s=> ‖coeff i (R.flow.warp s (x s))‖):= by
   have hε : i ≤ r := by simpa [S] using hu
   refine jackets (hG i hε) (history (H i) (Finset.range i) (fun j hj=> he i j ((mem_range.mp hj|>.le).trans hε))) ?_
   intro t; rw [Flow.through]; exact (norm_add_le ..).trans (add_le_add (le_refl _) (norm_sum_le ..))
 unfold Salaried; simp_rw [cstate]; exact history _ _ hv

lemma zeros : Salaried r α (fun _=>0):= ⟨0,0, le_rfl,Eventually.of_forall fun _=>by simp [cash, legUp, coin]⟩
lemma current (t:fps): Salaried r 0 (fun _=>t) := ⟨0,coin r t, coined t,Eventually.of_forall fun _=>by simp [cash,no_tilt,legUp]⟩
lemma immediate (hf : ∀ᶠ t in atTop, coin r (x t)≤ tilt t α) : Salaried r α x:= ⟨0,1,by positivity,hf.mono (fun s hs=>by simpa [cash,legUp] using hs)⟩
lemma trust (h :∀ i≤r, Polys (fun t=> tilt t (-α)* coeff i (x t))) : Salaried r α x := by
 obtain ⟨b,B,hb,H⟩:=Rates.earn h; refine ⟨b,B,hb,Eventually.of_forall (fun t=>?_)⟩
 have he:= mul_le_mul_of_nonneg_right (H t) (tilt_pos (s:=t) (ξ:=α) |>.le)
 rw [Real.norm_of_nonneg (mul_nonneg tilt_pos.le (coined _)),mul_comm (tilt t (-α)),mul_assoc,← tilted,neg_add_cancel,no_tilt,mul_one] at he; exact he

lemma priced {f:I→ℝ→fps}(S:Finset I)(h:∀ i∈S,Salaried r α (f i)) : Salaried r α (fun s=> ∑ i∈S,f i s) := recline (history (fun i s=> coin r (f i s)) _ h) (Eventually.of_forall fun _=> coin_fore ..) le_rfl
lemma cross {f:I→ℝ→fps} (β:I→ℝ) (S:Finset I)(h:∀ i∈S,Salaried r (β i) (f i)) : Salaried r (∑ i∈S,β i) (fun s=>∏ i∈S,f i s) := by
 induction S using Finset.induction_on with
 | empty=> simp_rw [sum_empty,prod_empty]; exact current _
 | insert i S hi ih=> simp_rw [sum_insert hi,prod_insert hi]; exact multiplied (h i (mem_insert_self ..)) (ih fun i hi=> h i (mem_insert_of_mem hi))
end Salaried
end Limits
end YM.FormalOPE.RG10.Clearing

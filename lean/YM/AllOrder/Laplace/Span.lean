import YM.AllOrder.Laplace.Gateway
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace
open PertExtension.Series Radial Tested MeasureTheory Function Set Filter Metric
open scoped Topology ENNReal ContDiff Classical
variable {a' b' k':ℕ} {f f' g h:ℝ→ℝ→ℝ}{a b c:ℕ→ℝ}{F G:ℝ→ℝ}{l n:ℕ}
lemma one_part (k:ℕ) {a b : ℕ→ℝ} (h:Bill (k+1) (peval a k-peval b k)) (he:∀ i<k,a i=b i): a k=b k := by
   obtain ⟨C,hC,H⟩:=h; by_contra hn
   have hv:0 < |a k-b k| := abs_pos.mpr (sub_ne_zero.mpr hn)
   obtain ⟨t,ht,hK,hL⟩:= (H.and (Tested.eventually_small (show 0 < |a k-b k| / (C+1) by positivity))).exists
   change ‖(peval a k t-peval b k t)‖ ≤_ at ht; unfold peval Zone.eval at ht; rw [Finset.sum_range_succ,Finset.sum_range_succ, show ∑ i∈Finset.range k,t^i • a i=∑ i∈Finset.range k,t^i• b i from Finset.sum_congr rfl (fun i hi=> he i (Finset.mem_range.mp hi) ▸ rfl), add_sub_add_left_eq_sub,← smul_sub,norm_smul,Real.norm_of_nonneg (pow_nonneg hK.le _),Real.norm_eq_abs,pow_succ] at ht
   have hx:= (lt_div_iff₀ (show 0 < C+1 by linarith)).mp hL
   nlinarith [pow_pos hK k]
lemma one_part' (k:ℕ) {a b:ℕ→ℝ} (h:Bill (k+1) (F-peval a k)) (hh:Bill (k+1) (F-peval b k))(he:∀ i<k,a i=b i): a k=b k:= one_part k (by rw [show _-_=_ from (show peval a k-peval b k= -(F-peval a k)+(F-peval b k) by abel)]; exact bill_add (bill_neg h) hh) he
lemma Receipt.unique (h:Receipt f a)(hh:Receipt f b): a=b:= by
 funext k; induction k using Nat.strong_induction_on with
 | h k ih=> obtain ⟨δ,H,H'⟩:= ((h k).and (hh k)).exists; exact one_part' k H H' ih
lemma polarize (h:Bill n F)(hH:Bill n G) {g':ℝ→ℝ}(he:F≤ᶠ[Tested.germ] g')(ht:g' ≤ᶠ[Tested.germ] G):Bill n g':=by
   obtain ⟨C,hC,H⟩:=h; obtain ⟨D,hD,H'⟩:=hH; refine ⟨C+D,add_nonneg hC hD,?_⟩
   filter_upwards [H,H',he,ht,Tested.eventually_pos] with i h₁ h₂ h' h hI; rw [Real.norm_eq_abs] at *; exact abs_le.mpr ⟨by linarith [(abs_le.mp h₁).1,(show 0≤D*i^n by positivity),show F i≤g' i from h'], by linarith [(abs_le.mp h₂).2,(show 0≤C*i^n by positivity), show g' i≤ G i from h]⟩ -- rw at * might fail
/-- every small collar bounds *some* small collar in the target order -/
def FansOut (f g:ℝ→ℝ→ℝ):Prop:= ∀ᶠ δ in Tested.germ,∀ᶠ ε in Tested.germ, f ε≤ᶠ[Tested.germ] g δ
/-- all small collars can be squeezed from above and below by some outer and inner collars arbitrarily small. -/
lemma fan_unique (hf: Receipt f a)(hg:Receipt g b)(h:FansOut f g)(he:FansOut g f):a=b:=by
 funext k; induction k using Nat.strong_induction_on with
 | h k ih=>
    obtain ⟨δ,hδ,H⟩:= ((hf k).and he).exists; obtain ⟨ε,hε,Q,H'⟩:= ((hg k).and (H.and h)).exists; obtain ⟨η,hη,K⟩:= ((hf k).and H').exists
    have hh := polarize hη hδ (show (f η-peval a k)≤ᶠ[Tested.germ] (g ε-peval a k) from (show f η≤ᶠ[Tested.germ] g ε from K).mono fun i hi=> sub_le_sub_right hi _) ((show g ε≤ᶠ[Tested.germ] f δ from Q).mono fun i hi=> (sub_le_sub_right hi _ : g ε i - peval a k i≤ f δ i - _))
    exact one_part' k (F:=g ε) hh hε ih
-- density product
private lemma power_proj (x y:ℕ→ℝ) (n:ℕ) (k:ℕ)(hk:k≤n) : conv (fun i=> if i≤n then x i else 0) (fun i=> if i≤n then y i else 0) k= conv x y k := by
 rw [conv,conv,term,term,PowerSeries.coeff_mul,PowerSeries.coeff_mul]; apply Finset.sum_congr rfl; intro i hi; have hi:= Finset.mem_antidiagonal.mp hi; simp only [PowerSeries.coeff_mk,if_pos (show i.1≤n from (by omega)), if_pos (show i.2≤n from (by omega))]
lemma bill_mul (h:Bill a' F) (hh:Bill b' G): Bill (a'+b') (F*G):= bill_of (by convert (of_bill h).mul (of_bill hh) using 1 <;> first | rfl| simp)
lemma bill_cross (h:Bill n F) (hh:Bill 0 G): Bill n (F*G):=bill_mul h hh
lemma bill_pe (a:ℕ→ℝ) (n:ℕ) : Bill 0 (peval a n) := bill_of (by convert (Aspiration.of_test (Aspiration.polynomial a n)).priced using 1)
lemma bill_est (h:Bill n (F - peval a k')): Bill 0 F := by rw [←sub_add_cancel F (peval a k')]; exact bill_add (bill_ge h (Nat.zero_le _)) (bill_pe ..)
lemma bill_prod (hf:Bill (n+1) (F - peval a n))(hg:Bill (n+1) (G-peval b n)) : Bill (n+1) (F*G-peval (conv a b) n):= by
 have hh := bill_cross hf (bill_est hg); have ht:= bill_cross hg (bill_pe a n); have he:= ((Aspiration.polynomial a n).prod (Aspiration.polynomial b n)) n
 rw [show peval _ n=_ from (funext fun t=> (show peval (conv _ _) n t=peval (conv a b) n t from Finset.sum_congr rfl fun i hi=> congr_arg (fun x:ℝ=>t^i• x) (power_proj a b n i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))))] at he -- fix
 exact (bill_match (show _ from (by
   have hy: F*G-peval (conv a b) n=(F-peval a n)*G+(G-peval b n)*peval a n+(peval a n*peval b n-peval (conv a b) n):= by ring
   exact hy.symm ▸ EventuallyEq.refl .. )) (bill_add (bill_add hh ht) he))
lemma Receipt.multiply (hf:Receipt f a)(hg:Receipt g b): Receipt (f*g) (conv a b):= fun n=> ((hf n).and (hg n)).mono fun _ h=>bill_prod h.1 h.2
end YM.AllOrder.Laplace

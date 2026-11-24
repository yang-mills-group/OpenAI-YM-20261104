import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Order.Filter.AtTopBot.Finite

/-!
# Log filtration for proofs on multi-contact shapes

Convenient precision for numerical comparison throughout nested shapes. As the
mesh scale, radii, nested gaps, etc vary along one filter, take a positive-price
rate exponent in units of a common diverging log length. All noninteger
precision parameters are real. Upper costs here are eventual so one may use
them **inside** a proof of failure by a tending subsequence (or filter), also
when taking slower subpowers of some of the radii. Not asserting rates
independent of such choices unless by that additional argument. Uses log-scale
additions to avoid replacing a radius receipt by one at another length.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Power
open Function Filter
open scoped Topology BigOperators

structure Pace (α : Type*) where
  net : Filter α
  scale : α→ℝ
  deep : Tendsto scale net atTop

namespace Pace
variable {α X Y : Type*}
variable (P : Pace α)
def rate (c : ℝ) (x : α) := Real.exp (c*P.scale x)

def Priced [Norm X] (c : ℝ) (f : α → X) : Prop := ∀ a:ℝ, c<a → ∀ᶠ i in P.net, ‖f i‖ ≤ P.rate a i
structure Rating (c : ℝ) (f : α→ℝ) : Prop where
  pos : ∀ᶠ i in P.net,0<f i
  tends : Tendsto (fun i=>Real.log (f i)/P.scale i) P.net (𝓝 c)

def Longer (b : ℝ) (f : α→ℝ) : Prop := ∀ a:ℝ, a<b → ∀ᶠ i in P.net,P.rate a i ≤ f i -- low inequality (doesn't follow from `Priced (-b)` on inverse without positivity)

lemma eventually_pos : ∀ᶠ i in P.net, 0 < P.scale i:= P.deep.eventually_gt_atTop 0
lemma rate_mono {a b:ℝ}(h:a≤b) : ∀ᶠ i in P.net,P.rate a i ≤ P.rate b i:= P.eventually_pos.mono fun _ h' => Real.exp_monotone (mul_le_mul_of_nonneg_right h h'.le)
lemma rate_gt {a b:ℝ}(h:a<b) : ∀ᶠ i in P.net,P.rate a i < P.rate b i:= P.eventually_pos.mono fun _ h' => Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right h h')
lemma rate_pos (a:ℝ)(i:α) : 0< P.rate a i := Real.exp_pos _
lemma rate_add (a b:ℝ)(i:α) : P.rate (a+b) i=P.rate a i*P.rate b i:=by rw [rate,add_mul,Real.exp_add];rfl
lemma rate_mul (a b:ℝ)(i:α) : P.rate (a*b) i = P.rate a i ^ b :=by unfold rate; rw [mul_right_comm a b _,Real.exp_mul]
lemma rate_sink {a:ℝ}(h:a<0) : Tendsto (P.rate a) P.net (𝓝 0) := Real.tendsto_exp_atBot.comp (P.deep.const_mul_atTop_of_neg h) -- check name
lemma rate_grow {a:ℝ}(h:0<a) : Tendsto (P.rate a) P.net atTop:= Real.tendsto_exp_atTop.comp (P.deep.const_mul_atTop h)
lemma rate_grade (a:ℝ) : P.Rating a (P.rate a) := by
  refine ⟨Eventually.of_forall (P.rate_pos a),tendsto_const_nhds.congr' (P.eventually_pos.mono fun i hi=> ?_)⟩
  dsimp only; rw [rate,Real.log_exp,mul_div_cancel_right₀ _ hi.ne']
lemma literal (x:ℝ) (h:0<x) : P.Rating 0 fun _ => x := ⟨Eventually.of_forall fun _=>h, tendsto_const_nhds.div_atTop P.deep⟩

variable {P}
namespace Rating
variable {a b:ℝ} {f g : α→ℝ}
lemma equivalently (h : P.Rating a f) (he : a=b) : P.Rating b f:= he ▸ h
lemma replaces (h : P.Rating a f) (hx : f =ᶠ[P.net] g) : P.Rating a g:= ⟨(h.pos.and hx).mono fun _ h=>(h.2 ▸ h.1),h.tends.congr' (hx.mono fun i hi=>by rw [hi])⟩
lemma longer (h : P.Rating a f) : P.Longer a f := by
  intro c hc; filter_upwards [h.pos,P.eventually_pos,h.tends.eventually (lt_mem_nhds hc)] with i hi hx hk
  exact (Real.le_log_iff_exp_le hi).mp ((le_div_iff₀ hx).1 (le_of_lt (show _< _ from hk)))
lemma upper (h : P.Rating a f) {b:ℝ} (hp:a<b) : ∀ᶠ i in P.net, f i ≤ P.rate b i:= by
  filter_upwards [h.pos,P.eventually_pos,h.tends.eventually (gt_mem_nhds hp)] with i hi hx hK
  exact (Real.log_le_iff_le_exp hi).mp ((div_le_iff₀ hx).mp (le_of_lt (show _<_ from hK)))
lemma priced (h : P.Rating a f) : P.Priced a f:=fun c hc=> (h.pos.and (h.upper hc)).mono fun i hi=> by rw [Real.norm_of_nonneg hi.1.le];exact hi.2
lemma pay (h : P.Rating a f) (hh : P.Rating b g) (he : a<b) : ∀ᶠ i in P.net,f i ≤ g i:=by
  obtain ⟨v,hv,hV⟩:=exists_between he; exact ((h.upper hv).and (hh.longer v hV)).mono fun _ h=>h.1.trans h.2
lemma mul (h : P.Rating a f)(he : P.Rating b g) : P.Rating (a+b) (fun i=>f i*g i):= ⟨(h.pos.and he.pos).mono fun _ hi=>mul_pos hi.1 hi.2,(h.tends.add he.tends).congr' ((h.pos.and he.pos).mono fun i hi=> by dsimp only; rw [Real.log_mul hi.1.ne' hi.2.ne',add_div])⟩
lemma div (h : P.Rating a f)(he : P.Rating b g): P.Rating (a-b) (fun i=>f i/g i):=⟨(h.pos.and he.pos).mono fun _ hi=>div_pos hi.1 hi.2,(h.tends.sub he.tends).congr' ((h.pos.and he.pos).mono fun i hi=> by dsimp only; rw [Real.log_div hi.1.ne' hi.2.ne',sub_div])⟩
lemma inv (h:P.Rating a f): P.Rating (-a) (fun i=>(f i)⁻¹):=by simpa only [one_div,zero_sub] using (P.literal 1 zero_lt_one).div h
lemma powers (h:P.Rating a f)(n:ℝ) : P.Rating (n*a) (fun i=> f i^n):=⟨ h.pos.mono fun _ hi=>Real.rpow_pos_of_pos hi _,(h.tends.const_mul n).congr' (h.pos.mono fun i hi=> by dsimp only; rw [Real.log_rpow hi, mul_div_assoc])⟩
lemma raise (h:P.Rating a f)(n:ℕ) : P.Rating (n*a) (fun i=> f i^n):=by simpa only [Real.rpow_natCast] using h.powers (n:ℝ)
lemma prod (s:Finset X)(f:X→α→ℝ)(c:X→ℝ)(h:∀ i∈s,P.Rating (c i) (f i)) : P.Rating (∑ i∈s,c i) (fun j=> ∏ i∈s,f i j):=by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using P.literal 1 zero_lt_one
  | insert i s hi ih=>
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).mul (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
lemma alsos {Z:Type*}[Norm Z]{g:α→Z} (h:P.Rating a f)(hf:P.Priced b g)(hq:b<a): ∀ᶠ i in P.net, ‖g i‖ ≤ f i := by
  obtain ⟨p,hp,hz⟩:= exists_between hq; exact ((hf p hp).and (h.longer p hz)).mono fun i hi=> hi.1.trans hi.2
lemma maximum (h : P.Rating a f)(hx : P.Rating a g): P.Rating a (fun i=>max (f i) (g i)) := by
  refine ⟨h.pos.mono (fun i h=> lt_of_lt_of_le h (le_max_left ..)),((h.tends.max hx.tends).congr' ?_) |> ((show max a a=a from by simp) ▸·)⟩
  filter_upwards [h.pos,hx.pos,P.eventually_pos] with i hi hj hk
  rcases le_total (f i) (g i) with he|he
  · rw [max_eq_right he, max_eq_right (div_le_div_of_nonneg_right (Real.log_le_log hi he) hk.le)]
  rw [max_eq_left he,max_eq_left (div_le_div_of_nonneg_right (Real.log_le_log hj he) hk.le)]
lemma squeeze (h : P.Rating a f){g g':α→ℝ}(hg : P.Rating a g)(hL:∀ᶠ i in P.net,f i ≤ g' i)(hU:∀ᶠ i in P.net,g' i ≤ g i): P.Rating a g' := by
  have he:= (h.pos.and hL).mono fun i hi=> lt_of_lt_of_le hi.1 hi.2
  refine ⟨he,tendsto_of_tendsto_of_tendsto_of_le_of_le' h.tends hg.tends ?_ ?_⟩
  · exact (h.pos.and (hL.and P.eventually_pos)).mono fun i hi=> div_le_div_of_nonneg_right (Real.log_le_log hi.1 hi.2.1) hi.2.2.le
  exact (he.and (hU.and P.eventually_pos)).mono fun i hi=> div_le_div_of_nonneg_right (Real.log_le_log hi.1 hi.2.1) hi.2.2.le
lemma combine (h : P.Rating a f)(hx : P.Rating a g): P.Rating a (fun i=> f i+g i) := by
  apply (h.maximum hx).squeeze (((P.literal 2 two_pos).mul (h.maximum hx)).equivalently (by simp))
  · filter_upwards [h.pos,hx.pos] with i hi hj; exact max_le (by linarith) (by linarith)
  filter_upwards with i; have he:= le_max_left (f i) (g i); have he':= le_max_right (f i) (g i); linarith
lemma plus (h : P.Rating a f)(hx:P.Rating b g): P.Rating (max a b) (fun i=> f i+g i):=by
  have he {a b: ℝ} {f g:α→ℝ} (h:P.Rating a f)(hx:P.Rating b g)(hh:b<a): P.Rating a (fun i=>f i+g i):= by
    apply h.squeeze (((P.literal 2 two_pos).mul h).equivalently (by simp)); exact hx.pos.mono fun _ hi=> le_add_of_nonneg_right hi.le
    exact (hx.pay h hh).mono fun i hi=> by linarith only [hi]
  rcases lt_trichotomy a b with ht|rfl|ht
  · rw [max_eq_right ht.le]; simpa only [add_comm] using he hx h ht
  · rw [max_self]; exact h.combine hx
  rw [max_eq_left ht.le]; exact he h hx ht
lemma sink (h:P.Rating a f)(ht:a<0): Tendsto f P.net (𝓝 0):=by
   obtain ⟨v,hv,hV⟩:= exists_between ht
   exact squeeze_zero' (h.pos.mono fun i hi=> hi.le) (h.upper hv) (P.rate_sink hV)
end Rating
end Pace
end YM.Contacts.Power

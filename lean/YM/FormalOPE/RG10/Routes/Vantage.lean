import YM.FormalOPE.RG10.Routes.Packet

/-!
# Primitive connected polynomial estimate

Authenticity uses the accepted interpolation theorem. Derivation of estimate in terms of only
polynomial Schur costs *shared* in J and finite legs on the chosen monomials. Trace bill bounded
without reference to volume; can then proceed to sum over all locations, even vacuum vertices,
and get spatial suppression or rooted weights. True at *any* appearing payload; `w` is economic,
not an analytic comparison domain nor a property of other Gauge arguments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route
open MvPolynomial Finset Marker Extra.Trajectories Joins Joins.Gauss Function
open Primitives.GCC Fused Probe Growth Moment Charge Expansion Grove
open Multi.Vacuum.Gauss
open scoped Topology BigOperators Classical
variable {I J B V : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq V]
    (q : I→Row J)

def crossing (q : I → Row J) (a b : I) := |crossed (q a) (q b)|
omit [Fintype I] [DecidableEq I] in
lemma crossing_nn (a b : I) : 0 ≤ crossing q a b := abs_nonneg _
omit [Fintype I] [DecidableEq I] in
@[simp] lemma crossing_self (a : I) : crossing q a a=squares (q a) := by rw [crossing,crossed_self,abs_of_nonneg (squares_nn _)]
def cov (K : ℝ) := ∀ a, ∑ b,crossing q a b ≤ K
variable {s : Finset V} {o : V} (ho : o∈s)
variable (M : V→ Index I B)

def pipes (a : Index I B) := (fine a).support
def rank (a : Index I B) := LocalPolynomial.length (fine a)

def cotton (a : Index I B) : Row I → ℂ := LocalPolynomial.placed 0 1 (glyph (fine a))
omit [Fintype I] [DecidableEq I] in
private lemma label (x : Row I) : Primitives.GCC.Words.entry 0 1 x = fun i => (x i:ℂ) := by
  funext i; simp [Words.entry]
omit [Fintype I] [DecidableEq I] in
lemma leaks (a : Index I B) : (leaking q (glyph (fine a))).val = fun x : Unit × Row J => cotton a (mapRows q x.2) := by
  ext x; rw [leaking_apply, cotton,LocalPolynomial.placed,label]; rfl

variable {q} {K : ℝ} (hr : cov q K)
omit [DecidableEq I] in
include hr in
lemma wages (a : I) : squares (q a) ≤ K := by rw [← crossing_self]; exact (single_le_sum (fun i _ => crossing_nn q a i) (Finset.mem_univ a)).trans (hr a)
variable (d : ℕ) (hd : ∀ i∈s,rank (M i) ≤ d) (hK : 1 ≤ K)

def share (K : ℝ) (n : ℕ) := (8*K*n)⁻¹
def toll (r : ℝ) (a : Index I B) : Row I := fun i => if i∈pipes a then r else 0
omit [Fintype I] in
lemma annuities {r : ℝ} (h : 0 ≤ r) (a : Index I B) (i) : 0 ≤ toll r a i := by unfold toll; split <;> positivity

include hK in
lemma share_pos {m : ℕ} (h : 0 < m) : 0 < share K m := by
  have hr : 0<K:=by linarith
  unfold share; positivity
include hK in
lemma share_divide {m : ℕ} (h : 0 < m) : (m:ℝ) * (share K m * K) = 1/8 := by
  unfold share; have hm : 0 < (m:ℝ):= by positivity
  have hp : 0<K:=by linarith
  field_simp

local notation "℘" => share K s.card
include hr hK in
omit [DecidableEq V] in
lemma able (hs:s.Nonempty) : Moment.base (fun _ : V => q) s (fun v => toll ℘ (M v)) := by
  have hp : 0 < ℘ := share_pos hK (card_pos.mpr hs)
  apply Moment.base.of (fun i _ a => annuities hp.le (M i) a)
  intro i hi a;
  apply le_trans (b:=∑ _j∈s,℘*K) (sum_le_sum fun j _ => ?_) (by rw [sum_const,nsmul_eq_mul,share_divide hK (card_pos.mpr hs)])
  apply le_trans (b:=∑ b, ℘*crossing q a b) (sum_le_sum fun b _ => mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)) (by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hr a) hp.le)
  unfold toll; split
  exacts [le_rfl,hp.le]

omit [Fintype I] [DecidableEq I] in
lemma card_rank (a : Index I B) : (pipes a).card ≤ rank a := by
  let k:=pipes a; rw [show rank a=∑ i∈k,fine a i from rfl]
  refine le_trans (b:=∑ _i∈k,1) (by simp [k]) (sum_le_sum fun i hi => ?_);
  exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
include hd hr hK in
omit [DecidableEq V] in
lemma total_due (hs : s.Nonempty) : due s (fun _=>q) (fun i => toll ℘ (M i)) ≤ d/8 := by
  have hp : 0 < ℘ := share_pos hK (card_pos.mpr hs)
  have h (i : V) (hi : i∈s) : ∑ b, toll ℘ (M i) b * squares (q b) ≤ d*(℘*K) := by
    simp_rw [toll, ite_mul,zero_mul]; rw [← sum_filter, show Finset.filter (· ∈ pipes (M i)) univ = pipes (M i) from (by ext; simp)];
    apply le_trans (b:=∑ _∈pipes (M i),℘*K) (sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (wages hr b) hp.le) ?_
    rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ((card_rank (M i)).trans (hd i hi))) (mul_nonneg hp.le (by linarith))
  apply le_trans (b:=∑ _∈s,(d:ℝ)*(℘*K)) (sum_le_sum h) ?_
  rw [sum_const,nsmul_eq_mul, mul_left_comm,share_divide hK (card_pos.mpr hs)]
  exact le_of_eq (by ring)

def scaleCost (r : ℝ) (d : ℕ) := (d.factorial:ℝ)*(max 1 (Words.height r d))^d
lemma scale_nn (r : ℝ) : 0 ≤ scaleCost r d := by unfold scaleCost; positivity
omit [Fintype I] [DecidableEq I] in
lemma screen (a : Index I B) : LocalPolynomial.markedOn (glyph (fine a)) (pipes a) := by
  intro s hs; rw [show s=fine a from ?_]; exact Subset.rfl; exact (Finset.mem_singleton.mp (Finsupp.support_single_subset hs)) -- check
omit [DecidableEq I] in
lemma lease (a : Index I B) : Reads (pipes a) (cotton a) := LocalPolynomial.covered _ _ (screen a)

lemma incurred (a : Index I B) (r : ℝ) (h : 0 < r) (k : ℕ) (he : rank a ≤ d) :
    Probe.Costs k (cotton a) (toll r a) (fun _=>scaleCost r d) := by
  have ha : (glyph (fine a)).totalDegree ≤ d := (totalDegree_monomial_le ..).trans he
  apply Primitives.GCC.Loan.longer (LocalPolynomial.produce 0 1 (glyph (fine a)) k d ha (pipes a) (screen a) (toll r a) (annuities h.le a) r 0 h le_rfl (fun b hb=>by simp [toll,hb])).2
  intro n; apply (LocalPolynomial.pile 1 _ n d ha r 0 le_rfl).trans
  unfold LocalPolynomial.lump Words.bulk scaleCost
  rw [show (glyph (fine a)).support={(fine a)} from by exact Finsupp.support_single _ (show (1:ℂ) ≠ 0 from one_ne_zero),sum_singleton]; simp [glyph]
omit [DecidableEq V] in
include hd hK in
lemma received (hs : s.Nonempty) : Valid s s.card (fun i=> cotton (M i)) (fun i=> toll ℘ (M i)) (fun _ _ => scaleCost ℘ d) := by
  -- Valid fields?
  exact ⟨fun i hi => incurred d (M i) _ (share_pos hK <| card_pos.mpr hs) s.card (hd i hi)⟩

-- handle rough K dependency
include hK in
lemma scale_le {m : ℕ} (h : 0 < m) : scaleCost (share K m) d ≤ (d.factorial:ℝ)*(8*((d:ℝ)+1)*K*m)^d := by
  unfold scaleCost; gcongr;
  apply max_le
  · have hh : (1:ℝ) ≤ m:= by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_left hK (show 0 ≤ (d:ℝ) by positivity)] -- inspect
  unfold Words.height share
  rw [div_inv_eq_mul, ← mul_assoc,← mul_assoc]
  have hh : (1:ℝ) ≤ m:= by exact_mod_cast h
  have hr : 1 ≤ (((d:ℝ)+1)*8*K*m) := by nlinarith [mul_le_mul_of_nonneg_left hK (show 0≤ (d:ℝ) by positivity)]
  rw [mul_comm 8 ((d:ℝ)+1)] -- inspect
  generalize hd : (((d:ℝ)+1)*8*K*m) = D at *
  nlinarith [Real.sq_sqrt (zero_le_one.trans hr)]


def rent (K : ℝ) (d n : ℕ) := (scaleCost (share K n) d)^n * Real.exp ((d:ℝ)/4)
lemma rent_sign (K : ℝ) (n : ℕ) : 0 ≤ rent K d n := mul_nonneg (pow_nonneg (scale_nn d _) _) (Real.exp_pos _).le
variable {R : Census V}

open Primitives.GCC.Anchor
open scoped BigOperators
include hK hr in
theorem cumulative [Fintype V] (t : R.Mode) (hs : o∈t.val) (hu : ∀ i∈t.val,rank (M i) ≤ d) :
    ‖TallyRow q t (fun i => M i.val)‖ ≤
      ∑ f∈options t.val {o}, beams t.val {o} f (contact (fun _=>q) (pipes ∘ M)) * rent K d t.val.card := by
  let w := fun i=> toll (share K t.val.card) (M i); let u := fun i : V => cotton (M i)
  let C:= scaleCost (share K t.val.card) d
  let Q:=fun _:V=>q
  have h : Valid t.val t.val.card u w (fun _ _ => C) := received M d hu hK ⟨o,hs⟩
  have hx : Moment.base Q t.val w := able M hr hK ⟨o,hs⟩; have h' : ({o}:Finset V) ⊆ t.val:= singleton_subset_iff.mpr hs
  let k := (t.val \ {o}).card; have hk : k+1=t.val.card := by unfold k; rw [card_sdiff_of_subset h',card_singleton,Nat.sub_add_cancel]; exact card_pos.mpr ⟨o,hs⟩
  have hi : TallyRow q t (fun i=> M i.val)= mixed Q u t {o} := by
    rw [TallyRow,← award_eq (φ:=fun i => leaking q (glyph (fine (M i))))]; simp_rw [leaks];
    change (tally (standardFeed J) t (joint u Q))=_; rw [tally, recognized u, ← PolyUtil.at_marker o (accounts R Q u) (accounts_quiet ..) t hs]; rfl
  rw [hi, detail t k {o} h' rfl Q u w (fun _ _ => C) hx (hk.symm ▸ h)]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro f hf
  have he:= (choices ..).mp hf
  have hn := h.lower (show k ≤ _ by omega)
  apply (signed t.val k _ h' f he Q u w (fun _ _ => C) hx hn).trans
  apply (tree_cost t.val k _ h' rfl f he Q u (pipes ∘ M) w (fun _ _ => C) hx hn (fun i _ => lease (M i))).trans
  rw [value,rent,tags,prod_const,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (prod_nonneg (fun _ _ => contact_nn ..));
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (scale_nn d _) _); apply Real.exp_monotone
  linarith [show due t.val Q w ≤ d/8 from total_due M hr d hu hK ⟨o,hs⟩]
end YM.FormalOPE.RG10.Route

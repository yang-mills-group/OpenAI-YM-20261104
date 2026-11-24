import YM.RG3.Script.Picnic.Party

/-! # Changing marker radii during Scripts.

Supports bought at stated reserve. Doesn't change field-coordinates,
witness or actual polynomials, only prior bounds; preserve vouchers for the
cut/readable/bulk computations separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script
open Function Lattice RG Wilson Marker Overlay RG3.Forms RG3.Press RG3.Held RG3.Law RG3.Ink
  Extra.Multi Ac Push.AbsoluteSums MeasureTheory Push.Corrected Finset Extra.Iteration Edition RG3.Primary Push.Local Source Estate Picnic
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {n : Side}{V ι : Type*}[DecidableEq V]{R:Census V}{ζ : V→Site n}{G : Gauge} {w:V→ℝ}

def view (θ:ℝ)(w:V→ℝ)(i:V):=θ*w i
lemma weigh (θ:ℝ)(i:R.Mode):Poly.toll (view θ w) i=θ^i.val.card*Poly.toll w i:= by
  unfold view Poly.toll; rw [Finset.prod_mul_distrib,Finset.prod_const]
 omit [DecidableEq V] in
lemma weigh_pos {θ:ℝ}(h:0<θ)(hw:∀ i,0<w i)(i):0< view θ w i:=mul_pos h (hw _)
lemma hook (hw:∀i,0<w i){θ:ℝ}(he:0≤θ)(ht:θ≤1)(i:R.Mode)(h:i.val.Nonempty):
    Poly.toll (view θ w) i ≤ θ*Poly.toll w i:=by
  rw [weigh]; apply mul_le_mul_of_nonneg_right _ (Poly.worth hw _).le
  simpa only [pow_one] using! pow_le_pow_of_le_one he ht (Finset.one_le_card.mpr h)
lemma wake (hw:∀i,0<w i){θ:ℝ}(he:1≤θ)(i:R.Mode)(N : ℕ)(hN:i.val.card≤N):
    Poly.toll (view θ w) i ≤ θ^N*Poly.toll w i:=by
  rw [weigh]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ he hN) (Poly.worth hw _).le

lemma transfer {a C θ θ' : ℝ}{B : ℕ}{S:ι→Support n}{c:ι→ℝ}{p:ι→R.Mode}{i:V}
    (hc : ∀ i,0≤c i)(H:SumBudget (per B a w p S c i) C)(ht:∀ i,0<view θ w i)(hh : ∀ i,Poly.toll (view θ w) (p i) ≤ θ'*Poly.toll w (p i))(hθ : 0 ≤ θ'):
    SumBudget (per B a (view θ w) p S c i) (θ'*C):= by
  refine budget_mono (budget_scale hθ H) (per_nn (fun _=> (ht _).le) hc · _) (fun i=>?_); unfold per; split
  · exact (mul_le_mul_of_nonneg_right (hh i) (mul_nonneg (Real.exp_pos _).le (hc i))).trans_eq (mul_assoc ..)
  simp

lemma billboard {P:Rep G n}(d:Deck R P){a vac mark : ℝ}{B:ℕ}
    (hw:∀i,0<w i){θ:ℝ}(he:0<θ)(ht:θ≤1)(hd:∀ i j,(d.contents.marks i j).val.Nonempty)
    (Y:Billboard d.contents w B a vac mark):Hit (fun j : ℕ×ℕ=> (P.activities.forced j.1).support) B (fun i=>Poly.toll (view θ w) (d.contents.marks i.1 i.2)*Y.bill i) a (θ*mark):= by
  intro i
  refine budget_mono (budget_scale he.le (Y.advert i)) (fun j=>?_ ) (fun j=>?_)
  · split; exact mul_nonneg (mul_nonneg (Poly.worth (weigh_pos he hw) _).le (Y.bill_pos _)) (Real.exp_pos _).le; rfl
  split
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hook hw he.le ht _ (hd _ _)) (Y.bill_pos j)) (Real.exp_pos _).le).trans_eq (by ring)
  simp

variable {Θ:Type*} {P : Rep G n} (d:Taste Θ ζ P R)
  {u c κ b a θ θ' : ℝ}

namespace Picnic

def changeMenu [Nonempty Θ]{v c : ℝ}(hw:∀i,0<w i)(hm:0<θ)(h:θ≤1)(T:d.Menu w v c)(he:∀ x,(d.leaf x).Active): d.Menu (view θ w) v (θ*c) where
  store x:= {
    T.store x with
    advert:=billboard (d.leaf x) hw hm h ((he x).articles.occurs) _ }
  vac_fixed := T.vac_fixed
  bill_fixed := T.bill_fixed

variable {T:Θ→ Edition ζ R G}{f g:ℕ→ℝ}{l : ℝ}{p:BudgetPoint}
variable (hk: Voucher T p w l u c a f g) (hw:∀ i,0<w i)
include hk hw
lemma empty_price (hθ:0<θ)(h:θ≤1) : Voucher T p (view θ w) l (θ*u) (θ*c) (θ*a) f g:= by
  have ht:=weigh_pos hθ hw
  have ha z:= hk.stays z
  have he z (i:ℕ):Poly.toll (view θ w) ((T z).pins i)≤ θ*Poly.toll w _ :=hook hw hθ.le h _ ((ha z).hot i)
  have ho z (i:ℕ):Poly.toll (view θ w) ((T z).footer.tag i) ≤ θ*Poly.toll w _:= hook hw hθ.le h _ ((ha z).vertical.card i)
  refine ⟨hk.toFirm,hk.stays,fun i=> ⟨fun j=>?_,(hk.backs i).nn,(hk.backs i).pay,fun j=>transfer ((hk.backs i).nn) ((hk.backs i).more j) ht (he i) hθ.le,
    fun j=>transfer (fun _=>norm_nonneg _) ((hk.backs i).captions j) ht (ho i) hθ.le⟩,hk.fiscal,fun i j=>transfer (fun h=> (hk.fiscal h).1) (hk.ticket i j) ht (ho i) hθ.le⟩
  unfold view; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ((hk.backs i).one j) hθ.le

-- structurally using whole permitted Mode arity, can strengthen if only certain screens needed after restricting first.
lemma restored (N : ℕ)(hN : ∀ i : R.Mode,i.val.card ≤ N)(hθ : 1 ≤ θ):Voucher T p (view θ w) l (θ*u) (θ^N*c) (θ^N*a) f g:= by
  have H:= zero_lt_one.trans_le hθ; have ht:=weigh_pos H hw
  have he (i:R.Mode):Poly.toll (view θ w) i≤ θ^N*Poly.toll w _ :=wake hw hθ i N (hN i)
  have h := pow_nonneg H.le N
  refine ⟨hk.toFirm,hk.stays,fun i=> ⟨fun j=>?_,(hk.backs i).nn,(hk.backs i).pay,fun j=>transfer ((hk.backs i).nn) ((hk.backs i).more j) ht (fun i=>he _) h,
    fun j=>transfer (fun _=>norm_nonneg _) ((hk.backs i).captions j) ht (fun _=>he _) h⟩,hk.fiscal,fun i j=>transfer (fun h=> (hk.fiscal h).1) (hk.ticket i j) ht (fun _=>he _) h⟩
  unfold view; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ((hk.backs i).one j) H.le

omit hk hw
variable [Nonempty Θ](hL:d.Snacks w u c κ b a)
include hL
lemma snack_low (hθ:0<θ)(hh:θ≤1): Nonempty (d.Snacks (view θ w) (θ*u) (θ*c) (θ*κ) b (θ*a)):= by
  let Q:=view θ w
  let z:=Classical.arbitrary Θ
  let Y:= hL.strong
  have hw:= Y.radii
  have ht:=weigh_pos hθ hw
  have He:=empty_price (grants d hL) hw hθ hh
  refine ⟨⟨Y.white,Y.black,Y.active,ht,Y.divisor,fun i=>(He.backs i).one, Y.bulk,(He.backs z).more,Y.spends,fun i=>?_⟩,hL.active,hL.gold,hL.given,He.ticket z⟩
  rw [mul_assoc]; exact transfer (θ:=θ) (fun i=> (Y.spends i.1 i.2).1) (Y.till i) ht (fun i:ℕ×ℕ=> hook hw hθ.le hh (d.menu.marks i.1 i.2) ((hL.strong.active z).occurs i.1 i.2)) hθ.le

lemma snack_high (N:ℕ)(hN:∀ i:R.Mode,i.val.card ≤ N)(hθ:1≤θ): Nonempty (d.Snacks (view θ w) (θ*u) (θ^N*c) (θ^N*κ) b (θ^N*a)):= by
  let Q:=view θ w; have hw:= hL.strong.radii
  let z:=Classical.arbitrary Θ
  let Y:= hL.strong
  have H:=zero_lt_one.trans_le hθ
  have ht:=weigh_pos H hw
  have He:=restored (grants d hL) hw N hN hθ
  refine ⟨⟨Y.white,Y.black,Y.active,ht,Y.divisor,fun i=>(He.backs i).one, Y.bulk,(He.backs z).more,Y.spends,fun i=>?_⟩,hL.active,hL.gold,hL.given,He.ticket z⟩
  rw [mul_assoc];
  exact transfer (θ:=θ) (fun i=> (Y.spends i.1 i.2).1) (Y.till i) ht (fun i:ℕ×ℕ=> wake hw hθ (d.menu.marks i.1 i.2) N (hN _)) (pow_nonneg H.le _)
end Picnic
end YM.RG3.Script

import YM.OPE.Laying.Origin
/-!
# Credit budget for a whole season

The output erosion is polynomial-log when it needs to be. Does not charge
adjacent ratio for the continuation of a sibling mark. Doesn't include *any*
absolute normalization required at cutoff. Honors ongoing marked prices in the
group as they are actually used. Keep factors explicit throughout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Book
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Local Marker MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid Extra.Multi
open Cells MeasureTheory Motion Backup Float Drapery Playout.Rake
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{I J V:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    [Fintype V][DecidableEq V]{k i j b q p N d T m:ℕ}{w x y α x':ℝ}{W r D}
    (L:LogPackage C W r D)(h:C.Makes)
set_option quotPrecheck false
local notation "Y"=> C.path.levels
local notation "Γ"=> (fun i=> (Y).clock.hatBeta (i+1))
local notation "δ₀"=> renal C.path.levels
local notation "η₀"=> near C.path.levels
local notation "ζ"=> fly C.path.levels
-- reserve in ticket window, independent of positions
structure Cash (x:ℝ) : Prop where
    have_ : 0<x
    cost : x≤1
lemma Cash.light (h:Cash x)(ht:Cash y) : Cash (x*y):= ⟨mul_pos h.have_ ht.have_,mul_le_one₀ h.cost ht.have_.le ht.cost⟩
lemma Cash.reserve (h:Cash x)(he:y≤x)(hf:0<y): Cash y:=⟨hf,he.trans h.cost⟩
lemma Cash.one : Cash 1:=⟨one_pos,le_rfl⟩
namespace Tariff
def shelf (C:Family G)(i:ℕ):=4*(1+(C.path.levels.params i).columns)*C.path.levels.clock.hatBeta (i+1)
def chary (C:Family G)(i d:ℕ):= fly C.path.levels d i/(8*shelf C i)
def platform (L: LogPackage C W r D)(T i j:ℕ)(x:ℝ):= cell C.path (i+1) j (T+2) (peer L T j) x^T
def tender (L:LogPackage C W r D)(T i j:ℕ)(x:ℝ) := platform L T i j x/(4*Γ i)
def debit (L:LogPackage C W r D)(T i j:ℕ)(x:ℝ):=δ₀ i*η₀ i*tender L T i j x*chary C i 0
def signedT (C:Family G)(i d:ℕ)(x y :ℝ):= x*y*chary C i d
local notation "L'"=> platform L T i j
local notation "w!"=> tender L T i j x
local notation "y!"=> debit L T i j x
-- size price in power units
lemma shelf_purchase : 1 ≤ shelf C i:=by
    have h:= (Y).fits.delayed (i+1); unfold shelf;
    calc 1 ≤ 1*((Y).clock.hatBeta (i+1)):= by rw [one_mul]; exact h.le
         _ ≤ _:= by
           have ht:0 ≤ (Y).clock.hatBeta (i+1):= zero_le_one.trans h.le; exact mul_le_mul_of_nonneg_right (by linarith only [(Y).params i|>.columns_ge]) ht
lemma cutCost : Cash (chary C i d):=by
    let s:= shelf C i; let v:= ζ d i; let r:= (Y).clock.hatBeta i; have hv:1 ≤ r:= ((Y).fits.delayed i).le; have h:0<v:=inv_pos.mpr (pow_pos (zero_lt_one.trans_le hv) _); have hp: v≤1:=inv_le_one_of_one_le₀ (one_le_pow₀ hv); have hr:1 ≤ s:=shelf_purchase
    refine ⟨div_pos h (mul_pos (by norm_num) (zero_lt_one.trans_le hr)),(div_le_self h.le (show 1 ≤ 8*s from (by linarith only [hr]))).trans hp⟩
lemma ticket_cut : 4*shelf C i* chary C i d ≤ ζ d i:=by
    let s:=shelf C i; let w:=chary C i d; let v:= ζ d i; have h : (8*s)*w= v:=by
       unfold w chary; rw [mul_comm]; exact div_mul_cancel₀ _ (mul_pos (by norm_num) (show 0<s from zero_lt_one.trans_le shelf_purchase)|>.ne')
    have hV : 0<w:= cutCost.have_; have hs:0<s:= zero_lt_one.trans_le shelf_purchase; linarith only [h,mul_pos hs hV]
lemma quote_size (w:ℝ) : stampOut C i d w= shelf C i / w*C.S.a (i+1)^d:= by unfold stampOut shelf resQuote; simp only [div_eq_mul_inv,mul_inv_rev]; ring
variable (hG:G.Simple)(hT:0 < T)(hw:Cash x)
include hT hw hG L
lemma amounts (he:i < j) : Cash (L' x) ∧ L' x ≤ x := by
    let p:= peer L T j; let y:= cell C.path (i+1) j (T+2) p x; obtain ⟨hy,hp,hz⟩:= peer_paid L hG hT (le_refl j); have hv : y ≤ x:= by refine (cellMore (H:=C.path) he (c':=0) (Nat.zero_le _) hy.le hp hw.have_.le le_rfl).trans (b:=cell C.path j j 0 p x) ?_; unfold cell; rw [div_self (C.S.a_pos _).ne',pow_zero,mul_one,one_pow,one_mul]
    have ht:0<y:=cell_pos hy hw.have_; have hL:y^T ≤ x:=(by simpa only [pow_one] using (pow_le_pow_of_le_one ht.le (hv.trans hw.cost) (show 1 ≤ T from hT)).trans ((pow_one y).trans_le hv)); exact ⟨hw.reserve hL (pow_pos ht T),hL⟩
lemma checkOut (he:i < j) : let b:= y!; Cash (w!) ∧ 4*w!*Γ i=L' x ∧ Cash b ∧ b≤ δ₀ i*η₀ i*w! ∧ b ≤ L' x ∧ 4*shelf C i*b ≤ ζ 0 i* L' x:=by
    intro b; let u:= L' x; let z:= w!; let w:=chary C i 0; let P:= shelf C i
    have he':1 < Γ i:= (Y).fits.delayed _; have ht:1 ≤ 4*Γ i:=(by linarith only [he']); have hp:= amounts L hG hT hw he|>.1; have hu:z ≤ u:= div_le_self hp.have_.le ht; have hZ := hp.reserve hu (show 0<z from div_pos hp.have_ (zero_lt_one.trans_le ht)); have hb : b=(δ₀ i*η₀ i*z)*w:=rfl; have hG(i):= L.system.costs.stay.water i (Nat.zero_le i)
    have hq:Cash (δ₀ i*η₀ i):= (show Cash (δ₀ i) from ⟨(hG i).2,renal_le L _⟩).light (show Cash (η₀ i) from ⟨(hG i).1, inv_le_one_of_one_le₀ he'.le⟩); have hw:Cash w:= cutCost; have hL:(δ₀ i*η₀ i)*z ≤ u:= (mul_le_of_le_one_left hZ.have_.le hq.cost).trans hu; have hK:b≤(δ₀ i*η₀ i)* z:= mul_le_of_le_one_right (hq.light hZ|>.have_.le) hw.cost;
    refine ⟨hZ,?_, (hq.light hZ).light hw,hK,hK.trans hL,le_trans (mul_le_mul_of_nonneg_left (show b ≤ w*u from ((mul_le_mul_of_nonneg_right hL hw.have_.le).trans_eq (mul_comm ..))) ?_) ?_⟩
    · change 4*z*Γ i=u; rw [show (4*z)*Γ i=z*(4*Γ i) from (by ring), show z*(4*Γ i)= _ from div_mul_cancel₀ u (zero_lt_one.trans_le ht).ne']
    · exact mul_nonneg (by norm_num) (zero_le_one.trans shelf_purchase)
    exact (mul_assoc _ w u|>.symm).trans_le (mul_le_mul_of_nonneg_right ticket_cut hp.have_.le)
-- sign eraser (x already aged step-price, x'=platform), pay.Size units.
omit L hG hT
local notation "p'"=> signedT C i d x x'
lemma erase_cash (he:Cash x'): Cash p'∧ p'≤x:=by
   have hh: Cash (chary C i d):= cutCost; refine ⟨(hw.light he).light hh,(mul_le_of_le_one_right (hw.light he|>.have_.le) hh.cost).trans (mul_le_of_le_one_right hw.have_.le he.cost)⟩
local notation "B"=> birthClock C i d 1
lemma eraseWidth (he: Cash x')(ha:0<α) : p' * α * (2*stampOut C i d (x'*α)) ≤ x*(birthClock C i d 1) ∧
    p' *α*‖alto C.path i d‖ *stampOut C i d (x'*α) ≤ ζ d i:=by
    let z:=p'; let q:= chary C i d; let p:= shelf C i; let f:= ζ d i; let r0 :ℝ:= C.S.a i ^ d; let r1:ℝ:= C.S.a (i+1)^d; let w:= stampOut C i d (x'*α)
    have h:0<q:= cutCost.have_; have hp:1 ≤ p:=shelf_purchase; have hv:0<x':=he.have_; have hP:0<p:=zero_lt_one.trans_le hp
    have hz: z * (α*w) = ((p*q)*x)*r1:=by unfold w; rw [quote_size]; unfold z signedT r1; dsimp only [p,q]; field_simp
    have hξ:4*p*q ≤ f:=ticket_cut; have hg : 2*(p*q) ≤ f:=(by linarith only [hξ,mul_pos hP h]); have hr0:0<r0:=pow_pos (C.S.a_pos _) _; have hr1: r1 ≤ r0:=pow_le_pow_left₀ (C.S.a_pos _|>.le) (C.S.strictAnti.antitone i.le_succ) d; have hx0:=hw.have_; have he' : 0 ≤ p*q*x:= (mul_pos (mul_pos hP h) hx0).le; have hz' : B=f*r0:=by unfold birthClock; rw [div_one]
    constructor
    · rw [hz']; nlinarith only [hz,mul_le_mul_of_nonneg_left hr1 he', mul_le_mul_of_nonneg_right hg (mul_pos hx0 hr0|>.le)] -- use r assoc maybe linarith substituted local f
    rw [alto_norm]; apply le_trans (le_of_eq (b:=(z*(α*w))*r0⁻¹) (by dsimp only [r0,z,w]; ring))
      ((mul_le_mul_of_nonneg_right (hz.trans_le (mul_le_mul_of_nonneg_left hr1 he')) (inv_pos.mpr hr0|>.le)).trans ?_)
    rw [mul_assoc, mul_inv_cancel₀ hr0.ne',mul_one] -- mul_assoc which?
    linarith only [hg,mul_pos hP h, mul_le_of_le_one_right (mul_pos hP h|>.le) hw.cost]
-- roll floor receipt
omit hw
lemma spaWidth (he:Cash x')(hy:0<y)(hp:4*shelf C i*y ≤ ζ 0 i*x')(hu:0<α) : y*α*(4*stampOut C i 0 (x'*α)) ≤ ζ 0 i:= by
    have h:0<x':=he.have_
    rw [quote_size,pow_zero,mul_one]; field_simp; linarith only [hp]
end Tariff
end YM.OPE.Log.Book

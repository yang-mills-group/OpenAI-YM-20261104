import YM.RG3.Script.Vaulted

/-! # Multiple uses on real-level script: pass the stronger K reserve on
all held coupons, for running more of the finite registry operations BEFORE
edition pricing. One commitment. The proof doesn't depend on changing P
or recovering any column. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Reserve
open Function Lattice RG Wilson Marker Overlay RG3.Forms RG3.Press RG3.Held RG3.Law RG3.Ink
  Extra.Multi Extra.Trajectories Ac Push.AbsoluteSums MeasureTheory Push.Corrected Finset Extra.Iteration Edition Push.Local Source Estate Picnic
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {n : Side}{V ι : Type*}[DecidableEq V][Fintype V][Nonempty V]{R:Census V}{ζ : V→Site n}{G : Gauge} {w:V→ℝ}
  {P : Rep G n}{X : Type*}[Nonempty X][Countable ι]
structure Coffer (a: Taste X ζ P R)(w:V→ℝ)(B γ: ℝ)(f : ℕ×ℕ→ℝ) : Prop where
  nonneg i : 0 ≤ f i
  black (i j): ∀ x U, ‖a.menu.force x i j U‖ ≤ f (i,j)
  site: Hit (fun k : ℕ×ℕ=> (P.activities.forced k.1).support) P.p.B (fun k=> Poly.toll w (a.menu.marks k.1 k.2)*f k) B γ
  roots v: SumBudget (per P.p.B B w (fun k : ℕ×ℕ=>a.menu.marks k.1 k.2) (fun k : ℕ×ℕ=> (P.activities.forced k.1).support) f v) γ
  pinned i (h : 0 < f i):∀ v∈(a.menu.marks i.1 i.2).val,a.menu.origins v∈(P.activities.forced i.1).support

variable {K:ℕ} {B q r χ γ s α c u α' c' dK b a :ℝ}{d z:Taste X ζ P R}{f :X→Feed G n R ι}{m:ι→ℝ}
  (H:d.Menu w α c)(L:Ledger f)(hw:∀i,0<w i)(hP:P.activities.ForcedFamily P.p)
variable (h:∀x,Join P.p (d.leaf x).log (z.leaf x).log w ζ (f x) m s) (he:∀x,(d.leaf x).Active)(hs:s≤1) (ha:Accessible P)
local notation "Y"=> bank H L hw hP h he hs
local instance : Countable (catalog (P:=P) (R:=R)).Patch:=by unfold Shelf.Patch Letters.Frame.Patch; infer_instance

include H L hw hP h he hs ha
lemma buxom
    (he':∀ x, Bar ((Y).planner x) B a α' c') (hχ:1≤χ)(hγ:0≤γ)(hp:χ*(α'+c')+2*a≤γ)(hg:(P.p.B+P.p.B+1:ℕ)^4*(γ:ℝ) ≤ 1):
    let T:=retire H L hw hP h he hs ha
    ∃ t:ℕ×ℕ→ℝ,Coffer T w B ((Real.exp γ-1)/χ) t:= by
  intro T
  let I:=Y; let Ht:=catalog (R:=R) (P:=P); let W:=wharf (p:=P.p) (W:=Ht) P ha
  let Z i:=(P.activities.forced i).support
  let b₁:= Shelf.Stock.credit Ht I.coins
  let out:= Article.voucher (R:=R) W ζ (Z ∘ W) b₁
  have hx(x:X): let u:=(I.planner x).coins; u=I.coins:=(I.shares _).symm
  have ht x := coupons _ B (he' x) (z.leaf x) ha χ γ hχ hp hγ hg
  have hw (x:X) : Article.voucher (R:=R) W (d.leaf x).contents.origins (Z ∘ W) (Shelf.Stock.credit Ht ((I.planner x).coins)) = out:= by rw [hx x,show (d.leaf x).contents.origins= ζ from d.root]
  have hHi x : ( (I.planner x).task ha (z.leaf x)).contents = T.menu.terms x := rfl
  have h1(x:X): ∀ i,0≤out i ∧ ∀ U,‖T.menu.force x i.1 i.2 U‖≤out i:=by rw [← hw x]; exact (ht x).1
  let i0:=Classical.arbitrary X
  refine ⟨out,⟨fun i=> (h1 i0 i).1,fun i j x=> (h1 x (i,j)).2,?_,?_,?_⟩⟩
  · rw [← hw i0]; exact (ht i0).2.1
  · rw [← hw i0]; exact (ht i0).2.2
  intro i hi
  unfold out Article.voucher Function.extend at hi; split at hi; swap; exact ((le_refl _).not_gt hi).elim
  next h'=>
    unfold Article.usury at hi; split at hi
    next hh=>
      rw [show i= _ from h'.choose_spec.symm]
      change ∀ v∈ ((T.menu.terms i0).marks (W h'.choose.1) (pin h'.choose)).val,T.menu.origins v∈ (P.activities.forced (W h'.choose.1)).support
      rw [← hHi, T.root]
      change ∀ v ∈ (((stamp (I.planner i0).stock).impression (z.leaf i0).contents W).marks _ _).val,_
      rw [Article.marked_pin]; exact hh
    exact ((le_refl _).not_gt hi).elim

omit H L hw hP h he hs ha
namespace Coffer
variable {d : Taste X ζ P R}{f':ℕ×ℕ→ℝ}(hf:Coffer d w B γ f')(hw:∀i,0<w i)
include hf hw
omit [Fintype V] [Nonempty X] [Nonempty V] in
lemma wherewith (N:ℕ)(hN:∀ i:R.Mode,i.val.card≤N)(hq:1 ≤ q): Coffer d (view q w) B (q^N*γ) f':= by
  have ht:=weigh_pos (zero_lt_one.trans_le hq) hw
  have hx:0≤q^N:=by positivity
  have H(i:R.Mode):=wake hw hq i N (hN i)
  let f i:= Poly.toll (view q w) (d.menu.marks i.1 i.2)*f' i
  refine ⟨hf.nonneg,hf.black,fun i=> budget_mono (budget_scale hx (hf.site i)) (fun j=>?_) (fun j=>?_),fun i=> transfer hf.nonneg (hf.roots i) ht (fun i=>H _) hx,hf.pinned⟩
  · split; exact mul_nonneg (mul_nonneg (Poly.worth ht _).le (hf.nonneg j)) (Real.exp_pos _).le; rfl
  split
  next _ => exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (H _) (hf.nonneg j)) (Real.exp_pos _).le).trans_eq (by ring)
  simp

end Coffer
end YM.RG3.Script.Reserve

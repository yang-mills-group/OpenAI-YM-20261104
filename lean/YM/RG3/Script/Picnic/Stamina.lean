import YM.RG3.Script.Picnic.Taste

/-!
# Register compiler's workings with Held for uniform purchases

One common price book through the whole demanded Θ domain. In particular
no multiplying merger estimates by dimension of external tests, or any ν_t
inside this price. Use Θ containing every ± and derivative address test (pass
finite-order Sob/P∞ objects after imposing all asked bounds, or include their
probes as separate slots in approved geometry). Radii can still be purchased
tiny then restored including on these coupons. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Picnic
open Function Lattice RG Wilson Marker Overlay RG3.Forms RG3.Press RG3.Held RG3.Ink
  Extra.Multi Ac Push.AbsoluteSums MeasureTheory Push.Corrected Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {n : Side}{V : Type*}[DecidableEq V]{R:Census V}{ζ : V→Site n}{G : Gauge}
  {X : Type*}{ι:Type*}{P : Rep G n}(d : Taste X ζ P R)
  (Q : Taste X ζ P R) {f:X→Feed G n R ι}{w:V→ℝ}

structure Ledger (f:X→Feed G n R ι) where
  column x y i : (f x).column i=(f y).column i

namespace Ledger
variable (L : Ledger f)
 include L
lemma fee_eq (m:ι→ℝ) (x y:X): (f x).coin m = (f y).coin m:=by
  replace L: (f x).column=(f y).column:=funext (L.column x y)
  -- coin depends only on column
  generalize h:f x=F at *; generalize h':f y=D at *
  rcases F with ⟨a,b⟩; rcases D with ⟨a',b'⟩; change a=a' at L; subst a'; rfl
end Ledger

variable {d Q} {s vac mark : ℝ} {m : ι→ℝ}
  (B : d.Menu w vac mark)(L: Ledger f)(hw:∀i,0<w i) (hP:P.activities.ForcedFamily P.p)
variable [Fintype V]
  (h:∀ x, Join P.p (d.leaf x).log (Q.leaf x).log w ζ (f x) m s)
  (he:∀ x,(d.leaf x).Active)(hs:s≤1) [Nonempty X]
include B L hP he h hs hw
private def pil (x:X): Forms.Test (d.leaf x) (f x) s w vac mark:= (h x).publish d.root (B.store x) hw hP (he x) hs

def bank : Held.Inspector d.leaf f w s vac mark ζ := {
  planner:=pil B hw hP h he hs
  coins:= (pil B hw hP h he hs (Classical.arbitrary X)).coins
  shares x := by
    funext i; rcases i with i|i
    · change (B.store _).merch i=(B.store _).merch i
      unfold Billboard.merch; rw [B.bill_fixed (Classical.arbitrary X) x,B.vac_fixed (Classical.arbitrary X) x]; rfl
    exact congrFun (L.fee_eq m (Classical.arbitrary X) x) i
  holds x := d.root }

local notation "I" => bank B L hw hP h he hs
local notation "fr"=>catalog (P:=P) (R:=R)
local instance : Countable ((catalog (P:=P) (R:=R)).Patch) := by unfold Shelf.Patch Letters.Frame.Patch; infer_instance
variable [Countable ι]
-- discharge without calling private lemma, at physical price
omit L [Nonempty X] in 
lemma sound (x : X) (χ γ:ℝ)(hχ:1≤χ)(hp:χ*(vac+mark)+2*s≤γ)(hγ:0≤γ)(hg:(P.p.B+P.p.B+1:ℕ)^4*(γ:ℝ) ≤ 1) :
    (stamp (pil B hw hP h he hs x).stock).Sound:=
    ((pil B hw hP h he hs x).service χ γ hχ hp hγ hg).1

variable (HA : Accessible P)
variable [Nonempty V]
include HA
def retire : Taste X ζ P R := { Q with menu:= (I).stay Q.menu HA, root:=Q.root }

local notation "N"=> retire B L hw hP h he hs HA

lemma imprint (χ γ:ℝ)(hχ:1≤χ)(hp:χ*(vac+mark)+2*s≤γ)(hγ:0≤γ)(hg:(P.p.B+P.p.B+1:ℕ)^4*(γ:ℝ) ≤ 1) {u c a : ℝ} (hA : Q.Store w u c a)
    {r b0 : ℝ} (H : (Real.exp γ-1)/χ ≤ r*b0) (hb : 0 < b0) {u0 c₀ k b a0:ℝ} (ht : ∀ x,(d.leaf x).Budget w u0 c₀ k b a0):
    let o:=N
    Nonempty (o.Snacks w u c r b0 a) ∧ ∀ x,(o.leaf x).density=(d.leaf x).density ∧ (o.leaf x).log=(Q.leaf x).log := by
  intro o
  let C := bank B L hw hP h he hs
  let a0:= Q.menu
  let S:=Shelf.Stock.credit fr C.coins
  let i0:=Classical.arbitrary X
  let z:= (Real.exp γ-1)/χ
  let W:=wharf (W:=fr) (p:=P.p) P HA
  have heq (x): (C.stampPage x).Hosting P W := by
    obtain ⟨hc,hS,hi,hf⟩ := wharf_fit P (C.planner x).stock HA rfl rfl
    exact ⟨hc,hS,hi,hf⟩
  have hx (x): (C.stampPage x).Sound:= by
    have hs₀:= sound B hw hP h he hs x χ γ hχ hp hγ hg
    refine ⟨?_,hs₀.ready,hs₀.honest,hs₀.query,hs₀.invariantTest,hs₀.reads⟩
    intro i
    have ht:=hs₀.payload i; change Width.LocalCharge P.p _ _ _ at ht ⊢; nth_rw 1 [show (d.leaf x).contents.origins=ζ from d.root] at ht; exact ht
  have hpr : Hit (fun i => (P.activities.forced (W i)).support) P.p.B (fun i => Poly.price w (S i)) P.p.supportExponent z := by
    have hv := Shelf.Stock.bought fr hw P.p.exponent_pos.le hχ hγ ((C.planner i0).offer χ γ hχ hp) hg
    simp_rw [S,C.shares i0]
    convert hv using 1; exact (funext ((heq i0).equal_span)).symm
  have Hi (i) (x) (U : Config G n): Width.Covered ((C.stampPage x).flow i U) (S i) := by
    let t:=C.planner x
    unfold S; rw [C.shares x]
    have h'' := t.stock.covered (g:=t.coins) (fun i U => show Width.Covered _ _ from by
      rcases i with i|i
      · exact (t.toBillboard.qual hw (by linarith [P.p.exponent_pos]) i U).receipts
      exact (f x).funded hw (by linarith [P.p.exponent_pos]) t.sufficesStamp t.budget i U) i U
    exact h''
  obtain ⟨Y⟩ := a0.issued C.stampPage _ Q.root hx heq S w Hi hpr H hb hw hA.fit hA.white hA.globe (by unfold a0; simp_rw [Q.root]; exact hA.present) hA.warrant
  refine ⟨⟨Y,hA.sound,hA.gold,hA.given,hA.ticket⟩,fun x => ⟨?_,rfl⟩⟩ -- nonempty nested bug
  let he' := (h x).copy d.root (B.store x) hw hP (he x) hs χ γ hχ hp hγ hg HA (Q.root) (ht x) H hb (hA.fit x) (Q.shelf hA x).1 (show (Q.leaf x).captions.Sound Q.menu.origins by rw [Q.root]; exact hA.sound x) (Q.shelf hA x).2
  exact he'.2.2
end YM.RG3.Script.Picnic

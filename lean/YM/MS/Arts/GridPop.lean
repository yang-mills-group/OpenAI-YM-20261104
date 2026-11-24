import YangMills.WilsonProof.NativeSupport.YM.MS.Arts.Tall
/-!
# Sturdy tree plane at all supports

Use vanishing on each strict extension leg. In attaching, moments need not
 satisfy net; rotation law maintained Off. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Momentum Landau Pilot Spin
open scoped Topology ContDiff
variable {G:Gauge}{I:Type}{m n k:ℕ}{b c:Bool}{F H:Mob G}{U:Rip G}
variable (h:m≤n)
lemma scatter_up (F:Shared (Shore G n) ℂ)(v:Legs (Shore G m)): scatter (field parity) (lift h v) F=scatter (field Landau.parity) v (fun x y=> F (lift h x) (lift h y)) := by
   induction v generalizing F with
   | nil=>rfl
   | cons i l ih=> rw [show lift h (i::l)= (embA (rises h) i.1,Left h i.2)::lift h l from rfl,scatter_cons, ih,scatter_cons]; congr 1; funext x y; rw [lifts_degree,show field Landau.parity (embA (rises h) i.1,Left h i.2)=field Landau.parity i from risesP _ _]; rfl

variable (HF:Sturdy b F)(HH:Sturdy b H)(HU:Ruddy b U)
include HF HH HU
def reverseF (U:Rip G): Prop:=∀ n, Reverse (U n) Landau.parity
lemma lights (l r:Legs (Shore G m))(i j:Cfield G m): radius Landau.parity (U n) (embA (rises h) i) (embA (rises h) j) (F n) (H n) (lift h l) (lift h r)= radius Landau.parity (U m) i j (F m) (H m) l r:= by
   unfold radius; simp only [neg_neg,lifts_degree, risesP, lifts_net, ← map_neg]; rw [HU.grows,show F n ((embA (rises h) i,Left h (-net l))::lift h l)= _ from HF.grows h ((i,-net l)::l), show H n ((embA (rises h) j,Left h (net l))::lift h r)= _ from HH.grows h ((j,net l)::r)]
def arbor (U:Rip G)(F H:Mob G)(m:ℕ): Rack G m:= tree Landau.parity (U m) (F m) (H m)
lemma a_tree (hw:reverseF U) (u:Legs (Shore G m)): tree Landau.parity (U n) (F n) (H n) (lift h u)= tree Landau.parity (U m) (F m) (H m) u:= by
    unfold tree; rw [scatter_up]; apply scatter_congr; intro l r hL; rw [convertR (hw n),convertR (hw m)]; let K :=radius Landau.parity (U n); let R (i j:Cfield G n):= K i j (F n) (H n) (lift h l) (lift h r); let V i := (embA (rises h) i:Cfield G n); let W (i: Apart m n)(p:Bool)(c:G.ColorIndex):= vleg p (aside h i) c
    have hu (i p c)(j:Cfield G n): R (W i p c) j =0:= by unfold R K radius; dsimp only; rw [lifts_net, ← map_neg, show F n ((W i p c, Left h (-net l))::lift h l) = _ from vanish_one h HF [] l i (-net l) c p]; simp
    have hv (i:Cfield G n)(j p c): R i (W j p c)=0:= by unfold R K radius; dsimp only; rw [lifts_net, neg_neg,show H n ((W j p c, Left h (net l))::lift h r)=_ from vanish_one h HH [] r j (net l) c p]; simp
    change (∑ i:Cfield G n,∑ j:Cfield G n, R i j)=_; rw [more h]; simp_rw [show ∀ i:Cfield G n,(∑ j,R i j)= (∑ j,R i (V j))+(∑ p:Apart m n,∑ s,∑ c,R i (W p s c)) from fun i=> more h (R i)]; change (∑ i:Cfield G m,((∑ j,R (V i) (V j))+(∑ p:Apart m n,∑ s,∑ c,R (V i) (W p s c))))+(∑ p:Apart m n,∑ s,∑ c,((∑ j, R (W p s c) (V j))+(∑ t:Apart m n,∑ f,∑ m,R (W p s c) (W t f m)))) = _; simp only [hu,hv,Finset.sum_const_zero,add_zero]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> lights h HF HH HU l r i j

def closedF (U:Rip G)(b:Bool): Prop:=∀ m,closed (U m) Landau.parity b
lemma arboreal (hw:reverseF U)(he:closedF U c): Sturdy b (arbor U F H) := by
    refine ⟨fun n K hK=>?_,fun h i=> a_tree h HF HH HU hw i⟩; unfold arbor; rw [(HU.turn n K hK).gatherR _ _ (he n) (he n), HF.turn n K hK, HH.turn n K hK]
end YM.MS.Arts

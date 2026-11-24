import YM.RegulatorIR.Uniform.OrderCost

/-!
Progress at a completely general interaction order. After matching the
period and kernel projections, **every** connection in the finite orbit
Wick step takes either tree propagation or a point-defect cost. In the recursing
heat-time variable this is just unary trace vs single binary knot. No graph
translations factor for the field-dependent output. Estimates also retain
point location and diameter, and bind summability to this L before using signed reindex.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Uniform
open Function Budget Diagram Budget.Packet Budget.Layer Budget.Tuple BudgetMore
open scoped Topology ENNReal BigOperators Classical
variable {W:Type}{I J: W → Type}{L:Meter W} {r : ℕ}

namespace Post
variable {A:Post I J}

def vgap (A:Post I J) (T:(w:W)→Packet (I w) r) (F:(w:W)→Packet (J w) r)(w): Packet (J w) r:= F w- (A.deck w).deckSum (T w)
lemma gap_factor {u:ℕ} {T:(w:W)→Packet (I w) r}{F:(w:W)→Packet (J w) r}(c:ℝ)(h:Claim L (A.pear u) 1 (vgap A T F)): Claim L (A.pear u) 1 (vgap A (fun w=>c • T w) fun w=> c • F w):=by
 unfold vgap; simp_rw [Deck.desk_smul,← smul_sub]; exact h.csmul _
lemma gap_plus {u v:ℕ}{T S:(w:W)→Packet (I w) r}{F G:(w:W)→Packet (J w) r}(h:Claim L (A.pear u) 1 (vgap A T F))(hf:Claim L (A.pear u) 1 (vgap A S G))(hT:Workday L (A.cone v) T)(hS:Workday L (A.cone v) S): Claim L (A.pear u) 1 (vgap A (fun w=> T w+S w) fun w=> F w+G w):=by
 obtain ⟨f,hf',H⟩:=hT; obtain ⟨g,hg,G'⟩:=hS
 convert h.add hf using 1; ext1 w; unfold vgap; rw [Deck.desk_sup (A.deck w) (H w) (hf'.cost w) (G' w) (hg.cost w)]; abel_nf; rw [add_assoc]
lemma gap_sum {u v:ℕ}{Z:Type}{T: Z→ (w:W)→ Packet (I w) r} {F:Z→ (w:W)→ Packet (J w) r} (p:Finset Z)(h:∀ i∈p, Claim L (A.pear u) 1 (vgap A (T i) (F i)))(hh:∀ i∈p,Workday L (A.cone v) (T i)):
 Claim L (A.pear u) 1 (vgap A (fun w=>∑ i∈p,T i w) (fun w=>∑ i∈p,F i w)):=by
 convert Claim.sum _ p h using 1; ext1 w; unfold vgap; rw [work_sum p hh w,Finset.sum_sub_distrib]
lemma gap_sym {u v:ℕ}{T:(w:W)→Packet (I w) r} {F:(w:W)→Packet (J w) r} (h:Claim L (A.pear u) 1 (vgap A T F))(hh:Workday L (A.cone v) T)(ht:∀ w,(A.deck w).Ready (T w)) :
 Claim L (A.pear u) 1 (vgap A (fun w=>symmetry (T w)) (fun w=>symmetry (F w))):=by
 obtain ⟨f,hf,H⟩:=hh; convert h.robust using 1; ext1 w; unfold vgap; rw [Deck.desk_sym _ (H w) (hf.cost w) (ht w),symmetry_sub]

section Joint
variable {K:(w:W) → Layer (I w) (I w)} [∀ w,Fintype (J w)]
lemma income (A:Post I J) {u b:ℕ}{T:(w:W)→Packet (I w) (r+2)}{F:(w:W)→Packet (J w) (r+2)}
  (h:Beam L (A.cone (u+b)) K) (hh:Workday L (A.cone (u+b+(u+b))) T)(hr:∀ w,Layer.Sym (A.deck w) (A.deck w) (K w))(ht:∀ w,(A.deck w).Ready (T w))(hf: Poly L (A.weight b))(hd:Claim L (A.pear u) 1 (vgap A T F))(hi:0<r): Claim L (A.pear u) 1
    (vgap A (fun w=>loop (T w) (K w)) (fun w=>loop (F w) (A.wrapK K w))):=by
 let K':=A.wrapK K
 have hK:= A.wrap_beam (A.descent (k:=u) h (by omega)) hr
 have hc:= Claim.loop_budget hd hK
 have he:= Claim.add hc (A.forged hh h ht hr hf (⟨0,hi⟩:Fin r))
 convert he using 1;ext1 w; unfold vgap; rw [loop_sub]; abel

lemma ahead (A:Post I J) {u:ℕ}{k:ℕ}{T:(w:W)→Packet (I w) (r+1)}{S:(w:W)→Packet (I w) (k+1)}{F:(w:W)→Packet (J w) (r+1)}{G:(w:W)→Packet (J w) (k+1)}
    (h:Beam L (A.cone u) K)(hd:∀ w,Layer.Sym (A.deck w) (A.deck w) (K w))(hh:Workday L (A.cone u) T)(ht:∀ w,(A.deck w).Ready (T w))(hg:Workday L (A.cone u) S)(hv:∀ w,(A.deck w).Ready (S w))
   (hp:Claim L (A.pear u) 1 (vgap A T F))(hq:Claim L (A.pear u) 1 (vgap A S G))(hz:0<r+k): Claim L (A.pear u) 1 (vgap A (fun w=>knot (K w) (T w) (S w)) (fun w=>knot (A.wrapK K w) (F w) (G w))):=by
 let X:=fun w=>(A.deck w).deckSum (T w); let Y:=fun w=>(A.deck w).deckSum (S w)
 have ha :Workday L (A.per u) G := by
     have he:= (Claim.submits hq (Poly.oneQ L)).add (A.deck_work hg hv)
     simpa only [vgap,sub_add_cancel] using he
 have hx:= A.wrap_beam h hd
 have he:= (Claim.knot_budget hp ha hx).add (Claim.knot_budget' (A.deck_work hh ht) hq hx)
 convert he using 1; ext1 w; unfold vgap
 obtain ⟨v,hv',V⟩:=h; obtain ⟨f,hf,Z⟩:=hh; obtain ⟨g,hg,H⟩:=hg
 let K' := A.wrapK K w
 rw [← Packet.knot_copy (A.deck w) (hd w) (V w).1 (V w).2 (ht w) (hv w) (Z w) (H w) (hf.cost w) (hg.cost w) (hv'.cost w) (⟨0,hz⟩:Fin (r+k))];change knot K' (F w) (G w)-knot K' (X w) (Y w)=knot K' _ _+knot K' _ _
 have hh:= knot_addL K' (F w-X w) (X w) (G w); rw [sub_add_cancel] at hh
 have hj:= knot_addR K' (X w) (G w-Y w) (Y w); rw [sub_add_cancel] at hj
 rw [hh,hj]; abel
end Joint
end Post
end YM.RegulatorIR.Uniform

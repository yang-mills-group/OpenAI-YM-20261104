import YM.Frontier6.Pair.Report
import YM.MergeProof.West.Compass

/-! Passing the physical off-seam geometry to every finer lattice address.
Useful for translations and a continuum O(4) bypass of seam restrictions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Platform
open Set Filter Function MeasureTheory Lattice Cells Wilson Extraction Spec Bid Work.B15 Next.UVStress OS MergeProof.Ribbons Around
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}(S:Schedule){C:Family G}{F:Extraction.Order}{b k l N p : ℕ}
/-- Margin g in physical units. -/
def atStop (b:ℕ)(u:Cover)(g:ℝ) (x:E4):Prop:=∀ i:Axis, |x i-S.gridPoint b u i| < S.a b / 2 - g
lemma atStop_open (b:ℕ)(u:Cover)(g:ℝ) : IsOpen {x:E4 | atStop S b u g x}:= by
   rw [show {x:E4|_}=⋂ i:Axis,{x:E4 | |x i-S.gridPoint b u i| < S.a b / 2 - g} by ext; simp [atStop]]; exact isOpen_iInter_of_finite fun i=>isOpen_lt (by fun_prop) continuous_const
lemma at_margin (p:ℕ)(u x:Cover)(hb:b≤ l)(hl:l ≤ N)(hk:k ≤ N) (hx:atStop S b u (3*S.a k) (S.gridPoint l x)) :
   let T:= center S p (hb.trans hl) 0
   Cells.location S l N p x ∈ T.margin (wrap (S.side b p) u) (3*Cells.span S hk p):=by
   intro T; let Y:=wrap (S.side b p) u; let X:=Cells.location S l N p x; let v:=pushSite S hl x; let w:=pushSite S (hb.trans hl) u
   let V:= wrap (S.side N p) v; have hX:X=V:=by unfold X V Cells.location; rw [dif_pos hl, Ratio.embed_wrap];rfl
   let W:= wrap (S.side N p) w; have hT:T.units.root Y=W:=by change (S.toDepth (hb.trans hl) p).root ((wrap (S.side b p)) u)=_; rw [Ratio.root_embed,Ratio.embed_wrap];rfl
   let M:= T.side.val; let h:=M/2; let A:= Cells.span S hk p; have hm: Odd M:= S.toDepth_odd (hb.trans hl) p; have ho : M=2*h+1:=by unfold h; obtain ⟨a,ha⟩:=hm; omega
   have hv (i:Axis) :∃ a:ℕ,T.coordinated Y X i=a∧3*A ≤ a∧ a+3*A < M:=by
      let c:ℤ:= h+(v i-w i); let B:= S.a N; have hB: 0 < B:=S.a_pos N
      have he:= hx i; rw [← finer S hl x,← finer S (hb.trans hl) u] at he
      change |B*(v i)-B*(w i)| < _ at he
      obtain ⟨h₁,h₂⟩:= abs_lt.mp he
      rw [← S.embeds_scale T.units,← S.embeds_scale (S.toDepth hk p)] at h₁ h₂ -- binder motive?
      have hq:(T.units.count.val:ℝ)=2*h+1:=by exact_mod_cast ho
      have ht₁ :(2:ℤ)*(3*A) ≤ 2*c:=by
          suffices hr:(((6*A:ℕ):ℝ)) < 2*(c:ℝ)+1 by
              have hh : ((6*A:ℕ):ℤ)< 2*c+1:=by exact_mod_cast hr
              omega
          apply lt_of_mul_lt_mul_left _ hB.le; unfold c; push_cast; unfold A Cells.span; unfold B at *; linarith only [h₁,show S.a N*(T.units.count.val:ℝ)=_ from congr_arg (S.a N*·) hq] -- use differently
      have ht₂ : c+3*A < (M:ℤ):=by
          suffices hr:2*((c:ℝ)+3*A) < 2*M by
              have hh : (2:ℤ)*(c+3*A)<2*M:=by exact_mod_cast hr
              omega
          apply lt_of_mul_lt_mul_left _ hB.le; unfold c; push_cast; unfold A Cells.span; change B*(2*(↑h+(↑(v i)-↑(w i))+ _ )) < B*(2*T.units.count.val); unfold B at *; linarith only [h₂,hB,show S.a N*(T.units.count.val:ℝ)=_ from congr_arg (S.a N*·) hq]
      have ht : T.coordinated Y X i=c.toNat:=by
          unfold Tiling.coordinated Tiling.starts; rw [hX,hT]; have hp:c.toNat < (S.side N p).val:=lt_trans (show c.toNat < M by omega) T.narrow
          rw [← ZMod.val_natCast_of_lt hp]; apply congr_arg (fun y:Per _=>y.val)
          change ((v i:ℤ):Per (S.side N p))-((0-(↑h:Per (S.side N p)))+ ((w i:ℤ):Per (S.side N p)))= _; rw [← Int.cast_natCast (R:=Per (S.side N p)) (n:=c.toNat), Int.toNat_of_nonneg (by omega)]; unfold c; push_cast; abel
      exact ⟨c.toNat,ht,by omega,by omega⟩
   refine ⟨fun i=>?_,fun i=>?_⟩
   · change T.coordinated Y X i < M; obtain ⟨a,r,-,he⟩:=hv i; omega
   obtain ⟨a,r,he,hg⟩:=hv i; change 3*A ≤ T.coordinated Y X i ∧ T.coordinated Y X i+3*A+1≤ M; rw [r]; exact ⟨he,hg⟩
end YM.Frontier6.Platform

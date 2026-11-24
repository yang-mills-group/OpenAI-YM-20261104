import YM.RegulatorIR.Uniform.MarkCost

/-! Discrepancy of a joint heat term at one order. We work with W's whole
unnormalized numerator tested, then do the vacuum normalization (implemented
by the drift equation, exact theorem Drained). Keep powers of source input
size and location gain explicitly before calls. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Uniform
open Function Budget Diagram Budget.Packet Budget.Layer Post
open scoped Topology BigOperators Classical ENNReal
variable {Y:Type}{I J: Y → Type}{L:Meter Y}{P:Post I J}
namespace Post
variable {s v:Y → ℝ≥0∞}{x:Y → Room}{u b n:ℕ}{r q:ℕ}
variable {K:(w:Y)→Layer (I w) (I w)} (h:Beam L (P.cone ((u+b)+b)) K)(hr:∀ w,Layer.Sym (P.deck w) (P.deck w) (K w))
     (hh:∀ w,s w≠⊤) (hk:Carry L v (fun w=>s w*(P.toll x b w)⁻¹))
include h hr hh hk
variable [∀ w,Fintype (J w)]
lemma simple_loop {T:(w:Y)→ Packet (I w) (r+2)}{S:(w:Y) → Packet (J w) (r+2)}
   (hT: Claim L (P.rooted x (u+b+b)) s T)(hs:Claim L (P.anchored x u) v (P.agap T S)):
   Claim L (P.anchored x u) v (P.agap (fun w=> loop (T w) (K w)) fun w=>loop (S w) (P.wrapK K w)):=by
 let R:= P.wrapK K
 have hb := Carry.charge (P.loop_marked x (P.descent h (by omega)) hT hh hr) hk
 have hv:= hs.loop_budget (P.wrap_beam (P.descent h (by omega)) hr)
 convert Claim.add hv hb using 1; ext1 w; unfold agap; rw [loop_sub]; abel
lemma narrow_node {T:(w:Y)→ Packet (I w) (r+1)}{S:(w:Y) → Packet (J w) (r+1)} {V:(w:Y)→Packet (I w) (q+1)}{U:(w:Y) → Packet (J w) (q+1)}
    (hT:Claim L (P.rooted x (u+b+b)) s T)(hs:Claim L (P.anchored x u) v (P.agap T S))(ht:Workday L (P.cone (u+b+b)) V)(he:∀ w,(P.deck w).Ready (V w))(hU:Claim L (P.pear (u+b)) 1 (P.vgap V U)):
    Claim L (P.anchored x u) v (P.agap (fun w=>knot (K w) (T w) (V w)) (fun w=>knot (P.wrapK K w) (S w) (U w))):=by
 let F:= P.wrapK K
 let X w:= (P.deck w).scroll (T w); let Z w:= (P.deck w).deckSum (V w)
 let Δ:=P.vgap V U
 have hO: Workday L (P.per u) U:=by
    have h':Workday L (P.per u) Δ:= by
       obtain ⟨f,hf,H⟩:=(Claim.submits hU (Poly.oneQ _)); refine ⟨_,hf,fun w i t=>?_⟩
       apply (quota_mono (fun z:Budget.Tuple.Hold i t=> Δ w z.val) ?_).trans (H w i t);intro z
       exact Tariff.diam_mono (A:=(P.per u w)) (B:=(P.per (u+b) w)) (fun a i=>Tariff.moment_mono (P.spacing w) (by omega) (Spatial.distance_nonneg (P.period w) ((P.deck w).atO a) ((P.deck w).atO i))) z.val
    have HB:= Workday.add h' (P.deck_work (P.writes ht (show u ≤ u+b+b by omega)) he)
    simpa [Post.vgap,Δ] using HB
 have hX:= hs.knot_budget hO (P.wrap_beam (P.descent h (by omega)) hr)
 have hz:= Carry.charge (P.cross_claim x (P.wrap_beam (P.descent h (by omega)) hr) (P.folded_claim x (P.narrower x hT (by omega))) hU) hk
 convert Claim.add hX hz using 1; ext1 w; unfold agap vgap
 obtain ⟨f,hf,H⟩:= h; obtain ⟨g,hg,G⟩:=ht
 rw [← Packet.knot_copy_mark _ (hr w) (H w).1 (H w).2 (he w) (ne_top_of_le_ne_top (hT.cost w (hh w)) (quota_mono _ fun _=>(P.rooted x (u+b+b) w).width_unit _)) (by exact G w) (hg.cost w) (hf.cost w)]
 have h₁:= knot_addL (F w) (S w-X w) (X w) (U w); rw [sub_add_cancel] at h₁
 have h₂:= knot_addR (F w) (X w) (U w-Z w) (Z w); rw [sub_add_cancel] at h₂
 change knot (F w) (S w) (U w) - knot (F w) (X w) (Z w) = knot (F w) (S w-X w) _ + knot (F w) _ (U w-Z w)
 rw [h₁,h₂]; abel
end Post
end YM.RegulatorIR.Uniform

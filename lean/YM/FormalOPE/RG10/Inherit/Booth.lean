import YM.FormalOPE.RG10.Inherit.Noise
/-!
 # Reference index type and truss transformations

 all cost predicates at any truss pull back first via `Atelier` to Reference=top timing.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Inherit
open Function Filter Topology MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Push.Loops Chart Lattice RG
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {V E:Type}
variable {f : Side} (L:Fabric G f)
 def reset {V E:Type}[Fintype E] (D:Loom V E) (T R:D.Truss): Atelier G T.Bulk R.Bulk where
  placement:= (T.relocation (K:=G.El) R).toMeasurableEquiv
  origin:= T.transfer_one _
  form:= T.transfer_diff R neighborhood_exp
  recover:= R.transfer_diff T neighborhood_exp
abbrev Reference:= Orb.Cotree f ⊕ L.More
-- equivalence to atop indices
 def entrance (i: Orb.Cotree f) : L.atop.Bulk:= ⟨.inl i.val, fun h=> i.property ((L.atop_branch i.val).mp h)⟩
 def terminal (i:L.More): L.atop.Bulk:= ⟨.inr i,L.atop_not i⟩
 def linkRef (L: Fabric G f) : Reference L ≃ L.atop.Bulk where
  toFun:=Sum.elim (entrance L) (terminal L)
  invFun i:= match i with
   | ⟨.inl v,h⟩=> Sum.inl (⟨v,fun e=>h ((L.atop_branch _).mpr e)⟩: Orb.Cotree f)
   | ⟨.inr v,_⟩=>Sum.inr v
  left_inv u:=by match u with
                            | .inl t=>rfl
                            | .inr t=>rfl
  right_inv u:= by match u with
                   | ⟨.inl _,_⟩=>rfl
                   | ⟨.inr _,_⟩=>rfl
 -- use measurable_pi. choose simple permutation.
 def bridge (L:Fabric G f): Atelier G L.atop.Bulk (Reference L) where
  placement:={
   toFun:=fun u=> u∘linkRef L
   invFun:=fun u=> u∘(linkRef L).symm
   left_inv u:= by ext1 i; exact congr_arg u ((linkRef L).apply_symm_apply i)
   right_inv u:= by ext1 i; exact congr_arg u ((linkRef L).symm_apply_apply i)
   measurable_toFun:=measurable_pi_lambda _ (fun i=> measurable_pi_apply (linkRef L i))
   measurable_invFun:=measurable_pi_lambda _ (fun i=>measurable_pi_apply ((linkRef L).symm i)) }
  origin:=rfl
  form:= fun _=> neighborhood_exp _
  recover:= fun _=> neighborhood_exp _

 def deck (u: Configuration G (Orb.Cotree f)): LinkFrame G f:= Orb.splitLink 1 u
 def key (u:Configuration G (Reference L)):= deck (u ∘ Sum.inl)
lemma key_agrees (u:Configuration G L.atop.Bulk): key L ((bridge L).placement u) = L.principal (L.atop.board u):= by
 ext1 i; by_cases h: Orb.Branch i
 · have hp:= Loom.Truss.stitch_tree L.atop (1:L.atop.Tree→G.El) u (⟨Sum.inl i,(L.atop_branch i).mpr h⟩ :L.atop.Tree); change Orb.splitLink _ _ i=L.atop.stitch 1 u (.inl i); rw [hp]; simp [Orb.splitLink,h]
 have he := (Loom.Truss.stitch_bulk L.atop (1:L.atop.Tree→G.El) u (entrance L ⟨i,h⟩)); change Orb.splitLink _ _ i= L.atop.stitch 1 u (entrance L ⟨i,h⟩).val; rw [he,Orb.splitLink,dif_neg h]; rfl
lemma terminal_agrees (u:Configuration G L.atop.Bulk): ((bridge L).placement u) ∘ Sum.inr=L.runoff (L.atop.board u):= funext fun i=> (Loom.Truss.stitch_bulk L.atop (1:L.atop.Tree→G.El) u (terminal L i)).symm
lemma accounting (u: Configuration G (Reference L)): Fabric.wilson (key L u)=Orb.account (u∘Sum.inl):=rfl

-- assemble transports via repeated `pull`; no need trans smooth
end YM.FormalOPE.RG10.Inherit

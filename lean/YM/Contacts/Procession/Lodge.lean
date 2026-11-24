import YM.Contacts.Procession.Rise
/-!
# Mark certificate systematic all-order response on the infinite cover

Combined estimate includes finite winding loss.Consumer inputs concrete power costs.
No assumption PDK is an approximate cover epoch. Uses tested-real rank and μ offset formula proved above.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Procession.Welcome
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch
open scoped Classical Topology BigOperators NNReal Matrix ContDiff
variable {α β γ ι:Type}{G:Gauge}{σ η:ℝ≥0}{b c d:ℝ}{T Q R:TableFee}{L q f m:Side}{u B i k j r n p t:ℕ}
section linear
variable [Fintype ι]
lemma pack_sum (K:α→β)(s:Finset γ){F:γ→Field ι α}(h:∀ i∈s,Summable (F i)) : packing K (∑ i∈s,F i) = ∑ i∈s, packing K (F i):= by unfold packing cram; funext v; simp_rw [Finset.sum_apply]; exact Summable.tsum_finsetSum (fun i hi=> (h i hi).subtype _)
lemma adds (s:Finset γ){c b:γ→ℝ}{F:γ→Field (Fin i) (Node α)}{V:γ→Field (Fin i) (Co m α)}{u:α} (h:∀ i ∈s, Alive σ (c i) (b i) u (F i) m (V i)): Alive σ (∑ i∈s,c i) (∑ i∈s,b i) u (∑ i∈s,F i) m (∑ i∈s,V i):= by
   refine ⟨Rest.sum (fun i hi=>(h i hi).room),Rest.sum (fun i hi=>(h i hi).portrait),?_⟩; rw [pack_sum _ s (fun i hi=> (h i hi).room.summ), ← Finset.sum_sub_distrib]; exact Rest.sum (fun i hi=> (h i hi).far)
lemma hoist_sum [Fintype α][Fintype β](H: Matrix α β ℝ)(F:γ→Field (Fin i) α)(s:Finset γ): hoist H (∑ i∈s,F i)=∑ i∈s,hoist H (F i):= by induction s using Finset.induction with| empty=> rw [sum_empty,sum_empty,hoist_erase]|insert i s hi ih=> simp_rw [sum_insert hi,hoist_add,ih]
end linear
abbrev plead (V:House α) (f : α→β) : House β:= fun i j=>packing f (V i j)
def thrill (p i:ℕ) [AddCommMonoid γ](F:(q k:ℕ)→ γ):= ∑ j∈ Finset.range (i+1),∑ k∈Finset.range (p+j+1), F j k
section
variable (C:Row α α)(R':Row α β)(A:House (Node α))(P:∀ m:Side, House (Co m α))(X:House (Node α))
def dart (i j:ℕ):ℕ:= i+j+1
def hearthC (p : ℕ)(C:Row α α)(R:Row α β) (A Y:House (Node α)):House (Node β):= fun i=> ∑ j∈Finset.range (i+1),∑ k∈Finset.range (p+j+1), ray C R A (dart i k) (i-j) (Y j k)
section
variable [Fintype α][Fintype β]
def planetC (p:ℕ)(C:Row α α)(R:Row α β)(V: House (Co m α))(X:House (Node α)): House (Co m β) := planeC (R.acts m) (canal (C.acts m) p V (plead X (lower m)))
lemma properB (p:ℕ)(F:House (Node α))(K:Node α→ γ)(h:Proper p F): Proper p (plead F K):=⟨fun i j=> poetic _ (h.sym _ _) _,fun i j hi=>by simp only [plead,h.thin _ _ hi,packing]; ext; simp [cram]⟩
lemma planet_bill (p j:ℕ)(X:House (Node α)){V: House (Co m α)}(C:Row α α)(R:Row α β)(hV:Snug V)(h:Proper p X): planetC p C R V X i j = thrill p i (fun i' k=> rose V (C.acts m) (R.acts m) (packing (lower m) (X i' k)) (i-i') j):= by unfold planetC planeC; rw [lantern _ p i _ _ (properB p _ _ h) hV]; simp_rw [Finset.sum_apply, hoist_sum]; rfl
-- accounting all elementary terms
variable {C R' A X P}
structure Price (X:House (Node α))(x:α)(σ:ℝ≥0)(Q:TableFee): Prop where
  lands i j: Rest (terrain σ α) (0,x) (X i j) (Q i j)
variable {hX:House (Node β)}{x:α}{y:β}
abbrev dump (K:ℕ)(f:ℕ→ℕ→ℝ) (p:ℕ) :ℝ := thrill p K f
def sweep (α β:Type)[Fintype α][Fintype β](p:ℕ)(Y:TableFee)(c d:ℝ)(g:TableFee)(i j:ℕ):= dump i (fun w k=> (j+1:ℕ)*skies α β g d c (Y w k) (dart i k+(i-w)) (j+1)) p
def rubble (α β:Type)[Fintype α][Fintype β](p:ℕ)(Y:TableFee)(c d:ℝ)(g:TableFee)(i j:ℕ):= dump i (fun w k=> (j+1:ℕ)*stalks α β g d c (Y w k) (dart i k+(i-w)) (j+1)) p
theorem outlook (h:Dome C R' A P T σ c d)(v:β)(Y:TableFee)(m:Side)(ht:Proper p X)(he: Price X x σ Y): Alive σ (sweep α β p Y c d T i j) (hush σ m*rubble α β p Y c d T i j) v (hearthC p C R' A X i j) m (planetC p C R' (P m) X i j) := by
   rw [planet_bill _ _ _ _ _ (h.warmed _) ht]; unfold hearthC sweep rubble dump thrill; simp_rw [mul_sum,Finset.sum_apply]; refine adds _ (fun a ha=> adds _ (fun w hw=>?_));
   have hz:=reading_block (m:=m) (e:=i-a) (B:=dart i w) (j:=j) (h.paidA m) (he.lands a w) h.Rfee h.beam h.hFee h.cbase v (h.warmed _) (by unfold dart; omega) (ht.sym a w) (by unfold dart; omega); rw [mul_left_comm (hush σ m)] -- bushes mult err
   exact hz
lemma hearth_terms (h:Dome C R' A P T σ c d)(v:β)(Y:TableFee)(ht:Proper p X)(he:Price X x σ Y):
   Price (hearthC p C R' A X) v σ (sweep α β p Y c d T) ∧ Proper p (hearthC p C R' A X) := by
   refine ⟨⟨fun i j=> (outlook h v Y 1 ht he).room⟩,fun i j=> ?_ ,fun i j hj=>?_ ⟩
   · unfold hearthC; simp_rw [Finset.sum_apply]; refine Poem.sum _ (fun _ _=> Poem.sum _ (fun _ _=>?_)); exact poem_scoop hoist_shape -- name args
   let m(k:ℕ):Side:=⟨k+1,by omega⟩; have hm:Tendsto (fun i=>(m i).val) atTop atTop:= StrictMono.tendsto_atTop (show StrictMono fun i=> (m i).val from strictMono_nat_of_lt_succ fun i=>(by change i+1 < i+1+1; omega)); have H (k:ℕ): planetC p C R' (P (m k)) X i j=0:= (paint_proper _ (marsh (C.acts _) (h.warmed _) (properB p X _ ht))).thin i j hj; let f (i:ℕ):= hush σ (m i); have hl : Tendsto f atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (Real.tendsto_exp_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp hm).const_mul_atTop (NNReal.coe_pos.mpr h.flag))); funext q; apply tendsto_nhds_unique (alive_approach (b:=_) (i:=j) (fun k=> outlook (i:=i) h v Y (m k) ht he) (by simpa [f] using hl.mul_const (rubble α β p Y c d T i j)) q hm); simp_rw [H,Pi.zero_apply]; exact tendsto_const_nhds
end
end
end YM.Contacts.Procession.Welcome

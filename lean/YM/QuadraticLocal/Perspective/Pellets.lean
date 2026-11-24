import YM.Progress.DIRECTED_RECIPE.Pellets
import YM.Work.H03
/-!
# HasSlots wlog for Mark comparisons.

The packing argument uses the support on singleLeft slots. All applications here will KEEP the old K
kernel and its old predicate constraints; NO change in any numerical expenditure. All costs
charged on the original addresses and lit before embedding. No ticket to pay only after
some different larger support cancellation. Use these in Mark.Glue.

Adaptor to actual `HasSlots` slots from any purchased output

Keep a map of old eligibility & tests even for the discarded slots. No permutation
constraint across this transform. This is needed when asking actual availability
or guide prices on a continuation. Preserves path & scalar exactly. Perturbative
Template if continuing a re-expression must ALSO reindex on e, including predicted
path differences **before** taking a new quotient.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunday.Filing
open Function Filter Set Lattice RG Wilson MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff Pointwise

open Progress.DirectedRecipe Progress.DirectedRecipe.Rack Ovens Ovens.Pipes
variable {G:Gauge} {n:Side} (A:Activities G n){B:Activities G n}{P:BudgetPoint} {δ w:ℝ}
-- Need softer orientation if using H.Digest; use constant `univ` with no charge & query.
def lanes : Pipes G n := ⟨A.reg,A.forced,fun _=>Finset.univ,fun _=> Finset.univ_nonempty⟩
def cards : Tap G n:=⟨A.E,A.K,0⟩
lemma opened (h:A.Valid P δ w): (lanes A).Digests (cards A) P δ w:=by
   refine ⟨h,fun _ _ he=>False.elim (he rfl),⟨0,summable_zero,fun _ _=>by unfold cards; simp⟩,fun _ _ _=>rfl,fun _ _ _ _ _=>rfl,fun _=>measurable_const,fun s b=>⟨Equiv.refl _,fun i=>?_,fun i U=>rfl⟩⟩
   change Finset.univ= Finset.univ.image (affine s b)
   let v:Equiv.Perm (Site n):=destination s b
   apply Finset.ext; intro x; simp only [Finset.mem_univ,Finset.mem_image,true_and,true_iff]; exact v.surjective x

def tag (i:ℕ):ℕ:=(lanes A).encoding.some.symm (singleLeft (lanes A) i)
def tags : ℕ↪ℕ:= (singleLeft (lanes A)).trans (lanes A).encoding.some.symm.toEmbedding
@[simp] lemma tagged i : (lanes A).encoding.some (tags A i)=singleLeft (lanes A) i:=Equiv.apply_symm_apply ..
def filesK:= (tags A).trans (nameUp ((lanes A).encoding.some))
def filesE:= Rack.upE (lanes A)
def troops (P:BudgetPoint): Activities G n:= fused (folio G n) P (widen (lanes A) (cards A))
lemma temporal {e e' k k':ℕ↪ℕ}{D:Activities G n}(hp:Readdress P e k A B)(hh:Readdress P e' k' B D): Readdress P (e.trans e') (k.trans k') A D:= by
   refine ⟨fun i=> (hh.same_reg _).trans (hp.same_reg _),fun i=> (hh.sup _).trans (hp.sup _),fun i=> (hh.inv _).trans (hp.inv _),fun i=> (hh.emits _).trans (hp.emits _),fun i=>(hh.kernels _).trans (hp.kernels _),fun i hi=>?_,fun i hi=>?_,fun i U h=>hh.admits (k i) U (hp.admits _ _ h)⟩
   · by_cases hx:i∈range e'; obtain ⟨j,rfl⟩:=hx; rw [hh.emits,hp.restE j (fun ⟨k,hk⟩=>hi ⟨k,(congr_arg _ hk)⟩)]
     exact hh.restE _ hx
   by_cases hx:i∈range k'; obtain ⟨j,rfl⟩:=hx; rw [hh.kernels,hp.restK j (fun ⟨k,hk⟩=>hi ⟨k,(congr_arg _ hk)⟩)]
   exact hh.restK _ hx
variable {p:BudgetPoint}{Y:Pipes G n}{x y:ℝ}
abbrev shear (Y : Pipes G n) (F: ℕ ≃ Y.Pellet): ℕ ↪ℕ:= (singleLeft Y).trans F.symm.toEmbedding
lemma packed {z:Tap G n}(hv:Y.Digests z p x y)(h:z.logarithm=0)(F: ℕ≃Y.Pellet): Readdress p (Embedding.refl _) (shear Y F) (Y.pours z) (fused F p z):= by
  let f:= shear Y F
  have hx i: (F (f i)).val={Sum.inl i}:= by rw [show F (f i)=singleLeft Y i from F.apply_symm_apply _]; rfl
  have hs i : (addr F p (f i)).support=(Y.kernel i).support:= by simp only [addr,hx,Pipes.skin,Finset.singleton_biUnion]; rfl
  have hi i : (addr F p (f i)).inventory=(Y.kernel i).inventory:= by change Y.plot _=_; rw [hx]; change (lefts {Sum.inl i}).biUnion _=_; ext; simp [lefts]
  have hk i U: (Y.kernel i).eligible p.threshold U → (addr F p (f i)).eligible p.threshold U:= by
     intro h; refine ⟨hs i|>fun e=> hi i|>fun y=> e.symm ▸ y.symm ▸ h.1,?_⟩
     unfold addr Pipes.condition
     dsimp only; rw [hx]; intro j hj; rw [show j=i by simpa [lefts] using hj]; exact h
  refine ⟨fun _=> rfl,hs,hi,fun _=> rfl,fun i=> ?_,fun i hi=> False.elim (hi ⟨i,rfl⟩),fun i hi=>?_,hk⟩
  · ext U
    change solid F p z (f i) U=z.forced i U
    unfold solid
    split
    · rw [hx, Finset.prod_singleton]; rfl
    next h' => exact Eq.symm (Classical.byContradiction fun hh=> h' (hk _ _ (hv.stamp.forced.permit _ _ hh)))
  let X:= F i
  obtain ⟨l,hl⟩ :∃ j:ℕ,Sum.inl j∈ X.val:= by simpa [lefts, Finset.Nonempty] using X.property.1
  have hy:∃ j:ℕ, Sum.inr j∈ X.val:= by
    by_contra! ht
    have hp {r s: Ovens.Label}(h: Ac.bonds Y.patch X.val r s): r=s:=by
       rcases r with r|r; rcases s with s|s
       · congr 1
         by_contra hk
         obtain ⟨i,hi,hi'⟩:= h.2.2
         exact Finset.disjoint_left.mp (X.property.2.2 (Finset.mem_toLeft.mpr h.1) (Finset.mem_toLeft.mpr h.2.1) hk) hi hi'
       · exact False.elim (ht _ h.2.1)
       exact False.elim (ht _ h.1)
    have he: X.val={Sum.inl l}:= by
       refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hl,fun i hi=>?_⟩
       exact Relation.ReflTransGen.trans_induction_on (X.property.2.1.2 _ hi _ hl) (motive:=fun {i j} _=> i=j) (by intros; rfl) (fun e=>hp e) (fun _ _ e f=> e.trans f)
    exact hi ⟨l,F.injective (Subtype.ext ((hx l).trans he.symm))⟩
  obtain ⟨j,hj⟩:=hy
  ext U
  change (solid F p z i U)=0
  unfold solid; split
  · exact Finset.prod_eq_zero hj (by simp [Ovens.Pipes.reach,h] : reach z (Sum.inr j) U=0)
  rfl
lemma employment (h:A.Valid P δ w): Readdress P (filesE A) (filesK A) A (troops A P):= temporal A (packed (opened _ h) (by rfl) (lanes A).encoding.some) (lift_fused (opened _ h) _)
lemma estate (h:A.Valid P δ w): (troops A P).Valid P δ w∧HasSlots P (troops A P):=by
   let X:=lanes A; let T:=cards A
   obtain ⟨he,hf⟩:= Work.H03.answer G n (drawer G n) (Rack.widen X T) (folio G n) δ w P (absorbs (opened A h)) -- arg number
   have H:=employment A h
   exact ⟨⟨H.regular h.regular,he,hf,H.Ebound h.boundE,H.Kbound h.boundK⟩,never_spent (opened _ h)⟩
end YM.QuadraticLocal.Sunday.Filing

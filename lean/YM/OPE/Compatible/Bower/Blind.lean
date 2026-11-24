import YM.OPE.Compatible.Bower.Lot
/-!
# Per-copy foreground mixtures, full product patterns and projection
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb
open scoped Topology BigOperators Classical
variable {X V G : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X) (F:Finset X) (v:X)
    (t:V→ G) (W:Type)[Fintype V][DecidableEq V][Fintype W][DecidableEq W]
-- rect. competing pivots at notch `v`: never costs more positions than invisible blanks.
def squareCut (D:Origin X)(F:Finset X)(W:Type)[Fintype W][DecidableEq W] (v:X) (t:V→G) (p:Marker.Census.Mode (Names V (brim D F ⊕ W))) :=
    (∀ i∈ p.val,∀ j∈p.val, t i.fst=t j.fst) ∧
     (∀ (i:V) (j k:W),(i,Sum.inr j)∈p.val→ (i,Sum.inr k)∈p.val→ j=k)∧
     (∀ (i:V)(j:W)(k:brim D F),(i,Sum.inr j)∈p.val→(i,Sum.inl k)∈p.val → ¬ v ≤ k.val)

def shades' : Guard (Names V (brim D F ⊕ W)) where
    safe := squareCut D F W v t
    quiet := by simp [squareCut,Census.quiet]
    fire i := by refine ⟨fun j hj k hk=> ?_,fun i j k hj hk=>?_ ,fun i j k hj hk=>?_⟩
                 · simp only [Census.fire,mem_singleton] at *; subst k j; rfl
                 · have he := (mem_singleton.mp hj).trans (mem_singleton.mp hk|>.symm); exact Sum.inr.inj (Prod.mk.inj he|>.2)
                 have he:= (mem_singleton.mp hj).trans (mem_singleton.mp hk|>.symm); exact False.elim (Sum.inl_ne_inr (Prod.mk.inj he.symm|>.2))
    sub h hh:= ⟨fun i hi j hj=>hh.1 i (h hi) j (h hj),fun i j k hi hj=>hh.2.1 i j k (h hi) (h hj),fun i j k hi hj=>hh.2.2 i j k (h hi) (h hj)⟩ -- implicit bind style check
-- use generic curtain after opening
variable (I:Type)[Fintype I][DecidableEq I] in
def curtain (p:V→G) : Guard (Names V I) where
    safe u:= ∀ i∈u.val,∀ j∈u.val,p i.1=p j.1
    quiet := by simp [Census.quiet]
    fire _ _ hi _ hj:= congr_arg _ (congr_arg _ ((mem_singleton.mp hi).trans (mem_singleton.mp hj|>.symm)))
    sub h hh i hi j hj:= hh i (h hi) j (h hj)
lemma shade_well (P:Ensemble V): (shades' D F v t W).Chordal P.v P.perms:=by
    constructor
    intro u hu j hj; constructor
    · rintro ⟨hv,hx,hR⟩; let f:= P.perms u; let w:=drum (slotsZ:=brim D F⊕W) f j
      have hK i (hi:i∈ w.val): i.1=u:= ((district_iff ..).mpr ((P.to_ref u) ▸ ((going f P.v j).mp hj))) hi -- district_iff orientation
      refine ⟨fun i hi k hk=> congr_arg _ ((hK i hi).trans (hK k hk|>.symm)),fun i x y hi he=> ?_,fun i y k hy hk=>?_⟩
      · apply hx (f.symm i) x y
        all_goals
          apply (mem_image_of_injective _ (ManyCopies.nome (slotsZ:=brim D F⊕W) f|>.injective)).1; change (f (f.symm i), _)∈w.val; rw [f.apply_symm_apply]; assumption -- `change`
      apply hR (f.symm i) y k
      all_goals
        apply (mem_image_of_injective _ (ManyCopies.nome (slotsZ:=brim D F⊕W) f|>.injective)).1; change (f (f.symm i), _)∈w.val; rw [f.apply_symm_apply]; assumption
    rintro ⟨hv,hP,hR⟩; refine ⟨fun i hi k hk=>?_,fun i x y hi hy=>hP _ _ _ (mem_image_of_mem _ hi) (mem_image_of_mem _ hy),fun i y k hy hi=>hR _ _ _ (mem_image_of_mem _ hy) (mem_image_of_mem _ hi)⟩
    rw [show i.1=P.v from (district_iff ..).mpr hj hi, show k.1=P.v from (district_iff ..).mpr hj hk]
variable {F}{K:Finset X}{m:X→ℕ}{n:ℕ}
open Wave
lemma shading (H:Wave m F K n)(he:v∈brim D K):∀ p:(Names V (brim D K ⊕ W)).Mode,
    (shades' D K v t W).safe p → (shades' D F v t W).safe (assembly (riseUp W D H) p):=by
   rintro p ⟨hH,hp,hQ⟩; let a:= assembly (riseUp W D H) p; let f:=riseUp W D H
   have hx(i):(i ∈ a.val)↔ (i.1,(raised W D H).bunch i.snd) ∈ p.val:=by unfold a assembly; rw [low_read,Fibers.reaped]; rfl
   refine ⟨fun i hi j hj=> hH _ ((hx i).1 hi) _ ((hx j).1 hj),fun u i j hi hj=> hp u i j ((hx _).1 hi) ((hx _).1 hj),fun i j k hi hk hv=>?_⟩
   let v':brim D K:= ⟨v,he⟩; have h : topHat D H k=v':= (topper D H k v').2 hv; exact hQ i j (topHat D H k) ((hx _).1 hi) ((hx _).1 hk) (h ▸ le_rfl)
lemma opens (p:(Names V (brim D F ⊕ W)).Mode)(v:brim D F)
   (h:(curtain (brim D F) t).safe (landed (atopBy V (foldTo v)) p))(he:Flat (atopBy V (foldTo v)) p) (hs:Crown F) : (shades' D F v.val t W).safe p:=by
   let f:= atopBy V (foldTo (W:=W) v); refine ⟨fun i hi j hj=> h (f i) (mem_image_of_mem f hi) (f j) (mem_image_of_mem f hj),fun i j k hj hk=> ?_,fun i j k hi hk ht=>?_⟩
   · exact Sum.inr.inj (Prod.mk.inj (he hj hk rfl)|>.2)
   have h : v=k:=by by_contra hp; exact brim_apart D F hs v.2 k.2 (Subtype.val_injective.ne hp) ht
   subst k; exact Sum.inl_ne_inr (Prod.mk.inj (he hk hi rfl)|>.2)
end YM.OPE.Arboreal

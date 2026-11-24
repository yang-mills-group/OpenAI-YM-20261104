import YM.OPE.Compatible.Emu.Gallery
/-!
# Routing on cube and gallery
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter Lattice Laurent Wilson Matrix RG
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
open Finset
variable {r s m i b k:ℕ} {n:Side}{x y:Cover}
namespace StepsL
lemma alter (a:Axis):∃ b:Axis,a≠b := by
     by_cases h:a=0
     · exact ⟨1,(by subst a; decide)⟩
     exact ⟨0,h⟩
theorem hall (x y:Cover)(h:x∈Lattice.box r)(hy:y∈Lattice.box r):StepsL x y (Lattice.box r) (10*r):=by
       let a:Axis:=0; obtain ⟨hi,hj⟩:=box_test.mp h; obtain ⟨hV,hY⟩:=box_test.mp hy; specialize hi a; specialize hj a; specialize hV a; specialize hY a; have hp: (y a).natAbs ≤ r:=by omega
       let z:=dye x a (y a); have hu:z a=y a:=update_self ..; have hZ:z∈Lattice.box r:= painted _ _ _ h hp
       obtain ⟨b,ha⟩:=alter a; have hs:= adjust a h hZ (fun i hi=>(update_of_ne hi ..).symm) (show (z a-x a).natAbs≤2*r from by omega) b ha.symm; have ht:=ceiling hZ hy a hu; have he:= both (B:=Lattice.box r) (hs.lend (filter_subset ..) le_rfl) (ht.lend (filter_subset ..) le_rfl); exact he.lend (by rfl) (by omega)
-- ring connected, choose one shared crossing-axis.Horiz if a/=a'
lemma portal {i j:Axis}(hp:i≠j){r:ℕ}{x y:Cover} (hx:x∈Lattice.box r)(hy:y∈Lattice.box r)(h:(x i).natAbs=r)(hv:(y j).natAbs=r): StepsL x y (RingP r) (16*r):=by
        let z:=dye x j (y j); have he:z j=y j:=update_self ..; have hB:z∈Lattice.box r:=painted _ _ (y j) hx hv.le
        let Q:= gallery hx h hB (show x i=z i from (update_of_ne hp ..).symm); let L:=gallery hB (show (z j).natAbs=r from he.symm ▸ hv) hy he; exact lend (both Q L) (by rfl) (by omega)
lemma ring_up (r:ℕ):RingP (r+1)= Lattice.box (r+1) \ Lattice.box r:=by
       ext x; rw [RingP,mem_filter, Finset.mem_sdiff]; refine and_congr_right fun h=>?_ ; obtain ⟨h1,h2⟩:=box_test.mp h; constructor
       · rintro ⟨i,h⟩ hZ; obtain ⟨hv,hh⟩:=box_test.mp hZ; specialize hv i; specialize hh i; omega
       intro h; by_contra he; apply h; rw [box_test]; push Not at he; constructor <;> intro i<;> specialize h1 i<;> specialize h2 i<;> specialize he i <;> omega
lemma crown (h:x∈RingP r)(hv:y∈RingP r): StepsL x y (RingP r) (32*r):=by
       obtain ⟨h,i,hi⟩:=mem_filter.mp h; obtain ⟨hv,j,hj⟩:=mem_filter.mp hv; by_cases ha:i=j; swap;· apply lend (portal ha h hv hi hj) (by rfl); omega
       subst j; obtain ⟨a,ha⟩:= alter i; let z:=dye x a ↑r; let H:= (show z∈Lattice.box r from painted _ _ (↑r) h (by omega)); have hZ:(z a).natAbs=r:=by rw [show z a=(r:ℤ) from update_self ..]; omega
       exact lend (both (portal ha h H hi hZ) (portal ha.symm H hv hZ hj)) (by rfl) (by omega)
noncomputable def anchorX (r:ℕ):Cover:=fun _=>r
lemma lodger (r:ℕ): anchorX r∈RingP r:=by
       rw [RingP,mem_filter]; refine ⟨?_,0,?_⟩ <;>simp [anchorX]
lemma reach (x:Cover)(w:Walk):visits (wrap n x) w= (visits x w).map (wrap n):=by
       induction w generalizing x with
       | nil=>rfl
       | cons a w ih=>
            simp only [visits,List.map_cons]; rw [← wrap_vec n a,←map_add]; exact congr_arg _ (ih _)
lemma rise (x:Cover)(h: x∈ RingP r)(H:Board n r): pdist (wrap n x)=r:=by
      apply le_antisymm (aery H (close h)); obtain ⟨i,hp⟩:= (mem_filter.mp h).2; rw[← hp]; nth_rw 1[← level H (close h)];exact component_le ..
lemma high (h:Board n r) (x:Site n):x∈(RingP r).image (wrap n) ↔ pdist x=r:=by
        rw [mem_image]; constructor
        · rintro ⟨k,hb,rfl⟩; exact rise _ hb h
        intro hx; refine ⟨lift x,?_, wrap_lift _⟩; have hv: lift x∈Lattice.box r:=(lift_le x).mp hx.le; by_cases hg:r=0; · exact mem_filter.mpr ⟨hv,0,by have ht:=component_le x 0; omega⟩
        obtain ⟨t,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hg; rw [ring_up,Finset.mem_sdiff]; exact ⟨hv,fun hp=> (by have hk:= (lift_le x).mpr hp; omega)⟩
lemma doorway (r:ℕ)(h:Board n r)(x:Site n)(ht: pdist x=r):∃ w:Walk, stop x w= wrap n (anchorX r)∧w.length ≤ 32*r∧∀ y∈visits x w,pdist y=r:=by
       obtain ⟨k,hk,rfl⟩:= mem_image.mp ((high h x).mpr ht); obtain ⟨w,hV,hy,he⟩:=(crown hk (lodger r)).sees; refine ⟨w,by rw[←wrap_stop_cover,hV],hy,?_⟩; intro y h; rw [reach] at h; obtain ⟨t,ht,rfl⟩:= List.mem_map.mp h; exact rise _ (he _ ht) (by assumption)
end StepsL
end YM.OPE.Merchant

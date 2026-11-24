import YM.OPE.Compatible.Seeds.Needle
/-!
# Closed cost flag (at one weight). Offer linear projections in rank towers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Exterior Matrix FreeResolvent Precision Tree Woody Bloch Work.F08 Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {r d' j k n m:ℕ}{U C :ℝ}{V I W:Type*}{G:Gauge}{c f:Side}{L:KernelChoices}{P:Flight j k}
namespace Script
open Page
lemma litSum [Fintype W] {p q:Script W r}(v:Fin r→deck W c) (h: Summable p)(hh:Summable q):scribe (0:Site c) (p+q) v=scribe 0 p v+scribe 0 q v:=by
   -- W needed Fintype. 
   unfold scribe; simp only [Pi.add_apply,add_mul]; exact (instruments _ h _ _).summable.tsum_add (instruments _ hh _ _).summable
lemma litScale (p:Script W r)(c:ℝ){N:Side}(v:Fin r→deck W N)(x:Site N):scribe x (c • p) v=c*scribe x p v:=by unfold scribe; simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,tsum_mul_left]
def cope (G:Gauge)(r m:ℕ):Submodule ℝ (Script (Shade G) r) where
   carrier p:= (∃ C,soot m p C)∧ p.abides∧p.painted ∧ p.sorted
   zero_mem':=⟨⟨_,Sack.zero (A:=0) le_rfl _⟩,fun i n w b=>by simp [scribe],fun n u x=>by simp [scribe],fun _=>rfl⟩
   add_mem':=by
      rintro p q ⟨⟨a,ha⟩,hp,h₁,H⟩ ⟨⟨b,hb⟩,hq,h₂,E⟩; have hP:=sootS ha; have hQ:=sootS hb; exact ⟨⟨_,ha.splits hb (fun i=>zero_le_one.trans (payer m _))⟩,fun i n w t=>by rw [litSum _ hP hQ,hp,hq,add_zero],fun n u x=>by rw [litSum _ hP hQ,litSum _ hP hQ,h₁,h₂],fun t=> congr_arg₂ (HAdd.hAdd (α:=Script (Shade G) r)) (H t) (E t)⟩
   smul_mem':=by
      rintro r p ⟨⟨a,ha⟩,hp,h,H⟩; exact ⟨⟨_,ha.scale_line _⟩,fun i n w b=>by rw [litScale,hp,mul_zero],fun n u x=> by rw [litScale,litScale,h],fun t=> show _= _ from congr_arg (fun z=> r • z) (H t)⟩
lemma patent (p:cope G r m): (∃ c,soot m p.val c) ∧ p.val.abides∧p.val.painted∧p.val.sorted:=p.property
-- linear roll and Mellin grades
lemma wellScale [Fintype V] (p:Shift V→ℝ) (l:ℝ)(f:Lieu V→ℝ): well (l • p) f=l*well p f:=by simp [well,mul_assoc,tsum_mul_left]
lemma wellSet {p q:Script W r} (h:soot m p U)(hp:soot m q C)(b:Ink W r)(l:List (Keys r))(hl:l.length≤m): well (sliceP (p+q) b) (tasting l) = well (sliceP p b) (tasting l) + well (sliceP q b) (tasting l):=by
    have hh:= flavor_part _ m hl; unfold well; change (∑' i,(sliceP p b i+sliceP q b i)*_)=_; simp_rw [add_mul]; exact (gardens hh (slices h _)).tsum_add (gardens hh (slices hp _))
def Hollow (G:Gauge)(r m n:ℕ) (h:n≤ m+1): Submodule ℝ (cope G r m) where
    carrier A:= A.val.Bells n
    zero_mem':= by intro i l h; simp only [Submodule.coe_zero];simp [well,sliceP]
    add_mem':=by
       rintro a b ha hb i l hx; obtain ⟨x,H⟩:= (patent a).1; obtain ⟨y,G⟩:= (patent b).1; change well (sliceP (a.val+b.val) i) (tasting l)=_; rw [wellSet H G i l (by omega),ha,hb,add_zero]; all_goals exact hx
    smul_mem':=by rintro k p hv i l hx; change well (k • sliceP p.val i) (tasting l)=_; rw [wellScale,hv i l hx,mul_zero]
def till (p:cope G r m):ℝ:= ∑' i:Page _ _,figure m i*‖p.val i‖
lemma patent_till (p:cope G r m):soot m p.val (till p):= by obtain ⟨c,h⟩:= (patent p).1; exact ⟨h.1,h.2.1,le_rfl⟩
lemma manyX {p q:Script V r}(h:soot m p U)(hh:soot m q C) {v:Fin r→fieldX V}{k:Fin r→ℕ}(ht:Glob v k)(hg:∑ i,k i≤m): wholeX (p+q) v=wholeX p v+wholeX q v:=by
   unfold wholeX; simp only [Pi.add_apply,add_mul]; exact (wordSum h ht hg).tsum_add (wordSum hh ht hg)
lemma scaleX (p: Script V r)(v:Fin r→fieldX V)(a:ℝ): wholeX (a • p) v=a*wholeX p v:=by unfold wholeX; simp [mul_assoc,tsum_mul_left]
def tiller (G:Gauge)(r m n:ℕ)(h:n≤m)(d:ℕ): cope G r m→ₗ[ℝ] partX G r n d where
    toFun p:=⟨honeyX p.val (patent_till p) h d, rollX _ _ (patent p).2.2.2 (patent p).2.2.1 _⟩
    map_add' a b:=by
       apply part_unique; intro q hq z; change honeyX (Subtype.val _) _ _ _ _=(honeyX _ _ _ _ _+honeyX _ _ _ _ _) -- ellipses
       rw [solid_mono,solid_mono,solid_mono, if_pos hq,if_pos hq,if_pos hq]; exact manyX (patent_till a) (patent_till b) (fun i=>low_quiet (ledgeL (z i (q i)).val)) (hq.trans_le h)
    map_smul' v a:=by
       apply part_unique; intro q hq z; change honeyX (Subtype.val _) _ _ _ _= v*honeyX _ _ _ _ _; rw [solid_mono,solid_mono,if_pos hq,if_pos hq]; exact scaleX ..
end Script
end YM.OPE.Flume

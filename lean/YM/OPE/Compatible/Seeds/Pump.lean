import YM.OPE.Compatible.Seeds.Lawn
/-! Opus mechanism on off-shell, Hubble -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Exterior Matrix FreeResolvent Precision Tree Woody Bloch Work.F08 Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {r d' j k n m:ℕ}{U C :ℝ}{V I W:Type*}{G:Gauge}{c f:Side}{L:KernelChoices}{P:Flight j k}
namespace Script
open Page
lemma hoist {A:Cross c V W}[Fintype W](h:Whole A) (u:Cover) {p q:Script V r}(hp:soot m p U)(hg:soot m q C): countermove A u (p+q)=countermove A u p+countermove A u q:=by
     obtain ⟨σ,b,hσ,hb⟩:=h; funext i; unfold countermove; simp only [Pi.add_apply,add_mul]; exact ((cashmoves hb hσ _ _ hp).collectible (payer m) i).of_norm.tsum_add ((cashmoves hb hσ _ _ hg).collectible (payer m) i).of_norm
lemma hoistS {A:Cross c V W} (u:Cover) (p:Script V r)(v:ℝ):countermove A u (v • p)= v • countermove A u p:=by ext1 i; unfold countermove; simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,tsum_mul_left] -- [Fintype]
def pipeX (K:KernelChoices)(G:Gauge)(P:Flight j k)(hb:P.patch.Branches K G)(ht:4≤k): cope G r m→ₗ[ℝ] cope G r m where
     toFun p:=⟨opal G.ColorIndex P K.penalty p.val,by
         have hL:= stored P _ K.penalty_pos ht; obtain ⟨hp,h,hx,g⟩:= patent p; obtain ⟨c,ha⟩:= hp; have hs:= sootS ha; refine ⟨?_,hubWorks P K _ hb ht hs h,hubTint P K _ ht hs hx,territory _ 0 hs _ (chrome_sum hL) g⟩; obtain ⟨η,U,h,hC⟩:=chrome_sum (W:=G.ColorIndex) hL; exact ⟨_,counterflow hC h _ _ ha⟩⟩
     map_add' a b:= Subtype.ext (hoist (chrome_sum (W:=G.ColorIndex) (stored P _ K.penalty_pos ht)) _ (patent_till a) (patent_till b))
     map_smul' x a:= Subtype.ext (hoistS _ _ x)
variable (ht:P.patch.Branches L G)(hx:4≤k)(p:cope G r m)
include hx ht
local notation "g" => pipeX L G P ht hx
local notation "L!"=> (P.L.val:ℝ)
lemma survives (h:n≤j) (he:n≤m+1)(hp:p∈ Hollow G r m n he): g p∈ Hollow G r m n he:=by
     intro i l hl; change well (sliceP (opal _ _ _ _) _) _=_; have hp':=show p.val.Bells n from hp
     rw [opus_well p.val (patent_till _) L.penalty_pos hx _ l (fun i u hu=>hp' i u (hu.trans hl)) (by omega) (hl.trans_le h), hp' i l hl, mul_zero]
lemma earnings (hp:n≤j-1)(hm:n<m) (hn:Hollow G r m n (show n≤m+1 from by omega) |>.carrier p) (hh:n ≤ d'): tiller G r m n hm.le d' (g p)=(L!⁻¹^(r+n)) • tiller G r m n hm.le d' p:=by
     let v:ℝ:=L!⁻¹^(r+n); have hJ:= P.legal; have hz:p.val.Bells n:= hn
     let T:= pipeX (r:=r) (m:=m) L G P ht hx -- notation
     let q:=g p - v • p; have H:(tiller G r m n hm.le d') q=0:=by
        let s:= n+1; have htX:q.val.Bells s:=by
            intro i l hl; let R:= v • p; have hs:=patent_till (T p); have hh:=patent_till (-R); let u:=T p; have hk: q=u+(-R):=sub_eq_add_neg ..
            rw [hk]; change well (sliceP ((T p).val+(-R).val) i) _=_; have hhx : l.length ≤ n := Nat.le_of_lt_succ hl
            rw [wellSet hs hh i l (hhx.trans hm.le),show sliceP (-R).val i=(-v) • sliceP p.val i from (neg_smul v _).symm]; change well (sliceP (opal _ _ _ _) i) _ + well ((-v) • sliceP p.val i) _ = _ -- maybe neg not def
            rw [opus_well _ (patent_till p) L.penalty_pos hx _ l (fun i t ht=>hz i t (ht.trans_le hhx)) (by omega) (by omega), wellScale]
            by_cases ht:l.length=n; rw [ht]; unfold v; ring
            rw [hz i l (lt_of_le_of_ne hhx ht)]; ring
        apply Subtype.ext; exact (roll_inject q.val (patent_till _) hm hh ((patent q).2.1) (fun i l hl=>htX _ _ (hl.trans (Nat.lt_succ_self n)))).2 htX
     exact sub_eq_zero.mp (by rw [show (tiller G r m n _ d') (g p) - _=tiller G r m n hm.le d' q from ?_]; exact H; unfold q;rw [map_sub,map_smul])
end Script
end YM.OPE.Flume

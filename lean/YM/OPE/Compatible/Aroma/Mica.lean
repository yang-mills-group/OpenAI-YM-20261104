import YM.OPE.Compatible.Aroma.Cloud
/-! # curl & co via torus exact. Polar sum signs. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Exterior Tensor WithLp Work.F08 Matrix Bloch Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {r d' m n j:ℕ}{b e s:ℝ}{I J W K:Type*} {L: Side}
namespace Script
open Page
private lemma summing {φ:Filter K}{p:K→I→ℝ}[Fintype I]{q:I→ℝ}(h:∀ i,Tendsto (fun j=>p j i) φ (𝓝 (q i))):Tendsto (fun j=>∑ i,p j i) φ (𝓝 (∑ i,q i)):= tendsto_finsetSum univ fun i _=> h i
-- needed transpose local stencil equality. compute d^T via transpose row, finite composition.
lemma coarea {v:fieldX (TypeFace 1)} (hp:Quiet v m)(i:PlaqAxes)(x:Cover):
    meetsX (cobound 1) v (x,plaquette i) = movesX ℝ i.val.1 (sea (coord i.val.2) v) x-movesX ℝ i.val.2 (sea (coord i.val.1) v) x:=by
       let z(t:ℕ):=closeX v (epochX t); have he:=received (V:=epochX) (show Tendsto (fun i=>(epochX i).val) atTop atTop from tendsto_add_atTop_nat 1) hp; have hh:Realized epochX atTop v z m:=he
       apply tendsto_nhds_unique_of_eventuallyEq ((meetings hh (Whole.boundary 1)).Onset (x,plaquette i)) ((hh.Onset (x+step i.val.1,coord i.val.2)).sub (hh.Onset (x,coord i.val.2)) |>.sub ((hh.Onset (x+step i.val.2,coord i.val.1)).sub (hh.Onset (x,coord i.val.1))))
       filter_upwards with t; simp only [unfoldX]; rw [d_plaquettes]; simp
lemma reverseFace {v:fieldX (TypeFace (r+1))}(hp: Quiet v m)(x:Cover)(i:TypeFace r):
    meetsX (transRows (cobound r)) v (x,i)=-(∑ k:Axis, ∑ j, left ℝ r k j i*swipe k v (x-step k,j)):=by
       unfold meetsX; let g(u:Cover)(j:TypeFace (r+1)):= transRows (cobound r) i j u*v (x+u,j)
       have hs:Summable (uncurry g):=meets_current (Whole.boundary r|>.flipped) hp x i
       change (∑' i,uncurry g i)=_; rw [hs.tsum_prod]; simp only [uncurry_apply_pair]; rw [← hs.tsum_comm,tsum_fintype, sum_comm,← sum_neg_distrib]
       apply Finset.sum_congr rfl;intro j _; unfold g transRows; rw [← (Equiv.neg Cover).tsum_eq]; simp only [Equiv.neg_apply, neg_neg]; rw [tsum_eq_sum (s:=Exterior.support)]; swap; · intro b hb; rw [Exterior.certified _ _ _ _ hb, zero_mul]
       unfold cobound; simp_rw [Finset.sum_mul]; rw [sum_comm,← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun k _=>?_; have h: (step k:Cover)∈Exterior.support:= mem_insert_of_mem (mem_image.mpr ⟨k,mem_univ k,rfl⟩)
       have he: (0:Cover) ∈ Exterior.support:= mem_insert_self ..
       simp only [mul_sub,sub_mul,mul_ite,ite_mul,mul_one,zero_mul,mul_zero, sum_sub_distrib,sum_ite_eq',if_pos h,if_pos he]; change _= -(left ℝ r k j i * (v _-v (x-step k,j)))
       rw [neg_zero,add_zero]; change _ = -(left ℝ r k j i * (v ((x-step k)+step k,j)-v _)); rw [sub_add_cancel]; simp [sub_eq_add_neg];ring
-- oriented blade wedge signs
lemma plank (i:PlaqAxes)(x y:Axis):
    left ℝ 1 x (plaquette i) (coord y)= if x=i.val.1∧y=i.val.2 then 1 else if x=i.val.2∧y=i.val.1 then -1 else 0:=by
       let s:=i.val.1; let t:=i.val.2; let B:=plaquette i; have hp:s<t:=i.property; have he:B.val={s,t}:=rfl; change left ℝ _ x B (coord y)= if x=s ∧ y=t then 1 else if x=t∧y=s then -1 else 0; simp only [left,Matrix.of_apply]; split
       next h =>
          obtain rfl|rfl: s=x ∨ t=x:=by simpa [he, eq_comm] using h -- cannot subst s
          · have ha: remove s B h=coord t:=by ext l; simp [remove,coord,he]; rintro rfl; exact hp.ne'
            rw [ha]; have h1: parity B.val s ℝ=1:=by simp [parity,pre,he,Finset.filter_insert, Finset.filter_singleton,hp.not_gt];
            simp [hp.ne,h1, coord_iff,eq_comm]
          have ha: remove t B h=coord s:=by ext l;by_cases ht:l=t<;>simp [ht,remove,coord,he,hp.ne']
          rw [ha]; have h1: parity B.val t ℝ= -1:=by simp [parity,pre,he,Finset.filter_insert,Finset.filter_singleton,hp]
          simp [hp.ne',h1,coord_iff,eq_comm]
       next h=>
          rw [he] at h; simp only [mem_insert,mem_singleton] at h; simp [not_or.mp h|>.1,not_or.mp h|>.2]
end Script
end YM.OPE.Flume

import YM.SchemeRG11.Long.Harness
/-! Action term has grade 4 in Nest; cut-shell coface similarly.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Long
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn
open Labels MvPolynomial
open scoped Classical
variable {G:Gauge} {T:Align.Itinerary}
def part (i j:Axis):Ban G:=fun _ x=>Tree.cost x i j
lemma speaks (i j:Axis)(s:Tree.FourSteps)(v:G.ColorIndex)(x:Cover):flex x (tongue (0:Cover) i j s v)=tongue x i j s v:=by fin_cases s <;> simp [tongue] <;> simp [flex,rise,add_comm]
lemma protrude(i j:Axis)(v:G.ColorIndex)(x:Cover):flex x (intake (0:Cover) i j v)=intake x i j v:=by simp only [intake,map_sum,speaks]
lemma stationary(i j:Axis)(p:G.ColorIndex)(x:Cover)(w:Cover): flex x (intake w i j p)=intake (x+w) i j p:=by rw [← protrude i j p w,flex_mul,protrude]
lemma carries(i j:Axis): Nest T 4 (part (G:=G) i j):=by
 by_cases h:i<j
 · let L(k:Axis)(v:G.ColorIndex):Ban G:=fun _ x=> leaf (tongue x i j k v)
   have he(v:G.ColorIndex)(s t:Axis):Nest T 2 (fun _ x=> stockpile x i j v s t):=by
      apply nest_pile (p:=fun b _ (x:Cover)=>∑ w:G.ColorIndex,Triangle.colorF b w v • staple x i j b w s t); intro p _
      apply nest_pile (p:=fun b _ (x:Cover)=> Triangle.colorF p b v • staple x i j p b s t); intro r _
      let H:Ban G:=fun _ (x:Cover)=> staple x i j p r s t
      change Nest T 2 (play (view (fun _=>Triangle.colorF p r v)) H); apply nest_c
      by_cases hp:s<t
      · have hh(a k):Nest T 1 (L a k):=by
           convert Nest.piece (T:=T) (tongue 0 i j a k) (blank_step _) using 1
           · norm_num
           funext j' x; rw [swift,speaks]
        rw [show H=L s p*L t r from funext fun _=>funext fun x=>if_pos hp]; exact (hh s p).mul (hh t r)
      rw [show H=0 from funext fun _=> funext fun _=> if_neg hp]; exact .zero _
   have hv(v:G.ColorIndex): Nest T 2 (fun _ x=>oreL x i j v):=by
      unfold oreL; apply nest_pile (p:=fun k _ (x:Cover)=>∑ t:Axis, stockpile x i j v k t); intro k _; exact nest_pile (p:=fun t _ (x:Cover)=> stockpile x i j v k t) Finset.univ 2 (fun t _=> he v k t)
   unfold Long.part Tree.cost; simp only [if_pos h]; refine nest_c (nest_pile (p:=fun a _ (x:Cover)=> leaf (intake x i j a)*oreL x i j a) _ _ ?_) _
   intro a _
   convert Nest.mul (.piece (T:=T) (intake 0 i j a) (high_i i j _ _)) (hv a) using 1
   · norm_num
   funext k x; simp only [Pi.mul_apply,swift,protrude]
 rw [show part (G:=G) i j=0 from funext fun k=>funext fun x=>if_neg h]; exact .zero _
lemma tracks (i j:Axis)(v:G.ColorIndex)(w:Cover):Nest T 2 (fun _ (x:Cover)=>leaf (intake (x+w) i j v)):=by
 have he:=Nest.piece (T:=T) (intake w i j v) (high_i i j _ _)
 convert he using 1
 · norm_num
 funext k x; simp only [swift,stationary]
-- η moving coface is grade m source. individual free from θ variable.
def cinders (B:Window)(j:Axis)(v:G.ColorIndex)(T: Itinerary):Ban G:=fun k x=>leaf (North.brim (cove T B k) ((x,j),v))
def budge(θ:Cover→ G.Color)(j:Axis)(v:G.ColorIndex):Ban G:=fun _ x=> leaf (North.drift θ ((x,j),v))
lemma railed (j:Axis)(a:G.ColorIndex):Nest T 1 (fun _ (x:Cover)=> (X (((x,j),a):Shaft G))) :=by
 have H:=Nest.piece (T:=T) (idi (((0:Cover),j),a)) (blank_step _); convert H using 1
 · norm_num
 funext k x; simp only [swift,flex_one, idi, leaf,Finsupp.linearCombination_single, one_smul, rise, zero_add]
lemma kindles (B:Window)(j:Axis)(v:G.ColorIndex): Nest T 3 (cinders B j v T):=by
 unfold cinders North.brim; simp only [map_smul,map_sum]
 apply nest_pile _ (p:=fun a k x=> _); intro a _
 convert (tracks (T:=T) a j v (-(step a):Cover)).scale (biker T B a) using 1 -- weights?
 · norm_num --?
 funext k x; simp only [play,barkS,sub_eq_add_neg]
lemma poplar {m:ℕ} {θ:Cover→G.Color}(h:θ∈cap G.Color (m+1))(j:Axis)(a:G.ColorIndex): Nest T (1-(m:ℤ)) (budge θ j a):=by
 unfold budge North.drift; simp_rw [map_sum]; simp only [leaf,Finsupp.linearCombination_single]
 apply nest_pile _ (p:=fun c k x=> _); intro c _
 let q: G.Color→ₗ[ℝ] ℝ:= (EuclideanSpace.proj a).toLinearMap.comp (G.ad (unitColor G c))
 let v(x:Cover):ℝ:= G.ad (unitColor G c) (θ (x+step j)+θ x) a
 have he:v= q ∘ (hop (step j) θ + θ):=rfl
 have hk: v ∈ cap ℝ (m+1):=by rw [he]; intro s hs; rw [plane_map, member.mp (Submodule.add_mem (cap G.Color (m+1)) (hop_cap h _) h) _ hs]; exact funext fun _=>map_zero _
 have hb :Plain T (-(-(m:ℤ))) (view v):=by rw [neg_neg]; exact branchCost _ _ hk
 rw [show (1:ℤ)-m=-(m:ℤ)+1 by omega]; exact (railed j c).scale hb
lemma drought(B:Window){m:ℕ} {θ:Cover→G.Color}(h:θ∈cap G.Color (m+1))(j:Axis)(a:G.ColorIndex): Nest T (4-(m:ℤ)) (cinders B j a T *budge θ j a):=by rw [show (4:ℤ)-m= 3+(1-(m:ℤ)) by omega]; exact (kindles ..).mul (poplar h j a)
end YM.SchemeRG11.Long

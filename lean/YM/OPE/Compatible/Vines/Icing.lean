import YM.OPE.Compatible.Vines.Pod
import YM.Maxwell.Exterior
/-! Low moments: shifts, curls and power-counting -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Tensor ContinuousMultilinearMap WithLp
open scoped Topology BigOperators Classical
variable {r d m n:ℕ}{c:ℝ}{T I:Type*}
namespace Script
open Page
abbrev fromX (t:Lieu Axis):E4:=toLp 2 t
abbrev invertX (u:E4):Lieu Axis:= fun i=>u i
lemma tgon (T:YM.Tensor.T E4 ℝ d):diagonal T∘fromX∈Flavor Axis d:=by
   let q : Fin d→Axis→Lieu Axis→ℝ:=fun _ i x=>x i; let p(g:Fin d→Axis):=∏ i,q i (g i)
   have he(v): ∑ g: Fin d→Axis, p g v * T (fun i=>basis (g i))= diagonal T (fromX v):=by
       let x:=fromX v; have hv : ∑ i:Axis,v i • basis i=x:=by ext a; change _=v a; simp
       unfold diagonal; rw [← (show _= fromX v from hv)]; change _=T.toMultilinearMap _; rw [MultilinearMap.map_sum_finset]; simp_rw [T.toMultilinearMap.map_smul_univ]; simp only [Fintype.piFinset_univ]; exact sum_congr rfl fun g _=>by unfold p; rw [Finset.prod_apply];rfl
   have hp (s:Finset (Fin d)) (g:Fin d→Axis): (∏ i∈s,q i (g i))∈Flavor Axis s.card:=by
      induction s using Finset.induction_on with
      | empty=>simp only [prod_empty,Finset.card_empty]; exact flavor_one _
      | insert i s hi ih=>rw [prod_insert hi, Finset.card_insert_of_notMem hi,add_comm]; exact flavor_prod (flavor_position _) ih
   rw [show diagonal T ∘ fromX=∑ g:Fin d→Axis,T (fun i=>basis (g i)) • p g from funext fun v=>by rw [comp_apply, ← he v,Finset.sum_apply]; exact sum_congr rfl (fun i _=>mul_comm ..)]
   exact (Flavor _ _).sum_mem (fun g _=> (Flavor _ _).smul_mem _ (by simpa only [Finset.card_univ,Fintype.card_fin] using hp univ g))
def gust (x:E4)(f:Lieu Axis→ℝ):Lieu Axis→ℝ:=fun t=> f (invertX (fromX t + x))- f t
def breeze (x:E4)(f:Lieu Axis→ℝ):Lieu Axis→ℝ:=fun t=> fderiv ℝ (f∘invertX) (fromX t) x
lemma gust_zero (x:E4):gust x 0=0:=by ext i; simp [gust]
lemma jig {f:Lieu Axis→ℝ}(h:f∈Flavor Axis d):Differentiable ℝ (f ∘ invertX):=by
    refine flavor_elim h (fun f=>Differentiable ℝ (f ∘ invertX)) (fun l _=>?_) (differentiable_const _) (fun _ _ _ _ a b=> Differentiable.add a b) (fun r _ _ h=> Differentiable.const_smul h r)
    induction l with
    | nil=> exact differentiable_const _
    | cons i l ih=> exact (compAxis i).differentiable.mul (ih (by simp_all; omega))
-- use rec n Flavor list for Gust first
lemma sudden (f:Lieu Axis→ℝ)(h:f∈Flavor Axis d)(x:E4): gust x f∈ Flavor Axis (d-1) ∧ (d=0→gust x f=0):=by
    let K:= Flavor Axis (d-1)
    apply flavor_elim h (fun f=> gust x f ∈ K ∧ (d=0→gust x f=0)) ?_ ?_ ?_ ?_
    · intro l hl
      have ht(l:List Axis):gust x (tasting l)∈Flavor Axis (l.length-1)∧(l=[]→gust x (tasting l)=0):=by
         clear hl; induction l with
         | nil=> have he: gust x (tasting [])=0:=by ext i; simp [gust,tasting]
                 rw [he]; exact ⟨(Flavor Axis _).zero_mem,fun _=>rfl⟩
         | cons i l ih=>
            refine ⟨?_,by simp⟩; let f:= tasting l; let g:Lieu Axis→ℝ:= fun t=> t i+x i
            rw [show gust x (tasting (i::l))= g*(gust x f)+(x i) • f from funext fun t=>by change (t i+x i)*tasting l _- t i*tasting l _= (t i+x i)*(tasting l _ - tasting l _)+ x i* tasting l _; ring, List.length_cons,Nat.add_sub_cancel]
            apply (Flavor Axis _).add_mem _ ((Flavor Axis _).smul_mem _ (flavor_part _ _ le_rfl)); by_cases hx:l=[]
            · erw [ih.2 hx,mul_zero]; exact (Flavor Axis _).zero_mem
            have he:1+(l.length-1)=l.length:=by cases l<;>simp_all [add_comm]
            exact flavor_up he.le (flavor_prod ((Flavor Axis 1).add_mem (flavor_position _) (flavor_cast _ _)) ih.1)
      exact ⟨flavor_up (by omega) (ht l).1,fun hh=>(ht l).2 (List.length_eq_zero_iff.mp (by omega))⟩
    · rw [gust_zero]; exact ⟨K.zero_mem,fun _=>rfl⟩
    · rintro v p hv hw ⟨hx,h⟩ ⟨hy,H⟩; rw [show gust x (v+p)=gust x v+gust x p from funext fun i=> by simp [gust]; abel]; exact ⟨K.add_mem hx hy,fun i=>by rw [h i,H i,add_zero]⟩
    rintro k v hv ⟨hx,H⟩; rw [show gust x (k • v)= k • gust x v from funext fun i=>by simp [gust,mul_sub]]; exact ⟨K.smul_mem k hx,fun i=> by rw [H i,smul_zero]⟩
end Script
end YM.OPE.Flume

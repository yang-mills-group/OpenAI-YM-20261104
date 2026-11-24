import YM.OPE.Compatible.Kiwi.Bite
/-! # Measure joint products. Character-independent. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Saga Shrew Maxwell Maxwell.Free
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {N:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {I J V:Type}{ℓ:Filter V}[LinearOrder I][LinearOrder J]{X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X]
variable (s:Finset I)(A:I→I→ℝ)(x:I→ Module.Dual ℝ X) (t:Finset J)(B:J→J→ℝ)(y:J→Module.Dual ℝ X)
local notation "Q"=> LakeT ℓ
open Finset
lemma cafe (μ:Measure X)[μ.IsAddHaarMeasure](W:Law X)(i:I)(hi:First i s):
     let P(s:Finset I)(t:Finset J):= W.average μ (fauna A x s*fauna B y t); let v:=s.erase i
     P s t=(∑ j∈t,W.wick (x i) (y j)*P v (t.erase j))+(∑ j∈v,(W.wick (x i) (x j)-A i j)*P (v.erase j) t):=by
        intro P v; unfold P; rw [hick μ W A x (incense B y t) hi, poHer,mul_sum]; simp_rw [mul_smul_comm]; rw [science μ W _ _ (fun j _=>Bond.scale _ ((incense ..).mul (incense ..)))]; simp_rw [scooted];rfl
-- pair master. Q convergence
variable (u:V→Side)(q:Side)(h:q.val>1) (p p':Cover)
variable (K:I→Reed G)(R:J→Reed G) {hu:4≤r} {H:∀ i,Even (u i).val}
local notation "Ψ"=> (fun i:V×ℕ=> boost (Nsp u q H i) (Train.top r) hu L (G:=G))
local notation "ρ"=> (fun i:V×ℕ=>Chart.tangent G (Weir.Limb (Nsp u q H i)))
-- Songs
abbrev PK (_p:Cover)(K: I→ Reed G)(s:Finset I)(H:Even N.val)(x:Site N):=fauna (fun a b=>firm (K a) (K b)) (fun a=>poseT H x (K a).2 (K a).1) s
abbrev rung (K:I→Reed G)(s:Finset I):=∑ i∈s,(K i).1.heat
include h
lemma pursuit (hp:Ncap u ℓ)(hx:p≠p'):
   Tendsto (fun i:V×ℕ=> ((baseR q i.2 ^ (rung K s+rung R t) * (Ψ i).average (ρ i) (PK p K s (Nsp u q H i) (stow u q p i)*PK p' R t (Nsp u q H i) (stow u q p' i)):ℝ):ℂ)) Q
         (𝓝 (Maxwell.Free.bond G (incVec 1 p) (incVec 1 p') (choms K s) (choms R t))) :=by
      let X(i:V×ℕ)(p:Cover)(b:Reed G):= ps (wedgeL b u q h p i.1) i.2 (Nsp u q H i)
      let f(s t i):= (Ψ i).average (ρ i) (PK p K s (Nsp u q H i) (stow u q p i)*PK p' R t (Nsp u q H i) (stow u q p' i)); let r(i:V×ℕ)(t:ℕ):= baseR q i.2^t
      let a:= incVec 1 p; let b:= incVec 1 p'; let w:= Maxwell.Free.bond G a b; have hz:a≠b:= scope_inj.ne hx
      let F(s t i):ℂ:= (r i (rung K s+rung R t) * f s t i:ℝ); change Tendsto (F s t) _ (𝓝 (w _ _))
      let M(v v': Reed G)(t z:Cover)(i:V×ℕ):= (Ψ i).wick (X i t v) (X i z v')-(if t=z then firm v v' else 0)
      have hv(t z:Cover)(v v':Reed G) : Tendsto (fun i=>(((r i (v.1.heat+v'.1.heat)*M v v' t z i):ℝ):ℂ)) Q (𝓝 ((Bsky v t v' z):ℂ)):= (Complex.continuous_ofReal.tendsto (Bsky v t v' z)).comp (stressY u q h t z v v' hp H hu L)
      induction s using Finset.strongInduction generalizing t with | _ s ih
      obtain rfl|he:=s.eq_empty_or_nonempty
      · clear ih; induction t using Finset.strongInduction with | _ t ih
        have hh(t:Finset J)(i:V×ℕ): f ∅ t i=(Ψ i).average (ρ i) (PK p' R t (Nsp u q H i) (stow u q p' i)):=by unfold f PK; rw [fanE,one_mul]
        have hF : choms K ∅=1:= Finset.prod_empty
        rw [hF]; obtain rfl|he:=t.eq_empty_or_nonempty
        · simp only [F,hh,PK,fanE,rung,sum_empty,r, pow_zero,add_zero, Law.empty,mul_one,choms, Finset.prod_empty,Complex.ofReal_one]; rw [show (w 1 1)= (1:ℂ) from unitsB a b G]; exact tendsto_const_nhds
        let i:= t.min' he; let T:= t.erase i; have ht:=innerA he; have hT:T ⊂ t:= erase_ssubset ht.1
        have hz(j)(hj:j∈T): Tendsto (F ∅ (T.erase j)) Q (𝓝 (w 1 (choms R (T.erase j)))):=ih _ (Finset.ssubset_of_subset_of_ssubset (erase_subset ..) hT)
        rw [show w 1 (choms R t)=0 from units_drift a b ‹a≠b› t he R]
        let X'(j:J)(b:V×ℕ):ℂ:= ((r b ((R i).1.heat+(R j).1.heat)*M (R i) (R j) p' p' b :ℝ):ℂ)
        have htF (j:J): Tendsto (X' j) Q (𝓝 0):=by simpa only [Bsky,ite_true,eq_self,Complex.ofReal_zero] using! hv p' p' (R i) (R j)
        rw [show F ∅ t=(fun i=>∑ j∈T,X' j i* F ∅ (T.erase j) i) from ?_, show (0:ℂ)= ∑ _∈T,(0:ℂ) from Finset.sum_const_zero.symm]; exact tendsto_finsetSum T (fun i hi=>by simpa using! (htF i).mul (hz i hi)) -- using hF rewriting issue
        funext j; unfold F; simp_rw [hh,PK]; rw [bloom_raw (ρ j) (Ψ j) _ _ ht, Finset.mul_sum, Complex.ofReal_sum]; apply sum_congr rfl; intro m hm; let W:(Finset J)→ℕ:=rung R
        have hg: rung K ∅=0:=Finset.sum_empty; rw [hg,zero_add,zero_add,show rung R t= ((R i).1.heat+(R m).1.heat)+W (T.erase m) from ?_,show r j (_+_)= r j ((R i).1.heat+(R m).1.heat) *r j (W (T.erase m)) from pow_add ..]; let Ev:= f ∅ (T.erase m) j; unfold X'; rw [← Complex.ofReal_mul]; apply congr_arg; unfold M; rw [if_pos (rfl:p'=p')]; let Ξ:= (Ψ j).wick (X j p' (R i)) (X j p' (R m)) - firm (R i) (R m); change r j ((R i).1.heat+(R m).1.heat)*r j (W (T.erase m)) *(Ξ* _) = (r j ((R i).1.heat+(R m).1.heat)*Ξ)*(r j (W (T.erase m))*_); ac_rfl -- try
        unfold W T rung; rw [← Finset.add_sum_erase _ _ (show i∈t from ht.1),← Finset.add_sum_erase (s:=t.erase i) _ hm];omega
      let i:=s.min' he; let T:=s.erase i; have ht:=innerA he; have hT:T⊂s:= erase_ssubset ht.1
      rw [chom_one K (show i∈s from ht.1),show w _ _= _ from (show w (planeLeg (K i)*choms K T) (choms R t)=_ from chom_bond R a b hz _ _ _)]
      let C' (j:J)(u):ℂ:= (r u ((K i).1.heat+(R j).1.heat)* M (K i) (R j) p p' u:ℝ)
      let D' (j:I)(u):ℂ:= (r u ((K i).1.heat+(K j).1.heat)* M (K i) (K j) p p u:ℝ)
      rw [show F s t =(fun z=> (∑ j∈t,C' j z*F T (t.erase j) z)+∑ j∈T,D' j z*F (T.erase j) t z) from ?_]; swap
      · funext z; let Λ:=rung K s+rung R t; let G j:= (Ψ z).wick (X z p (K i)) (X z p' (R j)); let S':=f s
        have hp: f s t z=(∑ j∈t, G j* f T (t.erase j) z) +(∑ j∈T,M (K i) (K j) p p z*f (T.erase j) t z):=by
           have htK(j:I): M (K i) (K j) p p z= (Ψ z).wick (X z p (K i)) (X z p (K j))-firm (K i) (K j):=by unfold M; rw [if_pos (rfl : p=p)] -- rhs mvar
           simp_rw [htK]; exact cafe s _ _ t _ _ (ρ z) (Ψ z) i ht
        unfold F; rw [hp,mul_add,Complex.ofReal_add]; simp_rw [Finset.mul_sum,Complex.ofReal_sum]; apply congr_arg₂ (·+·)
        · apply sum_congr rfl; intro a ha; unfold C'; rw [show M (K i) (R a) p p' z=G a from (by unfold M; rw [if_neg hx,sub_zero])]; rw [show rung K s + rung R t=((K i).1.heat+(R a).1.heat)+(rung K T+rung R (t.erase a)) from ?_]; swap; · unfold T rung; rw [← Finset.add_sum_erase _ _ (show i∈s from ht.1),← Finset.add_sum_erase t _ ha]; abel
          rw [show r z (_+_)=r z ((K i).1.heat+(R a).1.heat)*r z (rung K T+rung R (t.erase a)) from pow_add ..]; push_cast; ring
        apply sum_congr rfl; intro a ha; unfold D'; rw [show rung K s+rung R t=((K i).1.heat+(K a).1.heat)+(rung K (T.erase a)+rung R t) from ?_]; swap; · unfold T rung; rw [← Finset.add_sum_erase _ _ (show i∈s from ht.1),← Finset.add_sum_erase _ _ (show a∈ s.erase i from ha)]; abel
        rw [show r z (_+_)=r z ((K i).1.heat+(K a).1.heat)*r z (rung K (T.erase a)+rung R t) from pow_add ..];push_cast; ring
      have ht(i:I)(hi:i∈T):=ih _ (Finset.ssubset_of_subset_of_ssubset (erase_subset i T) hT) t
      have he(j:I): Tendsto (D' j) Q (𝓝 0):=by simpa only [Bsky,ite_true,eq_self,Complex.ofReal_zero] using! hv p p (K i) (K j)
      let bnd(z):=∑ j∈T,D' j z*F (T.erase j) t z; have hZ:Tendsto bnd Q (𝓝 0):=by rw [show (0:ℂ)=∑ i∈T,0 from Finset.sum_const_zero.symm]; exact tendsto_finsetSum _ (fun i hi=>by simpa using! (he i).mul (ht i hi))
      have hg(j): Tendsto (C' j) Q (𝓝 ((Maxwell.Free.K (rayLeg (K i)) (rayLeg (R j)) a b):ℂ)):=by simpa only [Bsky,if_neg hx] using! hv p p' (K i) (R j)
      rw [← add_zero (∑ i∈t,_)] -- underscore
      exact Tendsto.add (tendsto_finsetSum t (fun i hi=> (hg i).mul (ih T hT (t.erase i)))) hZ
end YM.OPE.Prairies

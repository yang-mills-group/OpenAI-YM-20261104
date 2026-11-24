import YM.MSbar.Chord.Unit
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform
open Precision Gauge MSbar.Wave StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset
variable {G:Gauge}{n:Side}{Q:FaceRail n G}{Z:ℝ}
local notation "S₀"=> Site n
local notation "E"=> Edge (Site n)
local notation "N"=> n.val
local notation "M"=> Moment Q
variable (x:Edge (Site n)) (u v:G.Color) (hG:G.Simple)(h:Ribbon Q)(hQ:Weigh Q Z) (hu:‖u‖=1)(hv:‖v‖=1) (e:G.Color) (he:‖e‖=1)
local notation "W"=> tumbler n Z
local notation "K"=>cost Q e Z
include h hQ hu hv hG he
lemma budgets (i j k:Axis) : |M x i u v [j,k]|≤ 2*cost Q e Z:=by
    have hp:= fundT x u v hQ hu hv; have hP : 100*W ≤ K:=by unfold cost; exact le_add_of_nonneg_left (abs_nonneg _)
    have ht(a):= mirrors x u v h hQ hu hv i j k a
    have hM : (∃ a:Axis,(if a=x.2 then (-1:ℝ) else 1)*(if a=i then -1 else 1)*((if a=j then -1 else 1)*(if a=k then -1 else 1))= -1)→|M x i u v [j,k]|≤ 2*K:=by
        rintro ⟨a,hA⟩; refine (ht a ?_).trans (by linarith only [hP,hp]); simpa only [sign,Signed.mirror,decide_eq_true_eq] using hA -- a=x or x=a
    by_cases hi:x.2=i
    · by_cases hj:j=k
      · subst i; subst k; by_cases hk:j=x.2
        · subst j; apply (hueQuad x u v h hQ hu hv x.2).trans; linarith only [hP,hp]
        exact (fares x u v hG h hQ hu hv e he hk).trans (by linarith only [hP,hp])
      apply hM; refine ⟨j,?_⟩; by_cases hx: j=i<;> simp_all
    -- off. Inspection.TestSwap.Leb
    have hz:|M x i u v [x.2,i]|≤ 2*K:=by
        let w:=M x i u v [x.2,i]; have hh :|M x x.2 u v [i,i]+2*w|≤80*W:=hueShift x u v h hQ hu hv _ i hi
        obtain ⟨h₀,h₁⟩:= abs_le.mp hh
        obtain ⟨h₂,h₃⟩:= abs_le.mp (fares x u v hG h hQ hu hv e he (Ne.symm hi)); apply abs_le.mpr; change -(2*K) ≤ w ∧ _; constructor<;>linarith only [h₁,h₀,h₂,h₃,hp,hP]
    by_cases hj:x.2=j
    · subst j; by_cases hk:i=k; subst k; exact hz
      exact hM ⟨i, by simp [hi,Ne.symm hi,hk]⟩
    by_cases hj': x.2=k
    · subst k; by_cases hk:i=j
      · subst j; rw [show M x i u v [i,x.2]= M x i u v [x.2,i] from ?_]; exact hz
        unfold Moment; apply Finset.sum_congr rfl; intro i _; simp only [mold,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil]; ring
      exact hM ⟨i, by simp [hk,hi,Ne.symm hi]⟩
    exact hM ⟨x.2, by simp [hi,hj,hj']⟩
-- Raw lift-centered coordinate.Cost for Taylor orders.
noncomputable def raw (Q:FaceRail n G)(x:E)(i:Axis)(u v:G.Color)(L:List Axis):= ∑ j:Site n, cell Q x (j,i) u v*(L.map (coord x.1 j)).prod
lemma bars (i:Axis)(L:List Axis)(ht:L.length≤2): |raw Q x i u v L| ≤32*cost Q e Z:=by
    obtain ⟨a,b⟩:= x; let p:= (a,b); have hv':= fundT p u v hQ hu hv; have hP :100*W ≤ K:= le_add_of_nonneg_left (abs_nonneg _)
    let g(i':Axis):=halfE b i' -halfE i i'; have hi (x:S₀)(l:Axis): coord a x l=middle p (x,i) l+g l:=by unfold middle zone p g; abel
    have hh(l): |g l|≤1:=by unfold g halfE; split_ifs <;> norm_num
    cases L with
    | nil=> apply (homeR p u v h hQ hu hv i).trans; linarith only [hv',hP]
    | cons j L=>
       let F:= M p i u v; have H₀: |F []| ≤ 16*W:=homeR p u v h hQ hu hv i; have H(l: Axis) : |F [l]| ≤ 17*W:= tick1 p u v h hQ hu hv i l

       have hx(l): |g l * F []|≤ 16*W:=by rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) (hh _)).trans H₀
       cases L with
       | nil=>
          rw [show raw Q (a,b) i u v [j]=F [j]+g j*F [] from ?_]; swap; · unfold F Moment raw; rw [Finset.mul_sum,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun x _=>?_); simp [mold,hi,p]; ring
          apply (abs_add_le ..).trans ((add_le_add (H _) (hx _)).trans ?_); linarith only [hv',hP]
       | cons k L=>
          have hh':L=[]:=by simpa using ht
          subst L
          rw [show raw Q (a,b) i u v [j,k]=F [j,k]+g k*F [j]+g j*F [k]+g j*(g k * F []) from ?_]; swap
          · unfold F Moment raw; simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun x _=>?_); simp only [List.map_cons,mold,List.map_nil,List.prod_cons,List.prod_nil]; rw [show coord (a,b).1 x j=_ from hi x j,show coord (a,b).1 x k=_ from hi x k]; unfold p; ring -- wrong lhs coord (a,b).fst
          have hs(t:Axis)(r:ℝ):|g t*r| ≤ |r|:=by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (hh t)
          refine (abs_add_le ..).trans ((add_le_add ((abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans (add_le_add (budgets p u v hG h hQ hu hv e he i j k) ((hs ..).trans (H _)))) ((hs ..).trans (H _)))) ((hs ..).trans (hx _))).trans ?_); linarith only [hv',hP]
end YM.MSbar.Midpoint

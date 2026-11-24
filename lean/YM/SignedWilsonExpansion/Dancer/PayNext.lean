import YM.SignedWilsonExpansion.Dancer.CashDesk
/-!
# Absolute cash on projection.Frame. Nominal ξ-cost needed for peer publicity.V.
-/
set_option autoImplicit false
set_option maxHeartbeats 440000
noncomputable section
namespace YM.SignedWilsonExpansion.Dancer.SeatsW
open XSpace XSpace.Structure1 Normalize Future Gauge Filter Function Matrix
open Asymptotics Maxwell Maxwell.Free Maxwell.Wick
open scoped BigOperators Topology Classical
variable {G:Gauge}{b d h t w n:ℕ}{ι σ E F K X:Type*}{l:Filter ι}{S:ι→ℝ}
section paysL
variable [NontriviallyNormedField K] {Φ:σ→Type*} [∀ i,AddCommGroup (Φ i)] [∀ i,Module K (Φ i)] [∀ i, FiniteDimensional K (Φ i)][Fintype σ]
private lemma themeO (T:MultilinearMap K Φ K)(y:∀ i,Φ i) {u:σ→ Type*}[∀ i,Fintype (u i)] (B:∀ i,Module.Basis (u i) K (Φ i)) : T y=∑ z:(∀ i,u i),(∏ i,(B i).coord (z i) (y i))*T (fun i=>B i (z i)):=by
    have he:= T.map_sum (fun i j=> (B i).repr (y i) j • B i j); simp_rw [Module.Basis.sum_repr] at he; nth_rw 1 [he]; exact Finset.sum_congr rfl fun i _=> T.map_smul_univ _ _
private lemma buysProdO (s:Finset σ)(X:ι→σ→ K)(w:∀ i∈s,(fun j=> X j i)=O[l] (1:ι→ℝ)): (fun j=>∏ i∈s,X j i)=O[l] (1:ι→ℝ):=by
    induction s using Finset.induction_on with
    | empty=> simp only [Finset.prod_empty]; exact isBigO_const_const _ one_ne_zero _
    | @insert i s hi ih=> simp_rw [Finset.prod_insert hi]; simpa only [Pi.one_apply,one_mul] using! ( w _ (Finset.mem_insert_self ..) ).mul (ih fun i t=> w i (Finset.mem_insert_of_mem t))
private lemma buysSubprod (s:Finset σ)(X Y:ι→σ→ K)(w:∀ i∈s,(fun j=> X j i)=O[l] (1:ι→ℝ))(p:∀ i∈s,(fun j=> Y j i)=O[l] (1:ι→ℝ))(o:∀ i∈s,(fun j=> X j i-Y j i)=O[l] S):
    (fun j=>(∏ i∈s,X j i)-∏ i∈s,Y j i)=O[l] S:=by
    induction s using Finset.induction_on with
    | empty=> simp only [Finset.prod_empty,sub_self]; exact isBigO_zero ..
    | @insert i s hi ih=>
       simp_rw [Finset.prod_insert hi]; let x(i):= ∏ j∈s,X i j; let y(i):=∏ j∈s,Y i j; let τ(j):= Y j i; let u(j):=X j i; have hx:(fun j=> x j-y j)=O[l] S:= ih (fun i h=> w _ (Finset.mem_insert_of_mem h)) (fun i h=> p _ (Finset.mem_insert_of_mem h)) (fun i h=> o _ (Finset.mem_insert_of_mem h)); have hK:= (w i (Finset.mem_insert_self ..)).mul hx; have hv: (fun j=> (u j-τ j)*y j)=O[l] S:=by simpa only [Pi.one_apply,mul_one] using! ( o i (Finset.mem_insert_self ..) ).mul (buysProdO s Y (fun i h=> p i (Finset.mem_insert_of_mem h)))
       refine ((IsBigO.add (hK.congr_right (g₂:=S) (fun k=>one_mul _)) hv).congr_left (fun j=>?_)); change u j* (x j-y j)+(u j-τ j)*y j=_*_ - τ j*y j; change _ = u j*x j-τ j*y j; ring
variable {Q:ι→ MultilinearMap K Φ K}{v p:ι→∀ i,Φ i}
lemma matNext (H:∀ x,(fun i=> Q i x)=O[l] (1:ι→ℝ))(V:∀ i:σ,Salary K l 1 (fun j=>v j i)) (P:∀ i:σ,Salary K l 1 (fun j=>p j i))(t:∀ i:σ,Salary K l S (fun j=> p j i-v j i)): (fun i=>Q i (p i)-Q i (v i))=O[l] S:=by
    let B(i):=Module.finBasis K (Φ i); conv=> arg 2; ext i; rw [ themeO (Q i) (p i) B, themeO (Q i) (v i) B,← Finset.sum_sub_distrib]; -- check conv arguments
    simp_rw [←sub_mul]; refine IsBigO.sum fun z _=>?_ ; exact ((buysSubprod _ _ _ (fun i _=> P i ((B i).coord (z i))) (fun i _=> V i ((B i).coord (z i))) (fun i _=> (t i ((B i).coord (z i))).congr_left fun i'=> (map_sub ..) )).mul (H _)).congr_right (fun j=>mul_one _)
end paysL

end YM.SignedWilsonExpansion.Dancer.SeatsW

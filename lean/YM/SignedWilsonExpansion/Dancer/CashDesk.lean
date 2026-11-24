import YM.SignedWilsonExpansion.Dancer.Lights
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
section tools
variable [NontriviallyNormedField K] [AddCommGroup E][Module K E] [FiniteDimensional K E]
variable {p q r:ι→ E}{F':σ→Module.Dual K E}(Y:Submodule K E)
def spillP (Y:Submodule K E) := ((Submodule.exists_isCompl Y).choose).projection Y ((Submodule.exists_isCompl Y).choose_spec.symm)
lemma pours {P:ι→ E}(H:∀ i,(fun j=> F' i (P j))=o[l] S) (v:∀ t:E,t∈Y ↔ ∀ i, F' i t=0): Discount K l S (spillP Y ∘ P) := by
   let V:=(Submodule.exists_isCompl Y).choose; let p:IsCompl V Y:= (Submodule.exists_isCompl Y).choose_spec.symm; let q(i):V:= ⟨spillP Y (P i),Submodule.projection_apply_mem p (P i) ⟩; intro x
   obtain ⟨A,f,h⟩:= bought (fun i=> (F' i).comp V.subtype) fun j h=> show _ from Subtype.ext (show j.val=(0:E) from Submodule.disjoint_def.mp p.disjoint j.val j.property ((v j).2 h) )
   have he(i): ( V.subtype (q i))=spillP Y (P i):=rfl; change (fun i=> x ( (spillP Y) (P i) ))=o[l] S; simp_rw [← he]; conv=> arg 2; ext i; rw [h (q i)] -- IsLittleO notation arg?
   simp_rw [map_sum,map_smul]; apply IsLittleO.sum; intro i hi; simp_rw [LinearMap.comp_apply, he]; refine (( H i.val ).const_mul_left (x (V.subtype (f i)))).congr_left fun j=> ?_; -- factor order
   have hx:= (v (P j-spillP Y (P j))).1 (Submodule.sub_projection_mem p (P j)) i.val; rw [map_sub] at hx; rw [sub_eq_zero] at hx; nth_rw 1 [hx]; exact mul_comm .. 
lemma aboveCeiling (h:Discount K l S p)(v:Discount K l S q): Discount K l S (fun i=> p i+q i):= fun T=> by simp_rw [map_add]; exact (h T).add (v T)
lemma belowCeiling (h:Discount K l S p)(v:Discount K l S q): Discount K l S (fun i=> p i-q i):= fun T=> by simp_rw [map_sub]; exact (h T).sub (v T)
lemma sameSalary {T:ι→ℝ}(h:Discount K l S p)(v:p=ᶠ[l]q)(t:S=ᶠ[l]T): Discount K l T q:=fun L=> (h L).congr' (v.fun_comp L) t
lemma coasts {Q:ι→K}{B:ι→ℝ}(h:Q=O[l] B)(v:Discount K l S p): Discount K l (fun i=>B i*S i) (fun i=> Q i • p i):=fun T=> by simp_rw[map_smul]; exact h.mul_isLittleO (v T)
-- real<br> angular repair needs real dual; from complex above
section tower
variable [Module ℂ E][Module ℝ E][IsScalarTower ℝ ℂ E][FiniteDimensional ℂ E]
def lambdaR (x:E→ₗ[ℝ]ℝ)(a:E) : ℂ→ₗ[ℝ]ℝ:= x.comp ((LinearMap.smulRight (LinearMap.id : ℂ→ₗ[ℂ]ℂ) a).restrictScalars ℝ)
lemma castReal (h:Discount ℂ l S p): Discount ℝ l S p:=by
    let B:=Module.finBasis ℂ E; intro x; have hv(i): x (p i)=∑ j,lambdaR x (B j) (B.coord j (p i)):=by nth_rw 1[←B.sum_repr (p i)]; rw [map_sum]; rfl
    rw [funext hv]; refine IsLittleO.sum fun i u=> (?_); exact (LinearMap.toContinuousLinearMap (lambdaR x (B i)) |>.isBigO_id _).comp_tendsto ( Filter.tendsto_map ) |>.trans_isLittleO (h (B.coord i)) -- id maybe names
-- output real constraints
end tower
end tools
section ledger
variable [NontriviallyNormedField K] {Φ:σ→Type*} [∀ i,AddCommGroup (Φ i)] [∀ i,Module K (Φ i)] [∀ i, FiniteDimensional K (Φ i)][Fintype σ]
private lemma modelAt (T:MultilinearMap K Φ K)(y:∀ i,Φ i) {u:σ→ Type*}[∀ i,Fintype (u i)] (B:∀ i,Module.Basis (u i) K (Φ i)) : T y=∑ z:(∀ i,u i),(∏ i,(B i).coord (z i) (y i))*T (fun i=>B i (z i)):=by
    have he:= T.map_sum (fun i j=> (B i).repr (y i) j • B i j); simp_rw [Module.Basis.sum_repr] at he; nth_rw 1 [he]; exact Finset.sum_congr rfl fun i _=> T.map_smul_univ _ _
private lemma sold (s:Finset σ)(X:ι→σ→ K)(w:∀ i∈s,(fun j=> X j i)=O[l] (1:ι→ℝ)): (fun j=>∏ i∈s,X j i)=O[l] (1:ι→ℝ):=by
    induction s using Finset.induction_on with
    | empty=> simp only [Finset.prod_empty]; exact isBigO_const_const _ one_ne_zero _
    | @insert i s hi ih=> simp_rw [Finset.prod_insert hi]; simpa only [Pi.one_apply,one_mul] using! ( w _ (Finset.mem_insert_self ..) ).mul (ih fun i t=> w i (Finset.mem_insert_of_mem t))
private lemma buysDiff (s:Finset σ)(X Y:ι→σ→ K)(w:∀ i∈s,(fun j=> X j i)=O[l] (1:ι→ℝ))(p:∀ i∈s,(fun j=> Y j i)=O[l] (1:ι→ℝ))(o:∀ i∈s,(fun j=> X j i-Y j i)=o[l] S):
    (fun j=>(∏ i∈s,X j i)-∏ i∈s,Y j i)=o[l] S:=by
    induction s using Finset.induction_on with
    | empty=> simp only [Finset.prod_empty,sub_self]; exact isLittleO_zero ..
    | @insert i s hi ih=>
       simp_rw [Finset.prod_insert hi]; let x(i):= ∏ j∈s,X i j; let y(i):=∏ j∈s,Y i j; let τ(j):= Y j i; let u(j):=X j i; have hx:(fun j=> x j-y j)=o[l] S:= ih (fun i h=> w _ (Finset.mem_insert_of_mem h)) (fun i h=> p _ (Finset.mem_insert_of_mem h)) (fun i h=> o _ (Finset.mem_insert_of_mem h)); have hK:= (w i (Finset.mem_insert_self ..)).mul_isLittleO hx; have hv: (fun j=> (u j-τ j)*y j)=o[l] S:=by simpa only [Pi.one_apply,mul_one] using! ( o i (Finset.mem_insert_self ..) ).mul_isBigO (sold s Y (fun i h=> p i (Finset.mem_insert_of_mem h)))
       refine ((IsLittleO.add (hK.congr_right (g₂:=S) (fun k=>one_mul _)) hv).congr_left (fun j=>?_)); change u j* (x j-y j)+(u j-τ j)*y j=_*_ - τ j*y j; change _ = u j*x j-τ j*y j; ring
variable {Q:ι→ MultilinearMap K Φ K}{v p:ι→∀ i,Φ i}
lemma matIncome (H:∀ x,(fun i=> Q i x)=O[l] S)(V:∀ i:σ,Salary K l 1 (fun j=>v j i)): (fun i=>Q i (v i))=O[l] S:=by
    let B(i):=Module.finBasis K (Φ i); rw [funext (fun i=> modelAt (Q i) (v i) B)]; refine IsBigO.sum fun z _=> ?_; exact ((sold _ _ (fun j _=> V j ((B j).coord (z j)))).mul (H _)).congr_right (fun j=> one_mul _)
lemma matDiscount (H:∀ x,(fun i=> Q i x)=o[l] S)(V:∀ i:σ,Salary K l 1 (fun j=>v j i)): (fun i=>Q i (v i))=o[l] S:=by
    let B(i):=Module.finBasis K (Φ i); rw [funext (fun i=> modelAt (Q i) (v i) B)]; refine IsLittleO.sum fun z _=> ?_; exact ((sold _ _ (fun j _=> V j ((B j).coord (z j)))).mul_isLittleO (H _)).congr_right (fun j=> one_mul _)
lemma matPays (H:∀ x,(fun i=> Q i x)=O[l] (1:ι→ℝ))(V:∀ i:σ,Salary K l 1 (fun j=>v j i)) (P:∀ i:σ,Salary K l 1 (fun j=>p j i))(t:∀ i:σ,Discount K l S (fun j=> p j i-v j i)): (fun i=>Q i (p i)-Q i (v i))=o[l] S:=by
    let B(i):=Module.finBasis K (Φ i); conv=> arg 2; ext i; rw [ modelAt (Q i) (p i) B, modelAt (Q i) (v i) B,← Finset.sum_sub_distrib]; -- check conv arguments
    simp_rw [←sub_mul]; refine IsLittleO.sum fun z _=>?_ ; exact ((buysDiff _ _ _ (fun i _=> P i ((B i).coord (z i))) (fun i _=> V i ((B i).coord (z i))) (fun i _=> (t i ((B i).coord (z i))).congr_left fun i'=> (map_sub ..) )).mul_isBigO (H _)).congr_right (fun j=>mul_one _)
end ledger
end YM.SignedWilsonExpansion.Dancer.SeatsW

import YangMills.WilsonProof.NativeSupport.TerminalRatios
import YangMills.WilsonProof.NativeSupport.JointShadow
import Mathlib.Analysis.Complex.Liouville

/-! Cauchy's estimate for all signed response tags at one common complex
parameter, with the vacuum denominator of that same marked density. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.TerminalGas
open Finset Marker Packet JointShadow Metric
open scoped Classical BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
local notation "Π₀" => Poly (YM.Stock.census V)

def fugacity (direction : Finset V) (z : ℂ) (i : V) : ℂ := if i∈direction then z else 1
def evaluated (direction A : Finset V) (P : Π₀) (z : ℂ) : ℂ :=
  sliceZ A (diagonal (fugacity direction z) P)

theorem diagonal_pass (a : V → ℂ) (H : Π₀) :
    diagonal a (Poly.pass H)=Poly.pass (diagonal a H) := by
  rw [Poly.pass,map_sum,Poly.pass]
  have linear (z:ℂ) (P:Π₀) : diagonal a (z • P)=z • diagonal a P :=
    MarkerSubstitution.on_smul (letter a) z P
  simp_rw [linear,map_pow]

theorem all_parameters (direction A : Finset V) (P : Π₀) : Differentiable ℂ (evaluated direction A P) := by
  have each (i:V) : Differentiable ℂ (fun z : ℂ=>fugacity direction z i) := by
    by_cases h : i∈direction <;> simp [fugacity,h]
  unfold evaluated sliceZ
  simp_rw [on_part]
  fun_prop

theorem smaller (direction : Finset V) (H : Π₀) {z : ℂ} (hz : ‖z‖≤1) (S:Finset V) :
    ‖(diagonal (fugacity direction z) H).part (tag S)‖≤ ‖H.part (tag S)‖ := by
  rw [on_part,norm_mul,norm_prod]
  apply mul_le_of_le_one_left (norm_nonneg _)
  apply prod_le_one (fun _ _=>norm_nonneg _)
  intro i _
  by_cases h : i∈direction <;> simp [fugacity,h,hz]

theorem disk_quotient (H : Π₀) (quiet : H.part (tag ∅)=0)
    (hit : ∀ x : V, ∑ T ∈ (univ : Finset (Finset V)).filter (fun T=>x∈T),
      ‖H.part (tag T)‖*2^(T.card-1) ≤ 1/2) (direction thermal physical : Finset V)
    (sep : Disjoint thermal physical) {z : ℂ} (hz : ‖z‖≤1) :
    evaluated direction thermal (Poly.pass H) z ≠ 0 ∧
      ‖evaluated direction (thermal∪physical) (Poly.pass H) z / evaluated direction thermal (Poly.pass H) z‖ ≤ (3/2:ℝ)^physical.card := by
  let K:=diagonal (fugacity direction z) H
  have k0 : K.part (tag ∅)=0 := by simp [K,on_part,quiet]
  have paid (x:V) : ∑ T ∈ (univ : Finset (Finset V)).filter (fun T=>x∈T),
      ‖K.part (tag T)‖*2^(T.card-1) ≤ 1/2 :=
    (sum_le_sum (fun T _=>mul_le_mul_of_nonneg_right (smaller direction H hz T) (by positivity))).trans (hit x)
  simpa only [evaluated,diagonal_pass,K] using And.intro (denominator K k0 paid thermal).1 (add_physical K k0 paid thermal physical sep)

theorem direction_estimate (H : Π₀) (quiet : H.part (tag ∅)=0)
    (hit : ∀ x : V, ∑ T ∈ (univ : Finset (Finset V)).filter (fun T=>x∈T),
      ‖H.part (tag T)‖*2^(T.card-1) ≤ 1/2) (direction thermal physical : Finset V)
    (sep : Disjoint thermal physical) :
    let P := Poly.pass H
    ‖deriv (fun z : ℂ => evaluated direction (thermal∪physical) P z / evaluated direction thermal P z) 0‖ ≤
      (3/2:ℝ)^physical.card := by
  intro P
  let R (z:ℂ) := evaluated direction (thermal∪physical) P z / evaluated direction thermal P z
  have disk := @disk_quotient V _ _ H quiet hit direction thermal physical sep
  have analytic : DifferentiableOn ℂ R (closedBall 0 1) :=
    (all_parameters direction _ P).differentiableOn.div (all_parameters direction thermal P).differentiableOn
      fun z hz=>(disk (by simpa only [mem_closedBall,dist_zero_right] using hz)).1
  have bound := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ)<1)
    (analytic.diffContOnCl_ball (Set.Subset.rfl)) (fun z hz=>(disk (by simpa only [mem_sphere,dist_zero_right] using (le_of_eq hz))).2)
  simpa only [div_one] using bound

/-- Alternatingly open every physical label. This is the whole physical
product when response sources are evaluated on the original joint field. -/
def opened (direction thermal physical : Finset V) (P : Π₀) (z : ℂ) : ℂ :=
  ∑ S∈physical.powerset, (-1:ℂ)^(physical.card-S.card)*
    (evaluated direction (thermal∪S) P z/evaluated direction thermal P z)

omit [Fintype V] in
theorem product_extraction (physical : Finset V) (f : V → ℂ) :
    ∑ S∈physical.powerset, (-1:ℂ)^(physical.card-S.card)*(∏ i∈S,(1+f i)) = ∏ i∈physical,f i := by
  calc
    _ = ∑ S∈physical.powerset,(∏ i∈S,(1+f i))*(∏ _i∈physical\S,(-1:ℂ)) := by
      apply sum_congr rfl
      intro S hS
      rw [prod_const,card_sdiff_of_subset (mem_powerset.mp hS),mul_comm]
    _ = ∏ i∈physical,((1+f i)+(-1:ℂ)) := (prod_add _ _ _).symm
    _ = _ := prod_congr rfl fun i _=>by ring

theorem opened_estimate (H : Π₀) (quiet : H.part (tag ∅)=0)
    (hit : ∀ x : V, ∑ T ∈ (univ : Finset (Finset V)).filter (fun T=>x∈T),
      ‖H.part (tag T)‖*2^(T.card-1)≤1/2) (direction thermal physical : Finset V)
    (sep : Disjoint thermal physical) :
    ‖deriv (opened direction thermal physical (Poly.pass H)) 0‖ ≤ (5/2:ℝ)^physical.card := by
  let P:=Poly.pass H
  let Q (S:Finset V) (z:ℂ) := evaluated direction (thermal∪S) P z/evaluated direction thermal P z
  let c (S:Finset V) := (-1:ℂ)^(physical.card-S.card)
  have nonzero := (disk_quotient H quiet hit direction thermal physical sep (z:=0) (by norm_num)).1
  have analytic (S:Finset V) : DifferentiableAt ℂ (Q S) 0 :=
    (all_parameters direction _ P).differentiableAt.div (all_parameters direction _ P).differentiableAt nonzero
  have d : HasDerivAt (opened direction thermal physical P) (∑ S∈physical.powerset, c S*deriv (Q S) 0) 0 :=
    HasDerivAt.fun_sum fun S _ => (analytic S).hasDerivAt.const_mul (c S)
  rw [d.deriv]
  calc
    _ ≤ ∑ S∈physical.powerset, ‖c S*deriv (Q S) 0‖ := norm_sum_le _ _
    _ ≤ ∑ S∈physical.powerset, (3/2:ℝ)^S.card := by
      apply sum_le_sum
      intro S hS
      simp only [c,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
      exact direction_estimate H quiet hit direction thermal S (sep.mono_right (mem_powerset.mp hS))
    _ = _ := by
      have form := prod_one_add (f:=fun _ : V=>(3/2:ℝ)) physical
      simpa only [prod_const,show (1:ℝ)+3/2=5/2 by norm_num] using form.symm

end YM.Integration.InletSusceptibility.TerminalGas

import YM.FVA2.Gen.Recipe
/-! # Full radial J coordinates from an actual connection -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Set Filter Finset MeasureTheory Topology
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Maxwell Labels Precision Lattice RG
variable {G:Gauge}{A: Sky G}{J J': Labels.Jet G}{f:Mist G}{u:E4→G.El}{x:E4}{i j:Axis}
local notation "P"=> E4
local notation "C"=> G.Color
local notation "δ"=> par
variable (h:Fluid A)(hp:Silent A)(n:ℕ)
include h hp n
-- Silent choose. Partial projection identity for all slots.
private lemma ready : ∃ U:Labels.Taylor G n, ∀ (x:E4)(i:Axis), U.value i x=(( (n+1).factorial:ℝ )⁻¹) • iteratedDeriv (n+1) (fun t:ℝ=> A i (t • x)) 0:=by
    let U (i:Axis):= (( (n+1).factorial:ℝ )⁻¹) • iteratedFDeriv ℝ (n+1) (A i) 0; have ht : (↑(n+1:ℕ):WithTop ℕ∞) ≤ ∞:=WithTop.coe_le_coe.mpr le_top; have hv(i:Axis)(x:P): Tensor.diagonal ( U i ) x= (( (n+1).factorial:ℝ )⁻¹) • iteratedDeriv (n+1) (fun t:ℝ=> A i (t • x)) 0:= by -- specify
        unfold U Tensor.diagonal; rw [ _root_.smul_apply, ← line (( h i ).contDiffAt.of_le ht) x ]; simp
    refine ⟨⟨ U,fun i x p=>?_,fun x=>?_⟩,fun x i=> hv i x⟩
    · exact congrArg ( ( ( ( n+1 ).factorial:ℝ )⁻¹ ) • · ) ( perm_fee (( h i ).contDiffAt.of_le ht) x p )
    simp_rw [hv, smul_comm (x _ ) ((( n+1 ).factorial:ℝ)⁻¹), ← Finset.smul_sum]; have he: (fun t:ℝ=> ∑ i:Axis,x i • A i ( t • x )) = (fun t:ℝ=> (0:C)):= funext (ray_quiet h hp x);
    apply smul_eq_zero.mpr ( Or.inr ?_ ); have hr(i:Axis):ContDiff ℝ ∞ (fun t:ℝ=> A i (t • x)):= (h i).comp (f:=fun t:ℝ=> t • x) (contDiff_id.smul contDiff_const)
    have H:=congrArg (fun p:ℝ→ C=> iteratedDeriv (n+1) p 0) he; rw [ iteratedDeriv_fun_sum (f:=fun i:Axis=> fun t:ℝ=> x i • A i ( t • x )) (fun i _=> ContDiffAt.const_smul (x i) ( (hr i).contDiffAt.of_le ht ) ), iteratedDeriv_fun_const_zero ] at H; simp_rw [ iteratedDeriv_fun_const_smul_field ] at H; exact H
-- canonical formula & relation. ANY choice.
omit h hp n
def equation (A: Sky G)(i:Axis)(x:E4)(n:ℕ): C:= (( (n:ℝ)+2 )*( n.factorial:ℝ ))⁻¹ • ∑ j:Axis,x j • gleam A x j i n 0
def Radials (A:Sky G)(J:Labels.Jet G): Prop:= ∀ i (x:E4)(n:ℕ), (J n).value i x=equation A i x n
lemma knows (h:Fluid A)(hp:Silent A)(J':Labels.Jet G): (∀ k:ℕ,∀ i x, (J' k).value i x=(( (k+1).factorial:ℝ )⁻¹) • iteratedDeriv (k+1) (fun t:ℝ=> A i (t • x)) 0) ↔ Radials A J':= by
    constructor; · intro H i x n; rw [ H n i x,eq_Jrad h hp x i n ]; rfl
    intro H n i x; rw [ H i x n,eq_Jrad h hp x i n ]; rfl -- nesting
lemma keeps (h:Fluid A)(hu:Lived u)(h0:u 0=1): Radials (skyturn u A) J ↔ Radials A J:= by
    have he: equation (skyturn u A) = equation A:= by funext i x n; unfold equation; simp_rw [ gleam_f h hu _,fantasy,h0,G.adjoint_one ]
    unfold Radials; rw [he]
theorem radix_eq (hA:Radials A J)(hB: Radials A J'): J=J':= by funext n; apply Labels.Taylor.value_ext; funext i x; rw [hA i x n,hB i x n]
theorem origin (h:Fluid A): ∃ J:Labels.Jet G,Radials A J:=by
    obtain ⟨p,hp⟩:= meets_real ( cCircle h ); obtain ⟨v,hv,h0,hf,hm⟩:= still_τ hp h; choose Y hp using ready hf hm; exact ⟨Y,( keeps h hv h0 ).mp ( ( knows hf hm _ ).mp fun k i x=> hp _ _ _ ) ⟩ -- clashes P
end YM.FVA2.Gen

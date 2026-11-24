import YM.Integration.WilsonMeasuredPublicEntranceProfileRegistry

/-! Signed sums of the originally tested cells on one fixed smooth profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceJointBilled
open Function Filter Finset MeasureTheory Lattice Extraction
open WilsonAddressedPhysicalCells WilsonMeasuredPublicEntranceProfileRegistry
open scoped Classical BigOperators Topology
variable {k:ℕ}{I:Type}[Fintype I](φ:Test k)(a scale:ℝ)(side:Side)

theorem original (positive:0<a)(c:I→ℂ)(D:I→Sites side k→ℂ)(rate:I→ℝ)
    (paid:∀i,Billed φ a scale side (D i) (rate i)):
    Billed φ a scale side (fun t=>∑i,c i*D i t) (∑i,‖c i‖*rate i):=by
  let Z:=(∫x,‖φ x‖)
  let heard:=fun i=>φ.applyTo (fun x=>D i (atSite a scale side x))
  have eq:=WilsonSeparatedPrefixCellProfile.tested φ a scale side positive (fun t=>∑i,c i*D i t)
  refine ⟨eq,?_⟩
  have agree:φ.applyTo (fun x=>∑i,c i*D i (atSite a scale side x))=∑i,c i*heard i:=by
    rw [eq]
    simp_rw [heard,(paid _).1,Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun u _=>by ring
  rw [agree]
  calc
    ‖∑i,c i*heard i‖≤∑i,‖c i*heard i‖:=norm_sum_le _ _
    _ ≤ ∑i,Z*(‖c i‖*rate i):=Finset.sum_le_sum fun i _=>by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (paid i).2 (norm_nonneg _)).trans_eq (by dsimp only [Z];ring)
    _ = _ :=by rw [Finset.mul_sum]

theorem four (positive:0<a)(D:Bool→Bool→Sites side k→ℂ)(rate:ℝ)
    (paid:∀i j,Billed φ a scale side (D i j) rate):
    Billed φ a scale side (fun t=>D false false t-D false true t-D true false t+D true true t) (4*rate):=by
  let c:Bool×Bool→ℂ:=fun b=>if b.1=b.2 then 1 else -1
  have h:=original φ a scale side positive c (fun b=>D b.1 b.2) (fun _=>rate) (fun b=>paid b.1 b.2)
  have factors (t:Sites side k):(∑b:Bool×Bool,c b*D b.1 b.2 t)=D false false t-D false true t-D true false t+D true true t:=by
    simp [c,Fintype.sum_prod_type];ring
  have salary:(∑b:Bool×Bool,‖c b‖*rate)=4*rate:=by
    simp [c,Fintype.sum_prod_type];ring
  simpa only [factors,salary] using h

end YM.Integration.WilsonMeasuredPublicEntranceJointBilled
end

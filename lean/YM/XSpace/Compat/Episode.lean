import YM.XSpace.Compat.NativeCompletion
import YM.Further.FREE_COVARIANCE_KP.KP.Episode

/-! Additive compatibility closure from pinned Oct15 ancestry.
Current baseline definitions are reused; extracted declaration text is unchanged.
Prepared for independent checking; no successful build is claimed here. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP.Episode
open YM.Further.FreeCovariance.KP
open YM.XSpace.Compat.KP
open Filter Set Function Metric Complex MeasureTheory Lattice Bloch Laurent Exterior Matrix Precision Next.Free RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {α Ω η k : ℝ} {j : ℕ} {n : Side}

theorem per_cost (k:ℝ) (hk : 0<k) (j:ℕ) (hj : 4≤j) (A B:List Axis) (a b:PA) : ∃ C:ℝ,0<C ∧ ∀ (v:Train j) (n:Side) (x:Cover),1≤‖rcast x‖→
    ‖slot checkout B (slot checkin A (found k v n (plaquette a) (plaquette b))) x-↑(decree A B a b (rcast x))‖ ≤ C*((‖rcast x‖^(5+A.length+B.length))⁻¹+(1+‖rcast x‖)/(n.val:ℝ)) := by
  obtain ⟨a',Ω,v',ha,hv,H⟩:=paid k hk hj
  obtain ⟨C,hC,K⟩:=k_per A B a b ha hv Ω
  refine ⟨C,hC,fun v n x hx=>?_⟩
  obtain ⟨f,hf⟩:=H v
  rw [← bridge k hk hj ha hv _ f hf]
  exact K f n x hx

end YM.Further.FreeCovariance.KP.Episode
end

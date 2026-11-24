import YM.Integration.WilsonSeparatedOriginalSlabWatchMean
import YM.Integration.WilsonMixedTaggedScattering

/-! One compact spatial room and one external derivative order for every admitted centre displacement. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchRoom
open Function Set Filter MeasureTheory Analysis Wilson Lattice RG Source Extra.Histories Extraction Spec OPE
open RG05Readout RG05Readout.Native RG05Readout.Pulse WilsonSeparatedOriginalSlabWatchMean
open scoped Topology BigOperators ContDiff Classical
variable {I:Type}[Fintype I]

def arrived (p:(Cloud I×E4)×ℝ):Cloud I:=fun i=>p.1.1 i+p.2 • p.1.2

def space (A:Set (Cloud I)):Set (Cloud I):=arrived '' ((A ×ˢ Native.box) ×ˢ Icc (0:ℝ) 1)

omit [Fintype I] in
theorem compact {A:Set (Cloud I)}(hA:IsCompact A):IsCompact (space A):=by
  apply ((hA.prod Pert.Cellular.cells_compact).prod isCompact_Icc).image;apply continuous_pi;intro i;change Continuous (fun p:(Cloud I×E4)×ℝ=>p.1.1 i+p.2 • p.1.2);fun_prop

theorem original (θ:ℝ)(ht:θ∈Icc (0:ℝ) 1)(Ψ:Wave I)(g:Body)(A:Set (Cloud I))(closed:IsCompact A)(inside:tsupport Ψ.val⊆A):
    tsupport (wave θ Ψ g).val⊆space A:=by
  apply closure_minimal _ (compact closed).isClosed;intro x live;by_contra outside
  have null (z:E4)(hz:z∈Native.box):leaf θ Ψ g (x,z)=0:=by
    have absent:x+delta θ z∉A:=by
      intro inside;apply outside;refine ⟨((x+delta θ z,z),θ),⟨⟨inside,hz⟩,ht⟩,?_⟩
      funext i;change (x i+ -(θ • z))+θ • z=x i;abel
    unfold leaf;rw [image_eq_zero_of_notMem_tsupport (fun h=>absent (inside h)),mul_zero]
  apply live;change (∫z in Native.box,leaf θ Ψ g (x,z))=0
  calc _=∫_z:E4 in Native.box,(0:ℂ):=setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet null
       _=0:=by simp

omit [Fintype I] in
theorem housing (A:Set (Cloud I)){η M:ℝ}(far:∀y∈A,∀i j:I,i≠j→η≤‖y i-y j‖)(bounded:∀y∈A,∀i,‖y i‖≤M):
    ∀y∈space A,(∀i j:I,i≠j→η≤‖y i-y j‖) ∧ ∀i,‖y i‖≤M+1:=by
  rintro _ ⟨⟨⟨y,z⟩,θ⟩,⟨⟨hy,hz⟩,ht⟩,rfl⟩;constructor
  · intro i j ij;change η≤‖(y i+θ • z)-(y j+θ • z)‖;rw [add_sub_add_right_eq_sub];exact far y hy i j ij
  · intro i;change ‖y i+θ • z‖≤_;apply (norm_add_le ..).trans;apply add_le_add (bounded y hy i);rw [norm_smul,Real.norm_of_nonneg ht.1];exact mul_le_one₀ ht.2 (norm_nonneg _) (Pert.Cellular.cells_bd hz)

theorem financed (s:I→ℕ)(Ψ:Wave I)(hs:HasCompactSupport Ψ.val):
    ∃X:ℝ,0<X ∧ ∀θ:ℝ,∀g:Body,Nuclear.Tall (wave θ Ψ g) (WilsonMixedTaggedScattering.order s+1) 1 (charge g*X):=by
  obtain ⟨X,positive,paid⟩:=WilsonMixedTaggedTestControl.derivatives Ψ hs (WilsonMixedTaggedScattering.order s+1)
  exact ⟨X,positive,fun θ g=>tall θ Ψ g paid⟩

end YM.Integration.WilsonSeparatedOriginalSlabWatchRoom

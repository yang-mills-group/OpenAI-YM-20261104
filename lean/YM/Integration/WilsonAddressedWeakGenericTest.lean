import YM.Integration.WilsonAddressedWeakStationGram

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakGenericTest
open Function Filter Set Metric MeasureTheory Extraction Extra.FD
open scoped BigOperators Classical Topology
theorem original :
    ∃ (w:E4) (φ:Test 2),(0:E4)≠w ∧ tsupport φ⊆generic 2 ∧ tsupport φ∈𝓝 (couple 0 w):=by
  obtain ⟨w,away,strict⟩:=WilsonAddressedWeakStationGram.direction
  let x₀:=couple (0:E4) w
  have legal:x₀∈conf 2:=couple_ok away
  let row (_ _:Fin 1) (_:Points 2):ℂ:=1
  have matrix:Matrix.of (fun i j=>row i j x₀)=1:=by ext i j;rw [Subsingleton.elim j i];simp [row]
  obtain ⟨φ,stencil,_,positive,_,_⟩:=MSSeparatedTestGram.matrix_test row
    (fun _ _ _ _=>continuousAt_const) legal (matrix.symm ▸ isUnit_one) (generic 2) ((genericOpen 2).mem_nhds strict)
  refine ⟨w,φ,away,stencil,?_⟩
  have nonzero:φ x₀≠0:=by intro h;rw [h,Complex.zero_re] at positive;exact lt_irrefl _ positive
  have living:{x:Points 2 | φ x≠0}∈𝓝 x₀:=φ.contDiff.continuous.continuousAt (isClosed_singleton.isOpen_compl.mem_nhds nonzero)
  exact mem_of_superset living (subset_tsupport φ)
end YM.Integration.WilsonAddressedWeakGenericTest
end

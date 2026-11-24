import YM.Integration.WilsonThermometerUnitFilingFlatGerms

/-! The true unmasked ordinary polynomial on the flat filing field is the pupil's own zero-direction graded bank. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFlatPupil
open Finset Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise
open Exterior Stationary Comparison.RG02 AllOrder AllOrder.Floe AllOrder.Floe.Step
open WilsonThermometerCenteredAlgebra
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {V X ι:Type} [DecidableEq V] {G:Gauge} {n:Side} {P:Passport n V} {J:Census V}
variable (M:ι → Row P J G X) (w:V → ℝ) (grades:V → ℕ) {σ c:ℝ} {p count shelf:ℕ}
  (estate:Scene.Armada M w grades σ c p count shelf) (hs:0<σ) (x:X) (layout:Layout G) (tape:Finset Age)
  (B:BudgetPoint) (g:ℝ)
local notation "student" => Air.craft M (fun i=>(M i).paint x) grades layout tape
local notation "height" j:max => Air.discharge (student) j (arm G n 1 (0:Link G n))

private theorem sumGrades {Y:Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [Module ℂ Y] [ContinuousSMul ℂ Y] (E:Finset ℕ) (f:ℕ → ι → Y) (s:ℕ → Y)
    (h:∀j∈E,HasSum (f j) (s j)):
    HasSum (fun i=> ∑j∈E,(g:ℂ)^j • f j i) (∑j∈E,(g:ℂ)^j • s j):=by
  induction E using Finset.induction_on with
  | empty=>simp
  | @insert j D outside ih=>
    simpa only [sum_insert outside] using
      ((h j (mem_insert_self ..)).const_smul ((g:ℂ)^j)).add (ih (fun k hk=>h k (mem_insert_of_mem hk)))

include estate hs in
theorem log_value :
    WilsonRootedKioskOccupiedSlip.bare (rendered M B g) x (1:Config G n)=
      ∑j∈range (p+1),(g:ℂ)^j • height j:=by
  classical
  letI : Fintype V := Fintype.ofInjective J.fire (fun a b h => (J.fire_inj a b).mp h)
  let ink (i:ι):=(M i).paint x
  let roster:=Air.license M ink grades w estate hs (fun i=>estate.honor i x)
  let f (j:ℕ) (i:ι):=Poly.send (M i).mode (ink i*Complex.ofReal ((M i).markReceipt j (0:Link G n)))
  have quoted (j:ℕ) (_:j∈range (p+1)):HasSum (f j) (height j):=
    Air.compared M ink grades roster layout tape (0:Link G n) j
  have combined:=sumGrades (ι:=ι) g (range (p+1)) f (fun j=>height j) quoted
  apply (combined.congr_fun ?_).tsum_eq
  intro i
  have same:=WilsonThermometerUnitFilingFlatGerms.realization (M i) g x (estate.purchases.usable i).1
  funext s
  symm
  change (∑j∈range (p+1),(g:ℂ)^j • f j i).part s=(Poly.send (M i).mode ((M i).nominal g x (1:Config G n))).part s
  simp only [Poly.part_sum,Poly.part_smul,f,Poly.part_send]
  by_cases named:s=(M i).mode
  · simp only [if_pos named]
    exact same.symm
  · simp [named]

include estate hs in
theorem original [Fintype V] (Q:Poly J) (face:J.Mode) :
    (Poly.pass (WilsonRootedKioskOccupiedSlip.bare (rendered M B g) x (1:Config G n))*Q).part face=
      (Poly.pass (∑j∈range (p+1),(g:ℂ)^j • height j)*Q).part face:=by
  rw [log_value M w grades estate hs x layout tape B]

end YM.Integration.WilsonThermometerUnitFilingFlatPupil

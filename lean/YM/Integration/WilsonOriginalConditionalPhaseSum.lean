import YM.Integration.WilsonThermometerOccupiedLinear

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalConditionalPhaseSum
open Function Finset MeasureTheory Lattice Wilson RG
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
open private summed from YM.Integration.WilsonThermometerOccupiedLinear
variable {G:Gauge} (R:Run G) {V:Type*} {N per f u:ℕ}
local notation "P" => R.family.path.rep N per f
local notation "X" j:max => Config G (R.family.side j per)

/-- The native posterior of a finite signed reading on one original numerator. -/
theorem original (roster:Finset V)(phase:V→ℂ)(field:V→X f→ℂ)
    (paid:∀v,Integrable (fun U=>(P).eval U • field v U) (prior G _)) (uf:u≤f) (W:X u):
    Integrable (fun U=>(P).eval U • ∑v∈roster,phase v*field v U) (prior G _) ∧
    actualTransport R.family (N:=N) (fun U=>∑v∈roster,phase v*field v U) uf W=
      ∑v∈roster,phase v*actualTransport R.family (N:=N) (field v) uf W:=by
  let row:=fun v (U:X f)=>(P).eval U • field v U
  have collect:(fun U=>(P).eval U • ∑v∈roster,phase v*field v U)=∑v∈roster,phase v • row v:=by
    funext U
    simp only [Finset.smul_sum,Finset.sum_apply,Pi.smul_apply,Complex.real_smul,smul_eq_mul,row]
    apply Finset.sum_congr rfl
    intro v _
    ring
  obtain ⟨total,linear⟩:=summed R (N:=N) roster phase row paid uf
  refine ⟨collect ▸ total,?_⟩
  unfold actualTransport
  rw [collect,linear]
  simp only [Finset.sum_apply,Pi.smul_apply,Finset.smul_sum,Complex.real_smul,smul_eq_mul,Complex.ofReal_inv,row]
  apply Finset.sum_congr rfl
  intro v _
  ring

end YM.Integration.WilsonOriginalConditionalPhaseSum
end

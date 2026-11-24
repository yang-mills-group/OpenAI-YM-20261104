import YM.Integration.WilsonThermometerUnitFilingCoarse
import YM.Integration.WilsonThermometerCompulsoryReturn

/-! The genuine dated posterior agrees with the original flat scalar
after the positive Wilson vacuum has been put back exactly once. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPosterior
open Lattice RG Wilson MergeProof.Accent PhysicalNext.Repeat.Legato
open Extra.Multi Extra.Histories Labels Source
open WilsonThermometerUnitFilingCoarse (reading)
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {N p b:ℕ}
local notation "C" => R.family
local notation "H" => R.family.path
local notation "W" => R.family.path.rep N p b

theorem weighted (f:Config G ((C).side b p)→ℂ) {j:ℕ} (jb:j≤b) :
    reading R (N:=N) (fun U=>((W).eval U:ℂ)*f U) j jb =
      actualTransport C (N:=N) f jb 1 := by
  simp only [reading,actualTransport,Complex.real_smul,Complex.ofReal_inv]

theorem original (bN:b≤N) (Ψ:Rep G ((C).side b p)) (quiet:Ψ.eval=(W).eval)
    (actual filed account:Config G ((C).side b p)→ℂ) (cap:ℝ)
    (paid:WilsonThermometerCompulsoryReturn.Heard R (top:=N)
      (fun U=>actual U/(Ψ.eval U:ℂ)-filed U-account U/(Ψ.eval U:ℂ)) cap) :
    let debt:=fun U=>actual U-((W).eval U:ℂ)*filed U-account U
    (∀ j (jb:j≤b),‖reading R (N:=N) debt j jb‖ ≤ cap) ∧
    ∀u v (ub:u≤b) (vb:v≤b),‖reading R (N:=N) debt u ub-reading R (N:=N) debt v vb‖ ≤ 2*cap := by
  intro debt
  let f:=fun U=>actual U/(Ψ.eval U:ℂ)-filed U-account U/(Ψ.eval U:ℂ)
  have booked:debt=fun U=>((W).eval U:ℂ)*f U:=by
    funext U
    have pos:((W).eval U:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson bN U).ne'
    dsimp only [debt,f]
    rw [congrFun quiet U]
    field_simp [pos]
  have hear (j:ℕ) (jb:j≤b):‖reading R (N:=N) debt j jb‖≤cap := by
    rw [booked,weighted R f jb]
    exact (paid j jb).1 1
  refine ⟨hear,?_⟩
  intro u v ub vb
  exact (norm_sub_le ..).trans (by linarith only [hear u ub,hear v vb])

end YM.Integration.WilsonThermometerUnitFilingPosterior

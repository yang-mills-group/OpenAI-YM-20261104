import YM.Integration.ActualNormalizedPush
import YM.Integration.WilsonOlderSignedOneMarkAdmitted

/-! Linear combination of actual occupied push readings is a single true
conditional hearing. The full unmarked Wilson density occurs once in its
numerator and denominator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphConditionalSum
open Lattice Wilson RG MeasureTheory Tree Marker LocalComparison
open scoped Classical BigOperators

variable {G:Gauge}(C:Family G){N per i:ℕ}(law:C.Makes)(hi:i<N)
variable {S:Type}[Fintype S][DecidableEq S]{K:Census S}{ι:Type}[Fintype ι]
local notation "fine" => C.path.rep N per (i+1)
local notation "coarse" => C.path.rep N per i
local notation "phase" => C.path.β N per (i+1)
local notation "step" => C.path.levels.clock.op i per
local notation "Fine" => C.side (i+1) per
local notation "Coarse" => C.side i per

include law hi in
theorem marked (name:K.Mode)(h:ι → ℂ)(P:ι → Config G Fine → Poly K)
    (live:∀z,Integrable (fun U=>((fine).eval U:ℂ) • P z U) (prior G Fine))
    (W:Config G Coarse):
    ((coarse).eval W:ℂ)*actualAverage C (N:=N) (fun U=>∑z,h z*(P z U).part name) W =
      ∑z,h z*(LocalComparison.actualPush C N per i (fun U=>((fine).eval U:ℂ) • P z U) W).part name:=by
  let slice(z:ι)(U:Config G Fine):=(step).density phase U W • (((fine).eval U:ℂ) • P z U)
  have integrable(z:ι):Integrable (slice z) (prior G Fine):=StepData.push_slice
    (C.path.levels.transition_mass i per phase) W _ (live z)
  let L:=(Poly.get name).restrictScalars ℝ
  have coordinates(z:ι):Integrable (fun U=>(slice z U).part name) (prior G Fine):=L.integrable_comp (integrable z)
  have readout(z:ι):(LocalComparison.actualPush C N per i (fun U=>((fine).eval U:ℂ) • P z U) W).part name =
      ∫ U,(slice z U).part name ∂prior G Fine:=(L.integral_comp_comm (integrable z)).symm
  have read(z:ι)(U:Config G Fine):(slice z U).part name =
      ((step).density phase U W:ℂ)*(((fine).eval U:ℂ)*(P z U).part name):=by
    change L ((step).density phase U W • (((fine).eval U:ℂ) • P z U))=_
    rw [L.map_smul,Complex.real_smul]
    rfl
  have nonzero:(((coarse).eval W:ℝ):ℂ)≠0:=by
    exact_mod_cast (Multi.AxisShift.chosen_positive law.wilson hi.le W).ne'
  rw [actualAverage_push,Complex.real_smul,Complex.ofReal_inv,←mul_assoc,mul_inv_cancel₀ nonzero,one_mul]
  change (∫ U,(step).density phase U W • ((fine).eval U • ∑z,h z*(P z U).part name) ∂prior G Fine)=_
  calc
    _ = ∫ U,∑z,h z*(slice z U).part name ∂prior G Fine:=by
      apply integral_congr_ae
      filter_upwards [] with U
      simp only [read,Complex.real_smul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = ∑z,h z*(∫ U,(slice z U).part name ∂prior G Fine):=by
      rw [integral_finsetSum Finset.univ (fun z _=>(coordinates z).const_mul (h z))]
      simp_rw [integral_const_mul]
    _ = _:=by simp_rw [←readout]

end YM.Integration.WilsonOlderFreshGraphConditionalSum
end

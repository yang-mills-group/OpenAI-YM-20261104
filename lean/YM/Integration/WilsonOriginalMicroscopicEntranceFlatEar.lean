import YM.Integration.WilsonMeasuredPublicEntranceSignedEar

/-! Read the two actual public ordinary products on the earlier normalized Wilson measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceFlatEar
open Finset Lattice RG Wilson QuadraticLocal Source Labels PhysicalNext PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingCoarse WilsonCoeffUV.Embroider
open WilsonMeasuredPublicEntranceOrder WilsonMeasuredPublicEntranceSignedEar
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G){N per f u:ℕ}(uf:u≤f)
variable {I:Type} (s:Finset I)
local notation "P" => R.family.path.rep N per f
local notation "X" => Config G (R.family.side f per)

theorem product (a:I→X→ℂ):
    reading R (N:=N) (weighted (N:=N) R (factors a s.toList)) u uf =
      actualTransport R.family (N:=N) (fun U=>∏i∈s,a i U) uf 1:=by
  have same : weighted (N:=N) R (factors a s.toList) = fun U=>(P).eval U • (∏i∈s,a i U):=by
    funext U
    simp only [weighted,factors,prod_map_toList,Complex.real_smul]
  rw [same]
  unfold reading actualTransport
  rw [Complex.real_smul,Complex.ofReal_inv]

theorem original (a b:I→X→ℂ){fee:ℝ}
    (paid:‖reading R (N:=N) (weighted (N:=N) R (factors a s.toList)) u uf -
      reading R (N:=N) (weighted (N:=N) R (factors b s.toList)) u uf‖≤fee):
    ‖actualTransport R.family (N:=N) (fun U=>∏i∈s,a i U) uf 1-
      actualTransport R.family (N:=N) (fun U=>∏i∈s,b i U) uf 1‖≤fee:=by
  rw [product R uf s a,product R uf s b] at paid
  exact paid

end YM.Integration.WilsonOriginalMicroscopicEntranceFlatEar
end

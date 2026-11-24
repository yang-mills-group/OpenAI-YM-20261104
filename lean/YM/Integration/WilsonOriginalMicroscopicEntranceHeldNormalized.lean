import YM.Integration.WilsonOriginalMicroscopicEntranceFlatEar
import YM.Integration.WilsonSeparatedPrefixCanonicalClearConvolution

/-! Normalize both honest whole product shares at their one specified earlier group field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldNormalized
open Finset Lattice RG Wilson QuadraticLocal Source Labels PhysicalNext PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingCoarse WilsonCoeffUV.Embroider
open WilsonMeasuredPublicEntranceOrder WilsonMeasuredPublicEntranceSignedEar
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G){N per f u:ℕ}(uf:u≤f)
variable {I:Type} (s:Finset I)
local notation "P" => R.family.path.rep N per f
local notation "X" => Config G (R.family.side f per)

open WilsonSeparatedPrefixCanonicalClearConvolution (readingAt)
variable (W:Config G (R.family.side u per))

theorem product (a:I→X→ℂ):
    readingAt R (N:=N) (weighted (N:=N) R (factors a s.toList)) uf W =
      actualTransport R.family (N:=N) (fun U=>∏i∈s,a i U) uf W:=by
  have same : weighted (N:=N) R (factors a s.toList) = fun U=>(P).eval U • (∏i∈s,a i U):=by
    funext U
    simp only [weighted,factors,prod_map_toList,Complex.real_smul]
  rw [same]
  unfold readingAt actualTransport
  rw [Complex.real_smul,Complex.ofReal_inv]

theorem original (a b:I→X→ℂ){fee:ℝ}
    (paid:‖readingAt R (N:=N) (weighted (N:=N) R (factors a s.toList)) uf W -
      readingAt R (N:=N) (weighted (N:=N) R (factors b s.toList)) uf W‖≤fee):
    ‖actualTransport R.family (N:=N) (fun U=>∏i∈s,a i U) uf W-
      actualTransport R.family (N:=N) (fun U=>∏i∈s,b i U) uf W‖≤fee:=by
  rw [product R uf s W a,product R uf s W b] at paid
  exact paid

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldNormalized
end

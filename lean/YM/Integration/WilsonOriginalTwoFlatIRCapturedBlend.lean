import YM.Integration.WilsonOriginalTwoFlatRoseIdentity
import YM.Integration.WilsonReceivedChronologicalMixture

/-! A scalar comparison between two original flat receivers commutes with a finite signed
source sum on the original conditional measure.  The common physical density is retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRCapturedBlend
open Function Finset MeasureTheory Lattice Wilson RG Source Marker
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFlatTelescope
open WilsonOriginalTwoFlatRoseIdentity WilsonReceivedChronologicalReadout WilsonReceivedChronologicalMixture
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N per c u v:ℕ}{V:Type}[DecidableEq V]{J:Census V}
  {I:J.Mode→Type*}[∀s,Fintype (I s)]
local notation "X" j:max => Config G (R.family.side j per)

theorem original (a:∀s,I s→ℂ)(Z:∀s,I s→∀j:ℕ,(X j)→Poly J)(s:J.Mode)
    (M:∀j:ℕ,(X j)→ℂ)(actual:numerator R N per c (M c)=fun U=>(mix R a Z c U).part s)
    (funded:∀t q,Integrable (Z t q c) (prior G _))(uc:u≤c)(vc:v≤c)(bill:I s→ℝ)
    (price:∀q,‖reading R (N:=N) (fun U=>(Z s q c U).part s) u uc-
      reading R (N:=N) (fun U=>(Z s q c U).part s) v vc‖ ≤ bill q):
    ‖cross R (N:=N) uc vc M‖ ≤ ∑q:I s,‖a s q‖*bill q:=by
  let held (q:I s)(j:ℕ)(h:j≤c):=reading R (N:=N) (fun U=>(Z s q c U).part s) j h
  have heard (j:ℕ)(h:j≤c):reading R (N:=N) (numerator R N per c (M c)) j h=
      ∑q:I s,a s q*held q j h:=by
    rw [actual,←flat R N per h _ (live R a Z funded) s,normalized R a Z h 1 s funded]
    exact sum_congr rfl fun q _=>congrArg ((a s q)*·) (flat R N per h _ (funded s q) s)
  rw [cross,heard u uc,heard v vc,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑q:I s,‖a s q*held q u uc-a s q*held q v vc‖:=norm_sum_le _ _
    _ ≤ _:=Finset.sum_le_sum fun q _=>by
      rw [←mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left (price q) (norm_nonneg _)

end YM.Integration.WilsonOriginalTwoFlatIRCapturedBlend
end

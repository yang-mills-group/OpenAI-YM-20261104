import YM.Integration.WilsonMatrixOriginalDeckRawAssay
import YM.Integration.WilsonMatrixOriginalDeckFiledInverse

/-! Decode the complete signed dressed trial on the measured finite Wilson frame before either regulator limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckRawDecoder
open Filter Set Finset MeasureTheory Spec Table Ward PhysMS RG17 MS MS.Land MS.Menus MS.Local.Physical
open Extraction Extraction.Order PhysicalNext.Repeat.Legato Next.UVStress Push.GridApprox OPE OPE.Therm FVA2.ColorCode
open Trace.Pilot WilsonMatrixOriginalDeckRelative WilsonMatrixOriginalDeckError WilsonMatrixOriginalDeckFiledDebit
open WilsonMatrixOriginalDeckRawAssay
open scoped Classical Topology BigOperators Matrix

theorem columns {I:Type*} [Fintype I] [DecidableEq I] (K:ℝ)(A X V:Matrix I I ℂ)(unit:IsUnit A)
    (paid:∀v:I→ℂ,(∑i,‖v i‖)≤K*∑i,‖(A*ᵥv) i‖):
    amount (A⁻¹*X-V)≤K*amount (X-A*V):=by
  let T:=A⁻¹*X-V
  have closed:A*T=X-A*V:=by
    unfold T;rw [Matrix.mul_sub,← Matrix.mul_assoc,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp unit),Matrix.one_mul]
  calc amount T = ∑j,∑i,‖T i j‖:=sum_comm
       _ ≤ ∑j,K*∑i,‖(A*T) i j‖:=sum_le_sum fun j _=>paid (fun i=>T i j)
       _ = K*amount (X-A*V):=by rw [←mul_sum,closed];congr 1;exact sum_comm

variable {G:Gauge} (R:Run G) {D:Deck G} (Q:MS.Land.Prescription D){f:Extraction.Order}{S:Table R.family.book}
variable (F:Spec.Final R.family f S)(L:Layout F)(J:ℝ→PhysMS.tower S)(h:ℕ){O:Booked D}
local notation "I"=>Glyph D h

theorem original (lead:PhysMS.Leading F J)(M:MS_Data G O)(g:Test 2)(pivot:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g)):
    ∃K:ℝ,0<K ∧ ∀ᶠr:ℝ in trail, ∀(hr:0<r)(_:R.family.ref h≤L.level r)(w:I→R.family.label h),
      (∀i,master L h r (w i)=J r h (WilsonMatrixOriginalDeckColumns.basis R.family D h i)) →
      ∀(u:Filter (ℕ×ℕ)) [u.NeBot],u≤L.lens → ∀ᶠz in u, ∀(s:ℝ)(v:I→R.family.label h)(a b:Roster D h)(V:Matrix I I ℂ),
      let T:=dilate hr g
      let C:=matrix R Q h T z a b
      let A:=matrix R Q h T z a a
      let E:=signed R F L Q h T z r s w v a b
      let H:=signed R F L Q h T z r r w w a a
      amount ((field R D F L h g hr r w w z)⁻¹*field R D F L h g hr s w v z-V) ≤
        K*(amount (C-A*V)+amount (E-H*V)):=by
  obtain ⟨K,hK,paid⟩:=WilsonMatrixOriginalDeckFiledInverse.purchased R D F L J h lead M g pivot
  refine ⟨K,hK,?_⟩;filter_upwards [paid] with r settled
  intro hr age w deliver u _ cut
  filter_upwards [(settled hr age w deliver u cut).1] with z live
  intro s v a b V
  have dec:=columns K (field R D F L h g hr r w w z) (field R D F L h g hr s w v z) V live.1 live.2
  refine dec.trans (mul_le_mul_of_nonneg_left ?_ hK.le)
  have c:=fields R F L Q h g hr s w v a b z
  have real:=fields R F L Q h g hr r w w a a z
  rw [c,real,add_mul]
  apply le_trans _ (add_cost _ _);apply le_of_eq;congr 1;abel

end YM.Integration.WilsonMatrixOriginalDeckRawDecoder

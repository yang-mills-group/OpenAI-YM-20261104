import YM.Integration.WilsonMeasuredPublicEntranceThermalRankPair
import YM.Integration.WilsonMeasuredPublicEntranceRecordedWick

/-! Each actual recorded field column has a native raw axis of exactly its engineering
weight and Wick length. The same axis gives its original quotient representative. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceRecordedPort
open Spec Trace Maxwell Labels Extra.FD
open scoped Classical
variable {G:Gauge}

theorem selected (F:Frames G)(d:ℕ)(B:RStage F d)(i:Fin (B.m+1)):
    ∃a:(F.level d).Index, (F.level d).grades a=B.w i ∧
      (freeTable F).project d (Pi.single a 1)=B.b i:=by
  obtain ⟨a, chosen⟩:=B.corners i
  have realField:writes F d (B.b i)≠0:=fun hz=>
    B.b.ne_zero i (writes_inj F d (hz.trans (map_zero _).symm))
  obtain ⟨m,term⟩:∃m,(writes F d (B.b i)).coeff m≠0:=by
    by_contra! empty
    exact realField (MvPolynomial.ext _ _ (fun m=>by simpa only [MvPolynomial.coeff_zero] using empty m))
  have both:=at_alcove F d a (show (writes F d (pack F a)).coeff m≠0 from chosen ▸ term)
  rw [weight_collapse] at both
  have ranks:(F.level d).grades a=B.w i:=by
    rw [←both]
    exact Prod.ext (B.weighs i term) (B.length i term)
  refine ⟨a,ranks,?_⟩
  rw [chosen]
  change (freeTable F).project d (Pi.single a 1)=(freeTable F).project d ((F.level d).coords ((F.level d).basis a))
  rw [Frame.coords_basis]; rfl

theorem original (C:Family G)(d:ℕ)(i:Fin ((recorded C.labels d).m+1)):
    ∃a:(C.labels.level d).Index, (C.labels.level d).grades a=(recorded C.labels d).w i ∧
      (freeTable C.labels).project d (Pi.single a 1)=(recorded C.labels d).b i:=
  selected C.labels d _ i
end YM.Integration.WilsonMeasuredPublicEntranceRecordedPort
end

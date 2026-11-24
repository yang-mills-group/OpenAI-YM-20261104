import YM.PhysMS.Frame.Faces
import YM.OPE.Orbits.Port

/-! Finite physical tests for comparing the unsymmetrized child field with the same measured packet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairPins
open Function Finset Filter Set Table Extraction Spec OPE OPE.Orbits OPE.Prescription
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{f:Order}{S:Table C.book}(F:Final C f S)
    {I:Type}[Fintype I]{d:I→ℕ}
    {P:Prescription F.sector.derivatives}

private lemma field_read (e:Exterior C.book)(v:Labels S d)(x:I→E4)(i:Mode F.sector.derivatives)
    (clear:Injective (beside x (bearing e))):
    reading S x (names v) 0 e=OPE.Orbits.whole S x v (bearing e) (fields S e):=by
  let Q:Prescription F.sector.derivatives:=⟨fun i=>0,fun _=>Finsupp.single e 1⟩
  have obs:=check_eq Q i F.room.kernel x 0 v
  have hx:away x 0=x:=funext fun j=>sub_zero _
  unfold checkRow Prescription.ope at obs
  simp [Q,hx,clear] at obs
  change ((1:ℂ) • sectionLabels (d:=Sum.elim d (expo e)) (fields S e)
    (moment S (beside x (bearing e)))) v=reading S x (names v) 0 e at obs
  rw [one_smul,sectionLabels_apply] at obs
  exact obs.symm

lemma transferred (e:Exterior C.book)(v:Labels S d)(x:I→E4){h:ℕ}(c:S.Field h)
    (i:Mode F.sector.derivatives)(clear:Injective (beside x (bearing e))):
    reading S x (names v) 0 e-S.spectra h c e=
      discrepancy S h x 0 v c (bearing e) (fields S e):=by
  have one:=one_test (S:=S) h e (S.representative h c) F.room.kernel
  rw [S.rep] at one
  have held:=field_read F (I:=Unit) (d:=fun _=>h) e (sole c) (sole 0) i (bearing_clear e)
  change reading S (sole 0) (sole (⟨h,S.representative h c⟩:C.book.Token)) 0 e=_ at held
  rw [←one,held,field_read F e v x i clear]
  rfl

lemma tomography (hp:P.Coherent)(h:ℕ)(x:I→E4)(v:Labels S d)(c:S.Field h)(D:ℝ)
    (heard:∀ i∈bands F.sector.derivatives h,∀e∈(P.sheet i).support,
      Injective (beside x (bearing e)) ∧ ‖discrepancy S h x 0 v c (bearing e) (fields S e)‖≤D):
    ‖shadowOld P h x 0 v-c‖≤
      (∑i∈bands F.sector.derivatives h,
        (∑e∈(P.sheet i).support,‖(P.sheet i) e‖)*‖P.loaded i h‖)*D:=by
  have obs(i:Mode F.sector.derivatives)(hi:i∈bands F.sector.derivatives h):
      ‖P.ope i x (names v) 0-P.test i h c‖≤(∑e∈(P.sheet i).support,‖(P.sheet i) e‖)*D:=by
    rw [sum_mul];apply near_shadow
    intro e he
    rw [transferred F e v x c i (heard i hi e he).1];exact (heard i hi e he).2
  change ‖(∑i∈bands F.sector.derivatives h,P.ope i x (names v) 0 • P.loaded i h)-c‖≤_
  conv_lhs=>arg 1;rhs;rw [←(hp h).rebuilds c]
  rw [←sum_sub_distrib,sum_mul]
  apply (norm_sum_le ..).trans
  refine sum_le_sum fun i hi=>?_
  rw [←sub_smul,norm_smul]
  calc
    _ ≤ ((∑e∈(P.sheet i).support,‖(P.sheet i) e‖)*D)*‖P.loaded i h‖ :=
      mul_le_mul_of_nonneg_right (obs i hi) (norm_nonneg _)
    _ = _:=by ring

end YM.Integration.WilsonThermometerWeakPairPins
end

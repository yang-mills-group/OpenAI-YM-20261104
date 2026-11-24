import YM.Integration.WilsonPhysicalExteriorTransportedFields
import YM.Integration.WilsonPhysicalExteriorFeePolynomial

/-! Reprice the independently marked Wilson field by two existing
polynomial register matrices. The inverse is taken over the original
three real polynomial variables, before evaluating any clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorSourceInverse
open Finset Matrix PowerSeries MS MS.Land MS.Menus MS.Rake FVAAlt2
open WilsonPhysicalExteriorFeeShift WilsonPhysicalExteriorRunningRows WilsonPhysicalExteriorTransportedFields
open scoped Classical BigOperators
variable {G:Gauge}{B:MS.Local.Physical.Deck G}
local notation "K" => MvPolynomial (Fin 3) ℝ
local notation "PS" => PowerSeries ℂ
variable (Q:Prescription B)

private theorem moved {I:Type} [Fintype I] [DecidableEq I] (a b:PowerSeries K)
    (v:Matrix I I (PowerSeries K)) (ha:constantCoeff a=0) (hb:constantCoeff b=0) (hv:IsUnit v) :
    IsUnit (show Matrix I I (PowerSeries K) from fun i j=>PowerSeries.subst a (PowerSeries.subst b (v i j))) := by
  let f:PowerSeries K→ₐ[K]PowerSeries K:=PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' ha)
  let g:PowerSeries K→ₐ[K]PowerSeries K:=PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' hb)
  have h:=hv.map ((f.comp g).toRingHom.mapMatrix)
  have e:(f.comp g).toRingHom.mapMatrix v=
      (show Matrix I I (PowerSeries K) from fun i j=>PowerSeries.subst a (PowerSeries.subst b (v i j))) := by
    apply Matrix.ext;intro i j
    change f (g (v i j))=_
    simp [f,g,PowerSeries.coe_substAlgHom]
  exact e ▸ h

theorem complete (d:ℕ) : IsUnit (WilsonPhysicalExteriorFeePolynomial.stored Q d) := by
  let A:=MSFeeCoordinates.matrix Q d
  have hinv:IsUnit A⁻¹:=⟨⟨A⁻¹,A,Matrix.nonsing_inv_mul _ (MSFeeCoordinates.determinant Q d),
    Matrix.mul_nonsing_inv _ (MSFeeCoordinates.determinant Q d)⟩,rfl⟩
  unfold WilsonPhysicalExteriorFeePolynomial.stored
  apply IsUnit.mul
  · exact (MSFeeCoordinates.unit Q d).map _
  · apply moved
    · rfl
    · exact PowerSeries.constantCoeff_substInvOfIsUnit ..
    · let j:Polynomial ℝ→+*K:=Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (1:Fin 3))
      exact hinv.map ((PowerSeries.map j).mapMatrix)

private def eval (x:Fin 3→ℝ):K→+*ℂ:=Complex.ofRealHom.comp (MvPolynomial.eval x)
private def key (i:Fin 3):Fin 3→Fin 3:=![2,i,2]
private def reset (q:Fin 3→Fin 3) : K→+*K := (MvPolynomial.rename q).toRingHom
private def book (d:ℕ) (i:Fin 3) :=
  (PowerSeries.map (reset (key i))).mapMatrix (WilsonPhysicalExteriorFeePolynomial.stored Q d)

private theorem reader (d:ℕ) (i:Fin 3) (x:Fin 3→ℝ) :
    (PowerSeries.map (eval x)).mapMatrix (book Q d i)=coordinates Q d (x 2) (x i) (x 2) := by
  have hom:(eval x).comp (reset (key i))=eval (fun n=>x (key i n)):=by
    apply MvPolynomial.ringHom_ext
    · intro r;simp [eval,reset]
    · intro j;simp [eval,reset]
  apply Matrix.ext;intro a b
  change PowerSeries.map (eval x) (PowerSeries.map (reset (key i)) _)=_
  calc
    _=PowerSeries.map (eval (fun n=>x (key i n))) (WilsonPhysicalExteriorFeePolynomial.stored Q d a b) := by
      apply PowerSeries.ext;intro k
      rw [PowerSeries.coeff_map,PowerSeries.coeff_map,PowerSeries.coeff_map];exact DFunLike.congr_fun hom _
    _=_:=congrFun (congrFun (WilsonPhysicalExteriorFeePolynomial.measured Q d (fun n=>x (key i n))) a) b

def tariff (d:ℕ) := (book Q d 0)⁻¹*book Q d 1

private theorem equation (d:ℕ) (v y z:ℝ) :
    coordinates Q d z v z * (reprice Q.team v z).toRingHom.mapMatrix (coordinates Q d v y v)=
      coordinates Q d z y z := by
  let φ:PS→+*PS:=(reprice Q.team v z).toRingHom
  let ψ:PS→+*PS:=(reprice Q.team y z).toRingHom
  have co:φ.mapMatrix ((reprice Q.team y v).toRingHom.mapMatrix (oldFrame Q d y))=
      ψ.mapMatrix (oldFrame Q d y):=by
    apply Matrix.ext;intro a b;exact successive Q.team y v z _
  have old:oldFrame Q d v * frame Q d v=1:=by
    rw [oldFrame,WilsonPhysicalExteriorFeeShift.frame,←map_mul,
      Matrix.nonsing_inv_mul _ (MSFeeCoordinates.determinant Q d),map_one]
  change (frame Q d z*φ.mapMatrix (oldFrame Q d v))*φ.mapMatrix
      (frame Q d v*(reprice Q.team y v).toRingHom.mapMatrix (oldFrame Q d y))=
      frame Q d z*ψ.mapMatrix (oldFrame Q d y)
  rw [map_mul,co,Matrix.mul_assoc,←Matrix.mul_assoc (φ.mapMatrix (oldFrame Q d v)),
    ←map_mul,old,map_one,Matrix.one_mul]

theorem measured (d:ℕ) (x:Fin 3→ℝ) :
    (PowerSeries.map (eval x)).mapMatrix (tariff Q d)=
      (reprice Q.team (x 0) (x 2)).toRingHom.mapMatrix (coordinates Q d (x 0) (x 1) (x 0)) := by
  have h:IsUnit (book Q d 0):=(complete Q d).map _
  let f:PowerSeries K→+*PS:=PowerSeries.map (eval x)
  have left:f.mapMatrix (book Q d 0)⁻¹*f.mapMatrix (book Q d 0)=1:=by
    rw [←map_mul,Matrix.nonsing_inv_mul _ ((book Q d 0).isUnit_iff_isUnit_det.mp h),map_one]
  rw [tariff,map_mul,reader,←equation Q d (x 0) (x 1) (x 2),←reader Q d 0 x,←Matrix.mul_assoc,left,Matrix.one_mul]

theorem coefficient (p:Label B) (a:Glyph B p.h) (k:ℕ) (x:Fin 3→ℝ) :
    coeff k (column Q p (x 0) (x 1) (x 2) a)=
      ((MvPolynomial.eval x (coeff k (tariff Q p.h (Land.read p.item) a)):ℝ):ℂ) := by
  have h:=congrFun (congrFun (measured Q p.h x) (Land.read p.item)) a
  change PowerSeries.map (eval x) (tariff Q p.h (Land.read p.item) a)=column Q p (x 0) (x 1) (x 2) a at h
  rw [←h,PowerSeries.coeff_map];rfl

end YM.Integration.WilsonPhysicalExteriorSourceInverse
end

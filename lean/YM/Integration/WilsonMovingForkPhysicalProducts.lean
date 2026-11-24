import YM.Integration.WilsonPublicForkInterchange
import YM.Integration.WilsonPublicForkTestProduct
import YM.Integration.WilsonMacroscopicRichPositionRows

/-! The two actual positive-output observations at independent reporting
radii are integrals of the complete position field at the named points. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkPhysicalProducts
open Function Filter Set MeasureTheory Table Spec RG17 OPE OPE.Orbits
open PhysMS Climb PhysicalNext.Repeat.Legato
open WilsonMacroscopicRichSignedAmplitude WilsonMacroscopicRichTestGeometry WilsonMacroscopicRichMovingPlane
open WilsonMacroscopicRichReflectedRoster
open WilsonPublicForkTestProduct
open private coordinate from YM.Integration.WilsonMacroscopicRichTestGeometry
open private field from YM.Integration.WilsonMacroscopicRichSignedAmplitude
open private joint from YM.Integration.WilsonPublicForkInterchange
open scoped Classical Topology
variable {n:ℕ}{G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
  (F:Final C f S)(J:ℝ → PhysMS.tower S)

def roster (r t:ℝ){d:Fin n → ℕ}{h:ℕ}(v:∀i,Free C (d i))(a:Free C h):Fin (n+1) → S.Tag:=
  Fin.append (fun i=>physical J r ⟨d i,v i⟩) (fun _:Fin 1=>physical J t ⟨h,a⟩)

theorem whole (ψ:Test n)(φ:Test 2){r t:ℝ}(tp:0<t){d:Fin n → ℕ}{h:ℕ}
    (v:∀i,Free C (d i))(a:Free C h)
    (safe:∀x∈tsupport ψ,∀z∈tsupport φ,placed r t x (relative z)∈conf (n+1)):
    appeared F (d:=d) (fun i=>J r _ (v i)) (stencil J φ tp ⟨h,a⟩) r ψ =
      WilsonPublicForkTestProduct.tested ψ φ (fun p=>S.useAt S (placed r t p.1 (relative p.2)) (roster J r t v a)):=by
  let A (x:Points n)(z:Points 2):=ψ x*(φ z*integrand J φ tp ⟨h,a⟩ r x (fun i=>⟨d i,v i⟩) z)
  have all:Integrable A.uncurry (volume.prod volume):=joint F J ψ φ tp v a safe
  have first(x:Points n):(∫z:Points 2,A x z)=ψ x*reading J φ tp ⟨h,a⟩ r x (fun i=>⟨d i,v i⟩):=by
    change (∫z:Points 2,ψ x*(_*_))=ψ x*(Next.UVStress.dilate tp φ).applyTo _
    rw [integral_const_mul,Next.UVStress.zoom_integral];rfl
  rw [(WilsonPublicForkInterchange.original F J ψ φ tp v a safe).2,WilsonPublicForkTestProduct.tested]
  calc
    _=∫x:Points n,∫z:Points 2,A x z:=integral_congr_ae (Eventually.of_forall fun x=>(first x).symm)
    _=∫p:Points n×Points 2,A p.1 p.2:=(integral_prod _ all).symm
    _=_:=by
      apply integral_congr_ae;filter_upwards with p
      by_cases hx:p.1∈tsupport ψ
      · by_cases hz:p.2∈tsupport φ
        · dsimp only [A];rw [field F J φ tp ⟨h,a⟩ r p.1 (fun i=>⟨d i,v i⟩) (safe p.1 hx p.2 hz)]
          exact (mul_assoc _ _ _).symm
        · simp [A,image_eq_zero_of_notMem_tsupport hz]
      · simp [A,image_eq_zero_of_notMem_tsupport hx]

end YM.Integration.WilsonMovingForkPhysicalProducts

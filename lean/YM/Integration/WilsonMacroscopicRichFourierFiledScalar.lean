import YM.Integration.WilsonMacroscopicRichBookedReportMeter
import YM.Integration.WilsonSeparatedOriginalSlabFourierCredit

/-! The same physical chamber and original upper gauge for an addressed field
and its own full, projected counterterm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichFourierFiledScalar
open Function Set MeasureTheory Lattice Wilson RG Source PhysicalNext.Repeat.Legato Trace.Physical.GermGraph RG16.Literal
open WilsonSeparatedOriginalSlabFourierCredit
open scoped Topology BigOperators Classical
variable {X:Type*} [TopologicalSpace X]
def diagonal : C(Fin 3→X,ℂ)→ₗ[ℂ]C(X,ℂ) where
  toFun:=gauge
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def atGauge (U:X) : C(Fin 3→X,ℂ)→ₗ[ℂ]ℂ where
  toFun f:=gauge f U
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

variable {G:Gauge}(R:Run G){N p h j:ℕ}
local notation "Upper"=>Config G (R.family.side N p)
def held (U:Upper) : R.family.label h →ₗ[ℂ]ℂ where
  toFun z:=R.family.O N p ((R.family.factory h N p).terminal z) 0 U
  map_add' a b:=by
    rw [map_add,(R.family.linearO N p h 0).map_add];rfl
  map_smul' a b:=by
    rw [map_smul,(R.family.linearO N p h 0).map_smul];rfl

def account (door:Opened R.family h j p) (live:j≤N) (f:C(Fin 3→Upper,ℂ)) (U:Upper) : ℂ :=
  gauge f U-held R U (topReport R.family N p h R.makes j door live (gauge f))

theorem purchased {K:Type*}(door:Opened R.family h j p)(live:j≤N)(weight:K→ℂ)
    (f:K→C(Fin 3→Upper,ℂ))(F:C(Fin 3→Upper,ℂ))
    (sum:∀ L:C(Fin 3→Upper,ℂ)→ₗ[ℂ]ℂ,HasSum (fun k=>weight k*L (f k)) (L F))
    (fb:∀k,Booked R.family N p h (gauge (f k)) j live)
    (whole:Booked R.family N p h (gauge F) j live) :
    (∀ ℓ:R.family.label h→ₗ[ℂ]ℂ,
      HasSum (fun k=>weight k*ℓ (topReport R.family N p h R.makes j door live (gauge (f k))))
        (ℓ (topReport R.family N p h R.makes j door live (gauge F)))) ∧
    ∀ U:Upper,HasSum (fun k=>weight k*account R door live (f k) U) (account R door live F U):=by
  obtain ⟨M,filed⟩:=WilsonMacroscopicRichBookedReportMeter.original R.family R.makes door live
  have coord (ℓ:R.family.label h→ₗ[ℂ]ℂ) := sum (ℓ.comp (M.comp diagonal))
  have paid (ℓ:R.family.label h→ₗ[ℂ]ℂ):HasSum (fun k=>weight k*ℓ (topReport R.family N p h R.makes j door live (gauge (f k))))
      (ℓ (topReport R.family N p h R.makes j door live (gauge F))) :=by
    simpa only [LinearMap.comp_apply,diagonal,LinearMap.coe_mk,AddHom.coe_mk,
      filed (gauge F) whole,fun k=>filed (gauge (f k)) (fb k)] using coord ℓ
  refine ⟨paid,fun U=>?_⟩
  have physical:=sum (atGauge U)
  simpa only [account,mul_sub,atGauge,LinearMap.coe_mk,AddHom.coe_mk,Pi.sub_apply] using
    (physical.sub (paid (held R U)))

end YM.Integration.WilsonMacroscopicRichFourierFiledScalar

import YM.Integration.WilsonMacroscopicRichSignedBookingSplit

/-! Both the split field and its counterterm are measured at the same upper
configurations, and the complementary signed family is booked in aggregate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichSignedBookingField
open Function Set Lattice Wilson RG Source PhysicalNext.Repeat.Legato Trace.Physical.GermGraph RG16.Literal
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) {N p h j:ℕ}
local notation "Upper"=>Config G (R.family.side N p)
local notation "B!"=>fun Y=>Booked R.family N p h Y j
def correction (door:Opened R.family h j p)(live:j≤N)(Y:C(Upper,ℂ))(U:Upper):ℂ:=
  Y U-R.family.O N p (WilsonMacroscopicRichChildRegistration.returned R.family R.makes door live Y) 0 U

def sample {E:Type*}[TopologicalSpace E](u:E):C(E,ℂ)→ₗ[ℂ]ℂ where
  toFun f:=f u
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

theorem physical {D K:Type*}[Fintype D](door:Opened R.family h j p)(live:j≤N)
    (P:(D→ℂ)→ₗ[ℂ]C(Upper,ℂ))(v:K→D→ℂ)(w:K→ℂ)(t:D→ℂ)
    (sum:HasSum (fun k=>w k•v k) t) (book:B! (P t) live):
    let ok:=fun k=>B! (P (v k)) live
    ∃g:D→ℂ,HasSum (fun k=>if ok k then w k•v k else 0) g ∧
      HasSum (fun k=>if ok k then 0 else w k•v k) (t-g) ∧
      B! (P g) live ∧ B! (P (t-g)) live ∧
      ∀U:Upper,HasSum (fun k=>if ok k then w k*correction R door live (P (v k)) U else 0)
        (correction R door live (P t) U-correction R door live (P (t-g)) U):=by
  intro ok
  obtain ⟨g,keep,rest,gb,rb,fees⟩:=WilsonMacroscopicRichSignedBookingSplit.resolved R door live P v w t sum book
  refine ⟨g,keep,rest,gb,rb,fun U=>?_⟩
  let L:(D→ℂ)→ₗ[ℂ]ℂ:=(sample U).comp P
  have read:=keep.mapL L.toContinuousLinearMap
  change HasSum (fun k=>L (if ok k then w k•v k else 0)) (L g) at read
  have val(k:K):L (if ok k then w k•v k else 0)=(if ok k then w k*P (v k) U else 0):=by
    by_cases hk:ok k <;> simp [hk,L,sample]
  have bal:L g=P t U-P (t-g) U:=by simp only [map_sub,ContinuousMap.sub_apply];change P g U=P t U-(P t U-P g U);abel
  have raw:HasSum (fun k=>if ok k then w k*(P (v k) U) else 0) (P t U-P (t-g) U):=by simpa only [val,bal] using read
  have all:=raw.sub (fees (WilsonMacroscopicRichFourierFiledScalar.held R U))
  let Kfield(Y:C(Upper,ℂ)):=R.family.O N p (WilsonMacroscopicRichChildRegistration.returned R.family R.makes door live Y) 0 U
  change HasSum (fun k=>(if ok k then w k*P (v k) U else 0)-(if ok k then w k*Kfield (P (v k)) else 0))
    ((P t U-P (t-g) U)-(Kfield (P t)-Kfield (P (t-g)))) at all
  have term(k:K):(if ok k then w k*P (v k) U else 0)-(if ok k then w k*Kfield (P (v k)) else 0)=
      (if ok k then w k*correction R door live (P (v k)) U else 0):=by
    by_cases hk:ok k <;> simp only [hk,ite_true,ite_false,correction,Kfield,mul_sub,sub_zero]
  have full:(P t U-P (t-g) U)-(Kfield (P t)-Kfield (P (t-g)))=
      correction R door live (P t) U-correction R door live (P (t-g)) U:=by
    dsimp only [correction,Kfield];abel
  simpa only [term,full] using all
end YM.Integration.WilsonMacroscopicRichSignedBookingField

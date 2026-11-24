import YM.Integration.WilsonMacroscopicRichSignedBookingField

/-! One signed source slot may be tested inside an already fixed joint
experiment without separating its other fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichSignedBookingTester
open Function Set Lattice Wilson RG Source PhysicalNext.Repeat.Legato Trace.Physical.GermGraph RG16.Literal
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) {N p h j:ℕ}
local notation "X"=>Config G (R.family.side N p)
local notation "B!"=>fun Y=>Booked R.family N p h Y j
def counterterm : R.family.label h→ₗ[ℂ]C(X,ℂ) where
  toFun z:=⟨R.family.O N p ((R.family.factory h N p).terminal z) 0,R.family.continuousO N p h ((R.family.factory h N p).terminal z) 0⟩
  map_add' a b:=ContinuousMap.ext (fun U=>(WilsonMacroscopicRichFourierFiledScalar.held R U).map_add a b)
  map_smul' a b:=ContinuousMap.ext (fun U=>(WilsonMacroscopicRichFourierFiledScalar.held R U).map_smul a b)

def corrected (door:Opened R.family h j p)(live:j≤N)(Y:C(X,ℂ)):C(X,ℂ):=
  Y-counterterm R (topReport R.family N p h R.makes j door live Y)

theorem tested {D K:Type*}[Fintype D](door:Opened R.family h j p)(live:j≤N)
    (P:(D→ℂ)→ₗ[ℂ]C(X,ℂ))(v:K→D→ℂ)(w:K→ℂ)(t:D→ℂ)
    (sum:HasSum (fun k=>w k•v k) t) (book:B! (P t) live):
    let ok:=fun k=>B! (P (v k)) live
    ∃g:D→ℂ,HasSum (fun k=>if ok k then w k•v k else 0) g ∧
      HasSum (fun k=>if ok k then 0 else w k•v k) (t-g) ∧
      B! (P g) live ∧ B! (P (t-g)) live ∧
      ∀M:C(X,ℂ)→ₗ[ℂ]ℂ,HasSum (fun k=>if ok k then w k*M (corrected R door live (P (v k))) else 0)
        (M (corrected R door live (P t))-M (corrected R door live (P (t-g)))):=by
  intro ok
  obtain ⟨g,keep,rest,gb,rb,fees⟩:=WilsonMacroscopicRichSignedBookingSplit.resolved R door live P v w t sum book
  refine ⟨g,keep,rest,gb,rb,fun M=>?_⟩
  let L:=M.comp P
  have read:=keep.mapL L.toContinuousLinearMap
  change HasSum (fun k=>L (if ok k then w k•v k else 0)) (L g) at read
  have val(k:K):L (if ok k then w k•v k else 0)=(if ok k then w k*M (P (v k)) else 0):=by
    by_cases hk:ok k <;> simp [hk,L]
  have bal:L g=M (P t)-M (P (t-g)):=by simp only [L,LinearMap.comp_apply,map_sub];abel
  have raw:HasSum (fun k=>if ok k then w k*M (P (v k)) else 0) (M (P t)-M (P (t-g))):=by simpa only [val,bal] using read
  let issued:=fun Y:C(X,ℂ)=>M (counterterm R (topReport R.family N p h R.makes j door live Y))
  have all:=raw.sub (fees (M.comp (counterterm R)))
  change HasSum (fun k=>(if ok k then w k*M (P (v k)) else 0)-(if ok k then w k*issued (P (v k)) else 0))
    ((M (P t)-M (P (t-g)))-(issued (P t)-issued (P (t-g)))) at all
  have term(k:K):(if ok k then w k*M (P (v k)) else 0)-(if ok k then w k*issued (P (v k)) else 0)=
      (if ok k then w k*M (corrected R door live (P (v k))) else 0):=by
    by_cases hk:ok k <;> simp only [hk,ite_true,ite_false,corrected,issued,map_sub,mul_sub,sub_zero]
  have full:(M (P t)-M (P (t-g)))-(issued (P t)-issued (P (t-g)))=
      M (corrected R door live (P t))-M (corrected R door live (P (t-g))):=by
    simp only [corrected,issued,map_sub];abel
  simpa only [term,full] using all
end YM.Integration.WilsonMacroscopicRichSignedBookingTester

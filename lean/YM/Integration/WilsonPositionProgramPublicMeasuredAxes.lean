import YM.Integration.WilsonPositionProgramPublicFourFrame
import YM.Integration.WilsonPositionProgramPublicEnrolledMatrix

/-! The genuine Maxwell quotient supplies one common field index for the
physical determining probes and every entry of the independent publication.
The physical matrix retains the signed measured rows at their own cutoff. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicMeasuredAxes
open Filter Function Lattice Wilson RG Source Extraction Table Spec RG17 FullVolume Climb
open PhysicalNext.Repeat.Legato Next.UVStress Trace.Pilot PhysMS
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register MS MS.Menus Local.Physical
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot
open WilsonThermometerUnitFilingFourSquare WilsonPositionProgramPublicGram
open WilsonPositionProgramPublicFiniteMatrix WilsonPositionProgramPublicOriented
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) (B:Deck G)(d:ℕ)

def axes : Module.Basis (Glyph B d) ℂ ((Bel R.family.book).Field d) :=
  (Theater.Daylight B d).map (Maxwell.Free.fields R.family.labels d).symm

theorem filed (i:Glyph B d):Maxwell.Free.fields R.family.labels d (axes R B d i)=
    Theater.Daylight B d i:=by
  rw [axes,Module.Basis.map_apply,LinearEquiv.apply_symm_apply]

variable {R d} {f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
    (Z:WilsonPrescription G){l:Ultrafilter (ℕ×ℕ)}(p:Profiles R d){r:ℝ}(hr:0<r)
    (arm:Bool→(y:S.Field d)→Arm R.family S (l:Filter _) d y)
    (L:(p.probes.index→ℂ)→L[ℂ](Bel R.family.book).Field d)
local notation "Γ" => Glyph B d

def position (i:Γ):S.Field d:=homogeneous F J Z r d (axes R B d i)

def issued (a:Bool)(i:Γ)(z:ℕ×ℕ):R.family.label d:=(arm a (position B F J Z (r:=r) i)).source z

def fee (a:Bool)(z:ℕ×ℕ)(y:(Bel R.family.book).Field d):p.probes.index→ℂ :=
  measured F J Z p hr (axes R B d) (issued B F J Z (r:=r) arm a) z y

def coordinate (a:Bool)(z:ℕ×ℕ)(w:Γ→ℂ):Γ→ℂ :=
  (axes R B d).equivFun (L (fee B F J Z p hr arm a z ((axes R B d).equivFun.symm w)))

theorem column (a:Bool)(z:ℕ×ℕ)(i:Γ):fee B F J Z p hr arm a z (axes R B d i) =
    WilsonPositionProgramPublicMicroscopic.sheet F J Z p hr z ((arm a (position B F J Z (r:=r) i)).source z):=
  WilsonPositionProgramPublicFiniteMatrix.entry ..

theorem replay (a:Bool)(z:ℕ×ℕ)(w:Γ→ℂ):
    ∑ i:Γ,coordinate B F J Z p hr arm L a z w i • axes R B d i =
      L (fee B F J Z p hr arm a z ((axes R B d).equivFun.symm w)) :=by
  apply (axes R B d).sum_repr

theorem fitted (z:ℕ×ℕ) (sold:Roster F J Z (axes R B d) p hr (issued B F J Z (r:=r) arm) L z):
    ∃U:(Γ→ℂ)≃ₗ[ℂ](Γ→ℂ),
      (∀w,coordinate B F J Z p hr arm L true z (U w)=coordinate B F J Z p hr arm L false z w) ∧
      (∀w,‖(axes R B d).equivFun.symm (U w)-(axes R B d).equivFun.symm w‖ ≤
          (2*‖L‖)*‖fee B F J Z p hr arm false z ((axes R B d).equivFun.symm w)-
            fee B F J Z p hr arm true z ((axes R B d).equivFun.symm w)‖) ∧
      ∀w,fee B F J Z p hr arm false z ((axes R B d).equivFun.symm w)=
          fee B F J Z p hr arm true z ((axes R B d).equivFun.symm w)→U w=w :=by
  obtain ⟨V,heard,price,exactly⟩:=sold
  let b: (Bel R.family.book).Field d ≃ₗ[ℂ](Γ→ℂ):=(axes R B d).equivFun
  let U:=b.symm.trans (V.trans b)
  have undo (w:Γ→ℂ):b.symm (U w)=V (b.symm w):=by
    change b.symm (b (V (b.symm w)))=_
    rw [LinearEquiv.symm_apply_apply]
  refine ⟨U,?_,?_,?_⟩
  · intro w
    change b (L (fee B F J Z p hr arm true z (b.symm (U w))))=_
    rw [undo]
    exact congrArg b (heard (b.symm w))
  · intro w
    change ‖b.symm (U w)-b.symm w‖≤_
    rw [undo]
    exact price (b.symm w)
  · intro w eq
    apply b.symm.injective
    rw [undo]
    exact exactly (b.symm w) eq

end YM.Integration.WilsonPositionProgramPublicMeasuredAxes

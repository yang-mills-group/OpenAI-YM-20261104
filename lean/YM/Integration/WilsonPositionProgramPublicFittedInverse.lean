import YM.Integration.WilsonPositionProgramPublicMeasuredAxes

/-! Stability of the actual fitted preframe in its public coefficient basis. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicFittedInverse
open Filter Function Lattice Wilson RG Source Extraction Table Spec RG17 FullVolume Climb
open PhysicalNext.Repeat.Legato Next.UVStress Trace.Pilot PhysMS
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register MS MS.Menus Local.Physical
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot
open WilsonThermometerUnitFilingFourSquare WilsonPositionProgramPublicGram
open WilsonPositionProgramPublicFiniteMatrix WilsonPositionProgramPublicPerturbation
open WilsonPositionProgramPublicOriented WilsonPositionProgramPublicMeasuredAxes
open scoped Topology BigOperators Classical

variable {G:Gauge} (R:Run G)(B:Deck G)(d:ℕ)
local notation "Γ" => Glyph B d
def condition : ℝ :=
  let b:=(axes R B d).equivFun
  ‖b.toLinearMap.toContinuousLinearMap‖*2*‖b.symm.toLinearMap.toContinuousLinearMap‖

theorem nonneg : 0≤condition R B d:=by unfold condition;positivity

variable {R d}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
    (Z:WilsonPrescription G){l:Ultrafilter (ℕ×ℕ)}(p:Profiles R d){r:ℝ}(hr:0<r)
    (arm:Bool→(y:S.Field d)→Arm R.family S (l:Filter _) d y)
    (L:(p.probes.index→ℂ)→L[ℂ](Bel R.family.book).Field d)

theorem original (reads:∀y,L (samples F J Z p r y)=y)(order:(l:Filter _)≤f.fuse):
    ∀ᶠ z in (l:Filter _),∃U:(Γ→ℂ)≃ₗ[ℂ](Γ→ℂ),
      (∀w,coordinate B F J Z p hr arm L true z (U w)=coordinate B F J Z p hr arm L false z w) ∧
      (∀w,‖U w-w‖≤condition R B d*‖coordinate B F J Z p hr arm L false z w-
        coordinate B F J Z p hr arm L true z w‖) ∧
      ∀w,fee B F J Z p hr arm false z ((axes R B d).equivFun.symm w)=
          fee B F J Z p hr arm true z ((axes R B d).equivFun.symm w)→U w=w :=by
  let a:=axes R B d
  let b:=a.equivFun
  let rows br i:=arm br (WilsonPositionProgramPublicMeasuredAxes.position B F J Z (r:=r) i)
  let M br z:=measured F J Z p hr a (fun i=>(rows br i).source) z
  have newCash:=acquired L (samples F J Z p r) reads (M true)
    (converges F J Z p hr a order (rows true))
  filter_upwards [submitted F J Z a p hr L reads order rows,newCash] with z sold h
  obtain ⟨V⟩:=h
  obtain ⟨U,heard,_,same⟩:=fitted B F J Z p hr arm L z sold
  refine ⟨U,heard,?_,same⟩
  have cap (w:Γ→ℂ) : ‖w‖ ≤ condition R B d * ‖coordinate B F J Z p hr arm L true z w‖ :=by
    let y:=V.change (b.symm w)
    have eq : V.change.symm y=b.symm w:=V.change.symm_apply_apply _
    have coord : b y=coordinate B F J Z p hr arm L true z w :=
      congrArg b (LinearMap.congr_fun V.reads (b.symm w))
    have pull : ‖y‖ ≤ ‖b.symm.toLinearMap.toContinuousLinearMap‖ * ‖b y‖ :=by
      simpa only [LinearMap.coe_toContinuousLinearMap',LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply] using b.symm.toLinearMap.toContinuousLinearMap.le_opNorm (b y)
    calc
      ‖w‖ = ‖b (V.change.symm y)‖ :=by rw [eq,LinearEquiv.apply_symm_apply]
      _ ≤ ‖b.toLinearMap.toContinuousLinearMap‖ * ‖V.change.symm y‖ :=
        b.toLinearMap.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖b.toLinearMap.toContinuousLinearMap‖*(2*(‖b.symm.toLinearMap.toContinuousLinearMap‖*‖b y‖)) :=
        mul_le_mul_of_nonneg_left ((V.price y).trans (mul_le_mul_of_nonneg_left pull (by norm_num))) (b.toLinearMap.toContinuousLinearMap.opNorm_nonneg)
      _ = _ :=by rw [coord];change _=(‖b.toLinearMap.toContinuousLinearMap‖*2*‖b.symm.toLinearMap.toContinuousLinearMap‖)*_;ring
  intro w
  have diff : coordinate B F J Z p hr arm L true z (U w-w) =
      coordinate B F J Z p hr arm L false z w-coordinate B F J Z p hr arm L true z w :=by
    rw [←heard]
    simp only [coordinate,fee,map_sub]
  simpa only [diff] using cap (U w-w)

end YM.Integration.WilsonPositionProgramPublicFittedInverse

import YM.Integration.WilsonMacroscopicRichFourierFiledScalar

/-! The reported product minus its own original upper counterterm on an addressed finite stencil. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichFourierCounterterm
open Function Set UnitAddTorus Lattice Wilson Source RG PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Native RG05Readout.Pulse RG05Readout.Address RG05Readout.Nuclear
open Trace.Physical.GermGraph WilsonSeparatedOriginalSlabFourierCredit WilsonMacroscopicRichFourierFiledScalar
open RG16.Literal WilsonSeparatedOriginalSlabFourierPositions WilsonSeparatedOriginalSlabFourierRoom WilsonSeparatedOriginalSlabPlaneTest WilsonSeparatedOriginalSlabFourierCharacters
open WilsonSeparatedOriginalSlabFourierLattice WilsonSeparatedOriginalSlabFourierAtlas WilsonSeparatedOriginalSlabFourierCylinder
open scoped Topology BigOperators Classical
local notation "I"=>Fin 3
local notation "K"=>Axes→ℤ
variable {G:Gauge}{A:Type*}[TopologicalSpace A]

variable (R:Run G)
theorem original (b:ℕ)(s:I→ℕ){r cap:ℝ}(rp:0<r)(cp:0≤cap)(Ψ:Wave I)(seen:∀y∈tsupport Ψ.val,∀i,‖y i‖≤cap){B:ℝ}(bp:0≤B)(fund:Tall Ψ (rank s+1) 1 B):
    let J:=WilsonSeparatedOriginalSlabActiveWeights.range R.family b r cap
    let P:=edge R.family b J r cap
    ∃F:C(UnitAddTorus Axes,ℂ),Summable (fun k:K=>‖mFourierCoeff F k‖*height k^load s) ∧
      (∑'k:K,‖mFourierCoeff F k‖*height k^load s)≤bank P (rank s+1) B*WilsonSeparatedOriginalSlabFourierBudget.charge Axes (load s) ∧

      ∀(N per:ℕ)(h:b≤N)(v:(i:I)→Palette R.family (s i))(g:Body)(m d j:ℕ)(hj:j≤N)(door:Opened R.family d j per),
        let S:=fun k:K=>restricted R (per:=per) s v h J (packet (wire P (r/R.family.S.a b) k) (r/R.family.S.a b)) r g m
        let Y:=constellation (C:=R.family) s v r Ψ h m g
        (∀k,Booked R.family N per d (gauge (S k)) j hj)→Booked R.family N per d Y j hj→
          (Booked R.family N per d (Y-R.family.O N per (WilsonMacroscopicRichChildRegistration.returned R.family R.makes door hj Y) 0) j hj ∧
           topReport R.family N per d R.makes j door hj (Y-R.family.O N per (WilsonMacroscopicRichChildRegistration.returned R.family R.makes door hj Y) 0)=0) ∧
          (∀ ℓ:R.family.label d→ₗ[ℂ]ℂ,HasSum (fun k=>mFourierCoeff F k*ℓ (topReport R.family N per d R.makes j door hj (gauge (S k))))
            (ℓ (topReport R.family N per d R.makes j door hj Y))) ∧
          ∀U:Config G (R.family.side N per),HasSum (fun k=>mFourierCoeff F k*account R door hj (S k) U)
            (Y U-R.family.O N per (WilsonMacroscopicRichChildRegistration.returned R.family R.makes door hj Y) 0 U):=by
  intro J P
  obtain ⟨F,law,bill,paid⟩:=WilsonSeparatedOriginalSlabFourierMeter.original R s b J rp cp Ψ seen bp fund
  refine ⟨F,law,bill,?_⟩;intro N per h v g m d j hj door S Y ink book
  let Z:=restricted R (per:=per) s v h J Ψ r g m
  have actual:(gauge Z:Config G (R.family.side N per)→ℂ)=Y:=by
    change (gauge (restricted R s v h J Ψ r g m):Config G (R.family.side N per)→ℂ)=_
    rw [selected R s v h rp Ψ seen g m]
    exact funext (WilsonSeparatedOriginalReplicaExperiments.diagonal R s v h Ψ r g m)
  have fb:Booked R.family N per d (gauge Z) j hj:=actual ▸ book
  obtain ⟨weights,fields⟩:=WilsonMacroscopicRichFourierFiledScalar.purchased R door hj (mFourierCoeff F) S Z (paid N per h v g m) ink fb
  refine ⟨WilsonMacroscopicRichChildRegistration.null R.family R.makes door hj Y (actual ▸ (gauge Z).continuous) book,?_,?_⟩
  · simpa only [actual] using weights
  · intro U
    simpa only [account,WilsonMacroscopicRichFourierFiledScalar.held,LinearMap.coe_mk,AddHom.coe_mk,WilsonMacroscopicRichChildRegistration.returned,actual] using fields U
end YM.Integration.WilsonMacroscopicRichFourierCounterterm

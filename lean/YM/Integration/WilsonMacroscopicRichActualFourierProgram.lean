import YM.Integration.WilsonMacroscopicRichFourierCellBank
import YM.Integration.WilsonMacroscopicRichSignedBookingTester

/-! One actual filed source with its signed conditional complement on the original finite child stencil. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichActualFourierProgram
open Function Set UnitAddTorus Lattice Wilson Source RG PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Native RG05Readout.Pulse RG05Readout.Address RG05Readout.Nuclear
open Trace.Physical.GermGraph WilsonSeparatedOriginalSlabFourierCredit WilsonMacroscopicRichFourierFiledScalar
open WilsonMacroscopicRichFourierCellBank WilsonMacroscopicRichSignedBookingTester
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
        let α:=fun k:K=>weights R s h J r g (packet (wire P (r/R.family.S.a b) k) (r/R.family.S.a b))
        let t:=weights R s h J r g Ψ
        let S:=measured R s h v J r m
        let Y:=constellation (C:=R.family) s v r Ψ h m g
        let ok:=fun k=>Booked R.family N per d (S (α k)) j hj
        Booked R.family N per d Y j hj→
        (S t:Config G (R.family.side N per)→ℂ)=Y ∧
        ∃G₀:Index R s h per→ℂ,
          HasSum (fun k=>if ok k then mFourierCoeff F k•α k else 0) G₀ ∧
          HasSum (fun k=>if ok k then 0 else mFourierCoeff F k•α k) (t-G₀) ∧
          Booked R.family N per d (S G₀) j hj ∧ Booked R.family N per d (S (t-G₀)) j hj ∧
          ∀M:C(Config G (R.family.side N per),ℂ)→ₗ[ℂ]ℂ,
            HasSum (fun k=>if ok k then mFourierCoeff F k*M (corrected R door hj (S (α k))) else 0)
              (M (corrected R door hj (S t))-M (corrected R door hj (S (t-G₀)))):=by
  intro J P
  obtain ⟨F,law,bill,weightsPaid⟩:=WilsonSeparatedOriginalSlabFourierWeights.original R.family b J s r cap Ψ rp cp seen bp fund
  refine ⟨F,law,bill,?_⟩
  intro N per h v g m d j hj door α t S Y ok source
  have scaled:S t=gauge (restricted R (per:=per) s v h J Ψ r g m):=WilsonMacroscopicRichFourierCellBank.field R s h v J r m g Ψ
  have full:(S t:Config G (R.family.side N per)→ℂ)=Y:=by
    rw [scaled,selected R s v h rp Ψ seen g m]
    exact funext (WilsonSeparatedOriginalReplicaExperiments.diagonal R s v h Ψ r g m)
  have donated:HasSum (fun k=>mFourierCoeff F k•α k) t:=allWeights R s h J Ψ weightsPaid g
  refine ⟨full,?_⟩
  exact WilsonMacroscopicRichSignedBookingTester.tested R door hj S α (mFourierCoeff F) t donated (full ▸ source)

end YM.Integration.WilsonMacroscopicRichActualFourierProgram

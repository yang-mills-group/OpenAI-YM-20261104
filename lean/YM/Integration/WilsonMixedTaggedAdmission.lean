import YM.Integration.WilsonMixedTaggedStart
import YM.Integration.WilsonMixedTaggedRide

/-! Both physical starts come from one originally represented fine field.
The adjacent Wilson endpoint supplies the intake in the course entry theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMixedTaggedAdmission
open Function Finset Lattice Wilson RG Marker MergeProof Accent RG05Readout
open RG05Readout.Many RG05Readout.Address Extra.Histories Push GridApprox.Nil Ac
open WilsonMixedTaggedRoster WilsonMixedTaggedOutput
open scoped Classical BigOperators

variable {G:Gauge}{n:Side}{V:Type}[DecidableEq V][Fintype V]{J:Census V}
variable {R:Rep G n} (I:V → Three G n) {o:V → Site n}{w:V → ℝ}{e δ:ℝ}{X:Config G n → Poly J}
local notation "phi" => fun v=>(I v).2.1
local notation "gas" => fun v=>profile R.activities (I v).2.2

theorem original
    (buy:∀Z:Config G n → Poly (census J),
      Served R (fun v=>(liveRow I v).2.1) (fun v=>profile R.activities (liveRow I v).2.2)
        Z (o ∘ Prod.fst) (w ∘ Prod.fst) e 1 →
      MenuBoard R (liveRow I) Z (o ∘ Prod.fst) (w ∘ Prod.fst) e 1)
    (dp:0 < δ) (source:Served R phi gas X o w e δ) :
    ∃Z:Config G n → Poly (census J),
      MenuBoard R (liveRow I) Z (o ∘ Prod.fst) (w ∘ Prod.fst) e 1 ∧
      (∀U,specialize J (δ:ℂ) (Z U)=X U) ∧
      (∀U,specialize J 0 (Z U)=restore R phi gas (0:Support n → Config G n → Poly J) 0 U) := by
  obtain ⟨H,K,here,hH,hK,field⟩:=source
  let Z:=WilsonMixedTaggedStart.lifted (R:=R) phi gas δ H K
  have combined:=WilsonMixedTaggedStart.represented phi gas dp here hH hK
  have regular:(fun v=>(liveRow I v).2.1)=liveRow phi:=by
    funext ⟨v,bit⟩
    cases bit <;> rfl
  have forced:(fun v=>profile R.activities (liveRow I v).2.2)=liveRow gas:=by
    funext ⟨v,bit⟩
    cases bit
    · rfl
    · funext box U
      simp [liveRow,profile,cram]
  refine ⟨Z,buy Z ?_,?_,?_⟩
  · rw [regular,forced]
    exact combined
  · intro U
    exact (WilsonMixedTaggedStart.endpoints phi gas dp here U).1.trans (congrFun field U).symm
  · intro U
    exact (WilsonMixedTaggedStart.endpoints phi gas dp here U).2

end YM.Integration.WilsonMixedTaggedAdmission

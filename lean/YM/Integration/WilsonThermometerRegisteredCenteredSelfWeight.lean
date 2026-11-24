import YM.Integration.WilsonThermometerRegisteredCenteredWallet
import YM.Integration.WilsonThermometerNominatedDeletion

/-! The physical connected pupil can be withdrawn with a uniform fee using just its true means. The independent connected output is a scalar fixed before the earlier Wilson law. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCenteredSelfWeight
open Finset Marker Extra.Trajectories Primitives.GCC.Anchor Comparison.RG02 WilsonFiniteOrdinaryInverse
open WilsonThermometerCenteredAlgebra WilsonThermometerCenteredScalar WilsonThermometerRegisteredSingletonCenter
open Lattice Laurent Exterior Wilson RG Precision Tree Matrix Bloch FormalBulk08 FormalBulk08.Flat
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonCoeffUV.Soil WilsonCoeffUV.Shard WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider PhysicalNext.Repeat.Legato Labels Source Next.Foundations
open WilsonConditionalTaylorWheelConnectedReadout WilsonThermometerCenteredAlgebra
open Extraction Table Spec Climb Trace.Pilot Next.UVStress Next.Rank RG12 RG17 PhysMS
open XSpace XSpace.Normalize XSpace.Rose WilsonPositionThermometerCapStation
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
open WilsonThermometerRegisteredCenteredInvoice

theorem zero_source {G:Gauge} (R:PhysicalNext.Repeat.Legato.Run G) (A:WilsonPositionThermometerCapStation.Group R.family 6)
    {N p:ℕ} (caps:Fin 3→ℕ) (levels:∀j,WilsonOriginalThermometerPalette.levels j<caps j)
    (phase:Fin 3→ℂ→ₗ[ℝ] ℝ) (j:ℕ) (volume:Lattice.Side) (lift:Lattice.Site (R.family.side N p) → Cover)
    (test:Case caps) (x:Fin 3→Lattice.Site (R.family.side N p)):
    Poly.pass (WilsonThermometerNominatedDeletion.filed R A caps levels phase j volume lift test (fun _ _=>0) x)=(1:Poly J):=by
  have empty:WilsonThermometerNominatedDeletion.filed R A caps levels phase j volume lift test (fun _ _=>0) x=0:=by
    apply Marker.Poly.ext;intro s
    change (0:_→ₗ[ℝ] ℂ) _=0
    rfl
  rw [empty,Extra.Trajectories.pass_zero]

theorem price (w:Fin 3→ℝ) (pos:∀v,0<w v) (F:Poly J) {S:ℝ} (means:∀v,w v*‖read F {v}‖≤S):
    restoration w F 1≤2*(1+3*S+2*S^2):=by
  have qu:(1:Poly J).part (J).quiet=1:=by rw [Poly.one_part,if_pos rfl]
  have inv:inverseMass (1:Poly J)=1:=by simpa only [one_mul] using right_inverse qu
  have shifted(v):w v*‖WilsonThermometerRegisteredSingletonCenter.shift F (1:Poly J) v‖≤S:=by
    have reserved:face {v}≠(J).quiet:=by fin_cases v <;> decide
    have mute:read (1:Poly J) {v}=0:=by change (1:Poly J).part (face {v})=0;rw [Poly.one_part,if_neg reserved]
    simpa only [WilsonThermometerRegisteredSingletonCenter.shift,mute,sub_zero] using means v
  let T:=invoice F 1
  have quiet:T.part (J).quiet=1:=invoice_unit F 1 qu
  have fare:Poly.price w T≤1+3*S+2*S^2:=by
    dsimp only [T,invoice]
    rw [inv,one_mul]
    exact WilsonThermometerRegisteredCenteredWallet.correction_price w pos _ S shifted
  let f:=fun s:(J).Mode=>Poly.toll w s*‖T.part s‖
  let proper:=Finset.univ.filter fun s:(J).Mode=>s≠WilsonThermometerCenteredAlgebra.full ∧ s≠(J).quiet
  have fee₀:f (J).quiet=1:=by
    dsimp only [f];rw [quiet,norm_one,mul_one]
    change (∏i ∈ (∅:Finset (Fin 3)),w i)=1
    rw [Finset.prod_empty]
  have outside:(J).quiet∉proper:=by simp [proper]
  have fits:insert (J).quiet proper⊆Finset.univ:=fun _ _=>Finset.mem_univ _
  have spent:1+∑s∈proper,f s≤Poly.price w T:=by
    rw [←fee₀,←Finset.sum_insert outside]
    exact Finset.sum_le_sum_of_subset_of_nonneg fits (fun s _ _=>mul_nonneg (Poly.worth pos _).le (norm_nonneg _))
  rw [charge w F 1 qu]
  change 2*(1+∑s∈proper,f s)≤_
  exact mul_le_mul_of_nonneg_left (spent.trans fare) (by norm_num)

end YM.Integration.WilsonThermometerRegisteredCenteredSelfWeight

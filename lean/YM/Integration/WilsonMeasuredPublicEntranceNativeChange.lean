import YM.Integration.WilsonMeasuredPublicEntranceNativeAppointment

/-! The true home-coordinate change and its inverse on the full two-home scale window. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeChange
open Function Set Filter Table Spec Climb Spin Trace Trace.Pilot Next.UVStress
open MergeProof.East Next.Rank Next.Rank.East Maxwell PhysMS PhysMS.Frame
open scoped Topology ContDiff Classical BigOperators

open WilsonPositionThermometerOrientedStation WilsonPositionThermometerCapStation
open WilsonPhysicalWeakWheelOffers
open WilsonPhysicalWeakWallBounded (atBasis slot head cost)
open Trace.Terrace Trace.Over FVA2 FVA2.Register
open WilsonMeasuredPublicEntranceNativeStaff
open WilsonMeasuredPublicEntranceNativeLeading WilsonMeasuredPublicEntranceNativeFrame
variable {G:Gauge}{C:Family G}{S:Table C.book}
local notation "D" => Table.Field (Bel C.book)

def change (U J:ℝ→tower S)(r:ℝ)(d:ℕ):D d →L[ℂ] D d:=
  LinearMap.toContinuousLinearMap ((J r d).trans (U r d).symm).toLinearMap

def changeUnit (U J:ℝ→tower S)(r:ℝ)(d:ℕ):(D d →L[ℂ] D d)ˣ where
  val:=change U J r d
  inv:=change J U r d
  val_inv:=by
    ext x
    change (U r d).symm ((J r d) ((J r d).symm ((U r d) x)))=x
    simp
  inv_val:=by
    ext x
    change (J r d).symm ((U r d) ((U r d).symm ((J r d) x)))=x
    simp

theorem directions {U J:ℝ→tower S}(aligned:localCost trail U J)(d:ℕ):
    Tendsto (fun r=>change U J r d) trail (𝓝 1) ∧
    Tendsto (fun r=>change J U r d) trail (𝓝 1):=by
  have forward:Tendsto (fun r=>change U J r d) trail (𝓝 1):=
    Dash.fit_plane (fun r=>((J r d).trans (U r d).symm).toLinearMap) LinearMap.id (aligned d)
  refine ⟨forward,?_⟩
  have inverse (r:ℝ):Ring.inverse (change U J r d)=change J U r d:=
    Ring.inverse_unit (changeUnit U J r d)
  letI : CompleteSpace (D d) := FiniteDimensional.complete ℂ (D d)
  have rear:=NormedRing.inverse_continuousAt (R:=D d →L[ℂ] D d) (1:(D d →L[ℂ] D d)ˣ)
  have step:=rear.tendsto.comp forward
  simpa only [Function.comp_def,inverse,Units.val_one,Ring.inverse_one] using step

private theorem margin {I E:Type*}[SeminormedAddCommGroup E] {l:Filter I}
    (x:I→E)(z:E)(hx:Tendsto x l (𝓝 z)){ε:ℝ}(positive:0<ε):∀ᶠ i in l,‖x i-z‖<ε:=
  (tendsto_iff_norm_sub_tendsto_zero.mp hx).eventually (gt_mem_nhds positive)

theorem window {U J:ℝ→tower S}(aligned:localCost trail U J)(d:ℕ)(ε:ℝ)(positive:0<ε):
    ∀ᶠ r in trail,∀t∈Ioc (0:ℝ) 1,
      (‖change U J r d-1‖<ε ∧ ‖change J U r d-1‖<ε) ∧
      (‖change U J (t*r) d-1‖<ε ∧ ‖change J U (t*r) d-1‖<ε):=by
  obtain ⟨front,back⟩:=directions aligned d
  have sale:∀ᶠ r in trail,‖change U J r d-1‖<ε ∧ ‖change J U r d-1‖<ε:=by
    have f₁:=margin (fun r=>change U J r d) (1:D d →L[ℂ] D d) front positive
    have f₂:=margin (fun r=>change J U r d) (1:D d →L[ℂ] D d) back positive
    exact f₁.and f₂
  obtain ⟨b,pos,paid⟩:=mem_nhdsGT_iff_exists_Ioc_subset.mp sale
  filter_upwards [Ioc_mem_nhdsGT pos] with r hr
  intro t ht
  exact ⟨paid hr,paid ⟨mul_pos ht.1 hr.1,(mul_le_of_le_one_left hr.1.le ht.2).trans hr.2⟩⟩

theorem physical (U J:ℝ→tower S)(d:ℕ)(r t:ℝ)(pos:0<t)(v:D d):
    Frame.cocycle d J r t pos v=(Pert.Scale.gearIso C.labels d t pos).symm
      (change J U r d ((U r d).symm (U (t*r) d (change U J (t*r) d v)))):=by
  simp [Frame.cocycle,change]

end YM.Integration.WilsonMeasuredPublicEntranceNativeChange
end

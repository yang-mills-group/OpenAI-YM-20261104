import YM.Integration.WilsonMeasuredSignedActionFitted
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionUnit
open Function Filter Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato MergeProof Campaign
open WilsonOriginalNullPlacedGermMap WilsonOriginalMicroscopicGuardedReporters
open WilsonMeasuredSignedActionCourse WilsonPositionProgramBlockedTrialVoice
open scoped Classical Topology
variable {G:Gauge}(R:Run G){T:Campaign R}(L:Pillars R T)
local notation "F₀" => R.family.labels.level 4
local notation "C₀" => R.family
local notation "B₀" => R.family.localSection 4
local notation "H₀" => R.family.path
local notation "P₀" => R.family.params

include L in
theorem original (simple:G.Simple):∀ᶠ j:ℕ in atTop,∀{N per n target:ℕ}(live:j+n≤N)
    {η:ℝ}(A:(C₀).label 4 ≃ₗ[ℂ] (C₀).label 4)
    (_home:Opened C₀ 4 j per)
    (_arrived:Arrived R 4 j (j+n) N per target (by omega) live η A
      (A (unitVec F₀ H₀ (j+n)))),
    A (unitVec F₀ H₀ (j+n))=unitVec F₀ H₀ j:=by
  filter_upwards [WilsonMeasuredSignedActionFitted.original R L simple] with j returned
  intro N per n target live η A home arrived
  let I:=denomination F₀ H₀ N (j+n)
  let v:=unitVec F₀ H₀ N
  let w:=unitVec F₀ H₀ (j+n)
  have top:Heard B₀ H₀ N per P₀ (j+n) (trial F₀ H₀ N per (j+n)):=
    enrolled R.makes.wilson (R.makes.sections 4) live
  have born:I v=w:=top.unit
  have inv:I.symm w=v:=I.symm_apply_eq.mpr born.symm
  obtain ⟨Z,hz,_,fields,_,_⟩:=returned live
  have point:=fields w
  change (Z.plays (I.symm w)).density 0 B₀ ((H₀).rep N per j)=_ at point
  rw [inv] at point
  have appointment (k:ℕ)(eq:k=n)(hk:j+k≤N):
      (Z.plays v).density 0 B₀ ((H₀).rep N per j)=
        WilsonPositionProgramOriginalBlockedTrial.carried R 4 (b:=j) (n:=k) (p:=per) hk 0 w:=by
    subst k;exact point
  have seen:=WilsonMeasuredSignedActionFitted.measured R (K:=j+n) (by omega) live arrived home hz v (by
    rw [LinearEquiv.symm_apply_apply];exact appointment _ (by omega) _)
  have actual:Z.index v=unitVec F₀ H₀ j:=hz.unit
  have empty:(F₀).core (F₀).e0=0:=by
    funext i
    by_cases z:i=0 <;> simp [Frame.core,Frame.e0,z]
  have cash:Z.charge v≤0:=by
    have b:=hz.cone v
    rwa [actual,unitVec,map_smul,empty,smul_zero,show (F₀).coeffSize 0=0 from by simp [Frame.coeffSize],mul_zero] at b
  obtain ⟨a,b,ha,hb,paid,_⟩:=(hz.earns v).2
  have consumed:Z.charge v=0:=le_antisymm cash ((add_nonneg ha hb).trans paid)
  rw [actual,consumed,mul_zero] at seen
  exact sub_eq_zero.mp <| norm_eq_zero.mp <| le_antisymm
    ((Push.Local.norm_le_size F₀ _).trans seen) (norm_nonneg _)

end YM.Integration.WilsonMeasuredSignedActionUnit
end

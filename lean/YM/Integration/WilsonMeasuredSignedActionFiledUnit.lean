import YM.Integration.WilsonMeasuredSignedActionUnit
import YM.Integration.WilsonMeasuredSignedActionBooked
import YM.Integration.WilsonPhysicalFiledSlotLinear
import YM.Integration.WilsonNeutralPhysicalGerm
import YM.Integration.WilsonMeasuredSignedActionWindow

/-! The unit in the positioned field is paid on the same elected weak book
and at the same actual filed germ as the action. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionFiledUnit
open Function Filter Set Finset Extraction Table Spec Climb Maxwell Maxwell.Free Lattice RG Wilson
open Trace Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph Source Labels
open Trace.Over Trace.Terrace Trace.Pilot TraceExtension MergeProof.East Next.Rank Next.UVStress
open PhysicalNext.Repeat.Legato Further.CorrectedLift
open WilsonMeasuredPublicEntranceGridDebit WilsonOriginalTwoFlatPublicBooks
open WilsonPositionThermometerCapStation WilsonOriginalThermometerPalette
open WilsonMeasuredSignedActionCourse WilsonMeasuredSignedActionAverage
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {H:(Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}{Z:Arch R.family}
local notation "C" => R.family
local notation "F₀" => R.family.labels.level 4

theorem measured (j N per:ℕ)(h:Opened C 4 j per)(hj:j≤N):
    fitted R 4 j N per ((C).refUnit 4)=unitVec F₀ (C).path j:=by
  have a:((C).S.a j:ℂ)^4 ≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ((C).S.a_pos j).ne')
  have born:=WilsonNeutralPhysicalGerm.projected R j h hj ((C).refUnit 4)
  rw [WilsonNeutralGradeFourTransport.atDate_unit,WilsonNeutralPhysicalGerm.unit] at born
  have cleared:=congrArg (fun v:(C).label 4=>((C).S.a j:ℂ)^4 • v) born
  simpa only [WilsonMeasuredPublicEntranceGridDebit.fitted,unitVec,smul_smul,mul_inv_cancel₀ a,one_smul] using cleared.symm

theorem source {D T:ℕ}{r:ℝ}(B:Book F (l:=l) H Z D T r)(fits:4≤D)
    (z:ℕ×ℕ)(live:B.W.k<z.1)(v:S.Field 4)(s:ℝ)(c:ℂ):
    let i:Fin (D+1):=⟨4,Nat.lt_succ_of_le fits⟩
    (B.V i).symm v=(s:ℂ) • stepField C+c • (Bel (C).book).unit 4 →
    ((B.rows i).arm true v).source z=
      (s:ℂ) • ((B.rows i).arm true (B.V i (stepField C))).source z+c • (C).refUnit 4:=by
  intro i ray
  let k:Fin (B.k+1):=⟨i.val,Nat.lt_succ_of_le ((Nat.le_of_lt_succ i.isLt).trans B.fits)⟩
  let L:=B.W.wheel.atCut z k
  have bare:L ((Bel (C).book).unit 4)=(C).refUnit 4:=by
    change Next.Rank.East.ladd _ _ _ _ _ _ _ (ladder _ _ _) = _
    rw [ladder_unit]
    exact Next.Rank.East.pure_start R.makes (B.checked.early k) (Nat.le_of_lt live) _
      _ (((B.checked.rate _ _ live).1 k).1)
  have y:((B.rows i).arm true v).source z=L ((B.V i).symm v):=(B.rows i).weak _ z
  have x:((B.rows i).arm true (B.V i (stepField C))).source z=L (stepField C):=by
    simpa only [L,LinearEquiv.symm_apply_apply] using (B.rows i).weak (B.V i (stepField C)) z
  rw [y,x,ray,L.map_add,L.map_smul,L.map_smul,bare]

theorem deposited {j N per:ℕ}(h:Opened C 4 j per)(hj:j≤N)
    (v u:(C).label 4)(s:ℝ)(c:ℂ)(e:v=(s:ℂ) • u+c • (C).refUnit 4):
    fitted R 4 j N per v=(s:ℂ) • fitted R 4 j N per u+c • unitVec F₀ (C).path j:=by
  let L:=WilsonPhysicalFiledSlotLinear.measured R 4 N per j h.post hj
  change L v=(s:ℂ) • L u+c • _
  have raw:L ((C).refUnit 4)=unitVec F₀ (C).path j:=measured R j N per h hj
  rw [e,L.map_add,L.map_smul,L.map_smul,raw]

theorem voted {j K:ℕ}(A:(C).label 4 ≃ₗ[ℂ] (C).label 4)
    (actual:A (unitVec F₀ (C).path K)=unitVec F₀ (C).path j)
    (v e:(C).label 4)(s k:ℝ)(c:ℂ)(hs:0 ≤ s) (hk:0 ≤ k)
    (stored:v=(s:ℂ) • e+c • unitVec F₀ (C).path j)
    (action:(F₀).core (pool F₀ (A.symm e))=(k:ℂ) • axis F₀):
    ∃z:ℝ,0≤z ∧ (F₀).core (pool F₀ (A.symm v))=(z:ℂ) • axis F₀:=by
  have unit:(F₀).core (unitVec F₀ (C).path K)=0:=by
    rw [unitVec,map_smul]
    suffices (F₀).core (F₀).e0=0 by rw [this,smul_zero]
    funext i
    by_cases iz:i=0 <;> simp [Frame.core,Frame.e0,Function.update,iz]
  have h:A.symm (unitVec F₀ (C).path j)=unitVec F₀ (C).path K:=A.symm_apply_eq.mpr actual.symm
  refine ⟨s*k,mul_nonneg hs hk,?_⟩
  rw [WilsonMeasuredSignedActionAverage.core] at action ⊢
  rw [stored,A.symm.map_add,A.symm.map_smul,A.symm.map_smul,h,map_add,map_smul,map_smul,
    unit,smul_zero,add_zero,WilsonMeasuredSignedActionWindow.scale,action,smul_smul,Complex.ofReal_mul]

end YM.Integration.WilsonMeasuredSignedActionFiledUnit
end

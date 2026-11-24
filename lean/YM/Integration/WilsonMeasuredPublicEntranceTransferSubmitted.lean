import YM.Integration.WilsonMeasuredPublicEntranceTransferFiled
import YM.Integration.WilsonMeasuredPublicEntranceCellWords
import YM.Integration.WilsonOriginalPublicTrialPhaseTrace

/-! The unscaled K entry compared on the genuine two-ear docket has a direct
all-site capital from the very same master fit, including its orientation. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferSubmitted
open Function Set Filter MeasureTheory Lattice RG Wilson Cells Labels Source Extra.Histories
open PhysicalNext.Repeat.Legato Push.GridApprox OPE.Strobe OPE.Therm
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceTransferWord (field price)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ)
variable {N p f K req pow t:ℕ}{up:f≤K}{live:K≤N}{B:ℝ}
local notation "C₀" => R.family
local notation "H" i:max => R.family.path.levels.clock.hatBeta i
local notation "n₀" => R.family.side K p
variable (A:Panel R d N p f K up live req pow t B)
def vector (i:Fin n):(C₀).label (d i):=
  (((C₀).S.a K:ℂ)^(d i))⁻¹ • Motion.patch ((C₀).labels.level (d i))
    (A.turn i) ((A.axis i).symm (fitted R (d i) (A.slot i) N p (A.names i)))

theorem wage (i:Fin n):((C₀).labels.level (d i)).coeffSize (vector R d A i)≤B*(H K)^pow:=by
  obtain ⟨a,_,aw,ab,as₀,_,_,quoted⟩:=WilsonReflectedMixedMasterAxes.placed R (A.fixed i)
    (A.turn i).1 (A.turn i).2 (A.loc i)
  have bound:=quoted 1 zero_le_one le_rfl
  rw [WilsonReflectedPublicGuardedMotion.coords,as₀,ab,aw,Prod.mk.eta] at bound
  refine (show ((C₀).labels.level (d i)).coeffSize (vector R d A i)≤_ from ?_).trans
    (show Motion.orbitCost ((C₀).labels.level (d i))*(A.tuition*(H K)^pow)≤_ from ?_)
  · simpa only [vector,Complex.ofReal_one,one_mul] using bound
  · rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (A.priced i) (pow_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed K).le) _)

theorem original (file:Filed R d K)(station:A.slot=file.station)(axes:A.axis=file.A N p)(s:(Stock.census (Fin n)).Mode):
    WilsonMeasuredPublicEntranceCellWords.submitted R d (N:=N) file up A.names A.turn A.loc s=
      field (N:=N) R d (vector R d A) (fun i=>((C₀).S.toDepth up p).embed (A.loc i)) s.val:=by
  unfold WilsonMeasuredPublicEntranceCellWords.submitted
  rw [←station,←axes]
  rfl

theorem capital (s:Finset (Fin n))(bp:0≤B):
    2*price (N:=N) (p:=p) (K:=K) R d (vector R d A) s≤
      WilsonAddressedFiniteGuardCapital.price R d B s*(H K)^(WilsonAddressedFiniteGuardCapital.power R d pow s):=
  WilsonMeasuredPublicEntranceTransferWord.cash R d (vector R d A) s live bp pow (wage R d A)

theorem density (s:Finset (Fin n))(place:Fin n→Site n₀):
    field (N:=N) R d (vector R d A) place s=
      WilsonOriginalPublicTrialPhaseTrace.word R (N:=N) (fun i:↥s=>d i.val)
        (fun i=>place i.val) (fun i=>vector R d A i.val):=by
  funext U
  exact (Finset.prod_attach s (fun i=>WilsonPositionProgramBlockedTrialAddBack.uncut R (d i) N p K (place i) (vector R d A i) U)).symm

end YM.Integration.WilsonMeasuredPublicEntranceTransferSubmitted
end

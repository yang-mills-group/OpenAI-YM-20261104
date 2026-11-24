import YM.Integration.WilsonMeasuredPublicEntranceTransferWord
import YM.Integration.WilsonMeasuredPublicEntrancePanel

/-! The actual appointed inverses, orientations and compensated K coordinates
of the original public panel pay the unrestricted field on every K-site. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferFiled
open Function Set Filter MeasureTheory Lattice RG Wilson Cells Labels Source Extra.Histories
open PhysicalNext.Repeat.Legato Push.GridApprox OPE.Strobe OPE.Therm
open WilsonMeasuredPublicEntrancePanel (Panel charged Guard)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonMeasuredPublicEntranceTransferWord (field price)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V](d:V→ℕ)
variable {N p f K requested power t:ℕ}{up:f≤K}{live:K≤N}{B:ℝ}
local notation "C₀" => R.family
local notation "H" i:max => R.family.path.levels.clock.hatBeta i
local notation "n₀" => (C₀).side K p
variable (A:Panel R d N p f K up live requested power t B)
def vector (i:V):(C₀).label (d i):=
  ((charged R d A i:ℂ)*(((C₀).S.a K:ℂ)^(d i))⁻¹) • Motion.patch ((C₀).labels.level (d i))
    (A.turn i) ((A.axis i).symm (fitted R (d i) (A.slot i) N p (A.names i)))

theorem wage (i:V):((C₀).labels.level (d i)).coeffSize (vector R d A i)≤B*(H K)^power:=by
  obtain ⟨a,_,aw,ab,as₀,_,_,quoted⟩:=WilsonReflectedMixedMasterAxes.placed R (A.fixed i)
    (A.turn i).1 (A.turn i).2 (A.loc i)
  have pos:0≤charged R d A i:=(WilsonReflectedPublicCommonDose.positive ..).le
  have shrink:charged R d A i≤1:=(WilsonReflectedPublicCommonDose.smaller _ _ _ (le_max_left ..)).1
  have bound:=quoted (charged R d A i) pos shrink
  rw [WilsonReflectedPublicGuardedMotion.coords,as₀,ab,aw,Prod.mk.eta] at bound
  refine bound.trans ?_
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right (A.priced i) (pow_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed K).le) _)

theorem original (s:(Stock.census V).Mode):
    Guard R d A s=field (N:=N) R d (vector R d A) (fun i=>((C₀).S.toDepth up p).embed (A.loc i)) s.val:=by
  unfold Guard
  rw [(WilsonAddressedFiniteGuardTrial.original R d live _ _ _ _ _).1]
  funext U
  apply Finset.prod_congr rfl
  intro i _
  apply congrArg (fun v=>
    WilsonPositionProgramBlockedTrialAddBack.uncut R (d i) N p K (((C₀).S.toDepth up p).embed (A.loc i)) v U)
  simp only [WilsonAddressedFiniteGuardTrial.submitted,WilsonOriginalAlternativeFiniteSource.fired,one_mul,vector]

theorem capital (s:Finset V)(bp:0≤B):
    2*price (N:=N) (p:=p) (K:=K) R d (vector R d A) s≤
      WilsonAddressedFiniteGuardCapital.price R d B s*(H K)^(WilsonAddressedFiniteGuardCapital.power R d power s):=
  WilsonMeasuredPublicEntranceTransferWord.cash R d (vector R d A) s live bp power (wage R d A)

end YM.Integration.WilsonMeasuredPublicEntranceTransferFiled
end

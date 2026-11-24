import YM.Integration.WilsonOriginalMicroscopicEntranceReader
import YM.Integration.WilsonOriginalMicroscopicEntranceEarlier
import YM.Integration.WilsonOriginalMicroscopicGuardedTrial
import YM.Integration.WilsonOriginalAlternativeBarePorts
import YM.Integration.WilsonReceivedCanonicalSocketPost

/-! The jointly born physical offer and the prescribed finite canonical trial have
their actual normalized coordinates on the same unaliased Wilson history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceFiling
open Function Finset MeasureTheory Lattice Wilson RG Source Labels Marker Push
open Extra.Histories Extra.Trajectories RG05Readout.Records MergeProof MergeProof.Accent MergeProof.East MergeProof.Replicums
open RG05Readout OPE.Therm PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonOriginalMicroscopicEntranceDeposits (funded)
open WilsonOriginalMicroscopicEntranceEarlier (face salary)
open WilsonOriginalMicroscopicGuardedTrial (guarded raw cap)
open WilsonOriginalThermometerPalette (probe)
open WilsonReceivedCanonicalSocketPost (lit)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)
local notation "J" => Stock.census (Fin 3)
variable (d:Fin 3→ℕ){N p K:ℕ}
local notation "X" i:max => Config G (R.family.side i p)

def units (K:ℕ)(s:(J).Mode):ℂ:=∏a∈s.val,(((R.family.S.a K:ℝ):ℂ)^(d a))⁻¹

def print (B:Fin 3→X K→ℂ)(U:X K):Poly (J):=
  fun s=>(R.family.path.rep N p K).eval U • (units R d K s*face B s U)

theorem bill (live:K≤N)(B:Fin 3→X K→ℂ)(paid:∀a,funded (B a)):
    Integrable (print R d (N:=N) B) (prior G _):=by
  apply integrable_pi_iff.mpr
  intro s
  obtain ⟨meas,M,cap⟩:=salary B paid s
  have source:Integrable (fun U=>(R.family.path.rep N p K).eval U • face B s U) (prior G _):=by
    have seen:=actualTransport_weighted_integrable R.family R.makes live meas.aestronglyMeasurable cap (le_rfl:K≤K)
    simpa only [actualTransport_base R.family R.makes live] using seen
  apply (source.const_mul (units R d K s)).congr
  exact Filter.Eventually.of_forall fun U=>by change _=(_ :ℝ) • (_*_);simp only [Complex.real_smul];ring

theorem supplied (o:Fin 3→Site (R.family.side K p))(v:∀a:Fin 3,R.family.label (d a))(a:Fin 3):
    funded (guarded R d N p K o v a) ∧ funded (raw R d N p K o v a):=by
  obtain ⟨hm,hr,h⟩:=WilsonOriginalMicroscopicGuardedTrial.unary R d N p K o v a
  exact ⟨⟨hm,cap R d N p K v a,fun U=>(h U).1⟩,⟨hr,cap R d N p K v a,fun U=>(h U).2⟩⟩

variable (Y:∀a:Fin 3,R.family.book.Ref (d a))(o:Fin 3→Site (R.family.side N p))
local notation "Z" => WilsonOriginalAlternativeBarePorts.offer R d N p Y o lit

theorem original (live:K≤N)(B:Fin 3→X K→ℂ)(paid:∀a,funded (B a)){u:ℕ}(step:u≤K)(s:(J).Mode)(W:X u):
    WilsonOriginalJointTrialHearing.read R N p W step
      (gust R.family.path N p N Z K live-print R d (N:=N) B) s=
      actualTransport R.family (N:=N) (fun U=>∏a∈s.val,R.family.O N p (Y a) (o a) U) (step.trans live) W-
      actualTransport R.family (N:=N) (fun U=>units R d K s*face B s U) step W:=by
  have upper:=WilsonOriginalAlternativeBarePorts.paid R d N p Y o lit (le_rfl:N≤N)
  rw [gust_base] at upper
  apply WilsonOriginalMicroscopicEntranceReader.original R live step _ _ s upper (bill R d live B paid) _ _
  · intro U
    unfold WilsonOriginalAlternativeBarePorts.offer birth Mach
    rw [Poly.part_smul,pass_fire,Complex.real_smul]
    simp only [probe,lit,one_mul]
  · intro U;rfl

end YM.Integration.WilsonOriginalMicroscopicEntranceFiling
end

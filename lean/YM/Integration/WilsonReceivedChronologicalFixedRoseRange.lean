import YM.Integration.WilsonReceivedChronologicalReadout
import YM.Integration.WilsonReceivedChronologicalLedger
import YM.Integration.WilsonOriginalTwoFlatTelescope
/-! The two endpoint transfers and change of receiver are separated from the earned, signed interior of each original socket. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseRange
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Legato
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonThermometerUnitFilingFlatTelescope (numerator feeAt)
open WilsonOriginalJointTrialHearing (fee)
open WilsonReceivedChronologicalLedger (stop)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N per:ℕ}{V:Type}[Fintype V][DecidableEq V]{J:Census V}
local notation "X" j:max => Config G (R.family.side j per)
variable (rows:(j:ℕ) → Config G (R.family.side j per) → Marker.Poly J)(s:J.Mode)



theorem interval {z c K:ℕ}(zc:z ≤ c)(ck:c ≤ K)(kn:K ≤ N)
    (paid:∀j,c ≤ j → j ≤ K → Integrable (rows j) (prior G _)):
    reading R (N:=N) ((fun U=>(rows K U).part s)) z (zc.trans ck)-
      reading R (N:=N) ((fun U=>(rows c U).part s)) z zc=
        ∑j∈Ico c K,fee R N per (1:X z) rows j s:=by
  let M:=WilsonReceivedChronologicalReadout.face R N per rows s
  have den (j:ℕ)(jk:j≤K):numerator R N per j (M j)=(fun U=>(rows j U).part s):=
    WilsonReceivedChronologicalReadout.density R N per rows s (jk.trans kn)
  have h:=WilsonOriginalTwoFlatTelescope.interval R zc ck kn M
    (fun j cj jk=>by rw [den j jk];exact ((Poly.get s).restrictScalars ℝ).integrable_comp (paid j cj jk))
  rw [den K le_rfl,den c ck] at h
  refine h.trans (sum_congr rfl ?_)
  intro j hj
  obtain ⟨cj,jk⟩:=mem_Ico.mp hj
  exact WilsonReceivedChronologicalReadout.original R N per rows s (zc.trans cj) (jk.trans_le kn)
    (paid (j+1) (cj.trans (Nat.le_succ _)) jk) (paid j cj jk.le)

private theorem endpoints (F:ℕ → ℂ){b K:ℕ}(hb:b+2≤K):
    ∑i∈Ico b K,F i=F b+(∑j∈Ico b (K-2),F (j+1))+F (K-1):=by
  induction K,hb using Nat.le_induction with
  | base =>
    rw [Finset.sum_Ico_succ_top (show b≤b+1 by omega),Finset.sum_Ico_succ_top (show b≤b from le_rfl)]
    simp
  | succ k h ih =>
    have one:k+1-2=(k-2)+1:=by omega
    have two:k+1-1=k:=by omega
    have middle:k-2+1=k-1:=by omega
    rw [Finset.sum_Ico_succ_top (show b≤k by omega),ih,one,two,Finset.sum_Ico_succ_top (show b≤k-2 by omega),middle]
    ring

theorem original {u b c K:ℕ}(ub:u≤b)(bc:b<c)(ck:c<K)(live:K≤N)
    (paid:∀j,b ≤ j → j ≤ K → Integrable (rows j) (prior G _)):
    reading R (N:=N) ((fun U=>(rows K U).part s)) u ((ub.trans bc.le).trans ck.le)-
      reading R (N:=N) ((fun U=>(rows b U).part s)) b le_rfl =
      (reading R (N:=N) ((fun U=>(rows c U).part s)) u (ub.trans bc.le)-
        reading R (N:=N) ((fun U=>(rows c U).part s)) b bc.le) +
      fee R N per (1:X b) rows b s +
      (∑j∈Ico b (K-2),fee R N per (1:X (stop u b c j)) rows (j+1) s)+
      fee R N per (1:X u) rows (K-1) s:=by
  let F:=fun j:ℕ=>if c≤j then fee R N per (1:X u) rows j s else fee R N per (1:X b) rows j s
  have high:=interval R rows s (ub.trans bc.le) ck.le live (fun j cj jk=>paid j (bc.le.trans cj) jk)
  have low:=interval R rows s le_rfl bc.le (ck.le.trans live) (fun j bj jc=>paid j bj (jc.trans ck.le))
  have joint:(∑j∈Ico c K,fee R N per (1:X u) rows j s)+(∑j∈Ico b c,fee R N per (1:X b) rows j s)=
      ∑j∈Ico b K,F j:=WilsonReceivedChronologicalLedger.combine bc.le ck.le _ _
  have same:(∑j∈Ico b (K-2),F (j+1))=∑j∈Ico b (K-2),fee R N per (1:X (stop u b c j)) rows (j+1) s:=by
    refine sum_congr rfl fun j _=>?_
    dsimp only [F]
    by_cases test:c≤j+1
    · rw [if_pos test,show WilsonReceivedChronologicalLedger.stop u b c j=u from if_pos test]
    · rw [if_neg test,show WilsonReceivedChronologicalLedger.stop u b c j=b from if_neg test]
  rw [endpoints F (by omega),same,show F b=fee R N per (1:X b) rows b s from if_neg (Nat.not_le.mpr bc),
    show F (K-1)=fee R N per (1:X u) rows (K-1) s from if_pos (by omega)] at joint
  linear_combination high+low+joint

end YM.Integration.WilsonReceivedChronologicalFixedRoseRange
end

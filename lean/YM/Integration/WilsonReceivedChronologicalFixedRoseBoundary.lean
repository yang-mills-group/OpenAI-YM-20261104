import YM.Integration.WilsonReceivedChronologicalFixedRoseRange

/-! Signed cutoff sockets at their original two observation dates, with the two boundary transfers and capture switch retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseBoundary
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Legato
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonOriginalJointTrialHearing (fee)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V]{J:Census V}
  {N per u b c K:ℕ}
variable (rows:(j:ℕ) → Config G (R.family.side j per) → Marker.Poly J)(s:J.Mode)

def lower (ub:u≤b)(bc:b<c):ℂ:=
  reading R (N:=N) (fun U=>(rows b U).part s) b le_rfl+
  (reading R (N:=N) (fun U=>(rows c U).part s) u (ub.trans bc.le)-
   reading R (N:=N) (fun U=>(rows c U).part s) b bc.le)+
  fee R N per (1:Config G (R.family.side b per)) rows b s+
  fee R N per (1:Config G (R.family.side u per)) rows (K-1) s

def interior:ℂ:=∑j∈Ico b (K-2),
  fee R N per (1:Config G (R.family.side (WilsonReceivedChronologicalLedger.stop u b c j) per)) rows (j+1) s

theorem split (ub:u≤b)(bc:b<c)(ck:c<K)(live:K≤N)
    (paid:∀j,b≤j  →  j≤K  →  Integrable (rows j) (prior G _)):
    reading R (N:=N) (fun U=>(rows K U).part s) u ((ub.trans bc.le).trans ck.le)=
      lower R (N:=N) (K:=K) rows s ub bc+interior R (N:=N) (u:=u) (b:=b) (c:=c) (K:=K) rows s:=by
  unfold lower interior
  linear_combination WilsonReceivedChronologicalFixedRoseRange.original R rows s ub bc ck live paid

variable {Q:Type}[Fintype Q](bank:Q → (j:ℕ) → Config G (R.family.side j per) → Marker.Poly J)
  (amount:Q → ℂ)

theorem original (ub:u≤b)(bc:b<c)(ck:c<K)(live:K≤N)
    (paid:∀q j,b≤j  →  j≤K  →  Integrable (bank q j) (prior G _))(originalRead:ℂ):
    originalRead-(∑q,amount q*lower R (N:=N) (K:=K) (bank q) s ub bc)=
      (originalRead-∑q,amount q*reading R (N:=N) (fun U=>(bank q K U).part s) u ((ub.trans bc.le).trans ck.le))+
      ∑q,amount q*interior R (N:=N) (u:=u) (b:=b) (c:=c) (K:=K) (bank q) s:=by
  simp_rw [split R _ s ub bc ck live (paid _),mul_add]
  rw [Finset.sum_add_distrib]
  ring

theorem charged (ub:u≤b)(bc:b<c)(ck:c<K)(live:K≤N)
    (paid:∀q j,b≤j  →  j≤K  →  Integrable (bank q j) (prior G _))(originalRead:ℂ)
    {arrival rent:ℝ}
    (entered:‖originalRead-∑q,amount q*reading R (N:=N) (fun U=>(bank q K U).part s) u ((ub.trans bc.le).trans ck.le)‖≤arrival)
    (earned:‖∑q,amount q*interior R (N:=N) (u:=u) (b:=b) (c:=c) (K:=K) (bank q) s‖≤rent):
    ‖originalRead-∑q,amount q*lower R (N:=N) (K:=K) (bank q) s ub bc‖≤arrival+rent:=by
  rw [original R s bank amount ub bc ck live paid originalRead]
  exact (norm_add_le _ _).trans (add_le_add entered earned)

end YM.Integration.WilsonReceivedChronologicalFixedRoseBoundary
end

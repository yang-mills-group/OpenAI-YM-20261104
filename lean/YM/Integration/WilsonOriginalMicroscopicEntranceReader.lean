import YM.Integration.WilsonOriginalJointTrialHearing
import YM.Integration.ActualWilsonAbsoluteTransport
import YM.RG05Readout.Records.Packet

/-! The physical corridor's entrance uses the original older divisor once.
Both submitted full tables retain their own true quiet and every proper face. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceReader
open Function Finset MeasureTheory Lattice Wilson RG OPE.Therm Source Labels Marker Push
open Extra.Histories Extra.Trajectories RG05Readout.Records MergeProof MergeProof.Accent
open PhysicalNext PhysicalNext.Repeat Legato
open WilsonOriginalJointTrialHearing (read)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N p:ℕ}{V:Type}[DecidableEq V]{J:Census V}
local notation "X" i:max => Config G (R.family.side i p)

theorem row {u k:ℕ}(step:u ≤ k)(Z:X k → Poly J)(s:J.Mode)(paid:Integrable Z (prior G _)):
    (fun U=>(gust R.family.path N p k Z u step U).part s)=
      gust R.family.path N p k (fun U=>(Z U).part s) u step:=by
  induction step using Nat.decreasingInduction with
  | self => rw [gust_base];simp_rw [gust_base]
  | of_succ i hi ih =>
    simp_rw [gust_step _ _ _ _ _ hi]
    exact (push_get (R.family.path.levels.transition_mass ..) (gust_live R.family.path N p k _ paid hi) s).trans (by rw [ih])

theorem normalized {u k:ℕ}(step:u ≤ k)(Z:X k → Poly J)(s:J.Mode)(paid:Integrable Z (prior G _))
    (H:X k → ℂ)(source:∀U,(Z U).part s=(R.family.path.rep N p k).eval U • H U)(W:X u):
    read R N p W step Z s=actualTransport R.family (N:=N) H step W:=by
  unfold WilsonOriginalJointTrialHearing.read actualTransport
  rw [congrFun (row (N:=N) R step Z s paid) W,show (fun U=>(Z U).part s)=_ from funext source]
  rw [Complex.real_smul,Complex.ofReal_inv]

theorem original {u K:ℕ}(live:K ≤ N)(earlier:u ≤ K)(Z:X N → Poly J)(Q:X K → Poly J)
    (s:J.Mode)(pz:Integrable Z (prior G _))(pq:Integrable Q (prior G _))(F:X N → ℂ)(H:X K → ℂ)
    (physical:∀U,(Z U).part s=(R.family.path.rep N p N).eval U • F U)
    (trial:∀U,(Q U).part s=(R.family.path.rep N p K).eval U • H U)(W:X u):
    read R N p W earlier (gust R.family.path N p N Z K live-Q) s=
      actualTransport R.family (N:=N) F (earlier.trans live) W-
        actualTransport R.family (N:=N) H earlier W:=by
  have filed:=gust_live R.family.path N p N Z pz live
  rw [WilsonOriginalJointTrialHearing.difference R N p W earlier _ Q filed pq s,
    normalized R earlier Q s pq H trial W]
  have upper(U:X K):(gust R.family.path N p N Z K live U).part s=
      (R.family.path.rep N p K).eval U • actualTransport R.family (N:=N) F live U:=by
    rw [congrFun (row (N:=N) R live Z s pz) U,show (fun U=>(Z U).part s)=_ from funext physical,
      actualTransport_unnormalize R.family R.makes le_rfl]
  rw [normalized R earlier _ s filed _ upper W,actualTransport_tower R.family R.makes le_rfl]

end YM.Integration.WilsonOriginalMicroscopicEntranceReader
end

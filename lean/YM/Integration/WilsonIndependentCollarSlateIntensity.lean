import YM.Integration.WilsonReceivedDepositedOrbitalPublication

/-! The source expense on an already filed Slate is exactly its original positive
row-height sum. This allows a weak or empty connected source its own intensity
before the actual binder is mounted. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarSlateIntensity
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Mentor
open QuadraticLocal.Affinity QuadraticLocal.Sunrise Push Push.AbsoluteSums Push.Local Paths Animals ConnectedActivityE6
open WilsonOlderFreshGraphSlate WilsonOlderFreshGraphArmada WilsonRegisteredPairUnaryWallet
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:Side}{q d:ℕ}{σ:ℝ}(T:Copy G d q σ)(site:Site n)
local notation "S" => WilsonOlderFreshGraphPointWallet.point site
local notation "M" => T.rows (S) disk

def amount:ℝ:=∑'z:T.Roster,((M) z).height σ

theorem spent (hs:0≤σ):SumBudget (fun z:T.Roster=>((M) z).height σ) (amount T site):=by
  have full:=WilsonOlderFreshGraphVote.before_tests (S) T.roll T.fare σ T.paid T.legal T.positive (value disk) hs
  exact ⟨full.1,full.2.1,le_rfl⟩

theorem original (hs:0≤σ){ord seats shelf:ℕ}(dep:q ≤ ord)(oc:1 ≤ seats)(size:d ≤ shelf):
    Scene.Armada (M) (fun _=>1) (fun _=>d) σ (amount T site) ord seats shelf:=by
  have existsPay:=(WilsonGeneralArityCopyAccount.original T site hs dep oc size).1
  refine ⟨existsPay.toMinistry,fun _=>zero_lt_one,?_,existsPay.purchases,existsPay.honor⟩
  intro x
  exact sumBudget_mono (spent T site hs)
    (fun z=>by split_ifs <;> simp_all [Poly.toll,(spent T site hs).1 z])
    (fun z=>by split_ifs <;> simp_all [Poly.toll,(spent T site hs).1 z]) le_rfl

end YM.Integration.WilsonIndependentCollarSlateIntensity
end

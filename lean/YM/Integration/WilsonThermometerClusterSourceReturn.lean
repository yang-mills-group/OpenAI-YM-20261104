import YM.Integration.WilsonThermometerClusterProjectionPaid

/-! A physical grouped scalar field is filed one original step earlier with its complete regular and forced remainder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerClusterSourceReturn
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi Extra.Trajectories
open ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus MergeProof.Float
open scoped Topology BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] [DecidableEq I]
local notation "A" => R.family.path.levels
local notation "β" => (A).clock.hatBeta
local notation "C" => R.family
local notation "H" => R.family.path

theorem original (simple:G.Simple) (cater:Cater R.family R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A)) (wage:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ m:ℕ in atTop,∀ N p:ℕ,m<N →
      let Υ:=R.family.path.rep N p (m+1)
      let Θ:=R.family.path.rep N p m
      ∀ (X:Config G ((C).side (m+1) p) → Poly (Stock.census I))
        (g:I → Config G ((C).side (m+1) p)→ℂ) (K:I → ℕ → Config G ((C).side (m+1) p)→ℂ)
        (o:I→Site ((C).side (m+1) p)) (w:I→ℝ),
      Served Υ g (fun v=>profile Υ.activities (K v)) X o w Υ.p.supportExponent 1 →
      (∀ v,Dominated (K v) ∧ Blade Υ (o v) (g v) (profile Υ.activities (K v)) 0 (4*(1/w v))) →
      Integrable X (prior G _) → ∀ v,0<w v → ((A).clock.op m p).ratio.parent (o v)=0 →
      ∃ Q:Coefficient ((C).labels.level 0) ((C).side m p),
        Q.Format 0 (C).params Θ ∧ Q.remBound 0 Θ (kappa (H) m) ((β m)^4*(4*(1/w v))) ∧
        ((C).labels.level 0).coeffSize Q.x ≤ (β m)^4*(4*(1/w v)) ∧
        Q.density 0 ((C).localSection 0) Θ =
          ((A).clock.op m p).push Υ.beta (fun U=>(X U).part ((Stock.census I).fire v)) := by
  filter_upwards [WilsonThermometerClusterProjectionPaid.original R simple bank wage] with m billed N p edge
  dsimp only
  intro X g K o w filed leaves live v room home
  let Θ:=(H).rep N p m
  let Υ:=(H).rep N p (m+1)
  have old:=WilsonThermometerClusterProjectionFee.original R simple (p:=p) (d:=0) edge (Nat.zero_le _)
  have pay:Address.Plated ((C).labels.level 0) (H) ((C).localSection 0) (C).params m N p
      (R.doors N p m edge) ((β m)^4):=by
    constructor
    intro x list M h0 belongs own
    have mono:=mul_le_mul_of_nonneg_right billed (show 0≤load M from mul_nonneg (Real.exp_pos _).le M.profit)
    exact (old.buys x list M h0 belongs own).weaken mono mono le_rfl
  let T:Three G ((C).side (m+1) p):=⟨fun U=>(X U).part ((Stock.census I).fire v),g v,K v⟩
  have useful:Useful Υ T:=by
    refine ⟨(leaves v).1,funext fun U=>?_,(Poly.get ((Stock.census I).fire v)).integrable_comp live⟩
    exact ((filed.relay (J:=Stock.census I) (fun i=>(leaves i).1)
      (R.makes.wilson.represents N p (m+1) edge).good.labels U).1 v).symm
  obtain ⟨_,_,course,_⟩:=cater.tiers m N p edge
  obtain ⟨Q,fmt,paid,size,ride⟩:=Address.peppers («C»:=R.family) R.makes pay home edge
    course.publishes.propagate (by positivity) useful (leaves v).2 (by positivity)
  refine ⟨Q,fmt,paid,size,?_⟩
  have delivered:=ride.exactStep
  change Q.density 0 ((C).localSection 0) Θ=(((C).S.block m).val:ℂ)^0 •
    ((A).clock.op m p).push Υ.beta (fun U=>(X U).part ((Stock.census I).fire v)) at delivered
  simpa only [pow_zero,one_smul] using delivered

end YM.Integration.WilsonThermometerClusterSourceReturn
end

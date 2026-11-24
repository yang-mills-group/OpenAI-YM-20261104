import YM.Integration.WilsonLocalCompactCumulants
import YM.Integration.WilsonLocalCompactProgramLaws

/-! The conditional two- and three-point responses of the genuine running
retained action, including the older Wilson history, are controlled by centered
moments on the original Wilson probability law at the same held field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactConnectedHistory
open Filter Finset MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension OPE OPE.Log Trace.Pilot
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLocalCompactHistory WilsonLocalCompactLinearity WilsonLocalCompactProbability
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I] {n:Side}

def pairPrice (P:Signal (G:=G) (n:=n)→ₗ[ℝ]ℝ) (τ:ℝ) (F H:Signal (G:=G) (n:=n)):ℝ:=
  τ*spread P (center P F*center P H)+(τ*spread P F)*(τ*spread P H)

def triplePrice (P:Signal (G:=G) (n:=n)→ₗ[ℝ]ℝ) (τ:ℝ) (F H J:Signal (G:=G) (n:=n)):ℝ:=
  let f:=center P F;let h:=center P H;let j:=center P J
  let cut:=fun X=>τ*spread P X;let cap:=fun X=>|P X|+cut X
  cut (f*h*j)+cut F*cap (h*j)+cut H*cap (f*j)+cut J*cap (f*h)+2*cut F*cut H*cut J

theorem original (R:Run G) (simple:G.Simple) (pace:WilsonWindowReportingPace.Slow R.kit)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (d:I→ℕ) {B:ℕ} (bp:0<B) (q grade:ℕ) (ord:q+7≤grade) {ε:ℝ} (ep:0<ε):
    ∀ᶠr:ℝ in trail,let j:=WilsonCloseCaptureDate.level R.family.S r
    let b:=WilsonMeasuredWindow.stop R.family.path.levels simple B r
    j≤b ∧ ∀k l:ℕ,j≤k→∀live:k≤l,l≤b→∀N:ℕ,b≤N→∀(interior:l<N) per
      (T:∀i,i<l→Forest (R.family.path.levels.clock.op i per).ratio)
      (o:∀i,i<l→I→Site (R.family.side (i+1) per)) u (past:u≤k),
    let K:=fun H:Config G (R.family.side l per)→ℝ=>actualTransport R.family (N:=N) H (past.trans live)
    let M:=fun H=>actualTransport R.family (N:=N) (program R interior grade d T o H live) past
    let τ:=ε*regulatorRun R.family N per b^q
    ∃(trueLaw:Laws K) (retainedLaw:Laws M),∀W,
      let P:=read trueLaw W;let A:=read retainedLaw W
      (∀F H,|covariance A F H-covariance P F H|≤pairPrice P τ F H) ∧
      ∀F H J,|third A F H J-third P F H J|≤triplePrice P τ F H J:=by
  obtain ⟨s,bank⟩:=eventually_atTop.1
    (WilsonLocalCompactProgramLaws.original R simple marks fees pace.2 d grade (by omega))
  filter_upwards [WilsonLocalCompactCenteredSegment.original R simple pace marks fees d bp q grade ord ep,
    (WilsonCloseCaptureDate.height R).grows.eventually_ge_atTop s] with r paid ready
  intro j b
  refine ⟨paid.1,?_⟩
  intro k l jk live lb N bn interior per T o u past K M τ
  have pk:Laws K:=transported R.family R.makes interior.le (past.trans live)
  have mk:Laws M:=after (bank k (ready.trans jk) l live N interior per T o)
    (transported R.family R.makes (live.trans interior.le) past)
  refine ⟨pk,mk,?_⟩
  intro W P A
  have price (F:Signal (G:=G) (n:=R.family.side l per)):|A F-P F|≤τ*spread P F:=by
    have test:((absolute (center P F)).1)=(fun U=>|F.1 U-P F|):=by
      funext U;change |F.1 U-P F*1|=_;rw [mul_one]
    change |M F.1 W-K F.1 W|≤τ*K (absolute (center P F)).1 W
    rw [test]
    exact (paid.2 k l jk live lb N bn interior per T o F.1 F.2.1 F.2.2).2.2.1 u past W (P F)
  exact ⟨WilsonLocalCompactCumulants.two P A (unit pk W) (unit mk W) price,
    WilsonLocalCompactCumulants.three P A (unit pk W) (unit mk W) price⟩

end YM.Integration.WilsonLocalCompactConnectedHistory

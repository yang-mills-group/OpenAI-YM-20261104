import YM.Integration.WilsonLocalCompactMomentRates

/-! Cumulant changes before all cutoffs for the true running Wilson law under separate measured cubic-moment budgets. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactMeasuredMoments
open Filter Finset MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension OPE OPE.Log Trace.Pilot
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLocalCompactHistory WilsonLocalCompactLinearity WilsonLocalCompactProbability
open WilsonLocalCompactMoments WilsonLocalCompactMomentRates
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I] {n:Side}

theorem positive (C:Family G) (makes:C.Makes) {N per k l:ℕ} (cut:l≤N)
    {H:Config G (C.side l per)→ℝ} (hn:∀U,0≤H U) (live:k≤l):
    ∀W,0≤actualTransport C (N:=N) H live W:=by
  induction live using Nat.decreasingInduction with
  | self => rw [actualTransport_base C makes cut];exact hn
  | of_succ i li ih =>
    rw [actualTransport_step C makes cut _ li]
    intro W
    exact integral_nonneg (fun U=>mul_nonneg (actualConditionalDensity_nonneg C makes (li.trans_le cut) W U) (ih U))

theorem budget (P:Signal (G:=G) (n:=n)→ₗ[ℝ]ℝ) (pos:Positive P) (one:P 1=1)
    (F:Signal (G:=G) (n:=n)) (a c:ℝ) (bounded:∀U,|F.1 U-c|≤a):Admitted P F (2*a):=by
  let X:=F-c • 1
  have shrunk:P (absolute X)≤P (a • 1):=mono P pos (fun U=>by
    change |F.1 U-c*1|≤a*1;simp only [mul_one];exact bounded U)
  rw [map_smul,one,smul_eq_mul,mul_one] at shrunk
  have center_bound:|P F-c|≤a:=by
    have h:|P X|≤a:=(signed P pos X).trans shrunk
    simpa only [X,map_sub,map_smul,one,smul_eq_mul,mul_one] using h
  have bill:P ((absolute (center P F))^3)≤P ((2*a)^3 • 1):=mono P pos (fun U=>by
    change |F.1 U-P F*1|^3≤(2*a)^3*1
    simp only [mul_one]
    have triangle:|F.1 U-P F|≤|F.1 U-c|+|P F-c|:=by
      rw [show F.1 U-P F=(F.1 U-c)-(P F-c) by ring];exact abs_sub .. 
    exact pow_le_pow_left₀ (abs_nonneg _) (by linarith only [triangle,bounded U,center_bound]) _)
  simpa only [Admitted,map_smul,one,smul_eq_mul,mul_one] using bill

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
      (∀ F H a b,0<a→0<b→Admitted P F a→Admitted P H b→
        |covariance A F H-covariance P F H|≤(2*τ+τ^2)*a*b) ∧
      ∀F H J a b c,0<a→0<b→0<c→Admitted P F a→Admitted P H b→Admitted P J c→
        |third A F H J-third P F H J|≤(5*τ+6*τ^2+2*τ^3)*a*b*c:=by
  filter_upwards [WilsonLocalCompactConnectedHistory.original R simple pace marks fees d bp q grade ord ep]
    with r bank
  intro j b
  refine ⟨bank.1,?_⟩
  intro k l jk live lb N bn interior per T o u past K M τ
  obtain ⟨trueLaw,retainedLaw,paid⟩:=bank.2 k l jk live lb N bn interior per T o u past
  refine ⟨trueLaw,retainedLaw,?_⟩
  intro W P A
  have tn:0≤τ:=mul_nonneg ep.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
  have p:Positive P:=fun _ h=>positive R.family R.makes interior.le h (past.trans live) W
  exact ⟨fun F H a b ap bp fm hm=>(paid W).1 F H |>.trans (pair P p (unit trueLaw W) F H ap bp tn fm hm),
    fun F H J a b c ap bp cp fm hm jm=>(paid W).2 F H J |>.trans
      (triple P p (unit trueLaw W) F H J ap bp cp tn fm hm jm)⟩

end YM.Integration.WilsonLocalCompactMeasuredMoments

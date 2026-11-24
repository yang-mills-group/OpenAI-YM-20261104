import YM.Integration.WilsonPositionScaleLawGuardDiagonal

/-! The complete homogeneous MS polynomial is uniformly invertible near the original ultraviolet clock. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardNear
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival PowerSeries
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawDressedTransport (guard)
open WilsonPositionScaleLawGuardSheet (atValue)
open WilsonPositionScaleLawGuardInvoice (sheet)
open WilsonPositionScaleLawKinetic (kinetic)
open scoped Topology Classical Asymptotics Polynomial

theorem atZero {A:Type*}[NormedRing A][NormedAlgebra ℂ A](q:ℕ)(a:PowerSeries A):atValue q a 0=coeff 0 a:=by
  induction q with
  | zero=>exact WilsonPositionScaleLawGuardDiagonal.zeroth a 0
  | succ q ih=>rw [WilsonPositionScaleLawGuardQuadratic.nextTerm,ih,zero_pow (by omega : q+1≠0),zero_smul,add_zero]

variable {G:Gauge}(C:Family G)(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
include H in
theorem original (d q:ℕ):∃K:ℝ,0≤K ∧ ∀(t:Ratio)(z:ℂ),‖z‖≤1→‖atValue q (sheet C Z M ν t d).homogeneous z-1‖≤K*‖z‖:=by
  let X:=(Bel C.book).Field d
  letI :NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  let p(t:Ratio):=(sheet C Z M ν t d).homogeneous
  obtain ⟨B,hB,fees⟩:=WilsonPositionScaleLawGuardBanks.bounded q (fun k t=>coeff k (p t)) (WilsonPositionScaleLawGuardBanks.homogeneous C Z M H ν d)
  let K:=((q+1:ℕ):ℝ)*((q:ℝ)*B)
  have hK:0≤K:=by dsimp only [K];positivity
  refine ⟨K,hK,?_⟩;intro t z hz
  let s:=WilsonPositionScaleLawIndependent.time t
  let data:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  have base:Base (guard Z M ν s d):=GroupS.true_N ν Z.scheme Z.criterion M σ hG data.Taylor data.still data.base s
  have root:atValue q (p t) 0=1:=by
    rw [atZero]
    change coeff 0 (WilsonPositionScaleLawGuardLift.pack C (guard Z M ν s d))=1
    rw [WilsonPositionScaleLawGuardLift.pack,PowerSeries.coeff_map,base.zero,map_one]
  have bill:=WilsonPositionScaleLawGuardLipschitz.original q (p t) z 0 hz (by simp)
  change ‖atValue q (p t) z-atValue q (p t) 0‖≤_ at bill
  rw [root,sub_zero] at bill
  exact bill.trans (mul_le_mul_of_nonneg_right (WilsonPositionScaleLawGuardValue.sliding q (p t) hB (fees t)) (norm_nonneg _))

variable {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
include H in
theorem measured (funded:Coupling G (kinetic Z F J))(d q:ℕ):∀ᶠr in trail,∀t:Ratio,
    ‖WilsonPositionScaleLawGuardPhysical.expected F J Z M ν d q r t-1‖≤1/4:=by
  let g:=kinetic Z F J
  obtain ⟨K,hK,fees⟩:=original R.family Z M H ν d q
  have small:Tendsto (fun r=>|g r|) trail (𝓝 0):=by simpa only [abs_zero] using (funded.conforms hG).abs
  have cap:Tendsto (fun r=>K*|g r|) trail (𝓝 0):=by simpa only [mul_zero] using (tendsto_const_nhds (x:=K)).mul small
  filter_upwards [(tendsto_order.mp small).2 1 zero_lt_one,(tendsto_order.mp cap).2 (1/4) (by norm_num)] with r hr hc t
  have hz:‖(g r:ℂ)‖≤1:=by simpa only [Complex.norm_real,Real.norm_eq_abs] using hr.le
  have cost:=fees t (g r:ℂ) hz
  rw [Complex.norm_real,Real.norm_eq_abs] at cost
  exact cost.trans hc.le

end YM.Integration.WilsonPositionScaleLawGuardNear

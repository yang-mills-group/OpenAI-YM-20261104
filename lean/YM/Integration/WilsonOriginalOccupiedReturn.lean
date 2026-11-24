import YM.Integration.WilsonOriginalOccupiedHearing
import YM.Integration.WilsonOriginalOccupiedWallet

/-! Full occupied physical withdrawal under the genuine earlier positive vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedReturn
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedTap WilsonOriginalOccupiedSource WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {N per m k b t:ℕ}
variable {V:Type} [DecidableEq V] [Fintype V] {marks:Marker.Census V}
variable (way:WayStation R.kit) (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (Q:D.Tab R.rolls) (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (ticket:TicketP R.alloy R.kit D Q)
  {X I:Type} [Countable I] [Nonempty X] (o:V → Site (R.family.side t per))
  (A:Gallery X I o (Ψ t) marks)(w:V → ℝ)(wp:∀v,0<w v)

include course ticket way wp in
theorem original (floor:m ≤ b)(top:t ≤ N)(bt:b ≤ t){load:ℕ}
    (stage:∀i,b ≤ i → load ≤ R.alloy.B.a.clock.J i) (load_ok:∀s:marks.Mode,s.val.card ≤ load)
    (cap:∀i,b ≤ i → LocalComparison.forcedDivisor R.family i ≤ 1)

    (s:marks.Mode)(n:ℕ)(np:0<n)(size:s.val.card ≤ n)
    (tiny:WilsonOriginalOccupiedWallet.inverseAmplitude n (LocalComparison.forcedDivisor R.family t) ≤ 1)
    (regular:A.E.Paid w (Ψ t).p.B (Ψ t).p.supportExponent 1)
    (hard:A.K.Paid w (Ψ t).p.B (Ψ t).p.supportExponent (LocalComparison.forcedDivisor R.family t))
    (x:X)(W:Config G (R.family.side b per))(clear:flags (Ψ b).p.threshold W=∅):
    Poly.toll (wallet R w bt) s *
      ‖(((Ψ b).eval W:ℂ)⁻¹)*((gust R.family.path N per t (A.density x) b bt W).part s-
      (gust R.family.path N per t (fun U=>((Ψ t).eval U:ℂ) • Poly.pass (A.E.log x U)) b bt W).part s)‖ ≤
        (WilsonOriginalOccupiedWallet.inverseAmplitude n (LocalComparison.forcedDivisor R.family t)*
          price n)*(shards marks s).card:=by
  let κ:=LocalComparison.forcedDivisor R.family t
  let q:=WilsonOriginalOccupiedWallet.inverseAmplitude n κ
  have kp:0<κ:=Real.sqrt_pos.2 (Real.exp_pos _)
  have qp:0<q:=by dsimp [q,WilsonOriginalOccupiedWallet.inverseAmplitude];positivity
  have fund:=WilsonOriginalOccupiedWallet.enrolled A w wp n np κ kp tiny hard
  have inv:((q⁻¹:ℝ):ℂ)*(q:ℂ)=1:=by exact_mod_cast inv_mul_cancel₀ qp.ne'
  have small:‖(q:ℂ)‖=q:=by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos qp]
  have h:=WilsonOriginalOccupiedHearing.original R way D Q π Γ Ψ course ticket o A w wp floor top bt
    stage load_ok cap s n size (q⁻¹:ℝ) (q:ℂ) inv (small.le.trans tiny) regular fund x W clear
  have erase:=funext fun U=>WilsonOriginalOccupiedWallet.origin A x U w wp (fund 0 (by simp [nodes]))
  rw [erase,small] at h
  exact h

end YM.Integration.WilsonOriginalOccupiedReturn

import YM.Integration.FVA1Physical.Marked.ChartEntry

/-! Rooted ordinary-chart derivatives of the genuine physical repeated-step
conditional reading, with its separately placed microscopic field lamps. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Finset Lattice RG YM.Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.Uniform RGComparison.Core16.Spool
open MSbar MSbar.Midpoint MSbar.Wave MSbar.Rolling
open Next.Foundations Integration.FVA1Physical.Round2.Curvature
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} {I:Type} [Fintype I] {d N n m:ℕ} (R:Run G)
local notation "H" => R.family.path
local notation "RI" => (H).rep N n (m+1)
local notation "RO" => (H).rep N n m
local notation "S" => (H).levels.clock.op m n

theorem current_run_chart (simple:G.Simple) (hm:m<N) (start:R.t 0 ≤ m)
    (a:I → CoverLabel G d) (ready:∀ j,R.t (a j).1.val ≤ m+1)
    (y:Site (R.family.side (m+1) n)) (o:I → Site (R.family.side (m+1) n)) (part:Bool)
    (radius:ℕ) (foot:∀ j,separation (o j-y) 0 ≤ radius) {α g:ℝ} (α0:0≤α)
    (k:ℕ) (base:Positions (Primary (R.family.side m n) G))
    (small:‖g•base‖<1) (clear:palace (g•base)∈Boulevard.sunny (RO).p)
    (order:k≤(RO).p.order) (room:α*k*(6*(RO).p.B+2:ℝ)≤(RO).p.supportExponent) :
    let z:=(S).ratio.parent y
    let v:=fun j=>o j-y
    let φ:=fun U=>look part (tally (freshLamps a) o U)
    let φ₀:=fun U=>look part (tally (freshLamps a) v U)
    let cost:=Doors.rate ((H).S.block m)*birthCost (RI).p (lampSupport a v) ((H).levels.clock.forcedAllowance (m+1))
      (localFieldTariff (RI).p a (R.alloy.B.a.params (m+1)).columns radius+‖(φ₀ 1:ℂ)‖) (2*stencilBound (freshLamps a))
    let F:=fun x=>Bulk.expect S RI (postcard G (R.family.side m n) g x) φ
    ContDiffAt ℝ k F base ∧ ∀ j,0<j → j≤k → ∀ w:Fin j → Primary (R.family.side m n) G,
       ‖YM.Push.Uniform.entry F base w‖ ≤ |g|^j*(earnE (RO).p G k*cost)*
         Real.exp (-α*spanSites (Measuring.chart (R.family.side m n) G) z w) := by
  intro z v φ φ₀ cost F
  obtain ⟨Q,shape,density,paid⟩:=current_run_field R simple hm start a ready y o part radius foot
  have germ:=current_germ H R.makes.wilson hm z φ Q density clear
  exact chart_entry (localSection G 0) shape paid (fun U=>Bulk.expect S RI U φ) small clear germ order α0 room
end YM.Integration.FVA1Physical.Marked

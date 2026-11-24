import YM.Integration.WilsonSingleHardMarginal
import YM.Extra.WILSON_STARTUP.Fast

/-! A finite Wilson descent keeps its whole newly emitted one-marker hard gallery
at every date. Its geometric price is uniform in the length of the earlier interval. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSingleHardRadius
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {N per m k b:ℕ} (way:WayStation R.kit)
   (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
   (ticket:TicketP R.alloy R.kit D Q)
   (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
   (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   {T:Type} [Nonempty T] {J:Census (Fin 1)}
local notation "V" j:max => Config G (R.family.side j per)
local notation "β" j:max => R.alloy.B.a.clock.hatBeta j
local notation "vac" j:max U:max => (R.family.path.rep N per j).eval U
local notation "sector" j:max o:max => Hard T (Ψ j).p (Ψ j).activities.forced (Ψ j).activities.K o J
local notation "fire" => J.fire 0
local notation "shape" j:max => Fin 1→Site (R.family.side j per)

def route (o:shape b) {j:ℕ} (jb:j ≤ b) : shape j :=
  Nat.decreasingInduction (motive:=fun j _=>shape j)
    (fun j _ z=>(R.family.path.levels.clock.op j per).ratio.parent ∘ z) o jb

theorem route_base (o:shape b) : route R o le_rfl=o := Nat.decreasingInduction_self ..

theorem route_step (o:shape b) {j:ℕ} (jb:j<b) : route R o jb.le=
    (R.family.path.levels.clock.op j per).ratio.parent ∘ route R o jb := Nat.decreasingInduction_succ_left ..

variable (o:Fin 1 → Site (R.family.side b per))
    (K:Hard T (Ψ b).p (Ψ b).activities.forced (Ψ b).activities.K o J) {W:ℝ} (Wpos:0<W)
   (bill:K.Paid (fun _=>W) (Ψ b).p.B (Ψ b).p.supportExponent 1)
   (top:b ≤ N) (base:m ≤ b)
local notation "siteOf" q:max => route R o q
local notation "head" t:max => (fun U=>((gallery K).density t U).part fire)
local notation "record" t:max i:max q:max => gust R.family.path N per b (head t) i q
local notation "stand" j:max w:max Z:max => Hard.Paid Z (fun _=>w) (Ψ j).p.B (Ψ j).p.supportExponent 1
local notation "salary" => Time.quoteHard R.alloy.B.a

include way ticket course top base Wpos bill in
/-- The same section and radius work for all probe values and on every held field.
Both the census of mandatory partners and the successive original root are retained. -/
theorem descent (simple:G.Simple) (u:ℕ) (floor:m ≤ u)
    (opened:∀ j,u ≤ j→j<b→salary j R.kit.book (Ψ (j+1)).beta ≤ 1/2)
    {i:ℕ} (ib:i ≤ b) (ui:u ≤ i) :
    ∃ (w:ℝ) (Z:sector i (siteOf ib)), 0<w ∧ stand i w Z ∧
      ∀ t U, ‖(vac i U)⁻¹ • ((record t i ib) U)-
        (vac i U)⁻¹ • ((gallery Z).density t U).part fire‖+2*(β b)/w ≤ 2*(β b)/W := by
  have integrable (t:T):Integrable (head t) (prior G _) :=
    (Poly.get fire).integrable_comp (QuadraticLocal.Tariff.integrable J o (fun _=>W) (fun _=>Wpos)
      (gallery K) t (intake K bill le_rfl) (Ψ b).p.exponent_pos.le
      (course.1.walk b base top).truep.valid)
  refine Nat.decreasingInduction (motive:=fun j jb => u ≤ j →
    ∃ (w:ℝ) (Z:sector j (siteOf jb)), 0<w ∧ stand j w Z ∧
      ∀ t U, ‖(vac j U)⁻¹ • ((record t j jb) U)-
        (vac j U)⁻¹ • ((gallery Z).density t U).part fire‖+2*(β b)/w ≤ 2*(β b)/W) ?_ ?_ ib ui
  · intro j jb ih ui
    obtain ⟨w,Z,wp,paid,prev⟩:=ih (ui.trans j.le_succ)
    have live:j<N:=jb.trans_le top
    have one:1 ≤ R.alloy.B.a.clock.J j:=by have := R.alloy.B.a.clock.adm j; omega
    have large : 1 ≤ β (j+1) := (R.alloy.B.a.fits.delayed _).le
    obtain ⟨I,L,_,good,intg,read⟩ := advance R way D Q ticket π Γ Ψ course (floor.trans ui) live
      (siteOf jb) Z wp paid one large
    have quote:=L.K.mono good (opened j ui jb)
    have enlarged:=raised L.K quote wp (by norm_num:0<(1/2:ℝ)) (by norm_num)
    have costs:stand j (2*w) L.K := by
      convert enlarged using 1
      ext v
      ring
    have beta : β (j+1)  ≤  β b := WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos simple).le jb
    rw [route_step R o jb]
    refine ⟨2*w,L.K,mul_pos (by norm_num) wp,costs,?_⟩
    intro t U
    let z:=2*(β b)/W-2*(β b)/w
    have above (A:V (j+1)) : ‖(vac (j+1) A)⁻¹ • ((record t (j+1) jb) A)-
        (vac (j+1) A)⁻¹ • ((gallery Z).density t A).part fire‖ ≤ z := by
      dsimp only [z]
      linarith only [prev t A]
    have payout (A:V j):‖(L.E.log t A).part fire‖ ≤ (β b)/w := by
      apply (le_div_iff₀ wp).mpr
      rw [mul_comm]
      exact (read t A).2.trans beta
    have view:(Ψ j).eval=(R.family.path.rep N per j).eval:=(course.1.walk j (floor.trans ui) live.le).view
    have receipt (A:V j) := (read t A).1
    simp_rw [view] at receipt
    have older:=propagate R live (record t (j+1) jb) ((gallery Z).density t)
      (fun A=>(L.E.log t A).part fire) (fun A=>((gallery L.K).density t A).part fire)
      (gust_live R.family.path N per b (head t) (integrable t) jb) (intg t) z ((β b)/w)
      above payout receipt U
    rw [gust_step R.family.path N per b (head t) jb]
    have reprice : 2*(β b)/(2*w)=(β b)/w := by field_simp
    rw [reprice]
    calc
      _ ≤ z+(β b)/w+(β b)/w := add_le_add_left older _
      _ = _ := by dsimp only [z]; ring
  · intro _
    rw [route_base]
    refine ⟨W,K,Wpos,bill,fun t U=>?_⟩
    rw [gust_base]
    simp

end YM.Integration.WilsonSingleHardRadius

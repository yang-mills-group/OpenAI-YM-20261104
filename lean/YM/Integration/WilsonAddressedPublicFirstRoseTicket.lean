import YM.Integration.WilsonAddressedPublicFirstRoseMovingDate
/-! The actual positions and both physical temperatures needed by the
compact first-edge test in one certificate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFirstRoseTicket
open Filter Function Lattice RG Wilson OPE Trace.Pilot PhysMS PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonAddressedPublicFirstRoseGeometry (Fits)
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "a" => R.family.S.a
local notation "σ" => R.family.S.scale
local notation "H" => R.family.path.levels.clock.hatBeta

structure Receipt (hi lo r θ:ℝ)(first f K c A:ℕ):Prop where
  positive : 0 < r
  coarse : max hi lo*r ≤ a (first+1)
  refined : 8*a f < min hi lo*r
  span : σ K-σ first ≤ (A:ℝ)*(1+Real.log (H (first+1)))
  heat : ∀N per:ℕ,c≤N → 0 < regulatorRun R.family N per (first+1) ∧
    regulatorRun R.family N per (first+1) ≤ 4*θ

theorem original (simple:G.Simple){θ:ℝ→ℝ}(law:Coupling G θ){hi lo:ℝ}(hp:0<hi)(lp:0<lo):
    ∀ᶠr:ℝ in trail,∀first f:ℕ,Fits R.family.S hi r first f → Fits R.family.S lo r first f →
      a f/r ≤ (θ r)^2 → max hi lo*r ≤ a (first+1) ∧ 8*a f < min hi lo*r:=by
  let L:=min hi lo
  have pos:0<L:=lt_min hp lp
  have gap:0<L/16:=div_pos pos (by norm_num)
  have budget:=WilsonThermometerUnitFilingCaptureCoupling.small simple law (Real.sqrt_pos.mpr gap)
  filter_upwards [self_mem_nhdsWithin,budget,law.positive] with r rp small gp
  intro first f front back clock
  have undo (k:ℝ)(kp:0<k)(h:Fits R.family.S k r first f):k*r≤a (first+1):=
    (WilsonCloseCaptureDate.bracket R.family.S (mul_pos kp rp) h.small).2.trans (R.family.S.strictAnti.antitone h.older)
  have square:θ r^2≤L/16:=(pow_le_pow_left₀ gp.le small 2).trans_eq (Real.sq_sqrt gap.le)
  have af:a f≤(L/16)*r:=(div_le_iff₀ rp).mp (clock.trans square)
  constructor
  · rcases le_total hi lo with small|large
    · simpa only [max_eq_right small] using undo lo lp back
    · simpa only [max_eq_left large] using undo hi hp front
  · change 8*a f < L*r
    linarith only [af,mul_pos pos rp]

theorem charge {hi lo r θ:ℝ}{first f K c A:ℕ}(ticket:Receipt R hi lo r θ first f K c A)
    {N per:ℕ}(live:c≤N)(p:ℕ):
    (regulatorRun R.family N per (first+1))^p ≤ (4:ℝ)^p*θ^p:=
  (pow_le_pow_left₀ (ticket.heat N per live).1.le (ticket.heat N per live).2 p).trans_eq (mul_pow ..)

end YM.Integration.WilsonAddressedPublicFirstRoseTicket
end

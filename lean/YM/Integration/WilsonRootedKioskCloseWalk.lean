import YM.Integration.WilsonRootedKioskCloseClock

/-! One full signed terminal gallery is carried on the recorded original Terrace.
The same gallery returned at each date is the input of the following step. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRootedKioskCloseWalk
open Function Filter Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Advent
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit AllOrder.Transit.WheelP
open ConnectedActivityE6 Extra.Histories AnalyticBridge VerifiedReset Push.PriceCompiler LocalComparison
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple) {V α:Type} [DecidableEq V] [Fintype V]
  [Nonempty α] (J:Census V) (w:V → ℝ) (positive:∀j,0 < w j)
  (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (table:root.Tab R.rolls) (way:WayStation R.kit) (ticket:TicketP R.alloy R.kit root table)

omit [DecidableEq V] [Fintype V] in
private theorem radius {d L:ℝ} (dp:0 < d) (lp:0 < L):
    Stoop.radius (Stoop.radius (fun j=>w j*L) d) (L/d)=w := by
  funext j
  dsimp only [Stoop.radius]
  field_simp

structure Carry {b m N per q:ℕ} (H:(i:ℕ) → Rep G (R.family.side i per))
    (o:(i:ℕ) → V → Site (R.family.side i per)) (Y:Estate α (o b) (H b) J) (ε:ℝ) where
  returned (i:ℕ) : m ≤ i → i ≤ b → Estate α (o i) (H i) J
  gallery : PaceR.Atlas (N:=N) R H (fun j=>w j*WilsonRootedKioskCloseClock.enlargement R b q)
    o Y m returned
  earned (i:ℕ) (lo:m ≤ i) (hi:i < b) :
    let field:=(returned i lo hi.le).canvas
    let g:=Coat.gStep (R.family.path.rep N per (i+1)).beta
    field.E.Paid w (H i).p.B (H i).p.supportExponent (ε*g^q) ∧ 
    field.K.Paid w (H i).p.B (H i).p.supportExponent (ε*g^q*forcedDivisor R.family i)

include simple positive way ticket
theorem original (l h q:ℕ) (load:∀s:J.Mode,s.val.card ≤ h) {Q ε:ℝ}
    (size:0 ≤ Q) (expense:0 < ε):
    ∀ᶠ b:ℕ in atTop,∀ m ≤ b,PaceR.Close R l Q m b → 
    ∀ (N per:ℕ), b ≤ N → 
    ∀ (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (H:(i:ℕ) → Rep G (R.family.side i per))
      (first k:ℕ),first ≤ m → Concourse R.alloy R.kit R.T π Γ first N per k H → 
    ∀ o:(i:ℕ) → V → Site (R.family.side i per),
      (∀ (i:ℕ),m ≤ i → i < b → 
        o i=(R.family.path.levels.clock.op i per).ratio.parent ∘ o (i+1)) → 
    ∀ Y:Estate α (o b) (H b) J,
      let L:=WilsonRootedKioskCloseClock.enlargement R b q
      Y.canvas.Pays w (H b).p.supportExponent (L^h)⁻¹ (L^h)⁻¹ → 
      Nonempty (Carry R J w (m:=m) (N:=N) (q:=q) H o Y ε) := by
  filter_upwards [WilsonRootedKioskCloseClock.original R simple l h q size expense way]
    with b day m before close N per bound π Γ H first k start course o positions Y L top
  obtain ⟨one,admit⟩:=day
  obtain ⟨head,room,prices⟩:=admit m before close
  let ww:=fun j=>w j*L
  have lp:0 < L:=zero_lt_one.trans_le one
  have rich(j:V):0 < ww j:=mul_pos (positive j) lp
  have unit:Stoop.radius ww L=w:=by
    funext j;change w j*L/L=w j;exact mul_div_cancel_right₀ _ lp.ne'
  have current:Y.canvas.Pays (Stoop.radius ww L) (H b).p.supportExponent (L^h)⁻¹ (L^h)⁻¹:=unit.symm ▸ top
  have enrolled:Y.canvas.Pays ww (H b).p.supportExponent 1 1:=by
    have a:=Stoop.retake ww Y.canvas.E load rich one current.budget
    have k' :=Stoop.budget ww load Y.canvas.K rich one current.wages
    rw [mul_inv_cancel₀ (pow_ne_zero h lp.ne')] at a k'
    exact ⟨a,k'⟩
  have hfirst:h ≤ R.alloy.B.a.clock.J m:=head
  have narrowed:Concourse R.alloy R.kit R.T π Γ m N per k H:=
    ⟨⟨course.1.start,fun i lo hi=>course.1.walk i (start.trans lo) hi,
      fun i lo hi=>course.1.visit i (start.trans lo) hi,
      fun i lo hi=>course.1.pace i (start.trans lo) hi⟩,
      fun i lo hi=>course.2 i (start.trans lo) hi⟩
  obtain ⟨T,atlas⟩:=PaceR.claim (R:=R) (h:=way) (D:=root) (Q:=table) (π:=π)
    (Γ:=Γ) (Ψ:=H) (v:=narrowed) (K₀:=ticket) (w:=ww) (hw:=rich) (o:=o) (hr:=positions)
    (hℓ:=hfirst) (hq:=load) (Y':=Y) (he:=bound) (hY:=enrolled) (hmi:=le_rfl) (hi:=before)
  refine ⟨⟨T,atlas,?_⟩⟩
  intro i lo hi
  have lo1:=Nat.le_succ_of_le lo
  have full:=atlas.covers i lo hi.le
  have previous:=atlas.payment i lo hi
  have high:=prices i lo hi N per bound
  have beforeR:=PaceR.roof_ge R i b
  have afterR:=PaceR.roof_ge R (i+1) b
  have beforeP:=zero_lt_one.trans_le beforeR
  have afterP:=zero_lt_one.trans_le afterR
  have beforeW (j:V):0 < Stoop.radius ww (PaceR.roof R i b) j:=div_pos (rich j) beforeP
  have afterW (j:V):0 < Stoop.radius ww (PaceR.roof R (i+1) b) j:=div_pos (rich j) afterP
  have reg:=Stoop.tighten _ _ beforeW (room i lo hi.le) full.budget
  have hard:=Stoop.leaves _ _ afterW (room (i+1) lo1 hi) previous.1.wages
  rw [radius w beforeP lp,mul_one] at reg
  rw [radius w afterP lp] at hard
  exact ⟨Lamps.loan_monotone _ reg high.1,Hard.mono _ hard (high.2 π Γ H first k start course)⟩

end YM.Integration.WilsonRootedKioskCloseWalk

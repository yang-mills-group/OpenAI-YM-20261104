import YM.Integration.WilsonOriginalNullPlacedLanding
import YM.Integration.WilsonOriginalNullPlacedHistory

/-! A charged original field at its own site is heard through all earlier
Wilson steps. The hard rows stay on their native representations and every
primary that they release remains inside its genuine remaining integral. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedLocatedDebit
open Function Filter MeasureTheory Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open QuadraticLocal QuadraticLocal.Advent AllOrder AllOrder.Floe AllOrder.Transit WheelP WilsonOriginalNullCorridor
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G)
local notation "C₀" => R.family

/-- The contribution of a single original, possibly compulsory, signed
defect at date b+n, including its incoming nonzero measured coordinate. -/
theorem original (d : ℕ) (simple : G.Simple) {ε : ℝ} (ep : 0 ≤ ε) :
    ∀ᶠ b : ℕ in atTop, ∀ m N p k n : ℕ, m ≤ b → b+n ≤ N →
    ∀ (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (W : ∀ j, Rep G ((C₀).side j p)),
    Concourse R.alloy R.kit R.T π Γ m N p k W →
    ∀ (o : ∀ j, Site ((C₀).side j p)),
    (∀ j<n, o (b+j)=((C₀).path.levels.clock.op (b+j) p).ratio.parent (o (b+j+1))) →
    (∀ j<n, WilsonOriginalNullPlacedParallel.Joined C₀ d N p (b+j) W (o (b+j+1)) ε) →
    ((C₀).path.levels.budget (b+n)).supportExponent ≤ 100 →
    ∀ (q : store C₀ d p (b+n)) (B : ℝ),
    q.Format (o (b+n)) (C₀).params (W (b+n)) →
    q.remBound (o (b+n)) (W (b+n)) (safety C₀ (b+n)) B →
    ((C₀).labels.level d).coeffSize q.x ≤ B →
    let T := fun j (x : (C₀).label d) =>
      (calValues (C:=C₀) d N p (b+j) x) ∘ Lattice.translate (o (b+j))
    let P := (C₀).path.rep N p b
    let wage := (2+4*stock C₀ (b+n))*B
    ∃ (a : (C₀).label d) (v w : store C₀ d p b) (x : ℕ → (C₀).label d) (u e : ℝ),
      mCost C₀ d N p (b+n) a ≤ 2*B ∧
      v.Format (o b) (C₀).params (W b) ∧ v.remBound (o b) (W b) (safety C₀ b) u ∧
      projection ((C₀).labels.level d) (C₀).params (W b).p.threshold (o b) v=0 ∧
      w.Format (o b) (C₀).params P ∧ w.remBound (o b) P (safety C₀ b) e ∧
      projection ((C₀).labels.level d) (C₀).params P.p.threshold (o b) w=0 ∧
      u+e ≤ gain C₀ b (b+n)*wage ∧
      (∀ j<n, mCost C₀ d N p (b+j) (x j) ≤ ε*gain C₀ (b+j) (b+n)*wage) ∧
      flow C₀ d N p b n (q.density (o (b+n)) ((C₀).localSection d) (W (b+n))) =
        v.density (o b) ((C₀).localSection d) (W b)+w.density (o b) ((C₀).localSection d) P+
        (∑ j ∈ Finset.range n, flow C₀ d N p b j (T j (x j))) + flow C₀ d N p b n (T n a) := by
  obtain ⟨opening,rooms⟩ := eventually_atTop.mp (open_late C₀ simple d)
  let bill := WilsonOriginalNullLanding.local_section R d simple
  filter_upwards [Filter.eventually_ge_atTop (max opening (eventually_atTop.mp bill).choose)] with b pre
  intro m N p k n mb top π Γ W course o route gates fixed q B fmt paid head
  dsimp only
  let t := b+n
  let S := (C₀).localSection d
  let P := (C₀).path.rep N p t
  let F := (C₀).labels.level d
  let root := o t
  have bt : b ≤ t := Nat.le_add_right b n
  have home : Opened C₀ d t p := rooms t (((le_max_left ..).trans pre).trans bt) p
  let α := projection F (C₀).params (W t).p.threshold root q
  let a := (fitting d N p t R.makes home top).symm α
  obtain ⟨h,k',c,hf,hp,hz,kf,kp,kz,small,mass,_,origin,full⟩ :=
    WilsonOriginalNullPlacedLanding.original R π Γ W course t d root simple (mb.trans bt) top home
      (((le_max_right ..).trans pre).trans bt) fixed q B fmt paid head
  have coordinate : mCost C₀ d N p t a = F.coeffSize α :=
    congrArg F.coeffSize ((fitting_apply (C:=C₀) d N p t R.makes home top a).symm.trans
      ((fitting d N p t R.makes home top).apply_symm_apply α))
  have rooms' (j : ℕ) (_ : j<n) : Opened C₀ d (b+j) p :=
    rooms _ (((le_max_left ..).trans pre).trans (Nat.le_add_right b j)) p
  have law (j : ℕ) (hj : j<n) : ∃ a c f t s : ℝ, (W (b+j)).Lawful a c f t s :=
    ⟨_,_,_,_,_,(course.1.walk (b+j) (by omega) (by omega)).truep.valid⟩
  obtain ⟨v,w,x,u,e,vf,vp,vz,wf,wp,wz,rem,feed,landed⟩ :=
    WilsonOriginalNullPlacedHistory.finite R d N p b W o ep n top route law rooms' gates h k' B c
      hf hp hz kf kp kz
  have f₁ : Integrable (h.density root S (W t)+k'.density root S P) (prior G _) :=
    ((h.envelope S (course.1.walk t (mb.trans bt) top).truep.valid hp hf).integrableC _).add
      ((k'.envelope S (R.makes.wilson.represents N p t top).good kp kf).integrableC _)
  obtain ⟨af,ap,_,word⟩ := WilsonOriginalNullFactoryRoute.entrance R d top home root a
  have f₂ : Integrable ((calValues (C:=C₀) d N p t a) ∘ Lattice.translate root) (prior G _) := by
    rw [←word]
    let ya := Drift.stamp root (Tour.placard C₀ R.makes N p top root) (((C₀).factory d N p).entries t a)
    exact (ya.envelope S (R.makes.wilson.represents N p t top).good ap af).integrableC _
  refine ⟨a,v,w,x,u,e,coordinate.trans_le mass,vf,vp,vz,wf,wp,wz,rem.trans
    (mul_le_mul_of_nonneg_left small (Real.exp_pos _).le),fun j hj => (feed j hj).trans
    (mul_le_mul_of_nonneg_left small (mul_nonneg ep (Real.exp_pos _).le)),?_⟩
  rw [full,origin,flow_add C₀ d N p b n _ _ f₁ f₂,landed]

end YM.Integration.WilsonTrueProjectedLocatedDebit

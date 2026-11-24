import YM.Integration.WilsonPhysicalHistoryWalletPhysicalCofactor

/-! The uniform global real-field hypotheses of the manuscript's nonlinear
signed transfer, for the actual enrolled full physical source on one run. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryWalletUniformBound
open Function Filter Finset MeasureTheory Lattice RG Wilson Source Labels Next.Foundations
open PhysicalNext.Repeat.Legato FVA1Physical.Wilson FVA1Physical.Round2.Curvature
open RGComparison.Core16.Spool WilsonConditionalTaylorLabels WilsonOffsetJointWick
open WilsonPhysicalHistoryWalletExperiment WilsonPhysicalHistoryWalletDeposit
open scoped BigOperators Topology Classical
variable {G : Gauge}

def reading (R : Run G) {N per j u : ℕ} (ju : j≤u) (a : Roster G) (s : Finset (Fin a.length))
    (o : Fin a.length→Site (R.family.side (u+1) per)) (i : Fin a.length)
    (y : Site (R.family.side (u+1) per)) (part : Bool) : Config G (R.family.side j per) → ℝ :=
  haarTape R N per (u+1) (fun U=>look part (tally (packet ⟨a,s⟩) (seated a s o i y) U)) j (ju.trans u.le_succ)

theorem incoming (R : Run G) {N per j u : ℕ} (live : u<N) (ju : j≤u) (a : Roster G)
    (s : Finset (Fin a.length)) (o : Fin a.length→Site (R.family.side (u+1) per)) (i : Fin a.length)
    (y : Site (R.family.side (u+1) per)) (part : Bool) :
    Continuous (reading R (N:=N) ju a s o i y part) ∧
      (∀W,|reading R (N:=N) ju a s o i y part W| ≤ stencilBound (packet ⟨a,s⟩)) ∧
      ∀W, (↑(reading R (N:=N) ju a s o i y part W):ℂ)=signal R (N:=N) ju a s o i y part W := by
  let J:=packet ⟨a,s⟩
  let pos:=seated a s o i y
  let φ:=fun U=>look part (tally J pos U)
  have original := true_tape_bound R live φ ((look part).continuous.comp (tally_cont J pos))
    (stencil_bounded J pos part) j (ju.trans u.le_succ)
  exact ⟨original.1,original.2,congrFun (WilsonPhysicalHistoryWalletTape.carried R (ju.trans u.le_succ) live φ)⟩

/-- The global signed input coefficient, with its exact measured hard and
exponential shares and an unconditional real uniform bound on the whole torus. -/
theorem stored (R : Run G) (simple : G.Simple) {N per j u : ℕ} (live : u<N) (ju : j≤u) (a : Roster G)
    (s : Finset (Fin a.length)) (o : Fin a.length→Site (R.family.side (u+1) per)) (i : Fin a.length)
    (y b : Site (R.family.side (u+1) per)) (part : Bool) (late : opens R a ≤ j) :
    ∃Q, Registered R (N:=N) ju a s o i y b part Q ∧ Measurable (reading R (N:=N) ju a s o i y part) ∧
      (∀W, |reading R (N:=N) ju a s o i y part W| ≤ stencilBound (packet ⟨a,s⟩)) ∧
      ∀W, (↑(reading R (N:=N) ju a s o i y part W):ℂ) =
        Q.exponentialEntry (anchor R ju b) (localSection G 0) (R.family.path.rep N per j) W+
        forcedShare Q (R.family.path.rep N per j) W := by
  obtain ⟨Q,q⟩ := issued R simple live ju a s o i y b part late
  have field := incoming R live ju a s o i y part
  exact ⟨Q,q,field.1.measurable,field.2.1,fun W=>(field.2.2 W).trans (q.2.2.2 W)⟩

/-- At every later genuine date this fixed-roster price is smaller than ANY
positive power of the true moving heat used by the signed one-step estimate. -/
theorem heat (R : Run G) (simple : G.Simple) (a : Roster G) (s : Finset (Fin a.length))
    {δ : ℝ} (positive : 0<δ) :
    ∀ᶠ k : ℕ in atTop, ∀ j≥k, stencilBound (packet ⟨a,s⟩) ≤ (R.family.path.levels.clock.hatBeta j)^δ := by
  let H:=R.family.path.levels
  have rise : Tendsto H.clock.hatBeta atTop atTop :=
    tendsto_atTop_add_const_left _ _ (H.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have grows := (tendsto_rpow_atTop positive).comp rise
  obtain ⟨K,after⟩ := eventually_atTop.mp (grows.eventually_ge_atTop (stencilBound (packet ⟨a,s⟩)))
  exact eventually_atTop.mpr ⟨K,fun k hk j hj=>after j (hk.trans hj)⟩

end YM.Integration.WilsonPhysicalHistoryWalletUniformBound


import YM.Integration.WilsonMeasuredCourseQuietSlots
import YM.Integration.WilsonThermometerWeightedCapture

/-! On the actual measured course the full addresses and eligibility of the
old forced operands agree. A filed coefficient keeps its original fees.
Its density discrepancy is confined to occupied, named-root hard returns. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMeasuredCoefficientTransport
open Function Finset Lattice Wilson RG Source Labels Extra.Histories Push.Local
open PhysicalNext Repeat Legato Org QuadraticLocal QuadraticLocal.Advent AllOrder AllOrder.Transit
open AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV Planned.GuardedAtom
open PhysicalNext.Repeat.Boulevard
open RG.Shoot Overlay Graces Roost Pressure Testing Input Precision Supply Push SectorMeasure PriceCompiler
open ConnectedActivityE6 Progress.DirectedRecipe AllOrder.Transit.WheelP
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {h : ℕ} {F : Frame G h}

def account (q : Coefficient F n) (P : Rep G n) (U : Config G n) : ℂ :=
  (Real.exp (P.exponent U):ℂ)*∑'b:Finset ℕ,q.marked P b U

theorem formats (q : Coefficient F n) (P W : Rep G n) (same : P.p=W.p)
    (owners : P.activities.forced=W.activities.forced) {y : Site n} {Y : Hol G}
    (fit : q.Format y Y W) : q.Format y Y P :=
  ⟨fun a=>by simpa only [same] using fit.smooth a,fit.origin,fit.identity_null,fit.projects,
    fun a U h=>by simpa only [same,owners] using fit.forcing a U h,
    fun a h=>by simpa only [owners] using fit.carried a h,fit.invariant,
    fun a=>by simpa only [same,owners] using fit.supported a,fit.borel⟩

theorem rent (q : Coefficient F n) (P W : Rep G n) (same : P.p=W.p)
    (owners : P.activities.forced=W.activities.forced) {y : Site n} {κ M : ℝ}
    (paid : q.remBound y W κ M) : q.remBound y P κ M :=by
  simpa only [Coefficient.remBound,same,owners] using paid

theorem income (q : Coefficient F n) (P W : Rep G n) (same : P.p=W.p) (quiet : W.eval=P.eval)
    (S : SectionData F) (y : Site n) (U : Config G n) :
    q.density y S W U-q.density y S P U=account q W U-account q P U :=by
  have soft : q.exponentialEntry y S P U=q.exponentialEntry y S W U:=by
    simp only [Coefficient.exponentialEntry,Coefficient.maskedTerm,same]
  unfold Coefficient.density account
  rw [soft,quiet]
  ring

theorem witness (q : Coefficient F n) (P W : Rep G n) (same : P.p=W.p) (quiet : W.eval=P.eval)
    {Y : Hol G} (S : SectionData F) (y : Site n) (fit : q.Format y Y P) (U : Config G n)
    (changed : q.density y S W U≠q.density y S P U) :
    ∃i,q.forced i U ≠ 0 ∧ y∈(P.activities.forced i).support ∧
      ∃z,z∈(P.activities.forced i).inventory ∧ z∈flags P.p.threshold U :=by
  have touch : ∃i,q.forced i U≠0:=by
    by_contra! absent
    have off (A : Rep G n) : account q A U=0 :=by
      have gone (b : Finset ℕ) : q.marked A b U=0 :=by
        unfold Coefficient.marked
        split
        · simp only [absent,zero_mul,sum_const_zero]
        · rfl
      simp only [account,gone,tsum_zero,mul_zero]
    have eq:=income q P W same quiet S y U
    rw [off,off,sub_self] at eq
    exact changed (sub_eq_zero.mp eq)
  obtain ⟨i,hi⟩:=touch
  have charged:=fit.forcing i U hi
  obtain ⟨z,hz⟩:=(P.activities.forced i).inventory_ne
  exact ⟨i,hi,fit.carried i (fun h=>hi (congrFun h U)),z,hz,
    (mem_inter.mp (charged.1.symm ▸ hz)).2⟩

theorem original (R : Run G) {m N per k i : ℕ}
    (π : ℕ→Layout G) (Γ : ℕ→Pace.Coin) (Ψ : ∀ j,Rep G (R.family.side j per))
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (start : m ≤ i) (live : i ≤ N)
    {h : ℕ} {F : Frame G h} (C₀ : Coefficient F (R.family.side i per)) (S : SectionData F)
    (Y : Hol G) (y : Site (R.family.side i per)) (κ M : ℝ) (fmt : C₀.Format y Y (Ψ i))
    (paid : C₀.remBound y (Ψ i) κ M) :
    let P:=R.family.path.rep N per i
    C₀.Format y Y P ∧ C₀.remBound y P κ M ∧
    (∀U,C₀.density y S (Ψ i) U-C₀.density y S P U=account C₀ (Ψ i) U-account C₀ P U) ∧
    ∀U,C₀.density y S (Ψ i) U≠C₀.density y S P U →
      ∃j,C₀.forced j U≠0 ∧ y∈(P.activities.forced j).support ∧
        ∃z,z∈(P.activities.forced j).inventory ∧ z∈flags P.p.threshold U :=by
  intro P
  obtain ⟨same,owners,-⟩:=WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course start live
  have eq : (Ψ i).eval=P.eval:=(later R π Γ Ψ course start live).view
  have f:=formats C₀ P (Ψ i) same owners fmt
  exact ⟨f,rent C₀ P (Ψ i) same owners paid,income C₀ P (Ψ i) same eq S y,
    witness C₀ P (Ψ i) same eq S y f⟩

end YM.Integration.WilsonMeasuredCoefficientTransport

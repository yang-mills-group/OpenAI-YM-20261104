import YM.LocalLTE.E6.Tickets
/-! Amplified E letters. Initial weighted per-label input EXACT threshold+cover measure. Not a substitution in `R`. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Raw
open Filter Function Lattice RG Pressure Pressure.Stores Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Push.AbsoluteSums.Paths Push.AbsoluteSums.Footprint
open SectorMeasure Presented Oriented PhysicalNext.Repeat.Height
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side}
-- includes derivative norm same units for all labels. It is used at E11 recur.
def Pumps (R: Rep G f) (F:ℕ→ ℝ) (e:ℝ) := (∀ i,1≤ F i) ∧ ∃ u:ℕ→ℝ,
   (∀ i, R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (u i)) ∧
   ∀ y : Site f, SumBudget (fun i=> if (R.activities.reg i).site=y then R.p.mass (R.activities.reg i).support (F i*u i) else 0) e
-- prop adaptation Receiving.core_bills
lemma aquifer (P : Teller G) (l : ℕ) {a ε : ℝ} (he : 0<ε) (ha : 0≤a) (hr : 4*ε<P.top.supportExponent) :
    ∃ n : ℕ, ∀ L : Side, n ≤ L.val → ∀ (E u:ℝ), -(11/10:ℝ)<u → ∀ᶠ x : ℝ in atTop,
    ∀ (c f:Side) (S: StepData c f) (T : Tube G S) (R: Rep G f), S.patch.L=L → Intake P T x R → ∀ (F:ℕ→ℝ), Pumps R F (E*incomingE G L x) →
     ∃ b:ℕ→ℝ, (∀ i U, |R.activities.regularOccurrence R.p i U| ≤ b i) ∧
          Sales (radiusB x) a ε (regularFoot S.ratio l (radiusB x) R) (fun i=> F i*b i) (regularExtra R) ((betaF G x L)^u):=by
  obtain ⟨n,hn⟩:= Fees.exponent (A:=P.top.supportExponent-2*ε) (l+5) he ha (by linarith)
  refine ⟨n,fun L hL E u hv =>?_⟩
  let J (x : ℝ):= extentCost (l+5) (radiusB x)
  let bill (x d:ℝ):= Footprint.payment (L.val^4) (J x) 0 ε 1 d a (preCost (l+5))
  have hh: Rate G L 0 (fun x=> (J x:ℝ)):= by simpa [extentCost,J] using (Rate.transfers (G:=G) (L:=L) (l+5+20) 0)
  have hk: Rate G L (-(11/10)) (fun x=> bill x (E*incomingE G L x)):=by
    simpa only [zero_add,bill] using! Rate.payment (Rate.const 1) ((incomingE_rate G L).mul_left E) hh (L.val^4) 0 ε a (preCost (l+5))
  filter_upwards [hk u hv,Fees.horizons G L l he ha (show 2*ε<P.top.supportExponent by linarith)] with x hx hh c f S T R hP hR F Ξ
  obtain ⟨hF,v,hw,h⟩:=Ξ
  let b (i:ℕ):=F i*v i; have hv i : 0 ≤ b i:= mul_nonneg (zero_le_one.trans (hF i)) (hw i).1
  refine ⟨v,fun i U=>?_,?_⟩
  · by_cases he' : Healthy R.p.threshold (R.activities.reg i).support U
    · rw [Activities.regularOccurrence,masked_eq _ _ _ _ he']; exact (hw i).2 _ he' [] (Nat.zero_le _) (by simp)
    rw [Activities.regularOccurrence,masked_ne _ _ _ _ he',abs_zero]; exact (hw i).1
  let p:=S.ratio; let B:= radiusB x; let Y i:=(R.activities.reg i).support
  have hP':p.count=L:= hP
  have hY: Anchored (fun i=> (R.activities.reg i).site) b (regularExtra R) (P.top.supportExponent) (E*incomingE G L x) := by
    rw [hR.exponent]; intro x; convert h x using 1; ext i; unfold BudgetPoint.mass regularExtra b; rw [mul_comm (Real.exp _)]
  have hm := Sales.anchored_sale (z:=b) (l:=l+5) (M:=R.p.B) p (fun i=> (R.activities.reg i).site) (Y:=Y)
      (fun i=> (R.activities.reg i).anchor) hY hv (X:=regularFoot p l B R) (fun i=> inspected_price p l B (Y i) hh.1) hh.1
      (by rw [hR.sizes,hP]; exact hh.2.1) (hn c f p (hP'.symm ▸ hL)) 0 (C:=1) zero_le_one
      (fun i=>⟨hv i,by simp⟩)
  apply hm.raise; rw [hP']; exact (le_abs_self _).trans hx
end YM.ConnectedActivityE6.Raw

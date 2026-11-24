import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Life
import YM.RGComparison01.Beacon

/-!
# First support census with extra tickets

Buy simultaneously
* extra penalties on the path tails / chain / Gaussian alarms;
* fugacities for a *distinguished* rough-input family when present.

Will recover prices on the actual representative `Rep` with E split and
these families paid individually. Doesn't re-enter engine at a new coupling,
assume smoothness in coupling, or drop nonanalytic factors inside a component.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Tithe
open Function Filter Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Push.AbsoluteSums.Footprint
open Precision Exterior Next.Fluctuations SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open PhysicalNext PhysicalNext.Repeat PriceCompiler
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G}
    {T : Tube G S} {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ}
    {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f} {μ q C' d v Y A b r B s α a i : ℝ}
    {k j n ℓ : ℕ} {χ : Chi} {H : Cash W s μ L Q o α T R}

section prices
variable (A : Activities G f)

/-- Coordinates, not measures/evaluation. Restrict via same stencils. -/
def portion (M : ℕ → Prop) : Activities G f := {A with E := fun i => if M i then A.E i else 0}

def bonus (M : ℕ → Prop) (t : ℝ) (i : ℕ) : ℝ := if M i then t else 1

lemma bonus_ge (M : ℕ → Prop) {t : ℝ} (ht : 1 ≤ t) : ∀ i, 1 ≤ bonus M t i := fun i => by unfold bonus; split <;> first|assumption|rfl

/-- Keep standard extra on every E list and take a distinguished booster on
chosen marks (e here *not* a root/source mark). -/
def Ticket (A : Activities G f) (p : BudgetPoint) (V : ℕ → ℝ) (t : ℝ) := (∀ i, 1 ≤ V i) ∧
    ∃ b : ℕ → ℝ, (∀ i, p.supBounds (A.reg i).site (A.reg i).support (A.E i) (b i)) ∧
      Anchored (fun i=> (A.reg i).site) (fun i => V i * b i) (fun i => coverNumber p.B (A.reg i).support) p.supportExponent t

lemma portion_tickets (A : Activities G f) (M : ℕ→Prop) (p : BudgetPoint) (w e t : ℝ) (hw : A.EBound p w)
    (hp : (portion A M).EBound p e) (ht : 1 ≤ t) (he : t * e ≤ w) : Ticket A p (bonus M t) (2*w) := by
  obtain ⟨b,hb,hB⟩:= hw; obtain ⟨c,hc,hC⟩:=hp
  let d i := if M i then c i else b i
  have hd i : p.supBounds (A.reg i).site (A.reg i).support (A.E i) (d i) := by
    unfold d; split
    next hi => simpa only [portion, if_pos hi] using hc i
    exact hb i
  refine ⟨bonus_ge _ ht,d,hd,fun i=>?_⟩
  have hv:= budget_plus (budget_scale (zero_le_one.trans ht) (hC i)) (hB i)
  refine budget_loosen (budget_mono hv ?_ ?_) (show t*e+w ≤ 2*w by linarith)
  · intro i; split
    next => exact mul_nonneg (mul_nonneg (zero_le_one.trans (bonus_ge M ht i)) (hd i).1) (Real.exp_nonneg _)
    next => exact le_rfl
  intro j; split
  next hi =>
    by_cases ht' : M j
    · refine le_trans ?_ (le_add_of_nonneg_right (by simpa only [hi, ↓reduceIte] using (hB i).1 j)); unfold portion d BudgetPoint.mass bonus;
      simp only [hi,↓reduceIte,ht']; exact (by ring : _=_).le
    refine le_trans ?_ (le_add_of_nonneg_left ((budget_scale (zero_le_one.trans ht) (hC i)).1 j)); unfold d BudgetPoint.mass bonus
    simp only [ht', ↓reduceIte]; rw [one_mul, mul_comm]
  next hz => simpa only [if_neg hz] using hv.1 j

lemma portion_regular (p : BudgetPoint) (hp : A.RegularFamily p) (M : ℕ→Prop) : (portion A M).RegularFamily p := by
  constructor
  · intro i; unfold portion; dsimp only; split
    · exact hp.smooth _
    exact AnalyticBridge.CouplingShape.reg_const _
  · intro i; unfold portion; dsimp only; split
    next => exact hp.at_flat _
    next => rfl
  intro i hx x y ht hu; unfold portion; dsimp only; split
  next => exact hp.vanish i hx x y ht hu
  next => unfold logHessian; simp

lemma no_charge (V : ℕ→ℝ) {p : BudgetPoint} {w : ℝ} (h : A.EBound p w) (_he : 0 ≤ w) (hv : ∀ i,V i=1) : Ticket A p V (2*w) := by
  rw [funext hv]; obtain ⟨b,h,hx⟩:=h
  refine ⟨fun _=>le_rfl,b,h,fun i=>?_⟩
  refine budget_mono (budget_loosen (hx i) (D:=2*w) (by linarith)) ?_ ?_
  · intro z; split <;> first|exact le_rfl|exact mul_nonneg (mul_nonneg zero_le_one (h _).1) (Real.exp_nonneg _)
  intro z; split <;> simp [*,BudgetPoint.mass,mul_comm]
end prices

/-- Separately upper bound only E habitat on an input certificate.
 Use in addition to `core_bills` which covers K. -/
theorem shore (P : Teller G) (l : ℕ) {a ε : ℝ} (he : 0<ε) (ha : 0≤a)
    (hr : 4*ε<P.top.supportExponent) : ∃ n : ℕ, ∀ L : Side, n ≤ L.val → ∀ u : ℝ,
    -(11/10:ℝ)<u → ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T:Tube G S) (R:Rep G f),
      S.patch.L=L → Intake P T x R → ∀ U : ℕ → ℝ, Ticket R.activities R.p U (2*incomingE G L x) →
      ∃ b : ℕ→ℝ, (∀ i, R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (b i)) ∧
        Sales (radiusB x) a ε (regularFoot S.ratio l (radiusB x) R) (fun i=> U i*b i) (regularExtra R) (betaF G x L ^ u) := by
  obtain ⟨n,hn⟩:= Fees.exponent (l+5) he ha (show 2*ε < P.top.supportExponent-2*ε by linarith)
  refine ⟨n,fun L hm u hr=>?_⟩
  let J (x : ℝ) := extentCost (l+5) (radiusB x)
  have hh : Rate G L 0 (fun x : ℝ => (J x:ℝ)) := by
    simpa [extentCost,J] using (Rate.transfers (G:=G) (L:=L) (l+5+20) 0)
  have ht:= Rate.payment (Rate.const 1) ((incomingE_rate G L).mul_left 2) hh (L.val^4) 0 ε a (preCost (l+5))
  rw [zero_add] at ht
  filter_upwards [ht u hr, Fees.horizons G L l he ha (show 2*ε<P.top.supportExponent from (by linarith))] with
    x hX h c f S T R hP hR U hH
  obtain ⟨hv,v,hV,hA⟩:=hH; let P':= fun i=> (R.activities.reg i).support
  let K i:=U i*v i
  have hu i:0≤ K i:= mul_nonneg (zero_le_one.trans (hv i)) (hV i).1
  have hP':S.ratio.count=L:= hP
  refine ⟨v,hV,?_⟩
  have hy:= Sales.anchored_sale (z:=K) (l:=l+5) (M:=R.p.B) S.ratio (fun i => (R.activities.reg i).site)
    (Y:=P') (fun i=> (R.activities.reg i).anchor) (hR.exponent.symm ▸ hA) hu
    (X:=regularFoot S.ratio l (radiusB x) R) (fun i=> inspected_price S.ratio l _ _ h.1) h.1 (by rw [hR.sizes,hP]; exact h.2.1)
    (hn c f S.ratio (hP'.symm ▸ hm)) 0 (C:=1) zero_le_one (fun i => ⟨hu i,by simp [K]⟩)
  apply hy.raise; rw [hP']; exact (le_abs_self _).trans hX
end YM.RGComparison01.Tithe

import YM.Integration.WilsonMatrixTicketLanesConnectedBudget
import YM.RGComparison.Core16.Lam.Wrap

/-! The positive-regulator connected one-block pair and its actual full spatial coefficient series. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesConnectedForecast
open Function Filter Set Real Lattice Gauge RG Wilson Tree Precision PhysicalNext.Repeat.Legato
open Next.Foundations PertExtension PertExtension.Series Tested
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Parcel RGComparison.Core16.Silk
open RGComparison.Core16.Forge RGComparison.Core16.Lumen RGComparison.Core16.Lumen.Planet
open RGComparison.Core16.Lam WilsonMatrixTicketLanesReflectedGauge WilsonMatrixTicketLanesConnectedBudget
open scoped Topology Classical BigOperators
variable {G : Gauge} (R : Run G) {c f : Side} (S : StepData c f) (T : Forest S.ratio)
    {P : Oven S.patch} (X : P.Form G) (u : Directions G c)

private theorem purse {I : Type} [Fintype I] (A : I→Lamp G) (x : I→Site f)
    (offer : P.Offers X S.kernel) (large : Bid.Larger (G:=G) S) (pinned : ∀i,‖u i‖ ≤ X.Q)
    {U V : Lumen.Stage} {q : ℕ} {C : ℝ} (later : U.L ≤ V.L)
    (bill : Spool.Price U q C (rank A S T X (Next.Foundations.chart G) u x) (reads A S u x)) :
    Lam.pursed V (normalized S T X u R A x) (fun g=>(reads A S u x g).re) q C := by
  rw [Spool.standard A x large pinned T T offer offer pinned (Next.Foundations.chart_ok G) R.alloy.B.ratio] at bill
  let forms:=rank A S T X R.metals.O u x
  have coeff : term (normalized S T X u R A x)=(Spool.look false) ∘ forms := by
    funext i;unfold term normalized;rw [PowerSeries.coeff_mk];rfl
  have c₀ : 0 ≤ C:=(norm_nonneg _).trans (bill.growth 0 (Nat.zero_le _))
  refine ⟨c₀,?_,?_⟩
  · intro i hi
    rw [coeff];exact (Complex.abs_re_le_norm (forms i)).trans (bill.growth i hi)
  · intro t late
    let g:=dollar t
    have range : g ≤ dollar U.L:=exp_monotone (neg_le_neg (later.trans late))
    have paid:=bill.cost g (dollar_pos _) range
    rw [coeff]
    have charted:peval (Spool.look false ∘ forms) q g=Spool.look false (peval forms q g):=
      WilsonXLocal.eval_map (Spool.look false) (a:=forms) g
    change |(reads A S u x g).re-peval (Spool.look false ∘ forms) q g| ≤ g^(q+1)*C
    rw [charted];exact (Complex.abs_re_le_norm (reads A S u x g-peval forms q g)).trans paid

abbrev row (e : Request G) := fun _ : Unit=>e.1.1.1
abbrev col (e : Request G) := fun _ : Unit=>e.1.2.1
abbrev left (e : Request G) := fun _ : Unit=>e.1.1.2
abbrev right (e : Request G) := fun _ : Unit=>e.1.2.2

/-- Each coefficient and the positive-coupling remainder holds before any choice of future
period, placement, forest, or permitted retained direction. -/
def Report (e : Request G) (b : ℕ) : Prop:=
  let D:=2+log (R.family.path.levels.clock.hatBeta b)
  ∃ (P : Oven (R.family.path.levels.clock.op b 0).patch) (X : P.Form G),
    P.Offers X R.family.path.levels.clock.kernel ∧ X.Q=(e.2.2:ℝ)+1 ∧ ∀ p : ℕ,
    let S:=R.family.path.levels.clock.op b p
    ∀ (T : Forest S.ratio) (_large : Bid.Larger (G:=G) S) (u : Directions G (R.family.side b p)),
    (∀i,‖u i‖ ≤ X.Q) → ∀ (x y : Unit→ Site (R.family.side (b+1) p)),
    let net:=WilsonMatrixTicketLanesReflectedGauge.gap S T X u R (row e) (col e) (left e) (right e) x y
    (∀H : ℕ,(∀i : Slice (first e),∀j : Slice (second e),H ≤ separation (legs (first e) x i).1 (legs (second e) y j).1) →
      ∀ j ≤ e.2.1,|nth j net| ≤ D/exp (D⁻¹*(H:ℝ))) ∧
    ∀g : ℝ,0<g → g ≤ (sqrt (R.family.path.levels.clock.hatBeta b/2))⁻¹ →
      |measured S u R (row e) (col e) (left e) (right e) x y g-Lam.factor g e.2.1 net| ≤ g^(e.2.1+1)*(D+Lam.pursed.forecastCost e.2.1 D D)

theorem original (paid : Paid G R.kit) (e : Request G) : ∀ᶠ b : ℕ in atTop,Report R e b:=by
  filter_upwards [paid e] with b sale
  obtain ⟨P,X,C,offer,width,c₀,tariff,rate,decay,single,other,both⟩:=sale
  let β:=R.family.path.levels.clock.hatBeta b
  let D:=2+log β
  let q:=e.2.1
  have d₀:0<D:=(inv_pos.mpr (shade_pos (X:=X))).trans_le rate
  have back : D⁻¹ ≤ shade X:=(inv_anti₀ (inv_pos.mpr (shade_pos (X:=X))) rate).trans_eq (inv_inv _)
  refine ⟨P,X,offer,width,?_⟩
  intro p S T large u pin x y net
  constructor
  · intro H far j early
    let fee:=bond_fee (look false∘sight (first e)) (look false∘sight (second e)) X.Q (absolute e)
    have old:=WilsonMatrixTicketLanesReflectedRank.coefficient S T X u R (row e) (col e) (left e) (right e) x y offer large pin early c₀ decay far
    change |nth j net| ≤ C / costLamp X H * fee at old
    calc
      _ ≤ (C*|fee|)/exp (shade X*(H:ℝ)):=old.trans (by
        rw [div_mul_eq_mul_div,costLamp]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) c₀) (exp_pos _).le)
      _ ≤ D/exp (D⁻¹*(H:ℝ)):=div_le_div₀ d₀.le tariff (exp_pos _) (exp_monotone (mul_le_mul_of_nonneg_right back (Nat.cast_nonneg _)))
  · intro g gp small
    obtain ⟨U₀,t₀,A⟩:=single;obtain ⟨U₁,t₁,B⟩:=other;obtain ⟨U₂,t₂,AB⟩:=both
    have late {U : Lumen.Stage} (h : g ≤ dollar U.L) : U.L ≤ -log g:=by
      have lx:=log_le_log gp h;rw [dollar,log_exp] at lx;linarith only [lx]
    let V : Lumen.Stage:=⟨-log g,0,U₀.high.trans (late (small.trans t₀))⟩
    have here : g ≤ dollar V.L:=by change g ≤ exp (- -log g);rw [neg_neg,exp_log gp]
    have fareA:=purse R S T X u (first e) x offer large pin (V:=V) (late (small.trans t₀))
      (A _ _ S.sizes large T u x pin)
    have fareB:=purse R S T X u (second e) y offer large pin (V:=V) (late (small.trans t₁))
      (B _ _ S.sizes large T u y pin)
    have fareAB:=purse R S T X u (together e) (Sum.elim x y) offer large pin (V:=V) (late (small.trans t₂))
      (AB _ _ S.sizes large T u (Sum.elim x y) pin)
    exact (fareAB.difference (fareA.product fareB)).expense gp here

end YM.Integration.WilsonMatrixTicketLanesConnectedForecast

import YM.Integration.WilsonRegisteredFlatLocal
import YM.Integration.WilsonRegisteredFrozenReading

/-! Price the complete true short marked remainder itself at the input
gauge. The unchanged original mask is retained for every signed term. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredWholeShort
open Filter Set Finset Lattice RG Wilson Source MSbar.Heath OPE.Therm PhysicalNext.Repeat.Legato Push.Local
open WilsonInheritedRegisteredField
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {N per k d:ℕ}

theorem field (J:Voice G) (clear:Clear G J) (a:Lattice.Order) (live:k ≤ N) (ref:R.family.ref d ≤ k)
    (v:R.family.label d) (o:Site (R.family.side k per)) (b H:ℕ) (τ r:ℝ) (weak:0 ≤ τ) (rp:0<r)
    (U:Config G (R.family.side k per)) (cut:U∈House.chilly (WilsonAxialWindow.cells o H) τ) :
    let P:=R.family.path.rep N per k
    let Z:=packet R.makes live v o
    let c:=(4*(H:ℝ)*Fintype.card PlaqAxes)*τ
    let L:=R.family.labels.level d
    b*(4*P.p.B+2)+2*P.p.B<H → 10*H<(R.family.side k per).val →
    c ≤ J.δ → J.C*c ≤ r*P.p.threshold → r*P.p.threshold ≤ J.r → 4*J.C*r ≤ 1 →
    ‖∑' i,if coverNumber P.p.B (Z.support i)<b then Z.maskedTerm P i U else 0‖
      ≤ r*((R.family.path.levels.params k).columns*L.coeffSize (L.core Z.x)) := by
  intro P Z c L located period small money capacity stay
  have room:2*H<(R.family.side k per).val:=by omega
  obtain ⟨D,admitted,healthy,kept⟩:=WilsonRegisteredFlatLocal.based (p:=P.p) J clear a o H room τ r weak rp U cut small money capacity stay
  have prior:=WilsonTranslatedFactory.based R.makes ref live o ((R.family.factory d N per).terminal.symm v)
  have form:Z.Format o R.family.params P:=prior.1
  obtain ⟨a₁,b₁,_,b0,total,_,⟨e,charge,estimate⟩,_⟩:=prior.2
  let f i:=if coverNumber P.p.B (Z.support i)<b then Z.maskedTerm P i U else 0
  have point (i:ℕ):‖f i‖ ≤ r*P.p.mass (Z.support i) (e i):=by
    have budget:P.p.supBounds o (Z.support i) (Z.regular i) (e i):=estimate i
    by_cases eligible:coverNumber P.p.B (Z.support i)<b
    · have range (x) (hx:x∈Z.support i):separation o x<H:=
        (WilsonRegisteredShortField.belongs R.makes live ref v o b i x eligible hx).trans_lt located
      have near:Nonwrapping (Z.support i) o:=by
        intro x hx
        rw [separation_comm]
        calc 10*separation o x ≤ 10*H:=Nat.mul_le_mul_left _ (range x hx).le
             _ < _:=period
      have zero:=form.projects i near
      have full:=WilsonRegisteredFlatLocal.projected R.family.params (form.smooth i) budget zero rp D admitted
        (fun t ht=>healthy t ht (Z.support i))
      have raw:‖Z.regular i U‖ ≤ r*e i:=(congrArg norm (kept (form.smooth i) range)).le.trans full
      have contraction:‖Z.maskedTerm P i U‖ ≤ ‖Z.regular i U‖:=by
        change ‖({U|Healthy P.p.threshold (Z.support i) U}:Set _).indicator (Z.regular i) U‖ ≤ _
        by_cases ok:Healthy P.p.threshold (Z.support i) U
        · rw [Set.indicator_of_mem ok]
        rw [Set.indicator_of_notMem ok,norm_zero];exact norm_nonneg _
      change ‖if coverNumber P.p.B (Z.support i)<b then Z.maskedTerm P i U else 0‖ ≤ _
      rw [if_pos eligible]
      exact contraction.trans (raw.trans (mul_le_mul_of_nonneg_left (P.p.loMass _ _ budget.1) rp.le))
    · change ‖if coverNumber P.p.B (Z.support i)<b then Z.maskedTerm P i U else 0‖ ≤ _
      rw [if_neg eligible,norm_zero]
      exact mul_nonneg rp.le (charge.1 i)
  have paid:=sumBudget_mono (sumBudget_mul_left charge rp.le) (fun i=>norm_nonneg (f i)) point le_rfl
  exact ((norm_tsum_le_tsum_norm paid.2.1).trans paid.2.2).trans
    (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right b0).trans total) rp.le)

end YM.Integration.WilsonRegisteredWholeShort
end

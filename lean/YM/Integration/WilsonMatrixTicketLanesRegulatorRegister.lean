import YM.Integration.WilsonMatrixTicketLanesRegulatorCoupon

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRegulatorRegister
open Filter Real FVA2 FVA2.CityHistory Lattice RG Wilson Tree Precision RG17 RG12 Extraction Spec
open RGComparison.Core16 RGComparison.Core16.Spool PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonMatrixTicketLanesReportedPivot WilsonMatrixTicketLanesReportedOneBlock
open WilsonMatrixTicketLanesReportedPrepaid WilsonMatrixTicketLanesRegulatorColumn
open WilsonMatrixTicketLanesRegulatorCoupon
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G)

/-- Install angular coefficients in the genuine upper factory at the stated
intermediate scale with its engineering factor restored exactly. -/
def filed (d k N p : ℕ) (z : R.family.label d) : R.family.label d :=
  (↑(R.family.S.a k^d):ℂ) • RG12.atK R.family R.makes d k (N,p) z

private theorem deposited (d k N p : ℕ) (age : R.family.ref d≤k) (future : k≤N) (z : R.family.label d) :
    ((R.family.factory d N p).entries k ((R.family.factory d N p).terminal.symm (filed R d k N p z))).x =
      (↑(R.family.S.a k^d):ℂ) • z := by
  let A := RG12.charts R.family R.makes d k (N,p)
  have actual (x : R.family.label d) : A x = ((R.family.factory d N p).entries k ((R.family.factory d N p).terminal.symm x)).x := by
    unfold A
    rw [RG12.charts,dif_pos ⟨age,future⟩]
    rfl
  rw [←actual]
  change A ((↑(R.family.S.a k^d):ℂ) • A.symm z) = _
  rw [map_smul,LinearEquiv.apply_symm_apply]

theorem column (d k N p : ℕ) (age : R.family.ref d≤k) (future : k≤N) (z : R.family.label d) :
    entry R d k N p (filed R d k N p z) = z := by
  rw [WilsonMatrixTicketLanesRegulatorColumn.entry,deposited R d k N p age future,smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (pow_ne_zero d (R.family.S.a_pos k).ne')),one_smul]

/-- At every compact configuration this is exactly the engineering-normalized
cutoff operator with the originally prescribed factory coefficients. -/
theorem placed (d k N p : ℕ) (age : R.family.ref d≤k) (future : k≤N) (z : R.family.label d)
    (o : Site (R.family.side k p)) (V : Config G (R.family.side k p)) :
    R.family.O k p (center R k N p (filed R d k N p z)) o V =
      (↑(R.family.S.a k^d):ℂ)*R.family.O k p ((R.family.factory d k p).terminal z) o V := by
  rw [center,deposited R d k N p age future,map_smul]
  exact congrFun ((R.family.linearO k p d o).map_smul (↑(R.family.S.a k^d):ℂ) _) V

variable {I : Type} [Fintype I]

/-- One actual finite Wilson numerator and its positive vacuum denominator. -/
def sheet {b k : ℕ} (d : I→ℕ) (N p : ℕ) (z : ∀i,R.family.label (d i))
    (stage : k=b+1) (u : Pins G (R.family.side b p)) (o : I→Site (R.family.side k p)) : ℂ :=
  let g := regulatorRun R.family N p k
  let D := step R p stage
  (Spool.spinVac D u g)⁻¹ • D.push (g⁻¹^2) (fun V=>bare (g⁻¹^2) V •
    ∏i,(↑(R.family.S.a k^(d i)):ℂ)*R.family.O k p ((R.family.factory (d i) k p).terminal (z i)) (o i) V)
    (Parcel.Oven.slice u g)

/-- The genuine finite-torus words retain the exact angular ratio between the
inherited coupling and the registered angular threshold. -/
def coefficients (d : I→ℕ) (k N p : ℕ) (z : ∀i,R.family.label (d i))
    (v : (∀i,(R.family.labels.level (d i)).Index) → ℂ) : ℂ :=
  ∑ j,(∏i,WilsonMatrixTicketLanesReportedMaster.color R (d i) k N p (z i) (j i))*v j

variable {f : Extraction.Order} {S : Table R.family.book} (F : Spec.Final R.family f S) (L : RG17.Layout F)

include L in
/-- All angular data may be chosen after the actual calendar. This is uniform
over all periodic regulators and over the coefficients of the including fields. -/
theorem original (simple : G.Simple) (paid : Paid G R.kit) {n : ℕ} (d : Fin n→ℕ)
    (q cap : ℕ) (ε : ℝ) (positive : 0<ε) :
    ∀ᶠ b : ℕ in atTop,∀ (k N p : ℕ) (stage : k=b+1),k≤N → (∀i,R.family.ref (d i)≤k) →
      ∀ (z : ∀i,R.family.label (d i)) (large : Bid.Larger (G:=G) (step R p stage)) (T : Forest (step R p stage).ratio)
        (u : Pins G (R.family.side b p)) (o : Fin n→Site (R.family.side k p)) (tag : (step R p stage).Choices)
        (v : (Descent.nil (top:=R.family.side k p)).Tags),(∀j,‖u j‖≤(cap:ℝ)+1) →
        ‖sheet R d N p z stage u o - coefficients R d k N p z
          (WilsonMatrixTicketLanesReportedCoupon.value R (N:=N) d (q+2) stage large T u o tag v)‖ ≤
          ε*regulatorRun R.family N p k^q*∏i,mass R.family (d i) (z i) := by
  filter_upwards [billed R F L simple paid d (fun _=>0) q cap ε positive] with b sale
  intro k N p stage future age z large T u o tag v inside
  let top i := filed R (d i) k N p (z i)
  have bank i : (R.family.S.a k^(d i))⁻¹*Next.UVStress.quota R.family (d i) k N p (top i) =
      mass R.family (d i) (z i) := by
    rw [←cost R F L (d i) k N p (age i) future,column R (d i) k N p (age i) future]
  have bought := sale k N p stage future age top (fun i=>mass R.family (d i) (z i))
    (fun i=>by simpa only [pow_zero,one_mul] using (bank i).le) (fun i=>mass_nonneg ..)
    large T u o tag v inside
  have same : fresh R d N p top stage u o = sheet R d N p z stage u o := by
    unfold fresh sheet
    dsimp only
    simp_rw [show ∀ i V,R.family.O k p (center R k N p (top i)) (o i) V =
      (↑(R.family.S.a k^(d i)):ℂ)*R.family.O k p ((R.family.factory (d i) k p).terminal (z i)) (o i) V from
      fun i V=>placed R (d i) k N p (age i) future (z i) (o i) V]
  have formal (v : (∀i,(R.family.labels.level (d i)).Index) → ℂ) :
      forecast R (k:=k) d N p top v = coefficients R d k N p z v := by
    unfold WilsonMatrixTicketLanesRegulatorCoupon.forecast coefficients
    simp_rw [show ∀ i,entry R (d i) k N p (top i) = z i from
      fun i=>column R (d i) k N p (age i) future (z i)]
  rw [same,formal] at bought
  simpa only [Finset.sum_const_zero,Nat.zero_add,Nat.mul_one] using bought

end YM.Integration.WilsonMatrixTicketLanesRegulatorRegister

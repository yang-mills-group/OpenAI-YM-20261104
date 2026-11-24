import YM.Integration.WilsonMatrixTicketLanesRegulatorRegister
import YM.Integration.WilsonMatrixTicketLanesCompensatedFields

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRegulatorIndependent
open Filter Real FVA2 FVA2.CityHistory MS.Local.Physical Lattice RG Wilson Tree Precision RG17 RG12 Extraction Spec
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Astage Next.Rank.Price
open PhysicalNext.Repeat.Legato Pert.Asymptotics WilsonMatrixTicketLanesReportedOneBlock
open WilsonMatrixTicketLanesReportedPrepaid WilsonMatrixTicketLanesNativePrices
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (B : Deck G)
variable {I : Type} [Fintype I]

/-- The independent finite Wick conversion here retains every lower angular grade,
with the actual inherited running coupling and stated reporting threshold. -/
def price (d h k N p : ℕ) (u : B.BIndex (d:ℤ) h) (i : (R.family.labels.level d).Index) : ℂ :=
  ((shrink R.family k N p^((R.family.labels.level d).grades i).2 : ℝ):ℂ) *
    FVAAlt2.Shop.valueP B (R.family.localSection d) (R.makes.sections d) (CoefficientBridge.run_valuation R d) u i

theorem filed (d h k N p : ℕ) (u : B.BIndex (d:ℤ) h) (i : (R.family.labels.level d).Index) :
    WilsonMatrixTicketLanesReportedMaster.color R d k N p ((warehouse R).qfits B d h u) i =
      price R B d h k N p u i := by
  rw [WilsonMatrixTicketLanesReportedMaster.color,Labels.Frame.scaled_apply,price]
  exact congrArg (fun z : ℂ=> ((shrink R.family k N p^((R.family.labels.level d).grades i).2 : ℝ):ℂ)*z)
    (((warehouse R).price_cast B u i).symm.trans (WilsonMatrixTicketLanesNativePrices.original R B d h u i))

def finite (d h : I → ℕ) (u : ∀i,B.BIndex ((d i):ℤ) (h i)) (k N p : ℕ)
    (field : (∀i,(R.family.labels.level (d i)).Index) → ℂ) : ℂ :=
  ∑j,(∏i,price R B (d i) (h i) k N p (u i) (j i))*field j

theorem receipt (d h : I → ℕ) (u : ∀i,B.BIndex ((d i):ℤ) (h i)) (k N p : ℕ)
    (field : (∀i,(R.family.labels.level (d i)).Index) → ℂ) :
    WilsonMatrixTicketLanesRegulatorRegister.coefficients R d k N p (fun i=>(warehouse R).qfits B (d i) (h i) (u i)) field =
      finite R B d h u k N p field := by
  unfold WilsonMatrixTicketLanesRegulatorRegister.coefficients finite
  simp_rw [filed R B]

/-- At the very same finite period, the real compact nonlinear Wilson observable
built from the independently filed basis columns. -/
def observed {b k : ℕ} (d h : I → ℕ) (w : ∀i,B.BIndex ((d i):ℤ) (h i)) (N p : ℕ) (stage : k=b+1)
    (u : Pins G (R.family.side b p)) (o : I→Site (R.family.side k p)) : ℂ :=
  let g := regulatorRun R.family N p k
  let D := step R p stage
  (Spool.spinVac D u g)⁻¹ • D.push (g⁻¹^2) (fun V=>bare (g⁻¹^2) V •
    ∏i,(↑(R.family.S.a k^(d i)):ℂ)*R.family.O k p
      (WilsonMatrixTicketLanesCompensatedFields.field R B k p (d i) (h i) (w i)) (o i) V) (Parcel.Oven.slice u g)

variable {f : Extraction.Order} {S : Table R.family.book} (F : Spec.Final R.family f S) (L : RG17.Layout F)
include L in
/-- Before all periods and cutoff geometries, the independently prescribed compensated
columns themselves have the numerical all-orders expansion in the authentic fresh
Wilson sheet. The forecast retains the very same finite-period FVA2 forest. -/
theorem original (simple : G.Simple) (paid : Paid G R.kit) {n : ℕ} (d : Fin n→ℕ) (q cap : ℕ)
    (ε : ℝ) (positive : 0<ε) :
    ∀ᶠ b : ℕ in atTop,∀ (k N p : ℕ) (stage : k=b+1),k≤N → (∀i,R.family.ref (d i)≤k) →
      ∀ (h : Fin n→ℕ) (w : ∀i,B.BIndex ((d i):ℤ) (h i))
        (large : Bid.Larger (G:=G) (step R p stage)) (T : Forest (step R p stage).ratio)
        (u : Pins G (R.family.side b p)) (o : Fin n→Site (R.family.side k p)) (tag : (step R p stage).Choices)
        (v : (Descent.nil (top:=R.family.side k p)).Tags),(∀j,‖u j‖≤(cap:ℝ)+1) →
        ‖observed R B d h w N p stage u o - finite R B d h w k N p
          (WilsonMatrixTicketLanesReportedCoupon.value R (N:=N) d (q+2) stage large T u o tag v)‖ ≤
          ε*regulatorRun R.family N p k^q*∏i,mass R.family (d i) ((warehouse R).qfits B (d i) (h i) (w i)) := by
  filter_upwards [WilsonMatrixTicketLanesRegulatorRegister.original R F L simple paid d q cap ε positive] with b sale
  intro k N p stage future age h w large T u o tag v inside
  rw [←receipt R B]
  exact sale k N p stage future age _ large T u o tag v inside

end YM.Integration.WilsonMatrixTicketLanesRegulatorIndependent

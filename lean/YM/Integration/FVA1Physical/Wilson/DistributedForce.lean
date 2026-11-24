import YM.Integration.FVA1Physical.Wilson.DistributedPurchase

/-! Discharge the rooted insertion hypothesis for the genuine first variation
of the full Wilson action, allowing coarse and fine link directions. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MeasureTheory Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling
open PhysicalNext.Repeat.Legato Push.Uniform Pressure RGComparison.Core16 Next.SectorChange
open scoped Classical Topology
variable {G : Gauge}

def actionForce (A : Mosaic.Issue G) (χ : ChartRatio G) (e : Joint A.F G) :=
  PowerSeries.mk fun i=> MvPolynomial.pderiv e (PowerSeries.coeff i (barbed A.F A.v χ A.T))

theorem distributed_force (J : Voice G) (clear : Clear G J) (χ : ChartRatio G) (hχ : LocalRatio χ)
    (simple : G.Simple) (H H' : Stage) (P : Patch) (K : KernelChoices) (branch : P.Branches K G)
    (p s q : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) (e : Joint A.F G),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      ‖z‖ ≤ A.fClock*D →
      let y:=tip G P.L x
      let b:=address A.F G e
      Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      ∀ U∈hotel A.F (boxX y b) (boxY y b) J (represent (tint G (Exterior.Body 1 A.c) z))
        (vest (priced A.F A.v A.pre.clip A.pre.path) z) (pillow y) (room y),
      ∀ i ≤ p, |PowerSeries.coeff i (bulkColumn A χ z (actionForce A χ e) p) -
        PowerSeries.coeff i (innerColumn A χ J y z b U (actionForce A χ e) p)| ≤ y^(-(q:ℝ)) := by
  filter_upwards [distributed_columns J clear χ hχ simple H H' P K branch p s (p+2) q le_rfl hD,
    distributed_action J χ hχ simple H H' P K p s (p+2) (ε:=1) zero_lt_one] with x price bound
  intro A z e patch ker season hz y b kind expanse wedge
  obtain ⟨_,act⟩:=bound A patch ker season kind expanse wedge
  apply price A z b patch ker season hz kind expanse wedge (actionForce A χ e)
  intro i hi
  have data:=act i hi
  simp only [Real.rpow_one] at data
  simp only [actionForce,PowerSeries.coeff_mk]
  exact ⟨data.1.2 e,pdeg e (data.2.trans (by omega))⟩

end YM.Integration.FVA1Physical.Wilson

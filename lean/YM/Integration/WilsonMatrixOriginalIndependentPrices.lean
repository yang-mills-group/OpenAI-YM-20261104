import YM.Integration.WilsonMatrixTicketLanesRetainedFare

noncomputable section
namespace YM.Integration.WilsonMatrixOriginalIndependentPrices
open Filter Real Lattice Wilson RG Tree Precision
open RGComparison.Core16 RGComparison.Core16.Lumen PertExtension.Series.Tested FVA2 FVA2.CityHistory
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonMatrixTicketLanesReportedOneBlock WilsonMatrixTicketLanesReportedWords
open WilsonMatrixTicketLanesReportedPrepaid WilsonMatrixTicketLanesRetainedFare WilsonMatrixTicketLanesDescentWords
open scoped Topology BigOperators Classical

variable {G:Gauge} (R:Run G)

def bound (b s:ℕ):ℝ :=
  ∑h∈Finset.range (s+1),((Real.sqrt (R.family.path.levels.clock.hatBeta b/2))⁻¹)^h*
    (2+Real.log (R.family.path.levels.clock.hatBeta b))

/-- The original transferred formal coefficient is bounded before the periodic box, uniformly on the purchased pin cap. -/
theorem coefficients (paid:Paid G R.kit) {n:ℕ} (d:Fin n→ℕ) (s cap:ℕ) :
    ∀ᶠb:ℕ in atTop,∀p (large:Bid.Larger (G:=G) (R.family.path.levels.clock.op b p))
      (T:Forest (R.family.path.levels.clock.op b p).ratio) (u:Pins G (R.family.side b p))
      (o:Fin n→Site (R.family.side (b+1) p)) (tag:(R.family.path.levels.clock.op b p).Choices)
      (v:(Descent.nil (top:=R.family.side (b+1) p)).Tags),
      (∀k,‖u k‖≤(cap:ℝ)+1)→∀(j:∀i,(R.family.labels.level (d i)).Index) (h : ℕ), h ≤ s →
      ‖WilsonCoherentJointReturn.series (lamps R d j) (R.family.path.levels.clock.op b p)
          T R.metals.O u o large tag v h‖≤2+Real.log (R.family.path.levels.clock.hatBeta b) := by
  have words (j:∀i,(R.family.labels.level (d i)).Index) :
      ∀ᶠb:ℕ in atTop,WilsonCoherentInheritedPermit.offered R (lamps R d j) ((cap:ℝ)+1) s start b :=
    paid.2 (code d j s cap)
  filter_upwards [eventually_all.mpr words] with b bills p large T u o tag v inside j h ordered
  obtain ⟨P,X,U,C,offer,width,_,_,expense,_,receipt⟩:=bills j
  let D:=R.family.path.levels.clock.op b p
  have money:=receipt _ _ D.sizes large T u o inside
  exact ((WilsonCoherentClockDebit.transferred (lamps R d j) D X (Next.Foundations.chart_ok G)
    R.alloy.B.ratio large T T u o offer (fun k=>(inside k).trans_eq width.symm)
    money tag v).growth h ordered).trans expense

/-- This controls the actual independently computed finite polynomial for any enrolled word
and any common incoming field, so a cutoff limit of weights may multiply it. -/
theorem reading (simple:G.Simple) (paid:Paid G R.kit) {n:ℕ} (d:Fin n→ℕ) (s cap:ℕ) :
    ∀ᶠb:ℕ in atTop,∀ {m:ℕ} (stage:m=b+1) (N p:ℕ),m≤N→
      ∀(large:Bid.Larger (G:=G) (step R p stage)) (T:Forest (step R p stage).ratio)
      (u:Pins G (R.family.side b p)) (o:Fin n→Site (R.family.side m p))
      (tag:(step R p stage).Choices) (v:(Descent.nil (top:=R.family.side m p)).Tags),
      (∀k,‖u k‖≤(cap:ℝ)+1)→∀j:∀i,(R.family.labels.level (d i)).Index,
      ‖WilsonMatrixTicketLanesRetainedFare.reading R (N:=N) d s stage large T u o tag v j‖≤bound R b s := by
  filter_upwards [coefficients R paid d s cap] with b growth m stage N p live large T u o tag v inside j
  subst m
  rw [←WilsonMatrixTicketLanesRetainedFare.identified R d s rfl large T u o tag v]
  unfold WilsonMatrixTicketLanesReportedCoupon.value peval bound
  obtain ⟨_,pos,small⟩:=WilsonCoherentInheritedSpool.temperature R simple b N p live
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro h range
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg pos.le h)]
  exact mul_le_mul (pow_le_pow_left₀ pos.le small h)
    (growth p large T u o tag v inside j h (by simpa using Finset.mem_range.mp range))
    (norm_nonneg _) (pow_nonneg (pos.le.trans small) _)

end YM.Integration.WilsonMatrixOriginalIndependentPrices

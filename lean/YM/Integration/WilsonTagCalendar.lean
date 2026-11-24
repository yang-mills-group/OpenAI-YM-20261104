import YM.Integration.WilsonTagThermalWindow
import YM.Integration.WilsonTagGateSchedule
import YM.Integration.QLocalPhysicalPatchGate

/-! The true rooted likelihood error at a varying block shape on one prepaid Wilson run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonTagCalendar
open Filter Set MeasureTheory Lattice RG Wilson Pressure Precision OPE.Therm
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Push.PriceCompiler Supply Testing Next.Scheduling
open PhysicalNext.JointLoad Heir Heir.Suite
open WilsonLimitConstruction.FundedCompanySelection
open WilsonTagThermalWindow WilsonAxialCoordinates WilsonAxialWindow
open scoped Topology BigOperators Classical
variable {G : Gauge}

def condition : QLocalPhysicalPatchGate.Condition G := fun j _ D K h z =>
  let T := Classical.choice (WilsonTagThermalWindow.purchase D K h)
  (Real.sqrt z)⁻¹*(Real.log z)^12 ≤ T.gate ∧
    2*T.r < 100*(1+radiusB z) ∧
    (((T.r+T.r+1)^4*Fintype.card PlaqAxes:ℕ):ℝ)*Real.exp (-(Real.log z)^2) ≤ (z^j)⁻¹

theorem prepaid (s : Sheet G) (K : MapPrices) :
    Prepaid (QLocalPhysicalPatchGate.Paid (condition (G:=G))) s K := by
  apply QLocalPhysicalPatchGate.prepaid
  intro j i D K h
  let T := Classical.choice (WilsonTagThermalWindow.purchase D K h)
  exact WilsonTagGateSchedule.stage T.r T.gate T.positive _ j

/-- The one threshold precedes all cutoffs, periods, local instruments and their actual
branch choices. The only combinatorial cost is the number of requested coarse bonds. -/
theorem selected (R : Run G) (hG : G.Simple) (P : Poetry R.family.path.levels)
    (paid : QLocalPhysicalPatchGate.Paid (condition (G:=G)) R.kit) (q : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ N, m<N → ∀ p, let a := R.family.path.levels
      let S := a.clock.op m p
      ∀ E : Finset (Edge (Site (a.S.side m p))),
        (scene R.family.path N p (m+1)).real (⋃ e∈E, activated (G:=G) S e) ≤
          E.card*(a.clock.hatBeta (m+1)^q)⁻¹ := by
  let a := R.family.path.levels
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (OPE.Therm.rare P hG R.makes.wilson),
    (tendsto_add_atTop_nat 1).eventually (a.fits.deep.eventually_ge_atTop q)] with m hit hq N hm p
  let S := a.clock.op m p
  let h : S.patch.Branches S.kernel G := (a.blocks m p).branches
  let T := Classical.choice (WilsonTagThermalWindow.purchase S.patch S.kernel h)
  let z := a.clock.hatBeta (m+1)
  let j := a.clock.J (m+1)
  let μ := scene R.family.path N p (m+1)
  letI : IsProbabilityMeasure μ := probability (H:=R.family.path) (p:=p) R.makes.wilson hm
  have hprice := QLocalPhysicalPatchGate.selected R condition paid p hm h
  change (Real.sqrt z)⁻¹*(Real.log z)^12 ≤ T.gate ∧ 2*T.r < 100*(1+radiusB z) ∧
    (((T.r+T.r+1)^4*Fintype.card PlaqAxes:ℕ):ℝ)*Real.exp (-(Real.log z)^2) ≤ (z^j)⁻¹ at hprice
  have hfit := a.fits.sizeT (m+1) p
  have hn : 2*T.r < (a.S.side (m+1) p).val :=
    hprice.2.1.trans_le (by simpa only [Nat.add_comm,RG.Calendar.coverSize,radiusB,z] using hfit)
  have hp (e : Edge (Site (a.S.side m p))) : μ.real (activated (G:=G) S e) ≤ (z^q)⁻¹ := by
    have hs : activated (G:=G) S e ⊆ excluded (S.ratio.embed e.1) T.r (cool a (m+1)) := by
      rintro U ⟨t,changed⟩
      by_contra absent
      exact T.clean S rfl rfl hn U t e (fun x hx => (outside absent x hx).trans hprice.1) changed
    calc
      _ ≤ _ := measureReal_mono hs
      _ ≤ _ := omitted μ _ _ _ _ (fun x _ => hit N hm p x)
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (WilsonAxialWindow.count _ T.r)) (Real.exp_pos _).le
      _ ≤ (z^j)⁻¹ := hprice.2.2
      _ ≤ _ := inv_anti₀ (pow_pos (zero_lt_one.trans (a.fits.delayed _)) _)
        (pow_le_pow_right₀ (a.fits.delayed _).le hq)
  change ∀ E : Finset (Edge (Site (a.S.side m p))),
    μ.real (⋃ e∈E, activated (G:=G) S e) ≤ E.card*(z^q)⁻¹
  intro E
  apply (measureReal_biUnion_finset_le (μ:=μ) E (fun e => activated (G:=G) S e)).trans
  exact (Finset.sum_le_sum fun e _ => hp e).trans_eq (by simp [nsmul_eq_mul])

end YM.Integration.WilsonTagCalendar

import YM.Integration.QLocalPhysicalBirthPurchase
import YM.Integration.QLocalPhysicalMarkedIncidence
import YM.Integration.FullQLocalRawInheritedRate

/-! The full original signed startup can be purchased at the prescribed raw
monitor after the fixed physical marker radius is charged. The cocontracted
menu and every individual compulsory output share the same true sheet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalPhysicalBirthRawRate
open Function Filter Finset Lattice Wilson RG Marker FVA1
open Extra.Histories Extra.Trajectories PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.Replicum MergeProof.Replicums MergeProof.Ribbon
open Packets Push.GridApprox.Nil Push.AbsoluteSums FullQLocal.RawInherited
open scoped BigOperators Classical Topology

variable {G : Gauge} (R : Run G)

def tolerance (L : ℕ) : ℝ := R.family.path.levels.clock.hatCoupling L / 8

theorem tolerance_pos (L : ℕ) : 0 < tolerance R L :=
  div_pos (inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (R.family.path.levels.fits.delayed L)))) (by norm_num)

theorem cost (hG : G.Simple) : ∀ᶠ L : ℕ in atTop,
    let r := QLocalPhysicalBirthPurchase.debit R L (tolerance R L)
    r + (Real.exp (r+r+R.family.path.levels.clock.forcedAllowance L)-1) ≤
      shape R.family.path.levels.clock 0 L := by
  let A := R.family.path.levels
  filter_upwards [(RG01.Physical.shrink hG A 1).eventually_le_const (by norm_num : (0:ℝ)<1/8)] with L h
  let b := A.clock.hatBeta L
  let g := A.clock.hatCoupling L
  let κ := A.clock.forcedAllowance L
  let r := QLocalPhysicalBirthPurchase.debit R L (tolerance R L)
  have hb : 1 < b := A.fits.delayed L
  have hz : 0 < Real.sqrt b := Real.sqrt_pos.mpr (zero_lt_one.trans hb)
  have hs : 1 ≤ Real.sqrt b := Real.one_le_sqrt.mpr hb.le
  have hsb : Real.sqrt b ≤ b := by nlinarith [Real.sq_sqrt (zero_lt_one.trans hb).le]
  have hκ : 0 ≤ κ := Real.exp_nonneg _
  have ht : 0 ≤ r := (QLocalPhysicalBirthPurchase.debit_pos R L (tolerance_pos R L)).le
  have hr : r ≤ g/8 := min_le_left _ _
  have hg : g ≤ 1 := inv_le_one_of_one_le₀ hs
  have hK : κ ≤ g/8 := by
    have hB : κ*Real.sqrt b ≤ (1:ℝ)/8 :=
      (mul_le_mul_of_nonneg_left hsb hκ).trans (by simpa only [pow_one,mul_comm,b,κ] using h)
    exact ((le_div_iff₀ hz).2 hB).trans_eq (by change 1/8/Real.sqrt b = (Real.sqrt b)⁻¹/8; ring)
  have hz₀ : 0 ≤ r+r+κ := by linarith
  have h1 : |r+r+κ| ≤ 1 := by rw [abs_of_nonneg hz₀]; linarith
  have he := (le_abs_self (Real.exp (r+r+κ)-1)).trans (Real.abs_exp_sub_one_le h1)
  rw [abs_of_nonneg hz₀] at he
  have hbnd : r+(Real.exp (r+r+κ)-1) ≤ g := by linarith [ht.trans hr]
  apply hbnd.trans
  change g ≤ (1+↑(A.clock.coverSize L))^0*(A.clock.threshold L+(A.clock.monitor L)⁻¹^2)+
    (1+↑(A.clock.coverSize L)+A.clock.monitor L+A.clock.loopCap L)^0*g
  simp only [pow_zero,one_mul]
  have hθ : 0 < A.clock.threshold L := (A.budget L).threshold_pos
  linarith only [hθ,sq_nonneg (A.clock.monitor L)⁻¹]

variable {V : Type} [DecidableEq V] [Fintype V]

/-- One physical original startup before all tests, in the zero-degree raw
monitor even for the genuine mixed forced outputs. The positive weights
publish exactly what is charged for each independent original label. -/
theorem menu (hG : G.Simple) : ∀ᶠ L : ℕ in atTop,
    ∀ (d : V → ℕ) (v : ∀ i, R.family.label (d i)), (∀ i, R.family.ref (d i) ≤ L) → ∀ C : ℝ,
    let r := QLocalPhysicalBirthPurchase.debit R L (tolerance R L)
    let w := QLocalPhysicalBirthWeights.weight R L d v C r
    (∀ i, 0 < w i) ∧ ∀ (N p : ℕ) (hL : L ≤ N) (o : Positions V (R.family.side L p)),
      (∀ i, (coverNumber (R.family.path.levels.budget L).B (ActualRunPhysicalPages.cover R p L (d i) o i) : ℝ) ≤ C) →
      ∃ B : Box (R.family.side L p) → Sheet (Ribbon.Bud V), (∀ s, 0 ≤ B s) ∧
        (∀ s U q, ‖(ActualRunUnmaskedPartners.actualCorrection R N p L o d v s U).part q‖ ≤ B s q) ∧
        Ac.Hit Prod.fst (R.family.path.rep N p L).p.B (fun s => wordsPrice w (B s))
          ((R.family.path.rep N p L).p.supportExponent-4) (shape R.family.path.levels.clock 0 L) ∧
        MenuSafe (ActualRunFullPages.pages R hG N p L hL o d v) o
          (ActualRunFullPages.prices R p L o d v B) w (shape R.family.path.levels.clock 0 L) := by
  filter_upwards [QLocalPhysicalBirthPurchase.prepaid R (V := V) hG,cost R hG] with L hp hc
  intro d v href C
  have hh := hp d v href C (tolerance R L) (tolerance_pos R L)
  refine ⟨hh.1.2.2,fun N p hL o hC => ?_⟩
  obtain ⟨B,hB,hcoef,hinc,hmenu⟩ := hh.2 N p hL o hC
  have h := hh.1.1
  refine ⟨B,hB,hcoef,fun x => ⟨(hinc x).1,(hinc x).2.1,?_⟩,hmenu.each,hmenu.radius,fun x => ?_⟩
  · exact (hinc x).2.2.trans (by dsimp only at hc; linarith)
  · exact ⟨(hmenu.hit x).1,(hmenu.hit x).2.1,(hmenu.hit x).2.2.trans hc⟩

/-- An independently chosen test configuration on each actual outgoing barcode
obeys the raw monitor divided by the radii of the occupied original markers. -/
theorem modes (hG : G.Simple) : ∀ᶠ L : ℕ in atTop,
    ∀ (d : V → ℕ) (v : ∀ i, R.family.label (d i)), (∀ i, R.family.ref (d i) ≤ L) → ∀ C : ℝ,
    let w := QLocalPhysicalBirthWeights.weight R L d v C (QLocalPhysicalBirthPurchase.debit R L (tolerance R L))
    ∀ (N p : ℕ) (_ : L ≤ N) (o : Positions V (R.family.side L p)),
      (∀ i, (coverNumber (R.family.path.levels.budget L).B (ActualRunPhysicalPages.cover R p L (d i) o i) : ℝ) ≤ C) →
      ∀ (q : (Ribbon.Bud V).Mode) (U : Box (R.family.side L p) → Config G (R.family.side L p)),
        Ac.Hit Prod.fst (R.family.path.rep N p L).p.B
          (fun s => ‖(ActualRunUnmaskedPartners.actualCorrection R N p L o d v s (U s)).part q‖)
          ((R.family.path.rep N p L).p.supportExponent-4) (shape R.family.path.levels.clock 0 L / Poly.toll w q) := by
  filter_upwards [menu R (V := V) hG] with L h
  intro d v href C w N p hL o hC q U
  obtain ⟨hw,h⟩ := h d v href C
  obtain ⟨B,hB,hcoef,hinc,_⟩ := h N p hL o hC
  exact QLocalPhysicalMarkedIncidence.recover _ B _ hw hB hcoef hinc q U

end YM.Integration.QLocalPhysicalBirthRawRate
end

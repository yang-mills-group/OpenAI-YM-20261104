import YM.Integration.WilsonReceivedWholeFieldMask
import YM.Comparison.RG02.Cumulants.Partition

/-! All proper and complete faces of the ordinary registered source on
the same named large-field event as the true Wilson readings. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedWholeFieldHot
open Finset Filter MeasureTheory Lattice Wilson RG Ac Marker QuadraticLocal Multi
open IterationFour PhysicalNext.Repeat.Legato Push.AbsoluteSums
open Push.AbsoluteSums.Animals OPE.Therm WilsonRootedKioskOccupiedSlip
open Comparison.RG02.Cumulants
open scoped Classical BigOperators Topology

variable {G : Gauge} {n : Side} {p : BudgetPoint} {V I T : Type} [DecidableEq V] [Fintype V]
  {Γ : Census V} {o : V → Site n} (L : Lamps T I G p o Γ)
  {w : V → ℝ} {a D : ℝ} (hw : ∀ v, 0 < w v) (ha : 0 ≤ a)
  (gross : Gross L w p.B a D)

def charge (s : Γ.Mode) (D : ℝ) : ℝ := ∑ h∈shards Γ s, D^h.val.card

include hw ha gross

theorem ordinary (t : T) (U : Config G n) (s : Γ.Mode) :
    Poly.toll w s * ‖(Poly.pass (bare L t U)).part s‖ ≤ charge s D := by
  have quiet := WilsonRootedKioskCompleteFiling.quiet L hw ha gross t U
  rw [pass_partition _ quiet]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Poly.worth hw s).le).trans
  rw [mul_sum,charge]
  apply sum_le_sum
  intro h hh
  have toll : Poly.toll w s = ∏ d∈h.val,Poly.toll w d.val := by
    rw [← show unionOf h = s from (mem_filter.mp hh).2]
    exact prod_biUnion (parts_wise h)
  rw [toll,norm_prod,←prod_mul_distrib,←prod_const]
  apply Finset.prod_le_prod
  · intro d _
    exact mul_nonneg (Poly.worth hw _).le (norm_nonneg _)
  · intro d _
    obtain ⟨v,hv⟩ := d.property
    exact WilsonReceivedWholeFieldMask.whole L hw ha gross t U d.val v hv

theorem borel [Countable I] (t : T) (s : Γ.Mode) :
    Measurable (fun U => (Poly.pass (bare L t U)).part s) := by
  have eqn : ∀ U : Config G n, (Poly.pass (bare L t U)).part s =
      ∑ h∈shards Γ s, ∏ d∈h.val,(bare L t U).part d.val :=
    fun U => pass_partition _ (WilsonRootedKioskCompleteFiling.quiet L hw ha gross t U) s
  simp_rw [eqn]
  exact Finset.measurable_sum _ fun h _ => Finset.measurable_prod _ fun d _ =>
    WilsonReceivedWholeFieldMask.measurable L hw ha gross t d.val

section Physical
variable (R : Run G) (simple : G.Simple) (calendar : Poetry R.family.path.levels)
local notation "H" => R.family.path
local notation "κ" => R.family.path.levels.clock.forcedAllowance
include simple calendar

omit [DecidableEq V] [Fintype V] hw ha gross in
/-- Integrate the entire registered ordinary face on a failed local collar
against the original earlier Wilson vacuum, retaining all proper faces.
The onset precedes the choice of field space, positions and catalogue. -/
theorem original {ρ : ℝ} (hr : 0 < ρ) (Q : ℕ) :
    ∀ᶠ i in atTop, ∀ N, i ≤ N → ∀ per (X : Support (R.family.side i per))
      (E : Set (Config G (R.family.side i per))), MeasurableSet E →
      E ⊆ SelectedCofactorAnchoredRegister.hot (ρ*(R.family.path.rep N per i).p.threshold) X →
      ∀ (V I T : Type) [DecidableEq V] [Fintype V] [Countable I] (Γ : Census V)
      (o : V → Site (R.family.side i per)) (p : BudgetPoint) (L : Lamps T I G p o Γ)
      (w : V → ℝ) (a D : ℝ), (∀ v, 0 < w v) → 0 ≤ a → 0 ≤ D → Gross L w p.B a D →
      ∀ (t : T) (s : Γ.Mode) (q : ℕ), q ≤ Q → ∀ u (hu : u ≤ i),
        Poly.toll w s * (∫ U, ‖actualTransport R.family (N:=N) (p:=per)
          (PhysicalWilsonHotIntegral.restricted (E:=E) ((Real.sqrt (κ i))^q)⁻¹
            (fun W => (Poly.pass (bare L t W)).part s)) hu U‖ ∂scene H N per u) ≤
        charge s D * (X.card * ballCost 2 * Fintype.card PlaqAxes : ℕ) * κ i := by
  filter_upwards [PhysicalWilsonHotIntegral.divided R simple calendar hr Q] with i heat
  intro N hi per X E hE hX V I T _ _ _ Γ o p L w a D hw ha hD gross t s q hq u hu
  have positive := Poly.worth hw s
  have nonneg : 0 ≤ charge s D := sum_nonneg fun z _ => pow_nonneg hD _
  have paid (W : Config G (R.family.side i per)) (_ : W ∈ E) :
      ‖(Poly.pass (bare L t W)).part s‖ ≤ charge s D / Poly.toll w s :=
    (le_div_iff₀ positive).mpr (by
      simpa only [mul_comm (Poly.toll w s)] using ordinary L hw ha gross t W s)
  have hearing := heat N hi per X E hE hX q hq _ (div_nonneg nonneg positive.le)
    _ (borel L hw ha gross t s) paid u hu
  exact (mul_le_mul_of_nonneg_left hearing positive.le).trans_eq (by
    field_simp [positive.ne'])
end Physical

end YM.Integration.WilsonReceivedWholeFieldHot

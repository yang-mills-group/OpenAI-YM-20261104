import YM.Integration.WilsonAddressedWeakReflectedArray
import YM.Push.CORRECTED_COLUMNS.Positions

/-! The literal displaced fine fields lie in the chamber of the original
physical reflection tiling. The cutoff is chosen before period and site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakChamber
open Function Filter Set MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox
open PhysicalNext.Repeat.Legato Extraction Table Spec Cells Push.Corrected
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {N p k : ℕ}

theorem top (q : Cover) : Cells.location R.family.S N N p q = wrap (R.family.side N p) q := by
  let g := R.family.S.toDepth (le_refl N) p
  have h : R.family.S.a N * (g.count.val:ℝ) = R.family.S.a N := R.family.S.embeds_scale g
  have count : g.count.val=1 := by
    exact_mod_cast (show (g.count.val:ℝ)=1 by nlinarith only [h,R.family.S.a_pos N])
  rw [Cells.location,dif_pos (le_refl _),Ratio.embed_wrap]
  change wrap _ (g.count.val • q)=_
  rw [count,one_smul]

theorem comfortable (u : ℕ) (ρ : ℝ) (hr : 0 < ρ) (x : Points 2) (i : Fin 2)
    (fit : ρ*‖x i‖+R.family.S.a N ≤ R.family.S.a u/4) :
    Positions.Comfortable R.family.S u N (address (R.family.S.a N) (ρ • x) i) := by
  intro j
  have round := coord_grid_bound (R.family.S.a_pos N) (ρ • x) i j
  have v : |x i j| ≤ ‖x i‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (x i) j
  let t := tag (R.family.S.a N) (address (R.family.S.a N) (ρ • x)) i j
  have first : |t - ρ*(x i j)| ≤ R.family.S.a N := round
  have second : |ρ*(x i j)| ≤ ρ*‖x i‖ := by rw [abs_mul,abs_of_pos hr];exact mul_le_mul_of_nonneg_left v hr.le
  change |t| ≤ _
  have both : |t| ≤ |t-ρ*x i j|+|ρ*x i j| := by simpa only [sub_add_cancel] using abs_add_le (t-ρ*x i j) (ρ*x i j)
  linarith only [both,first,second,fit]

theorem original (u D : ℕ) : ∀ᶠ N : ℕ in atTop, ∀ p (clock : u ≤ N) (k : ℕ) (live : k ≤ N)
    (d : Fin 2 → ℕ) (_ : ∀ i,d i ≤ D) (ρ : ℝ) (_ : 0 < ρ) (x : Points 2),
    (∀ i,ρ * ‖x i‖ + R.family.S.a N ≤ R.family.S.a u/4) →
    ∀ (y : (i:Fin 2) → Palette R.family (d i)) (r : (i:Fin 2) → Emblems R.family (d i)),
    let z := WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
    ∀ i,Interior ((center R.family.S p clock 0).chamber 0)
      (WilsonThermometerIntrinsicRoster.source R d z y r live i) := by
  have stock := Filter.eventually_all.mpr fun e : Fin (D+1) => Positions.interior R.makes e.val u
  filter_upwards [stock] with N hn
  intro p clock k live d hd ρ hr x fit y r
  let q := address (R.family.S.a N) (ρ • x)
  dsimp only
  intro i
  let e : Fin (D+1) := ⟨d i,Nat.lt_succ_of_le (hd i)⟩
  let v := ((R.family.factory (d i) N p).terminal
    ((finer (r i) live) (y i) (WilsonThermometerOwnOffsetField.primaryLetter (d i))))
  have row : Interior ((center R.family.S p clock 0).chamber 0)
      (R.family.O N p (d:=d i) v (Cells.location R.family.S N N p (q i))) :=
    hn e p N (q i) clock le_rfl (comfortable R u ρ hr x i (fit i)) v
  rw [top R] at row
  exact Interior.scale ((R.family.S.a k:ℂ)^(d i)) row

end YM.Integration.WilsonAddressedWeakChamber

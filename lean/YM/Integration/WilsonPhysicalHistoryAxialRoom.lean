import YM.Integration.WilsonPhysicalHistoryWalletHardRate

/-! The original signed transfer only requires a previous chart price on its
regular inputs. On these fields the physical postcard is an exact inverse and
the physical field width does not change under a genuine clock change. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryAxialRoom
open Function Filter MeasureTheory Set Lattice RG Wilson Source Labels Next.Foundations
open PhysicalNext.Repeat.Legato MSbar MSbar.Mosaic MSbar.Cacao MSbar.Heath MSbar.Heath.Stock
open Precision Tree Exterior Push.Uniform MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave
open MSbar.Bakery MSbar.Bakery.Film MSbar.Measuring RG01.Kernel RGComparison.Core16
open FVA1Physical.Wilson FVA1Physical.Round2.Curvature RGComparison.Core16.Spool
open WilsonConditionalTaylorLabels WilsonOffsetJointWick WilsonPhysicalHistoryWalletUniformBound
open scoped BigOperators Topology Classical
variable {G : Gauge}

theorem inverse {f : Side} {g h r : ℝ} (gp : 0<g) (hp : 0<h)
    (W : Config G f) (regular : W ∈ regularInputs g (r/g)) :
    postcard G f h (chartLog h W)=W ∧ ‖h • chartLog h W‖≤r := by
  refine ⟨recover_chartLog hp.ne' W (Set.mem_univ_pi.mp regular.1),?_⟩
  have clocks : h • chartLog h W = g • chartLog g W := by
    simp only [chartLog,smul_smul,mul_inv_cancel₀ hp.ne',mul_inv_cancel₀ gp.ne']
  rw [clocks,norm_smul,Real.norm_of_nonneg gp.le]
  calc
    _ ≤ g*(r/g) := mul_le_mul_of_nonneg_left regular.2 gp.le
    _ = _ := by field_simp

theorem next (R : Run G) {N per j u : ℕ} (ju : j<u) (a : Roster G) (s : Finset (Fin a.length))
    (o : Fin a.length→Site (R.family.side (u+1) per)) (i : Fin a.length)
    (y : Site (R.family.side (u+1) per)) (part : Bool) :
    reading R (N:=N) ju.le a s o i y part = fun V=>
      MSbar.Bulk.expect (R.family.path.levels.clock.op j per) (R.family.path.rep N per (j+1)) V
        (reading R (N:=N) ju a s o i y part) :=
  haarTape_step R (fun U=>look part (tally (packet ⟨a,s⟩) (seated a s o i y) U)) (Nat.lt_succ_of_le ju.le)

def errors {f : Side} (g r h : ℝ) (p : ℕ) (T : Nesting G f) (φ : Config G f → ℝ) : Set ℝ :=
  insert 0 ((fun W=>|φ W-clockReading p h T (chartLog h W)|) '' regularInputs g (r/g))

def price {f : Side} (g r h : ℝ) (p : ℕ) (T : Nesting G f) (φ : Config G f → ℝ) : ℝ :=
  sSup (errors g r h p T φ)

private theorem bounded {f : Side} (g r h : ℝ) (p : ℕ) (T : Nesting G f) (φ : Config G f → ℝ)
    {B : ℝ} (bnd : ∀W,|φ W| ≤ B) : BddAbove (errors g r h p T φ) := by
  obtain ⟨C,upper⟩ := (chartLog_envelope h (clockReading_continuous p h T)).cost
  refine ⟨|B|+|C|,?_⟩
  intro t ht
  rcases ht with rfl|⟨W,_,rfl⟩
  · exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  · apply (abs_sub _ _).trans
    exact add_le_add ((bnd W).trans (le_abs_self _))
      ((show |clockReading p h T (chartLog h W)| ≤ C by simpa only [Real.norm_eq_abs] using upper W).trans (le_abs_self _))

theorem purchased {f : Side} (g r h : ℝ) (p : ℕ) (T : Nesting G f) (φ : Config G f → ℝ)
    {B : ℝ} (bnd : ∀W,|φ W| ≤ B) :
    0 ≤ price g r h p T φ ∧ ∀W∈regularInputs g (r/g), |φ W-clockReading p h T (chartLog h W)| ≤ price g r h p T φ := by
  have funded := bounded g r h p T φ bnd
  exact ⟨le_csSup funded (Set.mem_insert _ _),fun W hw=>le_csSup funded (Or.inr ⟨W,hw,rfl⟩)⟩

/-- Only previously purchased *postcard* observations, on the physical width
actually needed at the next step, enter the regular-chart subtotal. -/
theorem tested {f : Side} {g r h D ε : ℝ} (gp : 0<g) (hp : 0<h) (width : r≤D) (ε0 : 0≤ε)
    (p : ℕ) (T : Nesting G f) (φ : Config G f → ℝ)
    (earlier : ∀Z,‖h • Z‖≤D → |φ (postcard G f h Z)-clockReading p h T Z|≤ε) :
    price g r h p T φ ≤ ε := by
  apply csSup_le ⟨0,Set.mem_insert _ _⟩
  intro t ht
  rcases ht with rfl|⟨W,hw,rfl⟩
  · exact ε0
  · obtain ⟨same,small⟩ := inverse gp hp W hw
    simpa only [same] using earlier (chartLog h W) (small.trans width)

end YM.Integration.WilsonPhysicalHistoryAxialRoom


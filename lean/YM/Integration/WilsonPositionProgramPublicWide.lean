import YM.Integration.WilsonPositionProgramPublicBulb
import YM.Integration.WilsonPositionProgramPublicFourPrice

/-! At the widened distance, each filed axis carries its own engineering
power, including the scalar. The four signed responses control the numerical
difference of the two original frames in their common public coordinates. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicWide
open Filter Function Extraction Table Spec PhysMS Lattice Source Labels Maxwell MS MS.Menus
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus Table.Pairing
open Local.Physical WilsonThermometerUnitFilingFourSquare
open WilsonPositionProgramPublicContrast WilsonPositionProgramPublicFourPrice
open WilsonPositionProgramPublicWickGram WilsonPositionProgramPublicReflectedRead
open scoped Topology BigOperators Classical
variable {G:Gauge} {B:Deck G} {h:ℕ} {K:Type} [Fintype K] (leg:K→Glyph B h)

def weighted (q:ℝ) (x:K→ℂ) (i:K) : ℂ := q^(leg i).1.val • x i

omit [Fintype K] in
theorem sub (q:ℝ) (x y:K→ℂ) : weighted leg q (x-y)=weighted leg q x-weighted leg q y := by
  funext i
  exact smul_sub _ _ _

theorem lower (q:ℝ) (hq:0≤q) (h1:q≤1) (x:K→ℂ) :
    q^h * ‖x‖ ≤ ‖weighted leg q x‖ := by
  have scaled : ‖(q^h) • x‖ ≤ ‖weighted leg q x‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have degree : (leg i).1.val ≤ h := Nat.le_of_lt_succ (leg i).1.isLt
    have row := mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq h1 degree) (norm_nonneg (x i))
    calc
      ‖((q^h) • x) i‖ = q^h * ‖x i‖ := by rw [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hq _)]
      _ ≤ q^(leg i).1.val * ‖x i‖ := row
      _ = ‖weighted leg q x i‖ := by rw [weighted,norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hq _)]
      _ ≤ _ := norm_le_pi_norm _ i
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hq h)] using scaled

variable {I:Type} [Fintype I] {C:Family G} {S:Table C.book} {f:Extraction.Order}
    {l:Filter (ℕ×ℕ)} [l.NeBot] {d:ℕ} (F:Final C f S) (sign:Signed)
    {m:I→S.Field d} (arm:(i:I)→Bool→Arm C S l d (m i)) (test:I→I→Test 2)
    (W:Initialize G) (V:Normalize.Store G) (axis:Axis)

theorem original (each:Injective leg) (order:l≤f.fuse) :
    ∃ (b:Bulb (center axis) axis) (k δ:ℝ), 0<k ∧ 0<δ ∧
      ∀ᶠ M in Front, ∀c∈M.Box, ∀ (q:ℝ), 0≤q → q≤1 →
        ∀ (w:ℕ×ℕ→I→ℂ) (u:ℕ×ℕ→Bool→K→ℂ) (p:ℕ×ℕ→K→K→ℂ) (A e:ℝ),
          (∀ᶠ z in l,charge (w z)≤A) →
          (∀ᶠ z in l,‖p z-WilsonPositionProgramPublicBulb.Gram axis W V leg b M c‖≤δ) →
          (∀ᶠ z in l,∀a t,‖assay (weighted leg q (u z a)) (weighted leg q (u z t)) (p z)-
            heard F sign arm test (w z) z a t‖≤e) →
          ∀η:ℝ, 0<η → ∀ᶠ z in l, k*(q^h*‖u z false-u z true‖)^2≤4*e+η := by
  obtain ⟨k,t,hk,ht,price⟩:=WilsonPositionProgramPublicFourPrice.original F sign arm test axis leg each order
  obtain ⟨b,meshes⟩:=WilsonPositionProgramPublicBulb.filed axis W V leg (half_pos ht)
  refine ⟨b,k,t/2,hk,half_pos ht,?_⟩
  filter_upwards [meshes] with M filed c hc q hq h1 w u p A e mass mesh fees η hη
  have base : ∀ᶠ z in l, ‖p z-reading axis (nodes axis) leg‖≤t := by
    filter_upwards [mesh] with z small
    exact (norm_sub_le_norm_sub_add_norm_sub (p z) (WilsonPositionProgramPublicBulb.Gram axis W V leg b M c) _).trans
      ((add_le_add small (filed c hc)).trans (by linarith))
  filter_upwards [price w (fun z r=>weighted leg q (u z r)) p A e mass base fees η hη] with z bound
  rw [←sub] at bound
  have shrink:=lower leg q hq h1 (u z false-u z true)
  exact (mul_le_mul_of_nonneg_left (by gcongr: (q^h*‖u z false-u z true‖)^2≤_) hk.le).trans bound
end YM.Integration.WilsonPositionProgramPublicWide

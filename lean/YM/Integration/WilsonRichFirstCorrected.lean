import YM.Integration.WilsonRichPhysicalSlotParity
import YM.Pert.First.OneArray

/-! First coefficient of the independently issued renormalized rich register:
the true first field fees are kept and the originally tangent coupling has no
first-order adjustment. The whole finite inversion read keeps its named parity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRichFirstCorrected
open Function Finset Lattice Wilson RG PhysicalNext.Repeat.Legato
open MS MS.Land MS.Menus MS.Rake MS.Dial MS.Book MS.Book.Program
open FVAAlt2 FVAAlt2.Lobby FVAAlt2.Billing RegulatorIR.FVAAlt2.Lodge
open WilsonRichPrimitiveTerminal WilsonRichPhysicalSlotParity PowerSeries
open scoped Classical BigOperators

theorem slide_zero (P : Team) (y : ℝ) (a : PowerSeries ℂ) :
    coeff 0 (redo P y a) = coeff 0 a := by
  simp only [redo,LinearMap.coe_mk,AddHom.coe_mk,coeff_mk]
  change (∑ j ∈ Iic (0:ℕ), cut (shift P y) j 0 • coeff j a) = _
  rw [sum_eq_single 0]
  · rw [root_first (share P y) (ann P y),one_smul]
  · intro j hj h
    exact (h (Nat.eq_zero_of_le_zero (mem_Iic.mp hj))).elim
  · simp

theorem slide_one (P : Team) (y : ℝ) (a : PowerSeries ℂ) :
    coeff 1 (redo P y a) = coeff 1 a := by
  simp only [redo,LinearMap.coe_mk,AddHom.coe_mk,coeff_mk]
  change (∑ j ∈ Iic (1:ℕ), cut (shift P y) j 1 • coeff j a) = _
  rw [sum_eq_single 1]
  · rw [root_first (share P y) (ann P y),one_smul]
  · intro j hj h
    have hj' := mem_Iic.mp hj
    have j0 : j=0 := by omega
    subst j
    simp [cut]
  · simp

variable {G : Gauge} (R : Run G) {B : MS.Local.Physical.Deck G}
  {I : Type} [LinearOrder I] [Fintype I] (p : I → MS.Rake.Label B) {n : Side}
  (x : I → Site n) (Q : Prescription B) (y e : ℝ)

abbrev Roster := (i : I) → Glyph B (p i).h
def board (v : Roster p) : I → MS.Rake.Label B := fun i => owner (v i)
def weight_zero (v : Roster p) : ℂ := ∏ i,constantCoeff (bore p Q y i (v i))
def weight_one (v : Roster p) : ℂ := ∑ i : I, coeff 1 (bore p Q y i (v i)) *
    ∏ j ∈ univ.erase i, constantCoeff (bore p Q y j (v j))

theorem one_register (v : Roster p) (hn : Even n.val) :
    coeff 1 ((∏ i,bore p Q y i (v i)) * redo Q.team y (closed R (board p v) x)) =
    if Even (named (board p v)) then
      weight_one p Q y v * coeff 0 (closed R (board p v) x)
    else coeff 1 (closed R (board p v) x) * weight_zero p Q y v := by
  let a := closed R (board p v) x
  let f := fun i : I => bore p Q y i (v i)
  have h0 : constantCoeff (redo Q.team y a) = coeff 0 a :=
    (coeff_zero_eq_constantCoeff_apply _).symm.trans (slide_zero Q.team y a)
  have hp : coeff 1 (∏ i,f i) = weight_one p Q y v := Pert.First.first_product f univ
  have hc : constantCoeff (∏ i,f i) = weight_zero p Q y v := map_prod .. 
  change coeff 1 ((∏ i, f i) * redo Q.team y a) = _
  rw [coeff_one_mul,h0,slide_one,hp,hc]
  by_cases he : Even (named (board p v))
  · rw [if_pos he]
    have ho : Odd (1+named (board p v)) := Nat.odd_iff.mpr (by have := Nat.even_iff.mp he;omega)
    have hz : coeff 1 a = 0 := closed_price R (board p v) x hn 1 ho
    rw [hz,zero_mul,add_zero]
  · rw [if_neg he]
    have ho : Odd (0+named (board p v)) := by simpa only [zero_add] using Nat.not_even_iff_odd.mp he
    have hz : coeff 0 a = 0 := closed_price R (board p v) x hn 0 ho
    rw [hz,mul_zero,zero_add]

theorem issued (hn : Even n.val) (he : e≠0) :
    coeff 1 (newEra R.metals.O (basisR R) Q y p x e) =
    (e:ℂ)⁻¹ ^ wt p * ∑ v : Roster p, if Even (named (board p v)) then
      weight_one p Q y v * coeff 0 (closed R (board p v) x)
    else coeff 1 (closed R (board p v) x) * weight_zero p Q y v := by
  rw [← normalized R p x Q y e he]
  unfold filed
  rw [coeff_C_mul,map_sum]
  exact congrArg (fun u : ℂ => (e:ℂ)⁻¹^wt p * u) (sum_congr rfl fun v _ => one_register R p x Q y v hn)

end YM.Integration.WilsonRichFirstCorrected

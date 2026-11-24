import YM.GradedFar.Continuation.Safe

/-! The T^h cost for a genuine detector inversion in M4. -/
namespace YM.FVA2.GradedFar.Continuation.Margin
noncomputable section
open Filter Set Real Topology Function PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe
open Window
open Stretch (till Deep Stiff)
open scoped Topology BigOperators Classical
variable {G : Gauge} {n h : ℕ} {N : WilsonPrescription G} {d : Fin n → ℕ}
  {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)

lemma matrix_estate {ι E : Type} [Fintype E] [DecidableEq E]
    (P : ι → Matrix E E ℂ) (L : Filter ι) (M : Matrix E E ℂ) (hm : IsUnit M)
    (h : ∀ j k, Tendsto (fun i => P i j k) L (𝓝 (M j k))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in L, IsUnit (P i) ∧ ∀ j k, ‖((P i)⁻¹) j k‖ ≤ C := by
  have hp : Tendsto P L (𝓝 M) := show Tendsto (f:=fun i j k => P i j k) L
    (𝓝 fun j k => M j k) from tendsto_pi_nhds.mpr fun j => tendsto_pi_nhds.mpr (h j)
  have hd : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hm).ne_zero
  have he := (Continuous.matrix_det (by exact continuous_id : Continuous (id : Matrix E E ℂ → _))).continuousAt (x:=M)
  have hinv : ContinuousAt Ring.inverse M.det := by
    have u : (Ring.inverse : ℂ → ℂ)=Inv.inv := funext Ring.inverse_eq_inv; rw [u]
    exact continuousAt_inv₀ hd
  have hI : Tendsto (fun i => (P i)⁻¹) L (𝓝 (M⁻¹)) := (continuousAt_matrix_inv M hinv).tendsto.comp hp
  obtain ⟨q,hq⟩ := Finite.bddAbove_range (fun x : E×E => ‖M⁻¹ x.1 x.2‖)
  let C := max 1 (q+1)
  have hQ (a b) : ∀ᶠ i in L, ‖(P i)⁻¹ a b‖ ≤ C := by
    have B : Continuous (fun i : Matrix E E ℂ => ‖i a b‖) := by fun_prop
    have lt : ‖M⁻¹ a b‖ < C := lt_of_le_of_lt (hq (show ‖M⁻¹ a b‖ ∈ _ from ⟨(a,b),rfl⟩))
      (lt_max_of_lt_right (lt_add_one q))
    exact ((B.continuousAt.tendsto.comp hI).eventually_lt_const lt).mono fun i hi => hi.le
  refine ⟨C,lt_max_of_lt_left zero_lt_one,?_⟩
  -- type at point
  have hx : Tendsto (fun i => (P i).det) L (𝓝 M.det) := he.tendsto.comp hp
  filter_upwards [hx.eventually_ne hd,(show ∀ᶠ i in L, ∀ a b, ‖(P i)⁻¹ a b‖ ≤ C from
    eventually_all.mpr (fun _ => eventually_all.mpr (fun _ => hQ ..)))] with i hi hz
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hi),hz⟩

variable {I : Type} (t : ℝ → ℝ) {c C η B : ℝ} (hb : 0<B) (hc : 0<c) (hC : c ≤ C)
  {p P : ℕ} (ht : Tendsto (fun r => t r/gYM G r) (𝓝[>] (0:ℝ)) (𝓝 1))
  {Z : ChangeAt G} {D0 : TagAt G (fun _ : Fin 1 => h) I h}
  (hp : Stretch.Deep p P B h h η) (hη : 0<η)
  (hD : ∀ L R, WithinError N M D0 Z (upper G C B) {0} {RootG} t p L R)

local notation "l₀" => Window.windows (band G c C B)
-- ∥·∥ as coordinate max on entries in this basis
include hD H hb hc hC ht hp hη
theorem pivot_safe :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ (w : Window) in l₀, ∀ i,
      IsUnit (measuredAt Z D0 w i) ∧ ∀ a b, ‖(measuredAt Z D0 w i)⁻¹ a b‖ ≤ R*w.Stretch^h := by
  obtain ⟨R,hR,hu⟩ := matrix_estate (fun w : Window × I => markedAt Z D0 w.1 w.2) _
    (Read.GramP G h) (Read.positive_unit Read.GramP_pos) (safe H t hb hc hC ht hp hη hD)
  refine ⟨R,hR,?_⟩
  filter_upwards [eventually_comap.mp hu,(Window.windows_separation _).eventually_ge_atTop (0:ℝ)] with w hw ht
  intro i
  let D:=measuredAt Z D0 w i; let E:=markedAt Z D0 w i
  have hu : IsUnit E ∧ ∀ j k, ‖E⁻¹ j k‖ ≤ R := hw ((w,i):Window×I) rfl
  let Y := Matrix.diagonal (fun a : Toon G h => toll a w)
  have hx : E = D*Y := by ext j k; exact (mul_comm ..).trans (Matrix.mul_diagonal (fun a => toll a w) D j k).symm
  have z : D*(Y*E⁻¹) = 1 := by
    rw [← _root_.mul_assoc, ← hx]; exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu.1)
  have hz : IsUnit D.det := Matrix.isUnit_det_of_right_inverse z
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).mpr hz,?_⟩; intro a b
  change ‖(D⁻¹) a b‖ ≤ _
  rw [left_inv_eq_right_inv (Matrix.nonsing_inv_mul _ hz) z, Matrix.diagonal_mul, norm_mul,toll_norm]
  rw [mul_comm]; exact mul_le_mul (hu.2 a b) (pow_le_pow_right₀ (Real.one_le_exp ht) (size_le a))
    (by unfold Window.Stretch; positivity) hR.le
end
end YM.FVA2.GradedFar.Continuation.Margin

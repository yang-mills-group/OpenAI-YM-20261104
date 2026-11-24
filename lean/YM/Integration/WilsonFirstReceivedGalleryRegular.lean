import YM.QuadraticLocal.Lamps
import YM.Comparison.RG02.Algebra.Markers

noncomputable section
namespace YM.Integration.WilsonFirstReceivedGalleryRegular

open Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Fusion.Attached Comparison.RG02 Finset
open Extra.Trajectories Primitives.GCC.Anchor Multi
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V T ι : Type} [DecidableEq V] {R : Census V}
variable {o : V → Site n} {P : Rep G n} {w : V → ℝ} {a b : ℝ}

theorem clear (A : Gallery T ι o P R) (t : T) (U : Config G n)
    (hU : flags P.p.threshold U = ∅) :
    A.gas t U = 1 := by
  unfold Gallery.gas
  rw [tsum_eq_single ∅]
  · have h : P.activities.admissible P.p U ∅ := by simp [Activities.admissible,hU]
    simp [packet,h]
  intro l hl
  have inad : ¬ P.activities.admissible P.p U l := by
    intro hlive
    obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hl
    obtain ⟨x,hx⟩ := (P.activities.forced i).inventory_ne
    have hv : x∈flags P.p.threshold U := by
      rw [←hlive.2]
      exact Finset.mem_biUnion.mpr ⟨i,hi,hx⟩
    simp [hU] at hv
  simp [packet,inad]

theorem measured [Fintype V] (A : Gallery T ι o P R) (t : T) (U : Config G n)
    (hU : flags P.p.threshold U = ∅)
    (sums : Summable fun i => A.E.frame i t U) :
    connected (((P.eval U : ℂ)⁻¹) • A.density t U) = A.E.log t U := by
  have e : (P.eval U : ℂ) = (Real.exp (P.exponent U) : ℂ) := by
    simp [Rep.eval,P.activities.gas_one P.p hU]
  rw [Gallery.density,clear A t U hU,mul_one,e,smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast (Real.exp_ne_zero (P.exponent U))),one_smul]
  exact connected_pass (Lamps.quiet_of_hasSum t U sums)

theorem occupied (L : Lamps T ι G P.p o R) (h : L.Paid w P.p.B a b)
    (ha : 0≤a) (hw : ∀v, 0<w v) (t : T) (U : Config G n) (s : R.Mode)
    (v : V) (hv : v∈s.val) :
    Poly.toll w s * ‖(L.log t U).part s‖ ≤ b := by
  obtain ⟨f,hf,per,hit⟩ := h.budget
  let x := o v
  let z (i : ι) : ℂ := (Poly.toll w s : ℂ) * (L.frame i t U).part s
  have wallet := hit x
  have row (i : ι) : ‖z i‖ ≤ if x∈L.ground i then
      Poly.toll w (L.mode i) * f i * Real.exp (a*coverNumber P.p.B (L.ground i)) else 0 := by
    by_cases hm : s=L.mode i
    · have root : x∈L.ground i := L.roots i v (hm ▸ hv)
      have hlt := L.light_size i t U (per i t _ (L.address i).anchor)
      have hwt := (Poly.worth hw s).le
      have hex : 1≤Real.exp (a*coverNumber P.p.B (L.ground i)) :=
        Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _))
      rw [if_pos root,←hm]
      simp only [z,Lamps.frame,Poly.part_send,if_pos hm,norm_mul,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg hwt]
      exact (mul_le_mul_of_nonneg_left hlt hwt).trans
        (le_mul_of_one_le_right (mul_nonneg hwt (hf i)) hex)
    · simp only [z,Lamps.frame,Poly.part_send,if_neg hm,mul_zero,norm_zero]
      split
      · exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (hf i)) (Real.exp_pos _).le
      · exact le_rfl
  have sum := wallet.2.1.of_nonneg_of_le (fun i=>norm_nonneg (z i)) row
  have eqn : (Poly.toll w s : ℂ) * (L.log t U).part s = ∑'i,z i := by
    rw [Lamps.log,Poly.share (h.sums ha hw t U),tsum_mul_left]
  have price := (norm_tsum_le_tsum_norm sum).trans ((sum.tsum_le_tsum row wallet.2.1).trans wallet.2.2)
  rw [←eqn,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Poly.worth hw s).le] at price
  exact price

end YM.Integration.WilsonFirstReceivedGalleryRegular
end

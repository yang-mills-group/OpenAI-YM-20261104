import YM.Integration.WilsonMacroscopicRichTransitionIncome

/-! Relative cost and measurability of the actual signed derivative of the normalized all-link likelihood, before the cutoff and period. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichConditionalJet
open Function Filter MeasureTheory Set Lattice Wilson RG Source Push.Local Push.Local.Kernel PhysicalNext.Repeat.Legato
open WilsonMacroscopicRichTransitionIncome WilsonMacroscopicRichNormalizedRows
open scoped Classical BigOperators Topology
open private chart_inv invRate_pos from YM.Push.LOCAL_SPLITTING.Response
variable {G : Gauge} {c f : Side}

theorem measurable (S : StepData c f) (hS : S.patch.Branches S.kernel G) (β : ℝ)
    (D : Config G f → ℝ) (hD : Integrable D (prior G f)) (pos : ∀ U, 0 < D U)
    (V : Config G c) (l : List (Directions G c)) :
    Measurable (fun U => leftDerivs (fun W => S.density β U W / S.push β D W) l V) := by
  have smooth := WilsonMacroscopicRichNormalizedRows.chart S hS β D hD (fun V => pass_pos S β Finset.univ hS V hD pos) V l.length
  have id U : leftDerivs (fun W => S.density β U W / S.push β D W) l V = weights S U ⇑(leftDerivs (kernel S β D) l V : C(Config G c,ℝ)) := by
    rw [conditional S β D U,left_linear _ _ smooth le_rfl,evaluated]
  simp_rw [id]; exact weights_meas S hS _

theorem relative (S : StepData c f) (hS : S.patch.Branches S.kernel G) (β : ℝ)
    (D : Config G f → ℝ) (hD : Integrable D (prior G f)) (pos : ∀ U, 0 < D U)
    (J : Edges c) (k : ℕ) {r C : ℝ} (hr : 0 ≤ r) (fee : (noiseFactor G (β*S.kernel.penalty) k J.card r)^k ≤ C)
    (U : Config G f) (V : Config G c) (l : List (Directions G c)) (hl : l.length ≤ k) (ha : ∀ A∈l,Born J r A) :
    ‖leftDerivs (fun W => S.density β U W / S.push β D W) l V‖ ≤
      (2^k * (C * invRate k C k)) * (S.density β U V / S.push β D V) := by
  have hC : 1 ≤ C := (one_le_pow₀ (noiseFactor_ge G _ k J.card hr)).trans fee
  let Z := Complex.ofRealCLM ∘ S.push β D
  let X : Config G c → ℝ := fun W => S.density β U W
  have zp (W : Config G c) : 0 < S.push β D W := pass_pos S β Finset.univ hS W hD pos
  have xp : 0 ≤ X V := (pdf_pos S β Finset.univ hS U V).le
  have zr (W : Config G c) : Chart k (S.push β D) W := smooth_pass S β Finset.univ hS hD W k
  have zc (W : Config G c) : Chart k Z W := Complex.ofRealCLM.contDiff.contDiffAt.comp _ (zr W)
  have xr : Chart k X V := by
    change Chart k (fun W => S.density β U W) V; rw [assigned S β U]
    exact (mixture S U).contDiff.contDiffAt.comp _ (smooth_lift S β Finset.univ V k)
  have xc : Chart k (Complex.ofRealCLM ∘ X) V := Complex.ofRealCLM.contDiff.contDiffAt.comp _ xr
  have hZ (W : Config G c) : ‖Z W‖ = S.push β D W := (Complex.norm_real _).trans (Real.norm_of_nonneg (zp W).le)
  have zn (W : Config G c) : Z W ≠ 0 := Complex.ofReal_ne_zero.mpr (zp W).ne'
  have hz := inv_bound (Z:=Z) (D:=Born J r) (V:=V) hC (le_refl k) zc zn (fun _ => negative) (fun s hs sb => by
    rw [hZ,show leftDerivs Z s V = _ from left_linear Complex.ofRealCLM s (zr V) hs]
    simpa only [Complex.ofRealCLM_apply,Complex.norm_real] using (denominator S hS β J k hr D hD (fun B => (pos B).le) V s hs sb).trans (mul_le_mul_of_nonneg_right fee (zp V).le))
  have hx (s : List (Directions G c)) (hs : s.length ≤ k) (sb : ∀ A∈s,Born J r A) :
      ‖leftDerivs (Complex.ofRealCLM ∘ X) s V‖ ≤ C * X V := by
    rw [left_linear Complex.ofRealCLM s xr hs]
    simpa only [Complex.ofRealCLM_apply,Complex.norm_real] using (numerator S β J k hr U V s hs sb).trans (mul_le_mul_of_nonneg_right fee xp)
  have price := left_mul_bound xc (chart_inv (zc V) (zn V)) hx hz l hl ha
  let scale : Config G c → ℝ := fun W => X W / S.push β D W
  have bill : Chart k scale V := xr.div (zr V) ((zp _).ne')
  have lifted : Complex.ofRealCLM ∘ scale = (Complex.ofRealCLM ∘ X) * (fun W => (Z W)⁻¹) := by
    funext W; exact (Complex.ofReal_div ..).trans (div_eq_mul_inv ..)
  rw [←lifted,left_linear Complex.ofRealCLM l bill hl,Complex.ofRealCLM_apply,Complex.norm_real,hZ] at price
  apply price.trans
  have hi : 0 ≤ invRate k C k := zero_le_one.trans (invRate_pos k hC k)
  calc _ ≤ (2:ℝ)^k * (C * X V * (invRate k C k * (S.push β D V)⁻¹)) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hl) (mul_nonneg (mul_nonneg (zero_le_one.trans hC) xp) (mul_nonneg hi (inv_nonneg.mpr (zp V).le)))
       _ = _ := by change _ = (2^k * (C * invRate k C k)) * (X V / S.push β D V); ring

end YM.Integration.WilsonMacroscopicRichConditionalJet

import YM.LocalLTE.Hall.Receipt
/-! # Re-box in curved coordinates, maintaining ambient jets -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox.Hall
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open Analysis Slide
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
section
-- Size from positive-degree tensor terms only.
variable {H E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H][NormedSpace ℝ H] {j n p:ℕ} {s b u a t:ℝ}
variable {W A:ℝ→ℝ} {F : H→E} {x:H} {f:E→ℝ}
open Tensor
lemma radiant {r:ℝ} (h: Brush j s r F x) (i:ℕ) {M:Type}[NormedAddCommGroup M][NormedSpace ℝ M](T:Tensor.T E M i) : Brush j (‖T‖ * s^i) ((i:ℝ)*r) (Tensor.diagonal T ∘ F) x:= by
  induction i generalizing M with
  | zero =>
    have he: Tensor.diagonal T=(fun _ => T (fun _=>0)):=funext fun y=> congr_arg T (Subsingleton.elim ..)
    simp only [he,pow_zero,mul_one]; have hp : Brush j (‖T (fun _=>0)‖) (↑(0:ℕ)*r) ((fun _:E=>T (fun _=>0)) ∘ F) x:= certified (by simp) _
    exact hp.climb (T.fin0_apply_norm.le) le_rfl
  | succ i ih=>
    let Q:= T.curryRight; have he:= ih Q; let R: (E →L[ℝ] M) →L[ℝ] E →L[ℝ] M:=ContinuousLinearMap.id ..
    apply ((he.twins h R).climb ?_ ?_).shimmy
    · refine Eventually.of_forall fun y=>?_ ; change Tensor.diagonal T (F y)= Q (fun _=>F y) (F y); unfold Q; simp only [ContinuousMultilinearMap.curryRight_apply]; unfold Tensor.diagonal; congr 1; ext k; induction k using Fin.lastCases <;> simp
    · have hq:0≤ (‖Q‖*s^i*s):= mul_nonneg (mul_nonneg (ContinuousMultilinearMap.opNorm_nonneg _) (pow_nonneg h.nonneg _)) h.nonneg
      refine le_trans (mul_le_of_le_one_left hq (ContinuousLinearMap.norm_id_le)) (le_of_eq ?_); unfold Q; rw [T.curryRight_norm]; ring
    push_cast; ring_nf; exact le_rfl
lemma rotunda (h: ∀ (q:ℕ), n > q → q > 0 → Blaze.normJ q f 0 ≤ b) (u:E)(hs:1 ≤ s)(hh: ‖u‖ ≤ s)(ht:0≤b)(hp: Brush j s 1 F x) : Brush j ((n:ℝ)* (2*b*s^n)*(1+(n:ℝ))^j) 1 (fun i=> stem n f (F i)- stem n f u) x:= by
   let a:=2*b*s^n; have ha:0≤a:= by unfold a; positivity
   let K (i:ℕ)(z:H):= Tensor.diagonal (coeff f i 0) (F z)-Tensor.diagonal (coeff f i 0) u
   have he (i:ℕ)(hi:i<n) : Brush j a (n:ℝ) (K i) x:= by
      by_cases h₁:i=0
      · subst i; have ht x: Tensor.diagonal (coeff f 0 0) x=Tensor.diagonal (coeff f 0 0) u:= congr_arg (coeff f 0 0) (Subsingleton.elim ..)
        rw [show K 0= (fun _=>0) from funext fun z=> sub_eq_zero.mpr (ht (F z))]; exact (Brush.certified (by positivity : 0≤ (n:ℝ)) (0:ℝ)).climb (norm_zero.trans_le ha) le_rfl
      let P:= coeff f i 0
      have hK : ‖P‖ ≤ b:= by
         unfold P coeff; rw [norm_smul,norm_inv,Real.norm_natCast]; exact (mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (by exact_mod_cast (Nat.factorial_pos i)))).trans (h i hi (Nat.pos_of_ne_zero h₁))
      have hv: Brush j s 1 (fun _:H=> u) x:=(Brush.certified zero_le_one _).climb hh le_rfl
      refine ((Brush.separating (radiant hp i P) (radiant hv i P)).climb ?_ ?_) -- edit
      · unfold a; have hZ := mul_le_mul hK (pow_le_pow_right₀ hs hi.le) (pow_nonneg hp.nonneg i) ht; linarith only [hZ]
      rw [mul_one]; exact_mod_cast hi.le
   have hv:= (Brush.spree (Finset.range n) _ (fun _=>a) (k:=j) (by positivity : 0≤ (n:ℝ)) (fun i hi=> he i (Finset.mem_range.mp hi))).trim
   simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hv
   apply hv.shimmy; apply Eventually.of_forall; intro i; unfold stem; simp only [Finset.sum_apply,← Finset.sum_sub_distrib]; rfl
end
end YM.LocalLTE.FrameBox.Hall

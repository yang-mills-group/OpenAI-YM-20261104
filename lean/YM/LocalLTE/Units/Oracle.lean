import YM.LocalLTE.Units.Norm
import YM.LocalLTE.Frame.Mantle
/-! BoxPoly shear: budget from input leases. Polynomial field type.
Can be rotated using an orientation-specific grove when moving. No gauge estimates outside its support. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard
open Analysis
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c : Side} {o q : Site c} {m d j:ℕ}
open Grove
local notation "E"=> Directions G c
open Cabana
def clear (X:Grove o)(m:ℕ)(P:Pkt (Directions G c) d):Pkt (Directions G c) d:= fun i=> Tensor.symmetrize ((P i).compContinuousLinearMap (fun _=> X.shore m))
lemma rays (X:Grove o)(m:ℕ)(P:Pkt (Directions G c) d) (x: Directions G c) : Cabana.actual (FrameBox.clear X m P) x=Cabana.actual P (X.shore m x):= by
  simp only [Cabana.actual,Finset.sum_apply,FrameBox.clear,Tensor.symmetrize_diagonal]; rfl
lemma cleans (X:Grove o)(m:ℕ)(P:Pkt (Directions G c) d) (x:Fin d):Tensor.Sym (FrameBox.clear X m P x):= Tensor.symmetrize_sym _

def realise (X:Grove o)(m:ℕ)(κ:ℝ)(P:Pkt (Directions G c) d)(U:Config G c):= Cabana.actual P (X.crook m Chi.canonical κ U)
def Polynomial (m:ℕ)(κ:ℝ)(o:Site c)(d:ℕ)(f:Config G c→ℝ):Prop:= ∃ (X:Grove o)(P:Pkt (Directions G c) (d+1)), f = FrameBox.realise X m κ P

lemma cups {A : Type} [NormedAddCommGroup A][NormedSpace ℝ A] {F:A→E} {s r:ℝ} {x:A} (h: Brush j s r F x) (i:ℕ) {M:Type}[NormedAddCommGroup M][NormedSpace ℝ M](T:Tensor.T (Directions G c) M i) : Brush j (‖T‖ * s^i) ((i:ℝ)*r) (Tensor.diagonal T ∘ F) x:= by
  induction i generalizing M with
  | zero =>
    have he: Tensor.diagonal T=(fun _=> T (fun _=>0)):=funext fun y=> congr_arg T (Subsingleton.elim ..)
    simp only [he,pow_zero,mul_one]; have hp : Brush j (‖T (fun _=>0)‖) (↑(0:ℕ)*r) ((fun _:E => T (fun _=>0)) ∘ F) x:= certified (by simp) _
    exact hp.climb (T.fin0_apply_norm.le) le_rfl
  | succ i ih=>
    -- curry right in accumulation
    let Q:= T.curryRight; have he:= ih Q; let R: (E →L[ℝ] M) →L[ℝ] E →L[ℝ] M:=ContinuousLinearMap.id ..
    apply ((he.twins h R).climb ?_ ?_).shimmy
    · refine Eventually.of_forall fun y=>?_ ; change Tensor.diagonal T (F y)= Q (fun _=>F y) (F y); unfold Q; simp only [ContinuousMultilinearMap.curryRight_apply]; unfold Tensor.diagonal; congr 1; ext k; induction k using Fin.lastCases <;> simp
    · have hq:0≤ (‖Q‖*s^i*s):= mul_nonneg (mul_nonneg (ContinuousMultilinearMap.opNorm_nonneg _) (pow_nonneg h.nonneg _)) h.nonneg
      refine le_trans (mul_le_of_le_one_left hq (ContinuousLinearMap.norm_id_le)) (le_of_eq ?_); unfold Q; rw [T.curryRight_norm]; ring
    push_cast; ring_nf; exact le_rfl

variable {κ k:ℝ}
lemma supply (G:Gauge)(d j:ℕ)(hk: Reliable G κ k): ∃ C:ℝ,0≤C ∧ ∀ (c:Side) (m:ℕ) (B:BudgetPoint) (o:Site c) (X:Grove o)(P:Pkt (Directions G c) (d+1))(ξ : ℝ) (s:Site c) (Z:Support c), B.supBounds s (Z) (FrameBox.realise X m κ P) ξ →
    ∀ (v r:ℝ),1≤v →0≤r→ ∀ (A : Type) [NormedAddCommGroup A][NormedSpace ℝ A](F:A→Directions G c)(x:A), Brush j v r F x →
      Brush j (C*ξ*B.threshold⁻¹^d*v^d) ((d:ℝ)*r) ((Cabana.actual (FrameBox.clear X m P)) ∘ F) x:=by
  obtain ⟨U,hU,h⟩:= sound_ball G (χ:=Chi.canonical) hk
  choose L hL hV using fun i:Fin (d+1)=> Cabana.price (d+1) i
  let C i:= L i*U⁻¹^(i.val:ℕ); refine ⟨∑ i,C i,sum_nonneg fun i _=> mul_nonneg (hL i) (by positivity),?_⟩
  intro c m B o X P ξ s Z he v r hv hr A _ _ F x hp
  let K:= FrameBox.clear X m P; let Q:=(X.crook (G:=G) m Chi.canonical κ); let b:= B.threshold
  have hb:1≤b⁻¹:= (one_le_inv₀ B.threshold_pos).mpr B.threshold_le
  have hp' (i:Fin (d+1)): ‖K i‖ ≤ L i * ξ * (U*b)⁻¹^i.val:= hV _ _ _ _ _ (cleans _ _ _) (mul_pos hU B.threshold_pos) he.1 fun y hy=> by
    obtain ⟨hh,hF⟩:= h c B o X m y hy; have hVp:= he.2 (soloV (X.shore m y)) (hF.mono_left (subset_univ _)) [] (by simp) (by simp); change ‖Cabana.actual P (Q _)‖ ≤ _ at hVp; rw [show Q _=_ from hh] at hVp; exact le_trans (le_of_eq (congr_arg _ (rays ..))) hVp
  rw [Finset.sum_mul, Finset.sum_mul,Finset.sum_mul]
  have hh (i:Fin (d+1)): Brush j (C i*ξ*B.threshold⁻¹^d*v^d) ((d:ℝ)*r) (Tensor.diagonal (K i) ∘ F) x:=by
    have he': i.val ≤ d:= by omega
    refine (cups hp _ (K i)).climb (le_trans (mul_le_mul (hp' _) (pow_le_pow_right₀ hv he') (pow_nonneg hp.nonneg _) ((ContinuousMultilinearMap.opNorm_nonneg _).trans (hp' i))) (mul_le_mul_of_nonneg_right ?_ (by positivity))) (by exact mul_le_mul_of_nonneg_right (by exact_mod_cast he') hr)
    calc _ = C i * ξ * b⁻¹^i.val := by unfold C; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb he') (mul_nonneg (mul_nonneg (hL i) (by positivity)) he.1)
  apply (spree Finset.univ _ _ (by positivity) (fun i _=> hh i)).shimmy
  apply Eventually.of_forall; intro y; simp only [Function.comp_apply,Cabana.actual, Finset.sum_apply]; rfl
end YM.LocalLTE.FrameBox

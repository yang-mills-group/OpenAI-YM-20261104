import YM.MatchingLedger.Compass.Program
import YM.UVExt.DualTiles
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Divisors
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Spectrum

/-!
# Recover exact `draft` even though winding prevents exact finite-horizon equality
  with stationary `thermal`.

 Use port `AsDivisors`; every admissible period measured here. No band's widths or read
 permitted to drift by volume or after-wave costs. Fourier polar prices *before* contraction
 not part of this exact calculation. Replicated inputs paid at actual period, still ANY
 polar pair, so no cover kernel limit required, and no tacit claim of finding a Sewing
 representation. Inspired by UVExt's stationary limit comparisons; unlike them this compares
 different SOLUTIONS not horizons large, no IR discretization left in `equal_draft`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.MatchingLedger.Compass
open Function Filter Set Precision RG Tree Wilson Lattice Work Exterior
open WilsonStartup.Change Extension.UV.LoopRate Extension.UV.StationaryData Bid
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {A:Levels G}{C:ChartRatio G} (ht:LocalRatio C)

namespace Mirrors
variable {c c' f f':Side} {P:Patch} {k:ℕ} {Y: f.val=c.val*P.L.val}{T:f'.val=c'.val*P.L.val}
    (h:c'.val=c.val*k)(he: 2≤c.val)
    (α:ℝ)(q:Clip)(W:PathData G)
    (hd:ContDiffAt ℝ ω (draft (c:=c') α W q) 0)
open PhysicalNext.Repeat.Pane Function Filter MeasureTheory
include h he hd Y T
abbrev H₂ {n : Side} (Z:fieldDir G n 1→ℝ) := iteratedFDeriv ℝ 2 Z 0
-- Exact multilinear response BEFORE normalization to one per-site
lemma gathers (p q':Site c) (σ τ : TypeFace 1→G.ColorIndex→ℂ) :
    let e:=wrap c' (k • lift p); let d:=wrap c' (k • lift q');
    H₂ (draft α W q) ![wave e σ,wave d τ] = (↑(k^4):ℝ)*H₂ (draft α W q) ![wave p σ,wave q' τ]:=by
   intro e d; let J:=coverC (h:=Y) (H:=T) (G:=G) h he
   have hv : 0<k:= Nat.pos_of_mul_pos_left (show 0<c.val*k from h ▸ c'.pos)
   let U:=draft (c:=c') α W q; let X:= draft (c:=c) α W q
   have hm: iteratedFDeriv ℝ 2 (U ∘ J) 0=(↑(k^4):ℝ) • H₂ X:=
     (compensate J (a:=X) (b:=U) (ε:=(↑(k^4):ℝ)) (Eventually.of_forall (fun x=>pays_pile (h:=Y) (H:=T) h he W q x α)) (by positivity) hd).2 _
   change H₂ U _= _
   rw [← show J (wave p σ)=wave e σ from oscillate (h:=Y) (H:=T) h he .., ← show J (wave q' τ)=wave d τ from oscillate (h:=Y) (H:=T) h he ..,show H₂ U ![_,_] = (iteratedFDeriv ℝ 2 (U ∘ J) 0) ![wave p σ,wave q' τ] from ?_,hm]
   · rfl
   rw [jet_liner J U hd,ContinuousMultilinearMap.compContinuousLinearMap_apply]; apply congr_arg (H₂ U); ext1 i;fin_cases i<;> rfl

section waves
omit Y T h he hd
variable {A:Type}[NormedAddCommGroup A][NormedSpace ℝ A]
private def evaluate (Z:Tensor.T A ℝ 2) : A→L[ℝ] A→L[ℝ] ℝ:= (continuousMultilinearCurryFin1 ℝ A ℝ).toContinuousLinearEquiv.toContinuousLinearMap ∘L Z.curryLeft
private lemma evaluate_price (Z:Tensor.T A ℝ 2) (x y:A): evaluate Z x y=Z ![x,y]:=by
    unfold evaluate; rw [ContinuousLinearMap.comp_apply]; change ((continuousMultilinearCurryFin1 ℝ A ℝ) _) y = _; rw [continuousMultilinearCurryFin1_apply,ContinuousMultilinearMap.curryLeft_apply]; apply congr_arg Z; ext1 i; fin_cases i <;> simp
open UVExt.Paths.Covering
lemma takes (U V : Tensor.T (Dir G c) ℝ 2) (h : ∀ p q:Site c,∀ σ τ,(∀ i j,‖σ i j‖≤1) → (∀ i j, ‖τ i j‖ ≤ 1) → U ![wave p σ,wave q τ]=V ![wave p σ,wave q τ]): U=V:=by
  have he (p q:Site c)(σ τ: TypeFace 1→G.ColorIndex→ℂ): evaluate U (wave p σ) (wave q τ)=evaluate V (wave p σ) (wave q τ):=by
    let x:ℝ := (1+max ‖σ‖ ‖τ‖)⁻¹; have hp : 1 ≤ 1+max ‖σ‖ ‖τ‖:= le_add_of_nonneg_right (by positivity)
    have hx: x≠0:= by unfold x; positivity
    have hf {a : TypeFace 1→G.ColorIndex→ℂ} (t:‖a‖ ≤ 1+max ‖σ‖ ‖τ‖): ∀ p k,‖(x:ℂ)*a p k‖ ≤1:= by
      intro r k; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by unfold x; positivity)]
      unfold x; exact le_trans (mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ _).trans (norm_le_pi_norm a r)|>.trans t) (by positivity)) (inv_mul_cancel₀ (by positivity)).le
    have hh:evaluate U (x • wave p σ) (x • wave q τ)=evaluate V (x • wave p σ) (x • wave q τ):=by
      rw [wave_scale p,wave_scale q, evaluate_price,evaluate_price]
      exact h _ _ _ _ (hf ((le_max_left ..).trans (le_add_of_nonneg_left zero_le_one))) (hf ((le_max_right ..).trans (le_add_of_nonneg_left zero_le_one)))
    simp only [map_smul,_root_.smul_apply] at hh; exact mul_left_cancel₀ hx (mul_left_cancel₀ hx hh)
  have ha(x y:Dir G c): evaluate U x y=evaluate V x y:=by
    obtain ⟨p,rfl⟩:=UVExt.Paths.Covering.wave_sum_rep x; obtain ⟨q,rfl⟩:=UVExt.Paths.Covering.wave_sum_rep y
    simp only [map_sum,_root_.sum_apply,he]
  ext1 i; rw [show i=![i 0,i 1] from (by ext1 j;fin_cases j <;> rfl), ←evaluate_price,← evaluate_price]; apply ha
end waves
end Mirrors
end YM.MatchingLedger.Compass

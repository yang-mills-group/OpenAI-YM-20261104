import YM.MS.Graphical.OscillatingPlane
import YM.MS.Fiddle.Tow

/-!
# Cost of phases inside continued-dimension integration

At a common fixed separation as the scale goes to zero. Keep axis variables
on the *same* physical 4-plane even at nested nonzero-regulator joins.
Here prove indexed estimates: later application includes functions indexed by
the logarithmic scale as well as by complex `z` running over a compact; `s i`
can e.g. be scale **length** relative to an upper scale.
-/

noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open Osc
open scoped Topology ContDiff
variable {X E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
    {G : Gauge} {a : Tone.QP} {w s : I → ℝ} {m n : ℕ} {u : ℝ}

lemma phase_smul (t : ℝ) (u : Tone.QP) (x : SectorP m) : phase m (t • u) x = phase m u (t • x) := by
  unfold phase Tone.bill Momentum.pairing; rw [map_smul]; simp only [Pi.smul_apply,smul_eq_mul,mul_assoc]; congr! 3; apply Finset.sum_congr rfl; intro; intros; ring

/-- The scaled displacement for dimensionless integration. -/
private def Tphase (s : I→ℝ) (a : Tone.QP) (i : I) := ((s i)⁻¹ : ℝ) • a
variable (hw : ∀ i,0<s i) (hs : ∀ i, s i≤1)

include hw hs
theorem gains {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : I → (SectorP m× X) × E → ℂ}
    (h : quiet 0 f w) (ha : a ≠ 0) (k : ℕ) : quiet 0 (fourierPlane (Px m) f (fun i => phase m ((s i)⁻¹ • a)))
     (fun i=> w i * s i^k) := by
  obtain ⟨x,hx,hp⟩:= Fiddle.flare (norm_pos_iff.mpr ha) (le_refl _)
  let U (i:I) := Tphase s a i; let L:= Left (Nat.zero_le m); let T i := L (s i • x); let C:= 1+‖L x‖
  have hC : 0<C:= by unfold C; positivity
  have hD i : ‖T i‖ ≤ C*s i:= by
    unfold T C; rw [map_smul,norm_smul]; rw [Real.norm_of_nonneg (hw i).le]; nlinarith [ hw i]
  have H (i:I) (z:SectorP m) : phase m (U i) (z-T i)= -1*phase m (U i) z:= by
      have ht : Tone.bill (U i) (Cl (Nat.zero_le m) (T i))= -1:= by
        change phase m (U i) (L (s i • x))= -1
        unfold U Tphase; rw [phase_up,phase_smul,inv_smul_smul₀ (hw i).ne']; exact hx
      unfold phase; rw [map_sub,Fiddle.lounge,ht, inv_neg,inv_one]
  have hv := every_plane (Px m) h (u:=fun i=>phase m (U i)) (fun i=>
     ⟨fun x=>(Tone.bill_norm ..).le, (Fiddle.bill_sm (U i)).continuous.comp (Cl (Nat.zero_le m)).continuous⟩)
     H (fun i=>(hD i).trans (mul_le_of_le_one_right hC.le (hs i))) hC.le hD k
  exact hv.monotone ⟨C^k,pow_pos hC _,0,fun i p _=> by
    simp only [pow_zero,mul_one]; rw [mul_pow]; apply le_of_eq; ring⟩

/-- multiplying the partially integrated value by the remaining external phase. -/
theorem keeps {f : I → X × E → ℂ} (a : Tone.QP) (L : X × E→L[ℝ] Tone.QP)
   (hf : ∀ k:ℕ, quiet 0 f (fun i=> w i*s i^k)) (k : ℕ) :
    quiet 0 (fun i p=> Tone.bill ((s i)⁻¹ • a) (L p) * f i p) (fun i=> w i*s i^k) := by
  intro j
  let S:= Arc.path (0:UScale I); let K:Cost I (X×E):= S.slow fun _=>Set.univ
  let Y(i:I)(p:X × E) := w i/(S.weight i p.1)^j
  have hq (i:I) : ‖(s i)⁻¹ • a‖=‖a‖*(1/s i):= by rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (hw i).le),mul_comm,one_div]
  have he (k:ℕ)(i:I)(p:X× E): Y i p*s i^k=w i*s i^k/S.weight i p.1^j := by unfold Y; ring
  obtain h := Fiddle.pulseCost L (K:=K) (S:=S) (g:=Y) (by intro k; simp_rw [he]; exact hf k j) hw hs
        (V:= fun i=> (s i)⁻¹ • a) ⟨1+‖a‖,(by positivity),0,
         fun i p _=> by simp only [hq,S,cheap_length,pow_zero,mul_one]; have hz:=hw i; gcongr; simp ⟩ k
  simp_rw [he] at h; exact h
end YM.MS.Graphical

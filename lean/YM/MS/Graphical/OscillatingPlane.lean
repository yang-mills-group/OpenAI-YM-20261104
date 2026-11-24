import YangMills.WilsonProof.NativeSupport.YM.MS.Arc.Forest
import YM.MS.Osc.Wave
import YangMills.WilsonProof.NativeSupport.YM.MS.Arc.Pumps
import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.Anchoring

/-!
# Oscillation inside a layer of the continued-dimension integral

Keep the rapid estimate in the remaining internal variable Y (and usual
polynomial bounds on E) after doing
this one Fourier integral. Arbitrarily many powers of decay in the frequency
parameter for the application via half-turn shifts in `every_plane`
(`PinPhases.lean`). This is not the mere pointwise Riemann-Lebesgue lemma. Here `z : UScale I` is just
a cost argument (we will apply e.g. with `z=0` and the *dimensional*
regulator separately allowed to run in a compact). The shift-cost rate `w`
majorizes the norm of the half-turn shift.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open Osc
open scoped Topology ContDiff
variable {X Y T I E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [MeasurableSpace X] [BorelSpace X] [FiniteDimensional ℝ X] (μ : Measure X) [μ.IsAddHaarMeasure]
variable {z : UScale I} {a w : I → ℝ} {f : I → (X × Y) × E → ℂ} {u : I → X → ℂ}
    (h : quiet z f a) (hx : ∀ i, Peak (u i))

def fourierPlane (f : I → (X × Y) × E → ℂ) (u : I → X → ℂ) (i : I) (p : Y × E): ℂ :=
    ∫ q, u i q * f i ((q,p.1),p.2) ∂μ

include h hx
/-- Uniform through all jet orders. Like `MS/Arc/Forest`'s `Q.Gquiet`. -/
lemma quiet_plane : quiet z (fourierPlane μ f u) a := by
  let A: (X×Y×E)→L[ℝ](X×Y)×E:= (((ContinuousLinearMap.fst ℝ X (Y×E)).prod
       ((ContinuousLinearMap.fst ℝ Y E).comp (ContinuousLinearMap.snd ℝ X (Y×E)))).prod
       ((ContinuousLinearMap.snd ℝ Y E).comp (ContinuousLinearMap.snd ℝ X (Y×E))))
  let F i x (q:Y×E):= u i x * f i ((x,q.1),q.2); have he i: Majorant μ (F i):= Vmajor (hx i) (Q.Gmajor μ h i)
  apply Q.fromM (fun i=> (he i).contDiff); intro j k; let N:=Module.finrank ℝ X+1
  let Lp (p:X):=((1+‖p‖)^N)⁻¹; obtain ⟨C,hC,b,hb⟩:= Arc.deep h j N k
  let D:=max 1 (∫ p:X, Lp p ∂μ); have hP (i:I): Integrable Lp μ:= by
    have hm:= Reserve.dustInteg (S:=Arc.path z) (μ:=μ) (i:=i) N (by unfold N; omega)
    convert hm using 1; unfold Lp; ext x; simp [Scale.dust, Scale.weight]
  refine ⟨C*D,mul_pos hC (lt_max_of_lt_left zero_lt_one),b,fun i p q=>?_⟩
  let W:=(1+‖p‖)^k; let Hx:=((1+|z i|)*(1+‖q‖))^b*a i; let U:=(p,q)
  have hw: W>0:= by unfold W; positivity
  have ht: 0≤Hx:= by have ht:=Q.nonneg h i; unfold Hx; positivity
  let t(x:X)(q:Y×E):= f i ((x,q.1),q.2);
  rw [(he i).identity]
  change ‖∫ x, iteratedFDeriv ℝ j (F i x) U ∂μ‖*W≤ C*D* _ * a i
  rw [show (C*D)*((1+|z i|)*(1+‖q‖))^b*a i=C*Hx*D from (by unfold Hx; ring)]; apply (le_div_iff₀ hw).mp
  refine (norm_integral_le_of_norm_le ((hP i).const_mul (C*Hx/W)) (Eventually.of_forall fun x=>?_)).trans ?_
  · have hZ := (h.smooth i).comp A.contDiff; have hy:= norm_extDer hZ x U j
    have hc: ContDiff ℝ ∞ (t x):= hZ.comp (f:=fun r:Y×E=>(x,r)) (contDiff_const.prodMk contDiff_id)
    rw [show F i x=(u i x) • t x from rfl, iteratedFDeriv_const_smul_apply (hc.contDiffAt.of_le (by exact_mod_cast le_top)),norm_smul]
    apply le_trans (mul_le_of_le_one_left (norm_nonneg _) ((hx i).pays _)); apply hy.trans
    have hz : (1+‖x‖)^N>0:= by positivity
    obtain hY:= hb i x p q; unfold Lp; dsimp only [U]; rw [← div_eq_mul_inv,le_div_iff₀ hz,le_div_iff₀ hw]
    exact hY.trans_eq (mul_assoc ..)
  rw [integral_const_mul]; unfold D; rw [div_mul_eq_mul_div]; gcongr; exact le_max_right ..

section gains
variable {T0 : I → X} {C : ℝ}
variable (hh : ∀ i x,u i (x-T0 i)= -1 * u i x) (hp : ∀ i, ‖T0 i‖ ≤ C) (hc : 0 ≤ C)
include hh hp hc

lemma every_plane (hw : ∀ i, ‖T0 i‖ ≤ w i) (k : ℕ) :
    quiet z (fourierPlane μ f u) (fun i=> a i*(w i)^k) := by
  induction k generalizing f a with
  | zero=> simpa using quiet_plane μ h hx
  | succ k ih=>
    let S:=Arc.path z
    have hv(i:I): S.length i * ‖(T0 i,(0:Y))‖ ≤ C := by simpa [S,Prod.norm_mk,norm_nonneg] using hp i
    let g:= Osc.shift (fun i=>(T0 i,(0:Y))) f
    have hg : quiet z g (fun i=> a i*w i):= (Osc.step h hv hc).monotone
        (Cost.of_le (fun i _ _=> by simpa [S,Prod.norm_mk,norm_nonneg] using mul_le_mul_of_nonneg_left (hw i) (Osc.sane h i)))
    let F i (p:X×(Y×E)):= f i ((p.1,p.2.1),p.2.2); let N:=Module.finrank ℝ X+1
    have H (i:I)(p:Y×E) := Osc.windCost (C:=C) (x:=a) (f:=F) hx
        (Reserve.cover (S:=S) (μ:=μ) N (by unfold N; omega)) (Q.trees h) hh
        (by simpa [S] using hp) hc (fun _=> measurePreserving_add_left μ _) i p
    have hQ : fourierPlane μ f u= (fun i x=> (2:ℂ)⁻¹*fourierPlane μ g u i x) := by
      funext i x; specialize H i x
      rw [show waveInt u (fun _=>μ) F i x=fourierPlane μ f u i x from rfl,
           show waveInt u (fun _=>μ) (Osc.shift T0 F) i x =fourierPlane μ g u i x from ?_] at H
      · rw [← H]; field_simp; ring
      unfold F g Osc.shift waveInt fourierPlane; obtain ⟨x,y⟩:= x; simp
    rw [hQ]; convert! (ih hg).L (ContinuousLinearMap.mul ℝ ℂ ((2:ℂ)⁻¹)) using 1; ext i; rw [pow_succ]; ring
end gains
end YM.MS.Graphical

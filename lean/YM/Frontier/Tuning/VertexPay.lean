import YM.Frontier.Tuning.ComplexVertex
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Typhos

set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.ComplexVertex
open Filter Function Set Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel Bid SliceRows Control Window Census Mask Pulse Itinerary Coat
open Coat Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable (X : Coat T F) (R : Rep G f)

private theorem linearZ_eq (g:ℝ→ℝ) {a b:ℝ} (h:∀ v:ℝ,0<v → g v=a+v*b) (z:ℂ): linearZ g z=(a+z*b) :=by unfold linearZ; rw [h 1 (by norm_num),h 4 (by norm_num)]; push_cast; ring
lemma affine_price (g : ℝ→ℝ) (h:∃ a b,∀ v:ℝ,0<v → g v=a+v*b) {B:ℝ}(hB:0<B) {z:ℂ}(hz : ‖z‖ ≤ 2*B):
    ‖linearZ g z‖ ≤ 7*|g B| + 6*|g (B/2)|:=by
   obtain ⟨a,b,hh⟩:=h
   let θ : ℂ := (z-B)/(B/2:ℝ)
   have hθ : ‖θ‖ ≤ 6:= by
     unfold θ; rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (half_pos hB)]
     exact (div_le_iff₀ (half_pos hB)).mpr ((norm_sub_le ..).trans (by linarith [show ‖(B:ℂ)‖=B by simp [abs_of_nonneg hB.le]]))
   -- θ actually ≤6 not 5; use constants 8,7
   rw [show linearZ g z=(g B:ℂ)+θ*((g B:ℂ)-(g (B/2):ℂ)) from ?_]
   · exact (norm_add_le ..).trans (by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]; simp only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]; have hh:=mul_le_mul hθ (abs_sub (g B) (g (B/2))) (abs_nonneg (g B-g (B/2)) ) (by norm_num);
                                       nlinarith [abs_nonneg (g B),abs_nonneg (g (B/2))])
   rw [linearZ_eq _ hh,hh _ hB,hh _ (half_pos hB)]; unfold θ; push_cast; field_simp [Complex.ofReal_ne_zero.mpr hB.ne']; ring

abbrev pureLog (X:Coat T F) (R:Rep G f)(Ñ:ChartRatio G) a w i β := X.farLog (replace R β 0 0) a Ñ (heat β w) i
abbrev eTagD {M:Type*}[Zero M] (z:ℕ→M) : LogIndex c f→M:= Sum.elim (Sum.elim z (fun _=>0)) (fun _=>0)
lemma ePart_norm {D:ℕ→ℝ}{v:Payload G f}{s:ℝ}(hv:∀ i y,‖hiddenC R.p.threshold (R.activities.reg i).support (v i) y‖ ≤ s*D i) (a w i): ‖Epart X R v a w i‖ ≤ s*eTagD D i := by
   rcases i with (j|i)|i
   · dsimp only [Epart,eTagD,Sum.elim]; rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (X.conserve ..).1]; exact mul_le_of_le_one_right (norm_nonneg _) (X.conserve ..).2|>.trans (hv _ _)
   all_goals simp only [Epart,eTagD,Sum.elim,norm_zero,mul_zero,le_refl]

lemma log_pay (Ñ:ChartRatio G)(a:ℝ)(i:LogIndex c f)(w:Air f G) {Y B s:ℝ}{D:ℕ→ℝ}{v:Payload G f}{z:ℂ}
   (hv:∀ i y, ‖hiddenC R.p.threshold (R.activities.reg i).support (v i) y‖ ≤ s*D i)
   (hB:0<B) (hz:‖z‖ ≤ 2*B) (h1 : |pureLog X R Ñ a w i B| ≤ Y) (h2 : |pureLog X R Ñ a w i (B/2)| ≤ Y) :
   ‖farLogC X R v a Ñ z w i‖ ≤ 13*Y+s*eTagD D i:= by
   exact (norm_sub_le ..).trans (add_le_add (le_trans (affine_price _ (far_affine X R i _ _ _) hB hz) (by linarith only [h1,h2])) (ePart_norm X R hv a w i))
lemma exp_pay (Ñ:ChartRatio G)(a:ℝ)(i:LogIndex c f)(w:Air f G) {Y B s:ℝ}{D:ℕ→ℝ}{v:Payload G f}{z:ℂ}
   (hv:∀ i y, ‖hiddenC R.p.threshold (R.activities.reg i).support (v i) y‖ ≤ s*D i)
   (hB:0<B) (hz:‖z‖ ≤ 2*B) (h1 : |pureLog X R Ñ a w i B| ≤ Y) (h2 : |pureLog X R Ñ a w i (B/2)| ≤ Y) (hp :13*Y+s*eTagD D i ≤ 1):
    ‖Complex.exp (farLogC X R v a Ñ z w i)-1‖ ≤ 2*(13*Y+s*eTagD D i):=by
   have h:=log_pay X R Ñ a i w hv hB hz h1 h2; have hh':=h.trans hp
   let g := farLogC X R v a Ñ z w i
   calc
    ‖Complex.exp g-1‖ = ‖Complex.exp g-1-g+g‖:=by rw [sub_add_cancel]
    _ ≤ 2*‖g‖:=by have ht := Complex.norm_exp_sub_one_sub_id_le hh'; have hd:=norm_add_le (Complex.exp g-1-g) g; dsimp only [g] at hd ⊢; nlinarith only [hd, ht,hh',norm_nonneg g]
    _ ≤ _ := by gcongr

def massPower (A:Stores S) := ((Fintype.card G.ColorIndex:ℝ) * (X.pens A).card/2 : ℝ)
lemma logPrice_re {Ñ : ChartRatio G}{z:ℂ} (hÑ:0<Ñ.scale) (hβ:0<z.re): (logMass Ñ z).re = (logMass Ñ (z.re:ℂ)).re -(Fintype.card G.ColorIndex:ℝ)/2*Real.log (‖z‖/z.re) :=by
  have hh : z ≠ 0:=by intro ht; subst z; simpa using not_lt.mpr (le_refl 0) hβ
  have hv' : ((Fintype.card G.ColorIndex:ℂ)/2) = Complex.ofReal ((Fintype.card G.ColorIndex:ℝ)/2):=by simp only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  unfold logMass; simp only [hv',Complex.log_re,Complex.sub_re, Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero,Real.log_div (norm_pos_iff.mpr hh).ne' hβ.ne']
  rw [Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg hβ.le]; ring
lemma steam_re (Ñ : ChartRatio G)(a:ℝ)(A:Stores S)(u:Directions G f) {z:ℂ} (ht : 0<z.re)(hr:R.beta=z.re)(hÑ:0<Ñ.scale):
    (steamC X Ñ z a A u).re = X.steamLog R Ñ a A u + massPower X A * Real.log (‖z‖/z.re):=by
   unfold steamC steamLog massPower; rw [hr];simp only [Complex.sub_re,Complex.add_re,Complex.mul_re, Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,zero_mul,Complex.neg_re,logPrice_re hÑ ht]
   rw [mass_real hÑ ht]; push_cast; simp [Nat.cast_mul]; ring

lemma pack_exact (Ñ:ChartRatio G)(a:ℝ)(A:Stores S) {B:ℕ}(hB:X.B=B) (l W m k v w) {z:ℂ} (ht : 0<z.re)(hr:R.beta=z.re)(hÑ:0<Ñ.scale):
  ‖rawCvertex X R v k Ñ z W a l m w (Sum.inl A)‖ ≤
    ‖X.vertex R Ñ W a l m (heat z.re w) (Sum.inl A)‖ * Real.exp ((massPower X A) * Real.log (‖z‖/z.re)):=by
  dsimp only [rawCvertex,vertex,Pack,steam,Sum.elim]; split_ifs with hg hm hf
  · rw [hr,restores X ht]; simp only [norm_mul,Complex.norm_real,Complex.norm_exp, steam_re X R Ñ a A (world X w) ht hr hÑ, Real.exp_add]; rw [Real.norm_of_nonneg (Real.exp_nonneg _)]; exact le_of_eq (by ring)
  all_goals try tauto
  all_goals simp
end YM.Frontier.Tuning.ComplexVertex

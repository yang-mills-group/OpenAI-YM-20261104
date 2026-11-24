import YM.LocalLTE.Inset.Harmony
/-! Abstract post-coupling Uniform fit. This lemma replaces the Sables.lean
comparison (at its own geometry). There, authority for each analytic estimate
on that path acquired through the right scheduling witnesses, also possible here.
Must repeat purchases on a *common* delayed vote. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Inset
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
section numerical
variable {G : Gauge} {L : Side} {w l : ℝ} (h₁ : -(1/2:ℝ)<w) (hW : w<vow)

abbrev cone (w y : ℝ):ℝ:= y^w
-- Need room for B/X derivatives and `Slide` before pricing. Choose w
-- fixed per horizon/demand only (p,j,+allowed slack), not by support size.
lemma within (p : ℕ) (η : ℝ) (h : 0<η):
    ∃ w, -(1/2:ℝ)<w ∧ w<vow ∧ 1+w*((p:ℝ)+3)< -((p:ℝ)+1-η)/2 := by
  let e := min (1/32:ℝ) (η/(4*(p+3:ℝ)))
  have ht : 0< (p+3:ℝ):=by positivity
  have he : 0<e:=lt_min (by norm_num) (by positivity)
  have hz : e*(p+3:ℝ)≤η/4:= by
    apply (le_div_iff₀ ht).mp ?_; rw [div_div]; exact min_le_right ..
  refine ⟨-1/2+e, ?_, ?_,?_⟩
  · linarith
  · unfold vow; linarith only [show e ≤ 1/32 from min_le_left ..]
  linarith only [hz,h]

local notation "ζ " t => betaF G t L
local notation "s " t => eaves G L t
include h₁ hW
theorem clearance : ∀ᶠ t in atTop, 0 < cone w (betaF G t L) ∧
    cone w (ζ t)+2*furl G L t < (s t) ∧ cone w (ζ t) ≤ (s t) ∧
    ∀ b : ℝ,(ζ t)/2 ≤ b → gStep b < cone w (ζ t):= by
  have hk : -1 ≤ w:=by linarith
  have ht:= (Sienna.belt G L).mul_left 2
  filter_upwards [Delay.shift_pos G L,Sienna.contraction G L (a:=1) (b:=1) zero_lt_one (Rate.add (Rate.power (a:=w)) (ht.weaken hk)) hW,
    Sienna.contraction G L (a:=1) (b:=1) zero_lt_one (Sienna.glim G L) h₁] with t hz hk hp
  rw [one_mul,one_mul] at hk hp
  have hδ : 0≤ 2*furl G L t := by unfold furl; positivity
  exact ⟨Real.rpow_pos_of_pos hz _, hk, le_trans (le_add_of_nonneg_right hδ) hk.le, fun b hb=> (Sienna.lamp G L hz b hb).2.trans_lt hp⟩
variable (j p:ℕ) (f H q b : ℝ→ℝ) (hf:Rate G L 0 f) (hH:Rate G L 0 H) (hq:Rate G L 0 q)
    (hb:Rate G L 0 b) (hl:1+w*(p+3:ℝ)<l) {σ C : ℝ}
omit hW
include hH hq hf hb hl
lemma currency' (J : BareRates.pre G σ C j) (c:Clip) (α : ℝ) : ∀ᶠ t in atTop,
    let B:=b t; let A:=cone w (betaF G t L); let k:=kinBill j J c (q t) (H t); let Z:= (ζ t)
    ∀ δ β : ℝ,|δ| ≤ |α| → β ≤ 2*Z → 0 ≤ k → 0≤q t → 0≤ BareRates.bill J c →
      B*A^(p+1) + Z^(1+w*(p+3:ℝ))+β*(k*A^(p+3)) + cryo J c (q t) (H t) δ (f t)*A^(p+1) ≤ Z^l:= by
  let u := 1+w*(p+3:ℝ)
  have hP₀ : w*(p+1:ℝ) ≤ u:=by unfold u; linarith only [h₁]
  let g(t:ℝ):= kinBill j J c (q t) (H t)
  let c'(t:ℝ):= cryo J c (q t) (H t) α (f t)
  have hW : Rate G L 0 (fun t=> wood j (H t)):= lumpRate j ((((Rate.const 1).add hH)).add ((Rate.const 1).add hH)) hH
  have ht k (u':ℝ→ℝ) (hh:Rate G L 0 u') : Rate G L 0 (fun t=>tollS (q t) k (u' t)) := by simpa only [zero_mul,zero_add] using! (hq.pow k).mul hh
  have hK: Rate G L 0 g:= (ht _ _ (Rate.const _)).add hW
  have hc: Rate G L 0 c':= (ht _ _ (((Rate.const _).add hf).mul_right _)).add (hW.add hH)
  have hP (j:ℕ): Rate G L (w*j) (fun t=>cone w (ζ t)^j):= Rate.power.pow j
  have hZ (f:ℝ→ℝ) (h:Rate G L 0 f): Rate G L u (fun t=> f t*cone w (ζ t)^(p+1)):= (h.mul (hP (p+1))).weaken (by push_cast; rwa [zero_add])
  have he: Rate G L u (fun t=> 2*betaF G t L*(g t*cone w (ζ t)^(p+3))):= (((Rate.hat (G:=G) (L:=L)).mul_left 2).mul (hK.mul (hP (p+3)))).weaken (by push_cast; unfold u; linarith)
  have hh := (((hZ b hb).add Rate.power).add he).add (hZ c' hc)
  filter_upwards [hh l hl, Delay.shift_pos G L] with t hv hz B A k y δ β hδ hβ hk hu hr
  have hA:0<A:=Real.rpow_pos_of_pos hz _; refine le_trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hβ (mul_nonneg hk (pow_pos hA _).le))) (mul_le_mul_of_nonneg_right ?_ (pow_pos hA _).le)) ((le_abs_self _).trans hv)
  unfold c' cryo tollS; gcongr
end numerical
end YM.LocalLTE.Inset

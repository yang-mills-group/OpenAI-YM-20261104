import YM.OPE.Log.PricePlot
/-!
# Extract matching bounds
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
set_option quotPrecheck false
open Function Filter Set Lattice RG Wilson MergeProof Accent Ribbons Source Overlay
open Bid ManyCopies Spec Extraction
open scoped Topology BigOperators Classical
section
variable {G:Gauge}{C:Family G}{F: Extraction.Order}{S:Table C.book} (U:Final C F S) {I J L : Type}[Fintype I][Fintype J] {φ:Filter L} [φ.NeBot] {T A p : L→ℝ}{b c d e q r s δ : ℝ}
variable {v k m n l j: L→ℕ}{u:L→I→ Cover} (x:I→ C.book.Token)(y:J→ C.book.Token) {X:L→I→ E4}{Y:L→J→ E4}(hT:Tendsto T φ atTop)
local notation "w"=> (fun i=> C.S.gridPoint (j i) ∘ u i)
include hT
variable {t:ℕ}
omit hT in
lemma mingle {v v':I→ C.book.Token} {x:I→ E4} (h: S.classTokens ∘ v'= S.classTokens ∘ v) (hx: Injective x): viewing U x v'= viewing U x v := by
    apply sub_eq_zero.mp; let f:=viewing U x v' - viewing U x v; refine (show ‖f‖≤0 ↔ f=0 from norm_le_zero_iff (a:=f)).mp ?_; refine ((glance_contract U (by norm_num: (0:ℝ) ≤ 0)).mpr ?_); intro i; unfold f; rw [map_sub,glance_sees U i _ _ hx,glance_sees U i _ _ hx]
    have ht:= (spectate U i).laws.toSymmetric; have hp:=spectate_respects U i
    rw [observe_exact _ _ ht hp hx, observe_exact _ _ ht hp hx, show (fun i=> S.classTokens (v' (runNames I i)))=(fun i=> S.classTokens (v (runNames I i))) from funext fun i=> congr_fun h _,sub_self,norm_zero] -- unfold f
variable {𝓕: Filter (ℕ×ℕ)} (h𝓕:𝓕 ≤ F.fuse)
include h𝓕
variable {P: L→ C.label t} {g:I→ C.book.Token}{h:Org.Grill C F}
local notation "D" => (fun i=> sole (⟨t,P i⟩ : C.book.Token))
local notation "R" => (fun i=> viewing U (beside (w i) (Y i)) (beside g y) - viewing U (beside (sole (0:E4)) (Y i)) (beside (D i) y))
-- exterior budgets may require d not fixed, introduce new rates b(main support),a ext clearance, u general cost alias
variable (hS:∀ᶠ i in φ, Dress (C:=C) 𝓕 S (k i) (m i) (j i) (A i) (p i) g (u i) t (P i))
    (hG: ∀ᶠ i in φ, Screen (C.S.gridPoint (j i) ∘ u i))
    (hΓ: ∀ᶠ i in φ, Injective (beside (C.S.gridPoint (j i) ∘ u i) (Y i)))
    (hA:RateLE φ T A δ)
    (hF:Height C.S φ T k b)(hJ:Height C.S φ T j d)(hb:b<d)
    (hp:Intervals φ T c (centerless L) Y)(he:Kept φ T e Y) (hc:c<b)(hh:c≤e)(hu:0≤ c)
local notation "a'"=> (↑(sigma y):ℝ)
-- exact rates by perturbed family for any slack
include h hS hT hF hJ hb hp he hc hh hu hA hG hΓ
private lemma cash_rate_L {r u' v' ξ ρ : ℝ}{q k' : L→ℕ}
    (hk:Height C.S φ T n r)(hk':Height C.S φ T q u') (hY: Height C.S φ T l v') (hV: Height C.S φ T k' ξ)
    (hv:r < u')(hf:u'<b)(hw:u'<v')(hz:v'<ξ)(hi:c<r)(hy:e<v')(hR:0<ρ): RateLE φ T R (δ+(a'+ρ*Fintype.card J)*ξ):=by -- m here current matcher m → c'>b, cannot! name f
    obtain ⟨μ,hμ,ht⟩:= admitted U y hT hV hR
    apply (hA.mul (hμ.pays hT)).of_norm_le; filter_upwards [hall_range hT hk hY hk' hV hF hv hw hf hz 1 (Fintype.card J), ht, hG, hS, hΓ,hp.short hi hT (Moment_gap hT hk hi), he.short hy hT (Moment_gap hT hY hy), hk.earlier ((hv.trans hf).trans hb) hT hJ] with i hP ht hX hs hg hr hZ hw
    obtain ⟨f',p,hV,hT,hY,⟨v',hc,K,hK,hQ⟩,-⟩:= hs.wins
    have HH := stylus_admits U h hK hw.le hX hZ hr hg hP (hT.trans h𝓕) hY hQ ht; rw [mingle U (show S.classTokens ∘ beside v' y=S.classTokens ∘ beside g y from by rw [beside_commutes,beside_commutes,hc]) hg] at HH; exact HH

lemma offered_L : RateLE φ T R (δ+(a')*e) :=by
    intro r hr; obtain ⟨μ,hμ,hU,hδ⟩: ∃ u : ℝ, 0<u∧ u<b-c ∧ δ+(a'+u*Fintype.card J)*(e+u) < r:=by
       let x u:=δ+(a'+u*Fintype.card J)*(e+u); have hv: x 0 < r:= by simpa [x] using hr
       have ht : ∀ᶠ u:ℝ in 𝓝[>] 0, x u < r:=
          ((show Continuous x from by unfold x; fun_prop).continuousAt.tendsto.eventually (gt_mem_nhds hv)).filter_mono nhdsWithin_le_nhds
       have hf : ∀ᶠ u:ℝ in 𝓝[>] 0,u<b-c:= eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (sub_pos.mpr hc))
       exact ((show ∀ᶠ u:ℝ in 𝓝[>] 0,0<u from self_mem_nhdsWithin).and (hf.and ht)).exists
    have hP:= C.path.levels.fits.mesh; obtain ⟨n,h₁⟩:= found hT hP (show 0≤c+μ/4 by positivity); obtain ⟨l,h₂⟩:= found hT hP (show 0≤c+μ/2 by positivity); obtain ⟨k',h₃⟩:= found hT hP (show 0≤e+3*μ/4 by linarith only [hu,hh,hμ]); obtain ⟨l',h₄⟩:= found hT hP (show 0 ≤ e+μ by linarith); exact cash_rate_L (h:=h) U y hT h𝓕 hS hG hΓ hA hF hJ hb hp he hc hh hu h₁ h₂ h₃ h₄ (by linarith) (by linarith only [hU,hμ]) (by linarith) (by linarith) (by linarith) (by linarith) hμ r hδ

lemma see_L (v:L→Viewers U) : RateLE φ T (fun i=> observe (spectator U (v i)) (beside (w i) (Y i)) (beside g y) - observe (spectator U (v i)) (beside (sole (0:E4)) (Y i)) (beside (D i) y)) (δ+(a')*e):=by
    apply (offered_L (h:=h) U y hT h𝓕 hS hG hΓ hA hF hJ hb hp he hc hh hu).transfer
    filter_upwards [(Kept.sole φ T (fun _=> (0:E4)) e|>.chorus he (hp.mono hh)).inject,hΓ] with i hi hh; rw [← glance_sees U (v i) _ _ hi,← glance_sees U (v i) _ _ hh, ← map_sub]; exact glance_bound ..
end
section
open Table
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S){I J L : Type}[Fintype I][Fintype J]{φ:Filter L}[φ.NeBot] {T A V : L→ℝ} {x v u a b c d y z : ℝ} {k m j: L→ℕ} (g:I→ C.book.Token) (r:J→ C.book.Token) {X:L→ I→ Cover}{Y:L→J→ E4} {q q':ℕ}
    {P:L→ C.label q}
set_option quotPrecheck false
local notation "Λ" => U.sector.derivatives
variable {R: Prescription U.sector.derivatives}

variable {𝓕: Filter (ℕ×ℕ)} (hT:Tendsto T φ atTop) [DecidableEq I]
local notation "w'"=> (fun i=>C.S.gridPoint (j i) ∘ X i)
variable (hS: ∀ᶠ i in φ, Dress (C:=C) 𝓕 S (k i) (m i) (j i) (A i) (V i) g (X i) q (P i))
include U hS hT
-- cost against the fixed detectors; no dependence on exterior probes in their lists
lemma det_L (h𝓕:𝓕≤F.fuse) (h:Org.Grill C F)(u : Mode Λ)(hG: ∀ᶠ i in φ, Screen (w' i))(hA:extentWithin φ T w' a)(he:Kept φ T a w')(hp:0<a)
    (hk:Height C.S φ T k b)(hj:Height C.S φ T j d) (hb:0<b)(hd:b<d)(hv:RateLE φ T A c) :
    RateLE φ T (fun i=> R.ope u (w' i) g 0-R.test u q (S.project q (P i))) c:=by
    let S':= (R.sheet u); let r i (x):= (S' x) * (Prescription.reading S (w' i) g 0 x - S.spectra q (S.project q (P i)) x)
    unfold Prescription.ope Prescription.test; simp_rw [computes,← Finset.sum_sub_distrib,← mul_sub]; apply RateLE.sum hT _; intro x hx
    obtain ⟨h₁,h₂⟩:= bearing_lifetime hT x; have he':=epoch_space hT he hA hp x
    have ha:= see_L (h:=h) U x.letter hT h𝓕 hS hG he' hv hk hj hd h₂ h₁ hb le_rfl le_rfl (fun _=>none)
    have hf: RateLE φ T (fun i=> Prescription.reading S (w' i) g 0 x-S.spectra q (S.project q (P i)) x) c:=by
       apply (RateLE.mono ha (by norm_num)).congr
       filter_upwards [he'] with i hi;
       -- one_test
       rw [← Prescription.one_test q _ _ U.room.kernel]; unfold Prescription.reading; simp only [sub_zero, if_pos hi, if_pos (bearing_clear _), spectator]; rfl
    exact ((RateLE.const (S' x) hT).mul hf).mono (by simp)
end
end YM.OPE.Log

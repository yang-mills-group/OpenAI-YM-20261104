import YM.RG17.Finite

/-!
The finite system deriving trace/storage amplitude from signed connected data.
No formal series operations on the actual a,d; all inverse uses require
only leading lower bound on fixed diagnostic. Asymptotic along continuous
r, measuring scale and coupling as announced. Spatial samples through
fixed derivative tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter MeasureTheory Spec Extraction Table OPE OPE.Orbits
open Points Trace
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
section scalar
open Complex
private lemma castUp (x c:ℝ→ℝ) (r:ℝ) : (↑(x r/(c r)^2:ℝ):ℂ) = (↑(x r):ℂ)/(↑(c r):ℂ)^2:= by simp
private lemma refSolved {a d g:ℝ→ℝ} {t σ p k:ℝ→ℂ} {b:ℝ}{K C:ℂ}
    (hσ : ∀ᶠ x in home, (a x:ℂ)*σ x+(d x:ℂ)*t x=0) (ht : ∀ᶠ x in home,(a x:ℂ)*p x+(d x:ℂ)*k x=t x)
    (hg:Tendsto g home (𝓝 0))(hi:∀ᶠ x in home,g x≠0)(hs:Tendsto (fun x=>σ x/(g x:ℂ)^2) home (𝓝 ((b:ℂ)*K)))
    (hK:Tendsto t home (𝓝 K))(hz:K≠0)(hk:Tendsto k home (𝓝 C))(hp:Tendsto p home (𝓝 K)):
    Tendsto a home (𝓝 1) ∧ Tendsto (fun x=>d x/g x^2) home (𝓝 (-b)):=by
    let C'(x:ℝ):ℂ:= -((σ x / (g x:ℂ)^2)/ t x)
    have hv:Tendsto C' home (𝓝 (-(b:ℂ))):=by simpa only [C',Pi.div_apply,mul_div_cancel_right₀ _ hz] using (hs.div hK hz).neg
    let D'(x:ℝ):ℂ:= (g x:ℂ)^2*C' x
    have hd:Tendsto D' home (𝓝 0):=by simpa only [D',Function.comp_def,ofReal_zero,zero_pow (by decide : 2≠0),zero_mul] using (((Complex.continuous_ofReal.continuousAt.tendsto.comp hg).pow 2).mul hv)
    have hc:(fun x=> (d x:ℂ)) =ᶠ[home] fun x=>D' x * a x :=by
       filter_upwards [hi,hσ,hK.eventually_ne hz] with x hN hU hX
       have h : (↑(g x):ℂ)≠0:=Complex.ofReal_ne_zero.mpr hN
       unfold D' C'; field_simp; linear_combination hU -- maybe
    have hx:= hp.add (hd.mul hk); rw [zero_mul,add_zero] at hx
    have ha:Tendsto (fun x=> (a x:ℂ)) home (𝓝 1) := by
        have h:= hK.div hx hz; rw [div_self hz] at h
        apply h.congr'; filter_upwards [hc,hx.eventually_ne hz,ht] with x hr hn ht
        apply (div_eq_iff hn).mpr; rw [← ht, (show (↑(d x):ℂ)=_ from hr)]; ring
    have ht':= Complex.continuous_re.continuousAt.tendsto.comp ha
    have hh:Tendsto (fun x=> ((↑(d x/g x^2:ℝ)):ℂ)) home (𝓝 (-(b:ℂ))):=by
       have H:=hv.mul ha; rw [mul_one] at H
       refine H.congr' ?_
       filter_upwards [hi,hc] with x hx h
       have hE:(g x:ℂ)≠0:= Complex.ofReal_ne_zero.mpr hx
       rw [castUp, (show (↑(d x):ℂ)= D' x*↑(a x) from h)]; unfold D'; field_simp; try ring
    exact ⟨by simpa using! ht',by simpa only [Function.comp_def,Complex.ofReal_re, Complex.neg_re] using! Complex.continuous_re.continuousAt.tendsto.comp hh⟩
end scalar
variable {G:Gauge}{C:Family G} {f:Extraction.Order}{S:Table C.book} {F:Final C f S} {L:Layout F}
    (Z:Ledger L) (A:Ports C) (H:Services C f S) (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (loc:Located L) (V:Tide Z A) (Q: Passage Z A)
include P H loc V Q
set_option quotPrecheck false
local notation "P!"=> portal L
structure Handles (L:Layout F) : Prop where
    aligned : ∀ᶠ r in home,Nonempty (Rectilinear F (L.frame 4 r) r)
lemma fasteners (p:Handles L):∃ (a d:ℝ→ℝ) (k:ℝ→ℂ), (∀ᶠ r in home, StressRay F (P! r) r (a r) (d r) (k r)) ∧
    Tendsto a home (𝓝 1) ∧ Tendsto (fun r=>d r/(Z.g r)^2) home (𝓝 (-(anomalyCoefficient G/2))) := by
   obtain ⟨N,hN⟩:=someRim C Z.simple
   let ψ := N.test;let t:=scalarRay P!
   have Hx:∀ᶠ r in home,∃ a b k,StressRay F (P! r) r a b k:= p.aligned.mono (fun i hi=> ray_of_alignment F P! hi.some Z.simple)
   rw [eventually_iff_exists_mem] at Hx; obtain ⟨W,hW,Hx⟩:= Hx
   choose! a d k hU using Hx
   have hh := mem_of_superset hW (fun x hx=>hU x hx)
   change ∀ᶠ x in home, StressRay F (P! x) x (a x) (d x) (k x) at hh
   have he : ∀ᶠ r in home, a r • (shiftAll P! ψ r (t r)) + d r • force P! ψ r (t r) = 0 := (positiveLength.and hh).mono fun i hi=> swept L ψ hi.1 hi.2 _
   have ht : ∀ᶠ r in home, a r • N.Qstress L r (t r) + d r • N.Qscalar L r (t r)= force P! ψ r (t r):= (positiveLength.and hh).mono fun i hi=> N.precise _ hi.1 hi.2
   refine ⟨a,d,k,hh,refSolved (t:=fun r=> force P! ψ r (t r)) (σ:=fun r=>shiftAll P! ψ r (t r)) (p:=fun r=> N.Qstress L r (t r)) (k:=fun r=>N.Qscalar L r (t r)) ?_ ?_ Z.vanishes (Eventually.of_forall fun r=> (Z.positive r).ne') ?_ (scalar_limit Z A H P loc V Q ψ) hN (pse_test Z A H P loc V Q N) (translate_test Z A H P loc V Q N)⟩
   · simpa only [Complex.real_smul] using he
   · simpa only [Complex.real_smul] using ht
   simpa only [Complex.real_smul] using (shift_limit Z A H P loc V Q ψ)
end YM.RG17


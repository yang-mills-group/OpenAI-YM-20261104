import YM.XSpace.Pala
/-!
# Absolutely convergent sectors for the continuum integral with a derivative
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Season
open Function Set Filter MeasureTheory Relief Sail Playpen Trace Litter Octave Lattice Further.FreeCovariance.KP
open scoped Topology BigOperators
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{x y:ι→Cover}
abbrev Breeze := E4→ℝ
def down (p:Toe)(a:ℝ)(x:E4):ℝ:= a⁻¹^4 * p (mark a x)
lemma gauging (p:Toe)(a:ℝ)(x:E4): (↑(down p a x):ℂ)= steps a (fun i=> ↑(p i)) x:= by unfold down steps; push_cast; rfl
variable {f g:Breeze}[L.IsCountablyGenerated][NeBot L]{p:ι→ Toe}
abbrev Consummate (L :Filter ι)(p:ι→Toe)(f:Breeze):Prop:= (Tendsto (fun i=>∑' w:Cover,p i w) L (𝓝 (∫ x:E4,f x))) ∧ Integrable f
lemma prince (s:Stage L a)(hg:Integrable g)(H:∀ᶠ i in L,∀ᵐ x:E4, ‖down (p i) (a i) x‖ ≤g x)(h:∀ᵐ x:E4,Tendsto (fun i=> down (p i) (a i) x) L (𝓝 (f x))): Consummate L p f:= by
  constructor
  · have hp : ∀ᶠ i in L,∀ᵐ x:E4, ‖steps (a i) (fun w=>(↑(p i w):ℂ)) x‖ ≤g x:= by simp_rw [← gauging,Complex.norm_real]; exact H
    have hx:= (flight (fun i w=>(↑(p i w):ℂ)) s.good hg (fun x=>(↑(f x):ℂ)) hp (h.mono (fun x hx=> (Complex.continuous_ofReal.continuousAt.tendsto.comp hx).congr (fun i=>gauging ..)))).2; simp_rw [← Complex.ofReal_tsum,integral_complex_ofReal] at hx; exact Complex.continuous_re.continuousAt.tendsto.comp hx
  obtain ⟨v,hv⟩:= Filter.exists_seq_tendsto L
  obtain ⟨n,hn⟩:= eventually_atTop.mp (hv.eventually (H.and s.good)); let F (i:ℕ):= down (p (v (i+n))) (a (v (i+n)))
  have he : ∀ᵐ x:E4,Tendsto (fun i=> F i x) atTop (𝓝 (f x)):= h.mono fun x hx=> hx.comp (hv.comp (tendsto_add_atTop_nat n))
  have hp(i:ℕ): Measurable (F i):= by
    let j:=v (i+n); set g:= fun x:Cover=>(↑(p j x):ℂ); have h:= fees_ok g (hn (i+n) (by omega)).2; refine (show F i=(fun x:E4=> Complex.re (steps (a j) g x)) from funext fun x=>?_ ) ▸ Complex.continuous_re.measurable.comp h; unfold g; rw [← gauging]; rfl -- ▸ direction?
  exact ⟨aestronglyMeasurable_of_tendsto_ae _ (fun i=> (hp i).aestronglyMeasurable) he, hasFiniteIntegral_of_dominated_convergence hg.hasFiniteIntegral (fun i=> (hn _ (by omega:n≤ i+n)).1) he⟩
lemma price (s:Stage L a)(C B:ℝ)(hc:0≤C)(H:∀ᶠ i in L,∀ x:Cover,p i x≠0→ a i*pad x≤ B ∧ ‖p i x‖≤ C*a i * rate 3 x)(h:∀ᵐ x:E4,Tendsto (fun i=> down (p i) (a i) x) L (𝓝 (f x))): Consummate L p f:=by
  have h':= close_pay C B (fun i x=> (p i x:ℂ)) hc s.good ?_
  · simp_rw [← gauging,Complex.norm_real] at h'; exact prince s ((near_minor (4*B+1)).const_mul (C*64)) h' h
  filter_upwards [H] with i hi w hw; simp only [ne_eq,Complex.ofReal_eq_zero] at hw; rw [Complex.norm_real]; exact ⟨(hi _ hw).1,by rw [← inv_pow]; exact (hi _ hw).2⟩
-- centers about x.
omit [L.IsCountablyGenerated] [NeBot L] in
lemma located {p:ι→Toe}(f:Breeze)(h:Consummate L (fun i w=> p i (w+x i)) f): Consummate L p f:= ⟨h.1.congr fun i=> Equiv.tsum_eq (Equiv.addRight (x i)) (p i),h.2⟩
omit [L.IsCountablyGenerated] [NeBot L] in
lemma remaining (u:E4): ∀ᵐ x:E4, x≠u:= mem_ae_iff.mpr (by change MeasureTheory.volume ({x:E4 | x≠u}ᶜ)=0; simp)
end YM.XSpace.Season

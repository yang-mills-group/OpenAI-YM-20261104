import YM.X.Chir.Livery
/-!
# microlocal reader. The TWO integrability budgets: near ε-bead & outside all beads.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir.Dock
open Lattice Wilson Next.Rank Normal PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset MeasureTheory Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Imprint CellsInt Beamer Asymptotics
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e c:ℝ}
local notation "ε"=> epsilon q
local notation "L"=>(atTop:Filter ℕ)
-- add
lemma enough {V:Type*}[NormedAddCommGroup V]{f:ℕ→ E4→V}{g:E4→V}{b:E4→ℝ}(hb:Integrable b)(hf:∀ᶠ i in L,AEStronglyMeasurable (f i))(hw:∀ᶠ i in L,∀ᵐ z:E4,‖f i z‖≤b z)(ht:∀ᵐ z:E4,Tendsto (fun i=> f i z) L (𝓝 (g z))): Integrable g:= by
    obtain ⟨N,h⟩:= eventually_atTop.mp (hf.and hw); let F(i:ℕ):= f (i+N); have hh(i:ℕ): AEStronglyMeasurable (F i) volume:= (h (i+N) (by omega)).1; have hs: ∀ᵐ z:E4,Tendsto (fun i=> F i z) L (𝓝 (g z)):= ht.mono (fun z hz=> hz.comp (tendsto_add_atTop_nat N))
    apply hb.mono' (aestronglyMeasurable_of_tendsto_ae _ hh hs); filter_upwards [hs,ae_all_iff.mpr (fun i:ℕ=>(h (i+N) (by omega)).2)] with z hz hu; exact le_of_tendsto' hz.norm (hu ·)
variable (S: Finset V)(x:V→Fielding.Walk)(p:V→E4)(hp:∀ i∈S,plot q (x i) (p i))(A:Apart S p R)(χ:Floor R)(hq:1<q.val)
include hp A hq
local notation "QuietL"=> Quiet q S x χ
local notation "Ξ"=> p '' (S:Set V)
-- explicit far.Bound integrable true. append.Lay
lemma horizon_bound (f:Lapse)(g:E4→ℂ)(h:Isle q S x p χ 6 f)(hg:∀ z:E4,z∉ Ξ → ∀ X,plot q X z→ Tendsto (fun i=> f (i,X i)) L (𝓝 (g z))): Integrable (fun z:E4=> Rest χ S p z • g z) ∧ Tendsto (fun i=> (ε i ^4) • (∑ z:Site (side q i), QuietL i z • f (i,lift z))) L (𝓝 (∫ z:E4, Rest χ S p z • g z)):= by
    obtain ⟨C,hc,hw⟩:= tip_budget S x p χ h; let F(i:ℕ):= mosaic (ε i) (Room q S x χ f i); have he:∀ᶠ i in L,AEStronglyMeasurable (F i) volume:= Eventually.of_forall fun i=> (mosaic_ok (epsilon_pos q i) (register S x χ f)).aestronglyMeasurable
    have hW: ∀ᶠ i in L,∀ᵐ z:E4, ‖F i z‖≤C*tipV z := hw.mono (fun i hi=> Eventually.of_forall (fun z=>hi z)); have hy: ∀ᵐ z:E4, Tendsto (fun i=> F i z) L (𝓝 (Rest χ S p z • g z)) := by
         apply Eventually.of_forall; intro z; let u(i):= index (ε i) z; have hz: plot q u z:= entrant hq z; by_cases hh:z∉Ξ; · apply ((quiet_path hq u S x p χ hz hp).smul (hg z hh u hz)).congr'; filter_upwards [plot_lift hq hz] with i hi; unfold F mosaic Room; rw [if_pos hi]
         push Not at hh; -- fix
         obtain ⟨v,hv,rfl⟩:= hh; have hh:= tends_zero_at hq u S x p hp χ A hv hz; have ha : Rest χ S p (p v)=0 := tendsto_nhds_unique (quiet_path hq u S x p χ hz hp) (tendsto_const_nhds.congr' (EventuallyEq.symm hh)); rw [ha,zero_smul]; refine tendsto_const_nhds.congr' ?_; filter_upwards [plot_lift hq hz,hh] with i hi hj; unfold F mosaic Room; rw [if_pos hi,hj,zero_smul]
    refine ⟨enough (tip_integrable.const_mul C) he hW hy,(tendsto_integral_filter_of_dominated_convergence _ he hW (tip_integrable.const_mul C) hy).congr fun i=> ?_⟩; change ∫ x:E4,mosaic _ _ x=_; rw [mosaic_sum (epsilon_pos q i) (register S x χ f),paisley,Finset.sum_image]; swap; · intro x _ y _ hh; exact Function.LeftInverse.injective (g:=wrap (side q i)) (fun i=> wrap_lift i) hh
    simp only [Room,wrap_lift,↓reduceIte]
abbrev Rhyme (q:ℕ+):= (i:ℕ)→ Site (side q i)→ ℝ
abbrev castV (f:Rhyme q): Lapse:= fun z=> Complex.ofReal (f z.1 (wrap (side q z.1) z.2))
omit hp A hq in
private lemma view_int (f:E4→ℝ)(h: Integrable (fun z=> (f z:ℂ))): Integrable f:= by exact h.re
lemma horizon (f:Rhyme q)(g:E4→ℝ)(h:Isle q S x p χ 6 (castV f))(hg:∀ z:E4,z∉ Ξ → ∀ X,plot q X z→ Tendsto (fun i=> f i (wrap _ (X i))) L (𝓝 (g z))): Integrable (fun z=>Rest χ S p z * g z) ∧ Tendsto (fun i=> galley (ε i) (QuietL i*f i)) L (𝓝 (∫ z:E4,Rest χ S p z * g z)):= by
    obtain ⟨he,ht⟩:= horizon_bound S x p hp A χ hq (castV f) (Complex.ofReal ∘ g) h (fun z he u hu=>Complex.continuous_ofReal.continuousAt.tendsto.comp (hg z he u hu))
    simp only [castV, comp_apply, Complex.real_smul, ← Complex.ofReal_mul,wrap_lift, ← Complex.ofReal_sum, integral_complex_ofReal] at he ht
    have hu : Tendsto (fun i=> galley (ε i) (QuietL i*f i)) _ _ := Complex.continuous_re.continuousAt.tendsto.comp ht
    exact ⟨view_int _ he, hu⟩
omit hp A hq
end YM.PositionX.Chir.Dock

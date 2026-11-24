import YM.OPE.Compatible.Moon.Zeal
/-! # Limits of populations. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot MergeProof Next.Extract Dash Analysis Extra.Histories Luke
open Next.Rank Next.Rank.Price Owl
open scoped Topology Classical BigOperators
variable {d k N i:ℕ} {G:Gauge}{C:Family G}(T:C.Makes)
set_option quotPrecheck false
local notation "F" => C.label d
local notation "L" => C.labels.level d
variable (A:Ultrafilter (ℕ×ℕ)){H:Extraction.Order}(hV:(A:Filter _) ≤ H.fuse)
include T A hV
variable (v:C.label d)
local notation "V!"=>tallyman T d k
lemma Mug (h:C.ref d ≤ k): ∃ P: C.label d ≃L[ℂ] C.label d,Tendsto V! (A:Filter _) (𝓝 (P.toContinuousLinearMap)):=by
       let C':=OPE.Columns.juice C.path.levels k; let U:ℝ:= C' * Fintype.card ((L).Index); have ht:0≤C':= le_trans zero_le_one (OPE.Columns.juice_pos ..)
       have hn:∀ᶠ i:ℕ × ℕ in (A:Filter _),k≤ i.1:=((Push.RelayDifference.cutoff_grows H).eventually_ge_atTop k).filter_mono hV
       have hM:∀ᶠ i:ℕ×ℕ in (A:Filter _), ‖V! i‖ ≤ U:= by refine hn.mono fun i hi=>?_ ; apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg ht (Nat.cast_nonneg _)); intro x; exact (Size.norm_le ..).trans ((capacity T h hi x).trans ((mul_le_mul_of_nonneg_left (Size.le_norm ..) ht).trans_eq (mul_assoc ..|>.symm)))
       letI:=FiniteDimensional.proper ℂ (C.label d→L[ℂ] C.label d); obtain ⟨p,hp⟩:= chant A hM; have hf: Injective p.toLinearMap:=by
             apply LinearMap.ker_eq_bot.mp; apply LinearMap.ker_eq_bot'.2; intro x hx; change p x=0 at hx; have hv: (L).coeffSize x ≤ outward C d k * (L).coeffSize (p x) := by
                    apply ge_of_tendsto (((Size.continuous (L)).continuousAt.tendsto.comp (Luke.arcing hp x)).const_mul _) -- named argument?
                    refine hn.mono (fun i hi=>?_); rcases i with ⟨a,b⟩; change (L).coeffSize x ≤ _*(L).coeffSize (V! (a,b) x); rw[tallyCurrent T x h hi]; exact at_current C T h hi b x -- p maybe
             rw [hx] at hv; exact Work.G08.size_separates _ x (by simpa [Labels.Frame.coeffSize] using hv)
       let V:= LinearEquiv.ofBijective p.toLinearMap ⟨hf,LinearMap.injective_iff_surjective.mp hf⟩; exact ⟨V.toContinuousLinearEquiv,hp⟩
lemma Enc (d:ℕ): ∃ Q:ℕ→ C.label d≃L[ℂ]C.label d, Conic T A Q:=by
       letI: Nonempty (C.label d ≃L[ℂ] C.label d):= ⟨ContinuousLinearEquiv.refl _ _⟩; choose! Q h using fun k hk=> Mug T (d:=d) (k:=k) A hV hk; exact ⟨Q,⟨h⟩⟩
noncomputable abbrev arT (d i:ℕ)(z:ℕ×ℕ):= if h: C.ref d≤ i ∧ i<z.1 then (OarX T h.1 h.2 z.2).toContinuousLinearMap else 0
lemma arcfocus {U:ℕ→ C.label d≃L[ℂ]C.label d}(M: Conic T A U)(h: C.ref d ≤ i) {r:ℝ} (he:∀ᶠ j:ℕ×ℕ in (A:Filter _),‖arT T d i j‖ ≤ r) : Tendsto (arT T d i) (A:Filter _) (𝓝 (turnover (U i) (U (i+1))).toContinuousLinearMap):= by
       let R':=arT T d i; obtain ⟨L',hL⟩:= chant A he; let x:= tallyman T d i; let y:=tallyman T d (i+1); let R:= (turnover (U i) (U (i+1))).toContinuousLinearMap
       have he := M.meeting _ h; have hv:= M.meeting _ (h.trans (Nat.le_succ i)); have hx:= tendsto_nhds_unique_of_eventuallyEq (he) (pulp hv hL) (((Push.RelayDifference.cutoff_grows H).eventually_gt_atTop i).filter_mono hV |>.mono ?_); swap
       · intro j hj; rcases j with ⟨n,p⟩; dsimp only [arT]; rw[dif_pos ⟨h,hj⟩]; apply ContinuousLinearMap.ext; intro w; change Pinwheel T h hj.le p w = (Pinwheel T h hj.le p) ((Pinwheel T (h.trans (Nat.le_succ i)) hj p).symm ((Pinwheel T (h.trans (Nat.le_succ i)) hj p) w)); exact congr_arg _ (ContinuousLinearEquiv.symm_apply_apply (Pinwheel T (h.trans (Nat.le_succ i)) hj p) w|>.symm) -- hdr
       have ht:R = L':=by apply ContinuousLinearMap.ext; intro v; obtain ⟨z,rfl⟩:= (U (i+1)).surjective v; rw [show R (U (i+1) z)=U i z from (by unfold R turnover; simp)]; exact DFunLike.congr_fun hx z
       rw [show (turnover (U i) (U (i+1))).toContinuousLinearMap = R from rfl,ht]; exact hL
end YM.OPE.Lake

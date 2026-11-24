import YM.OPE.Compatible.Glim.Nutr
/-! # turn marks for a step force. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell
variable {I J E F:Type}[Fintype I][Fintype J]
variable (T:I≃J)(x:I→Bool)(b:Bool)(p:I)
omit [Fintype I][Fintype J] in
lemma resetP {y:Keys G J} (z:G.Color) (hx:sword (!(b.xor (x p))) (-(y (T p))) z=-sword (b.xor (x p)) (y (T p)) z):
      Flick T x (lunge (T p) (b.xor (x p)) y z)= lunge p b (Flick T x y) z:=by
     funext i; rw [FlickP]; by_cases h:i=p
     · subst i; unfold lunge; simp only[ContinuousLinearMap.comp_apply,ContinuousLinearMap.single_apply,Pi.single_eq_same,FlickP]; rw [← Bool.not_not b]; cases b<;>cases e:x p <;> simp [e] at hx ⊢<;> exact hx.symm
     unfold lunge; simp [h]
variable [NormedAddCommGroup E][NormedSpace ℝ E]
lemma Pmp {f:Keys G I→E}(h:ContDiffAt ℝ ω f 0): ∀ᶠ y:Keys G J in 𝓝 0,DColor (b.xor (x p)) (T p) (f ∘ Flick T x) y= DColor b p f (Flick T x y):=by
     let Q:= Flick T x (G:=G); filter_upwards [((continuous_apply (T p)).tendsto (0:Libra.Keys G J)).eventually (swordV (b.xor (x p))), ((show Tendsto Q (𝓝 0) (𝓝 0) from Q.map_zero ▸ Q.continuous.tendsto 0)).eventually (h.eventually (by simp))] with y hx hp; apply ContinuousLinearMap.ext;intro v; unfold DColor; rw [fderiv_comp _ (g:=f) (f:=Q) (hp.differentiableAt (by simp)) Q.differentiableAt,Q.fderiv]; exact congr_arg (fderiv ℝ f (Q y)) (resetP T x b p v (hx v))
local notation "B"=> Phone G
local notation "μ"=> Tested.germ
variable {p b T}{f g:Keys G I→ℝ}{f' g':Keys G J→ℝ}{Y:Keys G I→G.Color}{Y':Keys G J→G.Color}{r:ℕ}
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in lemma Jet_const (X:ScriptJ E)(v:E):Mining X (fun _:ℝ=>v)=X v:= Gael.chooses (Reads.selves _)
lemma distillEq (h:Once f g)(hv:Variance.Cand r Y)(hp:Once f' g')(hy:Variance.Cand r Y')(L:Keys G J→L[ℝ] Keys G I) {b b':Bool}{p:I}{p':J}
  (hx:∀ᶠ x:Keys G J in 𝓝 0,∀ t:ℝ,τPower p' b' f' g' Y' r t x=τPower p b f g Y r t (L x)):
      Cake p' b' f' g' Y' r=Cake p b f g Y r ∘ L:=by
             funext z; let x(_:ℝ):=z; let y(_:ℝ):=L z; have hh : Mining (Cake p' b' f' g' Y' r) x=Mining (Cake p b f g Y r) y :=by
                 refine (Mixr hy hp x (Exists.intro _ (Reads.constants _))).equality ((Mixr hv h y (Exists.intro _ (Reads.constants _))).cong ?_); let w(v:ℝ):= v • z; have hw : Tendsto w μ (𝓝 0):=by unfold w; simpa using! (show Tendsto (fun i:ℝ=>i) μ (𝓝 0) from nhdsWithin_le_nhds).smul_const z
                 filter_upwards [hw.eventually hx] with i h; unfold x y; rw [← map_smul]; exact h i
             unfold x y at hh; rw [Jet_const,Jet_const] at hh; exact hh
-- syntactic ∘L from parser means comp notation ∘L expects continuous!
lemma OwnL (h:Once f g)(L:Keys G J →L[ℝ] Keys G I): Once (f∘ L) (g∘ L):=⟨ ((L.map_zero.symm ▸ h.sm : ContDiffAt ℝ ω f (L 0)).comp _ L.contDiff.contDiffAt), HushL L f h.sm _ h.zero, ((L.map_zero.symm ▸ h.sg : ContDiffAt ℝ ω g (L 0)).comp _ L.contDiff.contDiffAt)⟩
lemma CandL (h:Variance.Cand r Y) (L:Keys G J→L[ℝ] Keys G I):Variance.Cand r (Y ∘ L):=⟨((L.map_zero.symm ▸ h.smooth : ContDiffAt ℝ ω Y (L 0)).comp _ L.contDiff.contDiffAt), fun i=> HushL L _ (((B).coord i).toContinuousLinearMap.contDiff.contDiffAt.comp _ h.smooth) _ (h.silent i)⟩
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in -- lint may not needed
lemma LeafEq (T:I≃J)(h:Once f g)(hv:Variance.Cand r Y):
      let L:=Flick T x (G:=G)
      Cake (T p) (b.xor (x p)) (f∘ L) (g∘ L) (Y∘ L) r=Cake p b f g Y r ∘ L:=by
             intro L; apply distillEq h hv (OwnL h L) (CandL hv L) L; filter_upwards [Pmp T x b p h.sm,Pmp T x b p h.sg,Pmp T x b p hv.smooth] with i he ht hh u; unfold τPower ψPower; change DColor _ _ (f∘ L) i= _ at he; change DColor _ _ (g∘ L) i= _ at ht; change DColor _ _ (Y∘ L) i= _ at hh; rw [he,ht,hh];rfl
end YM.OPE.Variance

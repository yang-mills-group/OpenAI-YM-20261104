import YM.RGComparison.Core16.Therm.Island
import YM.Analysis.Exchange
/-!
# Bigrading bookkeeping for external Taylor and internal Wick powers at finite volume

Use radial factorial-normalized tensor. This file derives margin rule needed for
mass-vs-thermal compare. A margin on one linear fiber direction suffices; don't
invoke mixed bounds / spread in all directions without buying.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Therm
open Function Filter MeasureTheory Set Metric Asymptotics Analysis
open scoped Topology ContDiff NNReal
open PertExtension PertExtension.Series Tested Radial
section general
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
   {f g : E → ℝ} {x z : E} (y u : E) {k : ℕ}

def score (f : E→ℝ) (x y) (i : ℕ) := Tensor.diagonal (Tensor.coeff f i x) y

lemma score_jet : score f 0 y k = jet f k y := rfl
lemma score_succ (h : ContDiffAt ℝ ω f x) : score f x y (k+1)=((k+1:ℝ)⁻¹) * score (D y f) x y k := by
  unfold score Tensor.diagonal
  rw [show (fun _ : Fin (k+1)=>y)= Fin.cons y (fun _: Fin k=> y) from funext fun i=>by refine Fin.cases ?_ (fun n=>?_) i <;> simp,
    Tensor.coeff_apply_cons (h.of_le le_top),Nat.cast_add,Nat.cast_one]; rfl

lemma score_germ (he : f=ᶠ[𝓝 x] g) : score f x y k=score g x y k:= by rw [score,score,Tensor.GermCoeff k he]
lemma score_add (hf : ContDiffAt ℝ ω f x)(hg : ContDiffAt ℝ ω g x) : score (f+g) x y k=score f x y k+score g x y k := by rw [score, score, score,Tensor.coeff_add (hf.of_le le_top) (hg.of_le le_top)]; rfl
lemma score_sub (hf : ContDiffAt ℝ ω f x)(hg : ContDiffAt ℝ ω g x) : score (f-g) x y k=score f x y k-score g x y k := by
  rw [sub_eq_add_neg,score_add y hf (show ContDiffAt ℝ ω (-g) x from hg.neg),sub_eq_add_neg,score,score,Tensor.neg_coeff]; rfl
lemma score_base : score f x y 0=f x := Tensor.coeff_apply_zero ..
lemma score_scaling (c : ℝ) : score f x (c • y) k=c^k * score f x y k := Tensor.homogeneous ..
private lemma score_split (hf : ContDiffAt ℝ ω f x) : score f x (y+u) (k+1)=(k+1:ℝ)⁻¹*(score (D y f) x (y+u) k + score (D u f) x (y+u) k) := by
  rw [score_succ (y+u) hf, show D (y+u) f=D y f+D u f from funext fun x=> map_add (fderiv ℝ f x) y u, score_add _ (dSmooth hf y le_top) (dSmooth hf u le_top)]

lemma score_linear (L : E→L[ℝ] F)(a : F){g : F→ℝ} (hf : ContDiffAt ℝ ω g (a+L x)) : score (fun y=> g (a+L y)) x y k=score g (a+L x) (L y) k := by
  let X := fun y=> a+L y
  have hX : Continuous X := continuous_const.add L.continuous; have hX' : ContDiff ℝ ω X := contDiff_const.add L.contDiff
  induction k generalizing g with
  | zero => rw [score_base,score_base]
  | succ k ih=>
    change score (g ∘ X) x y (k+1)=_
    rw [score_succ _ (hf.comp (f:=X) x hX'.contDiffAt), score_succ _ hf]
    congr 1
    refine Eq.trans (?_ : score (D y (fun i=>g (a+L i))) x y k=score (fun i=> D (L y) g (a+L i)) x y k) (ih (dSmooth hf _ le_top))
    refine score_germ _ (((hX.tendsto x).eventually (hf.eventually (by simp))).mono ?_)
    intro z (he : ContDiffAt ℝ ω g (a + L z))
    have hi : HasFDerivAt X L z := by simpa only [X,zero_add] using! (hasFDerivAt_const a z).add L.hasFDerivAt
    exact DFunLike.congr_fun (he.differentiableAt (by simp) |>.hasFDerivAt.comp z hi |>.fderiv) y
end general
section plane
variable {E : Type*} [NormedAddCommGroup E][NormedSpace ℝ E]
    {f g : ℝ × E→ℝ} (τ : ℝ) {v : E} {x : ℝ} {k : ℕ}

def Held (f : ℝ × E → ℝ) (k : ℕ) (y : E) := ∀ i<k, ∀ᶠ x : ℝ in 𝓝 0, score f (x,0) (0,y) i = 0

def reflects : ℝ × E →L[ℝ] ℝ × E := (ContinuousLinearMap.id ℝ ℝ).prodMap (-ContinuousLinearMap.id ℝ E)

def evened (f : ℝ × E→ℝ) : ℝ × E→ℝ := f + f ∘ reflects

lemma reflected (z : E)(hi : ContDiffAt ℝ ω f (x,-z)) : ContDiffAt ℝ ω (f ∘ reflects) (x,z) := hi.comp (x,z) (f:=reflects) (reflects (E:=E)).contDiff.contDiffAt
lemma score_reflect (v x : ℝ) (y z : E)(h : ContDiffAt ℝ ω f (v,-y)) : score (f ∘ reflects) (v,y) (x,z) k = score f (v,-y) (x,-z) k := by
  have hz : ContDiffAt ℝ ω f (reflects (v,y)) := h
  simpa only [zero_add] using! score_linear (x:= (v,y)) (k:=k) (x,z) reflects 0 (by simpa only [zero_add] using hz)

private lemma threads (h : ContDiffAt ℝ ω f 0) : ∀ᶠ x : ℝ in 𝓝 0, ContDiffAt ℝ ω f (x,0) :=
  ((continuous_id.prodMk (continuous_const (y:=(0:E)))).tendsto (0:ℝ)).eventually (h.eventually (by simp))

-- Differentiate score functions on external line, without identifying coefficient margins only asymptotic in x.
private lemma horizontal (h : ContDiffAt ℝ ω f (x,0)) (y : E) (a : ℝ) : D a (fun x : ℝ=>score f (x,0) (0,y) k) x = score (D (a,0) f) (x,0) (0,y) k := by
  let L : ℝ→L[ℝ] ℝ × E:= ContinuousLinearMap.inl ℝ ℝ E
  let W (z : ℝ×E):= score f z (0,y) k; let S := Tensor.coeff f k
  let A := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k=>ℝ×E) ℝ (fun _=>(0,y))
  have hx : HasFDerivAt S (fderiv ℝ S (x,0)) (x,0):= ((Tensor.coeff_smooth (h.of_le le_top) k).differentiableAt (by simp)).hasFDerivAt
  have he : HasFDerivAt (A ∘ S) (A ∘L (fderiv ℝ S (x,0))) (x,0) := A.hasFDerivAt.comp (x,0) hx
  have hi : D a (fun x => W (x,0)) x = D (a,0) W (x,0) := by
    change D a ((A ∘ S) ∘ L) x = D (a,0) (A ∘ S) (x,0); rw [D,D,(he.comp x L.hasFDerivAt).fderiv,he.fderiv]; rfl
  have hh : D a (fun z=> score f (z,0) (0,y) k) x=A (D ((a,0):ℝ×E) S (x,0)) := by rw [hi]; change D _ (A ∘ S) _=_; rw [D,he.fderiv]; rfl
  rw [hh,Tensor.D_coeff (j:=k) (h.of_le le_top) (u:=(a,0))]; rfl

namespace Held
lemma zero : Held f 0 v := by intro i hi; omega
lemma shorten {j} (h : Held f k v) (he : j ≤ k) : Held f j v:= fun _ hp =>h _ (hp.trans_le he)
lemma rise (h : Held f (k+1) v) (hf : ContDiffAt ℝ ω f 0) : Held (D (0,v) f) k v:= by
  intro i hi; filter_upwards [threads hf,h (i+1) (by omega)] with x he hh
  rw [score_succ _ he] at hh; exact (mul_eq_zero.mp hh).resolve_left (by positivity)
lemma sun (a : ℝ) (h : Held f k v)(hf : ContDiffAt ℝ ω f 0) : Held (D (a,0) f) k v := by
  intro i hi; let L : ℝ→ℝ:= fun x=> score f (x,0) (0,v) i; have he : L =ᶠ[𝓝 0] 0 := h i hi
  filter_upwards [Filter.EventuallyEq.fderiv (𝕜:=ℝ) he,threads hf] with x h h'
  rw [←horizontal h' v]; change D a L x = 0; rw [D,h]; simp

lemma each (h : Held f k v) (hf : ContDiffAt ℝ ω f 0) : ∀ i<k, jet f i (τ,v)=0:= by
  intro i hi
  induction k generalizing f i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => exact ((jet_zero ..)).trans ((score_base (0,v)).symm.trans ((h 0 hi).self_of_nhds))
    | succ i =>
      rw [←score_jet, show (τ,v)=((τ,0):ℝ×E)+(0,v) from by simp, score_split _ _ hf]
      simp only [Prod.mk_add_mk,add_zero,zero_add,score_jet]
      rw [ih ((sun τ h hf).shorten (Nat.le_succ k)) (dSmooth hf _ le_top) _ (by omega), ih (h.rise hf) (dSmooth hf _ le_top) _ (by omega),add_zero,mul_zero]

lemma at_lead (h : Held f k v) (hf : ContDiffAt ℝ ω f 0) : jet f k (τ,v)=jet f k (0,v) := by
  induction k generalizing f with
  | zero => rw [jet_zero,jet_zero]
  | succ k ih=>
    rw [←score_jet,←score_jet,show (τ,v)=((τ,0):ℝ×E)+(0,v) from by simp,score_split _ _ hf,score_succ _ hf, show ((τ,0):ℝ × E)+(0,v)=(τ,v) by simp, score_jet,score_jet,(sun τ h hf).each τ (dSmooth hf _ le_top) k (by omega), zero_add,score_jet]; rw [ih (h.rise hf) (dSmooth hf _ le_top)]
lemma flip (h : Held f k v) : Held f k (-v):= by
  intro i hi; filter_upwards [h i hi] with x hx
  rw [show ((0,-v):ℝ × E)=(-1:ℝ) • (0,v) by rw [neg_one_smul]; simp,score_scaling, hx, mul_zero]
lemma reflecting (h : Held f k v) (hf : ContDiffAt ℝ ω f 0): Held (f ∘ reflects) k v := by
  intro i hi; filter_upwards [threads hf,h.flip i hi] with x hx hh
  rw [score_reflect]; simp [hh]; simpa only [neg_zero] using hx
lemma even (h : Held f k v)(hf : ContDiffAt ℝ ω f 0) : Held (evened f) k v := by
  intro i hi; filter_upwards [threads hf,h.reflecting hf i hi,h i hi] with x hx hp hh; rw [evened,score_add _ hx (reflected _ (by simpa only [neg_zero] using hx)),hp,hh,zero_add]
lemma odd_gain (h : Held f k v)(hf : ContDiffAt ℝ ω f 0) (hk : Odd k) : Held (evened f) (k+1) v:= by
  intro i hi; rcases (Nat.le_of_lt_succ hi).eq_or_lt with rfl|hh; swap; exact h.even hf i hh
  filter_upwards [threads hf] with x hx
  rw [evened,score_add _ hx (reflected _ (by simpa only [neg_zero] using hx)), score_reflect _ _ _ _ (by simpa only [neg_zero] using hx),neg_zero, show ((0,-v):ℝ × E)=(-1:ℝ) • (0,v) from by rw [neg_one_smul]; simp,score_scaling,hk.neg_one_pow]; ring
end Held
end plane
end YM.RGComparison.Core16.Therm

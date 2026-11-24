import YM.RGComparison.Core16.Barrier
import YM.Progress.STATIONARY_SCENES.Frames
import YM.PertExtension.BareChart

/-!
# The finite path action germ, true tags and bulk-branch independence

Actual exponential chart `G.lieExp` everywhere, real coordinates. No torus inversion quotient.
Keeps option of general rescaled coarse-link log in the germ. Not assuming stationary phase for
arbitrary inherited regular terms.
-/
set_option autoImplicit false
noncomputable section

namespace YM.RGComparison.Core16.Descent
open Lattice RG Tree Wilson Push.BetaTransport Precision Exterior
open Progress.StationaryScenes PertExtension
open Function Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n c f : Side} (d : Descent n c)

abbrev Coordinates (G : Gauge) (d : Descent n c) := d.Links → G.Color

def tablePath (x : Coordinates G d) : d.Links → G.El := Chart.expLinks G d.Links x

@[simp] lemma tablePath_zero : d.tablePath (G := G) 0 = 1 := funext fun _ => G.mat_lieExp_zero

-- Use the true log-link normalization on the tree slice.
def sliceCoord (S : StepData c f) (T : Forest S.ratio) : (T.Free → G.Color) →ₗ[ℝ] Push.In G f where
  toFun u := Bid.stretch T (0,u)
  map_add' u v := by
    funext i; simp only [Pi.add_apply, Bid.stretch,linearCopy,collect]; split <;> split <;> simp
  map_smul' t u := by
    funext i; simp only [Bid.stretch,linearCopy, collect, Pi.smul_apply]; split <;> split <;> simp

lemma drape_coord (S : StepData c f) (T : Forest S.ratio) (x : T.Free → G.Color) :
    T.drape (fun i => G.lieExp (x i)) = represent (sliceCoord S T x) := by
  funext i
  change _ = G.lieExp (collect G (Bid.stretch T (0,x)) i) * (1:G.El)
  rw [Work.F01.collect_vertical, mul_one]
  split
  next h => rw [G.mat_lieExp_zero]; exact T.on_tree _ ⟨i,h⟩
  next h => exact T.off_tree _ ⟨i,h⟩

variable {d}
section flat
variable (h : d.OK G) (t : d.Tags)

private lemma drape_one (g : Lattice.Ratio c f) (T : Forest g) : T.drape (1 : T.Slice G) = 1 := by
  funext i; by_cases he : i ∈ T.trunks
  · exact T.on_tree _ ⟨i,he⟩
  exact T.off_tree _ ⟨i,he⟩

lemma fine_flat (d : Descent n c) : d.fine (1 : Config G c) 1 = 1 := by
  induction d with
  | nil => rfl
  | @push m i S T d ih => change d.fine (T.drape (1:T.Slice G)) 1 = 1; rw [drape_one, ih]

private lemma tag_energy_flat {S : StepData c f} (h : S.patch.Branches S.kernel G) (t : S.Choices) :
    tagEnergy S t (1 : Config G f) 1 = 0 := by simp [tagEnergy,noiseEnergy,linkEnergy,Push.settled S h]

include h in
lemma account_flat (β : ℕ → ℝ) : d.account β t (1 : Config G c) 1 = 0 := by
  induction d generalizing β with
  | nil => rw [account]; simp [energy,Progress.DirectedRecipe.face1]
  | @push m i S T d ih =>
    change β 1 * tagEnergy S t.1 (T.drape (1:T.Slice G)) 1 + d.account (upβ β) t.2 (T.drape (1:T.Slice G)) 1 = 0
    rw [drape_one,ih h.2,tag_energy_flat h.1,mul_zero,zero_add]
end flat

private lemma pred_eq {S : StepData c f} (h : S.patch.Branches S.kernel G) (t u : S.Choices) :
    (fun x : Push.In G f => S.prediction (represent x) t) =ᶠ[𝓝 0]
      fun x => S.prediction (represent x) u := by
  filter_upwards [(frameField h).roots] with z hz
  funext i
  have ht := hz.2 t; have hu := hz.2 u
  have hc : S.connector (represent z) t.1 i = S.connector (represent z) u.1 i := by
    funext p; unfold StepData.connector; rw [ht.1,ht.1,hu.1,hu.1]
  simp only [StepData.prediction, Patch.predict, hu.2.2 i, if_true, hc]

private lemma noise_smooth {S : StepData c f} (h : S.patch.Branches S.kernel G) (t : S.Choices) :
    ContDiffAt ℝ ω (fun u : Push.In G f × Push.In G c => tagEnergy S t (represent u.1) (represent u.2)) 0 := by
  unfold tagEnergy noiseEnergy linkEnergy
  refine ContDiffAt.sum fun i _ => ContDiffAt.mul contDiffAt_const
    (Work.F03.price_smooth (A := fun u : Push.In G f × Push.In G c => represent u.2 i *
      (S.prediction (represent u.1) t i)⁻¹) ?_)
  simp only [G.mat_mul, G.mat_inv]
  exact ((Work.F03.represent_smooth (G := G) i).contDiffAt.comp (f := Prod.snd) _ contDiffAt_snd).mul
    ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _
      ((Push.prediction_cont S h i t).comp (f := Prod.fst) (0 : Push.In G f × Push.In G c) contDiffAt_fst))

private lemma energy_smooth (G : Gauge) (n : Side) : ContDiffAt ℝ ω (fun u : Push.In G n => energy (represent u)) 0 :=
  ContDiffAt.sum fun i _ => Work.F03.price_smooth (A := fun u => faceValue (represent u) i) (Push.writes ..)

-- path coordinate (parametric in smooth logs of coarse/root and all fine links)
section atlas
variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable (h : d.OK G) {v : Y → Coordinates G d} {Bg : Y → Push.In G c} (hv : ContDiffAt ℝ ω v 0)
    (hv' : v 0 = 0) (hf : ContDiffAt ℝ ω Bg 0) (hf' : Bg 0 = 0)
    (t u : d.Tags)

private lemma nextCoord {S : StepData c f}
    {T : Forest S.ratio} {d : Descent n f} {v : Y → Coordinates G (push S T d)}
    (hv : ContDiffAt ℝ ω v 0) (hv' : v 0 = 0) :
    let w : Y → Push.In G f := fun y => sliceCoord S T fun i => v y (Sum.inl i)
    let z : Y → Coordinates G d := fun y i => v y (Sum.inr i)
    ContDiffAt ℝ ω w 0 ∧ w 0 = 0 ∧ ContDiffAt ℝ ω z 0 ∧ z 0 = 0 := by
  refine ⟨((sliceCoord S T (G := G)).toContinuousLinearMap.contDiff.contDiffAt.comp
    (f := fun x => fun i => v x (Sum.inl i)) _ (contDiffAt_pi.mpr fun i => contDiffAt_pi.mp hv _)), ?_,
      contDiffAt_pi.mpr fun i => contDiffAt_pi.mp hv _, ?_⟩
  · dsimp only; rw [hv']; exact map_zero (sliceCoord S T)
  dsimp only; rw [hv']; rfl

include h hv hv'
lemma branch_uniform : (d.probability (G := G) t ∘ d.tablePath ∘ v) =ᶠ[𝓝 0]
    fun _ => (Fintype.card d.Tags : ℝ)⁻¹ := by
  induction d with
  | nil =>
    filter_upwards with x
    change 1 = (Fintype.card Unit : ℝ)⁻¹; simp
  | @push m i S T d ih =>
    let w (x : Y) := v x ∘ Sum.inr
    let z (x : Y) := sliceCoord S T (v x ∘ Sum.inl)
    obtain ⟨h₁,h₂,h₃,h₄⟩ := nextCoord hv hv'
    have ht : Tendsto z (𝓝 0) (𝓝 0) := by
      have he : Tendsto z (𝓝 0) (𝓝 (z 0)) := h₁.continuousAt
      rwa [show z 0=0 from h₂] at he
    filter_upwards [ih (v := w) h.2 h₃ h₄ t.2, ht.eventually (likelihood_here h.1)] with x hx (he : ∀ t : S.Choices, S.likelihood (represent (z x)) t=_)
    change S.likelihood (T.drape (fun i => G.lieExp (v x (Sum.inl i)))) t.1 *
      (d.probability t.2 ∘ d.tablePath ∘ w) x = (Fintype.card (S.Choices × d.Tags) : ℝ)⁻¹
    rw [hx, drape_coord]; change S.likelihood (represent (z x)) t.1 * _ = _
    rw [he t.1, Fintype.card_prod (α := S.Choices) (β := d.Tags),Nat.cast_mul,mul_inv]

include hf hf'
lemma branch_smooth (β : ℕ → ℝ) : ContDiffAt ℝ ω (fun x => d.account β t (represent (Bg x)) (d.tablePath (v x))) 0 := by
  induction d generalizing β with
  | nil => exact contDiffAt_const.mul (((hf'.symm ▸ energy_smooth G n)).comp 0 hf)
  | @push m i S T d ih =>
    let w : Y → Coordinates G d := fun x => v x ∘ Sum.inr
    let z (x : Y) := sliceCoord S T (v x ∘ Sum.inl)
    obtain ⟨h₁,h₂,h₃,h₄⟩ := nextCoord hv hv'; change z 0 = 0 at h₂
    change ContDiffAt ℝ ω (fun x => β 1 * tagEnergy S t.1 (T.drape fun i => G.lieExp (v x (Sum.inl i))) (represent (Bg x)) + d.account (upβ β) t.2 (T.drape (fun i => G.lieExp (v x (Sum.inl i)))) (d.tablePath (w x))) 0
    have he (x : Y) : T.drape (fun i => G.lieExp (v x (Sum.inl i))) = represent (z x) := drape_coord _ _ _
    simp_rw [he]
    have hz : (z 0, Bg 0) = 0 := by rw [h₂,hf']; rfl
    exact (contDiffAt_const.mul ((hz.symm ▸ noise_smooth h.1 t.1).comp (f := fun i => (z i,Bg i)) 0 (h₁.prodMk hf))).add
      (ih h.2 h₃ h₄ h₁ h₂ t.2 _)

omit hf hf' in
lemma branch_independent (β : ℕ → ℝ) :
    (fun x => d.account β t (represent (Bg x)) (d.tablePath (v x))) =ᶠ[𝓝 0]
      (fun x => d.account β u (represent (Bg x)) (d.tablePath (v x))) := by
  induction d generalizing β with
  | nil => exact Filter.EventuallyEq.rfl
  | @push m i S T d ih =>
    let w : Y → Coordinates G d := fun x => v x ∘ Sum.inr
    let z (x : Y) := sliceCoord S T (v x ∘ Sum.inl)
    obtain ⟨h₁,h₂,h₃,h₄⟩ := nextCoord hv hv'
    have ht : Tendsto z (𝓝 0) (𝓝 0) := by
      have he : Tendsto z (𝓝 0) (𝓝 (z 0)) := h₁.continuousAt
      rwa [show z 0=0 from h₂] at he
    filter_upwards [ih (β := upβ β) (v := w) (Bg := z) h.2 h₃ h₄ t.2 u.2, ht.eventually (pred_eq h.1 t.1 u.1)] with x hx he
    have hk : T.drape ((push S T d).tablePath (v x) ∘ Sum.inl) = represent (z x) := drape_coord S T _
    rw [account, account, hk, tagEnergy, tagEnergy, he]
    exact congrArg (_ + ·) hx
end atlas
end YM.RGComparison.Core16.Descent

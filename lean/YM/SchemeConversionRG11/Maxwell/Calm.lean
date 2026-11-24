import YM.SchemeConversionRG11.Maxwell.Cartan
import YM.SchemeConversionRG11.Detector.Poll
import YM.Pert.Rigid.Camera
import YM.Work.C07.Euclid

/-! # Real infinitesimal stabilizers. Turn into a common finite map on all
separated reports, then extract its orthogonal action on real Wick symbols. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter MeasureTheory Metric Maxwell Maxwell.Free Wick Tensor Set
open NormedSpace
open Pert.Position Horizon
open scoped Topology BigOperators RealInnerProductSpace InnerProduct ComplexOrder ContDiff

variable {G : Gauge} (F : Labels.Frames G) {d n : ℕ}

lemma plaza (x : Points n) (p : Fin n → E F d) : visible F d x p=moment G x (address F d ∘ p) :=
  display F (fun i ↦ (⟨d,p i⟩ : (freeTable F).Tag))
def Calm (B : Buffer F d) := ∀ (r : ℕ) (p : Fin r→ E F d) (x : Points r),x∈conf r →
    ∑ i:Fin r,visible F d x (update p i (B.val (p i)))=0
lemma erases (H : G.Simple) {B : Buffer F d} (hx : Calm F B) (h : 4≤d) : restr F h B=0 := by
  apply Pert.Rigid.frozen_four F H; intro r p x hp
  rw [← hx r (incl F h ∘ p) x hp]; apply Finset.sum_congr rfl; intro i _
  have hw : (update (incl F h ∘ p) i (B.val ((incl F h ∘ p) i)))=incl F h ∘ (update p i ((restr F h B).val (p i))) := by
    funext a; rcases eq_or_ne a i with h|H
    · subst a; simp [restrictions]
    simp only [Function.comp_apply, update_of_ne H]
  rw [hw]; exact (Detector.Poll.visibleIncl _ x h).symm
lemma erases_small (H : G.Simple) {B : Buffer F d} (hx : Calm F B) (h : 4 ≤ d) (p : E F 4) : B.val (incl F h p)=0 := by
  rw [← restrictions, erases F H hx h]; change incl F h 0=0; rw [map_zero]

section
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
private def iter (K : A →L[ℝ] A) (t : ℝ) := NormedSpace.exp (t • K)
private lemma iter_cost (K : A →L[ℝ] A) (t : ℝ) (v : A) : HasDerivAt (fun s : ℝ ↦ iter K s v) (K (iter K t v)) t := by
  have he : HasDerivAt (iter K) (K*iter K t) t := hasDerivAt_exp_smul_const' K t
  exact (ContinuousLinearMap.apply ℝ A v).hasFDerivAt.comp_hasDerivAt t he
omit [CompleteSpace A] in
private lemma iter_zero (K : A →L[ℝ] A) : iter K 0=1 := by simp [iter]
end
def flange (B : Buffer F d) (t : ℝ) : operator F d := iter B.val t
lemma flange_zero (B : Buffer F d) : flange F B 0=1 := iter_zero _
lemma earning (B : Buffer F d) (t : ℝ) (v : E F d) : HasDerivAt (fun s:ℝ ↦ flange F B s v) (B.val (flange F B t v)) t := iter_cost B.val t v

lemma running_null (B : Buffer F d) {f g : ℝ → E F d} (he : ∀ t, HasDerivAt f (B.val (f t)) t) (hf : ∀ t, HasDerivAt g (B.val (g t)) t) (h : f 0=g 0) : f=g := ODE_solution_unique_univ (s:=fun _ ↦ univ) (fun _ ↦ B.val.lipschitz.lipschitzOnWith) (fun t ↦ ⟨he t,mem_univ _⟩) (fun t ↦ ⟨hf t,mem_univ _⟩) h

lemma flange_small (H : G.Simple) {B : Buffer F d} (hx : Calm F B) (h : 4 ≤ d) (p : E F 4) (t : ℝ) :
    flange F B t (incl F h p) = incl F h p := by
  let q := incl F h p
  have hu (s:ℝ) : HasDerivAt (fun _:ℝ ↦ q) (B.val q) s := by rw [erases_small F H hx h p]; exact hasDerivAt_const ..
  exact congr_fun (running_null F B (fun s ↦ earning F B s q) hu (by rw [flange_zero]; rfl)) t

lemma flange_bar (B : Buffer F d) (p : E F d) (t : ℝ) : flange F B t (bar F d p)=bar F d (flange F B t p) := by
  let L : E F d →ₗ[ℝ] E F d := {
    toFun := bar F d
    map_add' u v := map_add _ _ _
    map_smul' t u := by
      change bar F d (t • u)=t • bar F d u
      rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), RCLike.real_smul_eq_coe_smul (K:=ℂ), map_smulₛₗ]; simp }
  let g (s:ℝ) := L (flange F B s p)
  have hg s : HasDerivAt g (B.val (g s)) s := by
    have he : B.val (g s)= L (B.val (flange F B s p)) := (B.property.2.2.1 _).symm
    rw [he]; exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s (earning F B s p)
  exact congr_fun (running_null F B (fun s ↦ earning F B s (bar F d p)) hg (by unfold g; rw [flange_zero]; rfl)) t

private def listen (x : Points n) (d : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E F d) ℂ :=
  (⟨visible F d x,Work.C07.continuous_cap_multilinear (fun _ ↦ d) (visible F d x)⟩ : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ E F d) ℂ).restrictScalars ℝ

lemma absorbs {B : Buffer F d} (hx : Calm F B) (t : ℝ) {x : Points n} (h : x ∈ conf n) (V : Fin n → E F d) : visible F d x (flange F B t ∘ V)=visible F d x V := by
  classical
  let f (t:ℝ) : ℂ := visible F d x (flange F B t ∘ V)
  have hf t : HasDerivAt f 0 t := by
    let L := listen F x d
    let p s := flange F B s ∘ V
    let w i := B.val (p t i)
    have he : HasDerivAt p w t := hasDerivAt_pi.mpr (fun i ↦ earning F B t (V i))
    rw [← show L.linearDeriv (p t) w=0 from ?_]
    · exact L.hasFDerivAt (p t) |>.comp_hasDerivAt t he
    rw [ContinuousMultilinearMap.linearDeriv_apply]; exact hx _ (p t) _ h
  have he : f 0=visible F d x V := by unfold f; rw [flange_zero]; rfl
  exact congr_fun (ODE_solution_unique_univ (s:=fun _ ↦ univ) (v:=fun _ : ℝ ↦ (fun _ : ℂ ↦ (0:ℂ))) (fun _ ↦ (LipschitzWith.const _).lipschitzOnWith)
    (fun t ↦ ⟨hf t, mem_univ _⟩) (fun t ↦ ⟨hasDerivAt_const t _,mem_univ _⟩) he) t

def squads (r : Flavor 0) : E F 4 := (fields F 4).symm ⟨team G r r,team_label r r le_rfl⟩
lemma squares (r : Flavor 0) : address F 4 (squads F r)=team G r r := by unfold squads; rw [address_eval, LinearEquiv.apply_symm_apply]
lemma glaze {B : Buffer F d} (H : G.Simple) (hx : Calm F B) (h : 4 ≤ d) (p : Fin n → E F d) (t : ℝ) :
    Muted duelP (duelW (address F d ∘ p) (address F d ∘ flange F B t ∘ p)) := by
  classical
  intro m e V S hv x hh
  let L : Fin m → E F d := extend e p (fun i ↦ incl F h (squads F (S i)))
  simp only [Fintype.sum_bool,duelP, Bool.false_eq_true,↓reduceIte, neg_mul,one_mul]
  rw [neg_add_eq_zero]; let R := address F d; let A := flange F B t
  have hp : V false=R ∘ L := by
    funext i; by_cases hi : ∃ a,e a=i
    · obtain ⟨a,rfl⟩ := hi; rw [hv.1,Function.comp_apply,show L (e a)=p a from e.injective.extend_apply _ _ a]; rfl
    rw [hv.2 i (not_exists.mp hi),Function.comp_apply]; unfold L Function.extend; simp only [dif_neg hi]; exact ((address_rise F _ h _).trans (squares F (S i))).symm
  have hq : V true=R ∘ A ∘ L := by
    funext i; by_cases hi : ∃ a,e a=i
    · obtain ⟨a,rfl⟩ := hi; rw [hv.1,Function.comp_apply,Function.comp_apply,show L (e a)=p a from e.injective.extend_apply _ _ a]; rfl
    rw [hv.2 i (not_exists.mp hi),Function.comp_apply,Function.comp_apply]; unfold L Function.extend; simp only [dif_neg hi]; unfold A; rw [flange_small F H hx]; exact ((address_rise F _ h _).trans (squares F (S i))).symm
  rw [hp,hq]; exact ((plaza F _ (A ∘ L)).symm.trans ((absorbs F hx _ hh L).trans (plaza F _ L))) -- orientation
end YM.SchemeConversionRG11.Corona

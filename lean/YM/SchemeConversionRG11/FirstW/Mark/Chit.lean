import YM.SchemeConversionRG11.FirstW.Mark.Rail
/-! Actual bare analytic link ray completions through second order, at every derivative size. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Lattice Pert Topology Maxwell Filter Function
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {X : Type*} [AddCommGroup X] [One X] {G : Gauge} {j : ℕ}
abbrev Echo (G : Gauge) (j : ℕ) (X : Type*) := Wind G X →ₗ[ℝ] Wind G X →ₗ[ℝ] Labels.Taylor G j
def rush (G : Gauge) (x : Four X) (j : ℕ) : Wind G X →ₗ[ℝ] Wind G X →ₗ[ℝ] Bare.Response G j where
 toFun A:= LinearMap.pi (fun i => LinearMap.pi (fun a=> LinearMap.pi (fun p=> (j.factorial:ℝ)⁻¹ • ∑ s:Finset (Fin j), Bare.sign s • swerve x (patch (Bare.walk p s) i a) A)))
 map_add' A B:= by
    apply LinearMap.ext; intro C; funext i a p; simp [Finset.sum_add_distrib, smul_add]
 map_smul' c A:= by
    apply LinearMap.ext; intro C; funext i a p; simp only [RingHom.id_apply,map_smul, LinearMap.pi_apply,LinearMap.smul_apply,LinearMap.sum_apply, Pi.smul_apply]; rw [smul_comm c]; congr 1; rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun i _=>smul_comm ..)
def sheer (G : Gauge) (j : ℕ) (x : Four X) : Echo G j X := (Fintype.card Signed:ℝ)⁻¹ • ∑ s : Signed, let L:= Bare.wideLink G (R:=X) s; (((rush G (affine s⁻¹ 0 x) j).compl₂ L).comp L).compr₂ (Labels.Taylor.turn s.ortho ∘ₗ Bare.radialMap)
def glint (x : Four X) (j : ℕ) := (1/4:ℝ) • (sheer G j x + (sheer G j x).flip)
def echoAt (x : Four X) (k : Labels.Key G) := (glint (G:=G) x k.1).compr₂ ((Labels.axes G k.1).coord k.2)
def echoLeg (h : ℝ) (x : Four X) (k : Labels.Key G) := (h^mass k)⁻¹ • echoAt x k
lemma glint_once (x : Four X) (k : ℕ) (A B : Wind G X) : glint x k A B = (1/4:ℝ) • (sheer G k x A B+sheer G k x B A) := rfl
lemma echoAt_symm (x : Four X) (k : Labels.Key G) (A B : Wind G X) : echoAt x k A B= echoAt x k B A := by simp_rw [echoAt,LinearMap.compr₂_apply,glint_once,add_comm (sheer G _ _ B A)]
lemma sheer_eq (A B : Wind G X) (j : ℕ) (x) : sheer G j x A B=(Fintype.card Signed:ℝ)⁻¹ • ∑ s:Signed, Labels.Taylor.turn s.ortho (Bare.radialMap (rush G (affine s⁻¹ 0 x) j (Bare.wideLink G s A) (Bare.wideLink G s B))) := by simp [sheer]
lemma scan_road (t : Walk) (x : Four X) (A : Wind G X) : ContDiff ℝ ∞ (fun r:ℝ=> G.mat (travel (pointU A r) x t)) := by
  induction t generalizing x with
  | nil=> simp_rw [travel]; exact contDiff_const
  | cons d t ih=>
    simp only [travel, G.mat_mul]
    apply ContDiff.mul _ (ih _); unfold Step.read pointU; split
    · simp_rw [G.mat_inv]; exact ((starL ℝ).contDiff).comp ((G.exp_jet.of_le le_top).comp (f:=fun r:ℝ=>r • _) (contDiff_id.smul contDiff_const))
    exact (G.exp_jet.of_le le_top).comp (contDiff_id.smul contDiff_const)
open Pert.First
lemma shine (j : ℕ) (x : Four X) (A : Wind G X) : ContDiff ℝ ∞ (fun r : ℝ=> Bare.diffU j (pointU A r) x) := by
  apply contDiff_pi.mpr; intro i; apply contDiff_pi.mpr; intro a; apply contDiff_pi.mpr; intro p
  simp only [Bare.diffU,← trace_ride,recover_group]
  refine ContDiff.const_smul _ (ContDiff.sum fun w _=>ContDiff.const_smul (c:=Bare.sign w) ?_)
  exact (recoverL G).contDiff.comp (g:=recoverL G) (scan_road _ x A)
lemma roll_two (j : ℕ) (x : Four X) (A : Wind G X) : iteratedDeriv 2 (fun r:ℝ=> Bare.diffU j (pointU A r) x) 0= rush G x j A A := by
  funext i a p
  let L : Bare.Response G j →ₗ[ℝ] G.Color := LinearMap.proj p ∘ₗ LinearMap.proj a ∘ₗ LinearMap.proj i
  change L (iteratedDeriv (F:=Bare.Response G j) 2 _ _)= _; rw [←First.iterated_linear (E:=Bare.Response G j) (D:=G.Color) L _ (shine _ x A)]
  dsimp only [L,LinearMap.comp_apply,LinearMap.proj_apply]; simp only [Bare.diffU]; erw [iteratedDeriv_fun_const_smul_field]
  have e (w): ContDiffAt ℝ (2:ℕ) (fun r:ℝ=>Bare.sign w • Bare.plateU (pointU A r) x (Bare.walk p w) i a) 0 := by
    simp only [←trace_ride,recover_group]; exact (((recoverL G).contDiff.comp (g:=recoverL G) (scan_road _ _ A)).const_smul _).contDiffAt.of_le (by decide)
  rw [iteratedDeriv_fun_sum (fun _ _ => e _)]
  simp only [rush,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.pi_apply, LinearMap.sum_apply,LinearMap.smul_apply]
  exact congrArg _ (Finset.sum_congr rfl fun w _=> by erw [iteratedDeriv_fun_const_smul_field]; rw [echo_exact])
lemma point_pull (s : Signed) (r : ℝ) (A : Wind G X) : pointU (Bare.wideLink G s A) r = pull s 0 (pointU A r) := by
  funext y; unfold pointU pull Step.read; rw [Bare.wideLink_apply,affine,add_zero]; split_ifs <;> simp [Work.F03.exp_neg_color]
lemma oval_blip (A : Wind G X) (s : Signed) (h : ℝ) (x) (j) :
    ContDiff ℝ ∞ (fun r:ℝ=> Bare.oval s h (pointU A r) x j) ∧ iteratedDeriv 2 (fun r:ℝ=> Bare.oval s h (pointU A r) x j) 0 = h ^ (-(j+2:ℤ)) • Labels.Taylor.turn s.ortho (Bare.radialMap (rush G (affine s⁻¹ 0 x) j (Bare.wideLink G s A) (Bare.wideLink G s A))) := by
  let L : Bare.Response G j→ₗ[ℝ] Labels.Taylor G j := Labels.Taylor.turn s.ortho ∘ₗ (h ^ (-(j+2:ℤ)) • Bare.radialMap)
  simp only [Bare.oval,←point_pull,Bare.rawJet]; constructor
  · exact (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Bare.Response G j) (F:=Labels.Taylor G j) (LinearMap.toContinuousLinearMap L)).comp (g:=L.toContinuousLinearMap) (shine _ _ _)
  have H:=iterated_linear (E:=Bare.Response G j) (D:=Labels.Taylor G j) L 0 (d:=2) (shine j (affine s⁻¹ 0 x) (Bare.wideLink G s A)); rw [roll_two] at H; exact H.trans (by simp [L])
lemma tensor_ride (A : Wind G X) (h : ℝ) (x) (j) :
  ContDiff ℝ ∞ (fun r:ℝ=> Bare.tensorJet h (pointU A r) x j) ∧ iteratedDeriv 2 (fun r:ℝ=> Bare.tensorJet h (pointU A r) x j) 0= h ^ (-(j+2:ℤ)) • sheer G j x A A := by
  unfold Bare.tensorJet; constructor
  · exact ContDiff.const_smul _ (ContDiff.sum (fun s _=> (oval_blip A s h x j).1))
  erw [iteratedDeriv_fun_const_smul_field, iteratedDeriv_fun_sum (fun s _ => (oval_blip A s h x j).1.contDiffAt.of_le (by decide))]; simp only [(oval_blip ..).2,← Finset.smul_sum, sheer_eq]; rw [smul_comm]
end YM.RG11.FirstW

import YM.SchemeConversionRG11.FirstW.Mark.Chit
/-! Orbit weight-1 variations and symmetry equivariance. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {X : Type*} [AddCommGroup X] [One X]
lemma pl_adapt (x : Site n) (w : Walk) (i j : Axis) (a : Orb.Potential G n) : Bare.plateU (Orb.positiveLinks a) x w i j = G.curvature (travel (Orb.positiveLinks a) x (patch w i j)) := (trace_ride ..).symm
lemma jet_straight (x : Site n) (j : ℕ) (h : ℝ) : ContDiff ℝ ∞ (fun A : Orb.Potential G n=>Bare.tensorJet h (Orb.positiveLinks A) x j) := by
  unfold Bare.tensorJet
  refine ContDiff.const_smul _ (ContDiff.sum (s:=Finset.univ) fun s _=>?_)
  unfold Bare.oval Bare.rawJet; simp_rw [← Bare.rotation_links]
  let L : Bare.Response G j→L[ℝ] Labels.Taylor G j := LinearMap.toContinuousLinearMap (Labels.Taylor.turn s.ortho ∘ₗ ((h ^ (-(↑j+2:ℤ))) • Bare.radialMap))
  apply ContDiff.comp (g:=L) (f:=fun A:Orb.Potential G n=>Bare.diffU j (Orb.positiveLinks (Bare.rotation s A)) (affine s⁻¹ 0 x)) (ContinuousLinearMap.contDiff (𝕜:=ℝ) (F:=Labels.Taylor G j) (E:=Bare.Response G j) L)
  have hU (i a : Axis) (w : Walk) (q : Site n) : ContDiff ℝ ∞ (fun A : Orb.Potential G n=>Bare.plateU (Orb.positiveLinks (Bare.rotation s A)) q w i a) := by
    simp_rw [pl_adapt,Pert.First.recover_group]; let S : Orb.Potential G n →L[ℝ] Orb.Potential G n := (Bare.rotation s).toContinuousLinearMap
    exact (Pert.First.recoverL G).contDiff.comp (g:=Pert.First.recoverL G) (((Bare.travel_mDiff q (patch w i a) (G:=G)).of_le le_top).comp (f:=S) S.contDiff)
  apply contDiff_pi.mpr; intro i; apply contDiff_pi.mpr; intro k; apply contDiff_pi.mpr; intro p
  exact ContDiff.const_smul (F:=G.Color) _ (ContDiff.sum fun u _=> (hU i k (Bare.walk p u) _).const_smul _)
set_option maxHeartbeats 400000 in
lemma echo_actual (k : Labels.Key G) (o : Site n) (h : ℝ) (c : Orb.Coords G n) : PowerSeries.coeff 1 (Bare.seriesLex h o c k) = (echoLeg h o k (Orb.expand G n c).val (Orb.expand G n c).val:ℝ) := by
  let A := Orb.expand G n c
  let L : Labels.Taylor G k.1 →L[ℝ] ℂ := Complex.ofRealCLM ∘L ((Labels.axes G k.1).coord k.2).toContinuousLinearMap
  have ht : ContDiff ℝ ∞ (Bare.datum h o k) := by
    have e : Bare.datum h o k = (L ∘ (fun v=>Bare.tensorJet h (Orb.positiveLinks v) o k.1)) := rfl
    rw [e]; exact (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Labels.Taylor G k.1) (F:=ℂ) L).comp (jet_straight (G:=G) o k.1 h)
  unfold Bare.seriesLex; rw [PowerSeries.coeff_mk, Pert.First.lineJet _ _ _ ht]
  let F := fun r:ℝ=> Bare.tensorJet h (pointU A.val r) o k.1
  have he : (fun r:ℝ=>Bare.datum h o k (r • A))=fun r=> L (F r) := rfl
  rw [show (1:ℕ)+1 = 2 by decide]
  have hh : ∀ r : ℝ,Bare.datum h o k (r • Orb.expand G n c)= L (F r) := congrFun he
  simp_rw [hh]
  have hq := (Pert.First.iterated_clm L (f:=F) (d:=2) 0 (tensor_ride A.val h o k.1).1)
  rw [hq]; unfold F; rw [(tensor_ride ..).2]; unfold echoLeg echoAt
  simp only [LinearMap.smul_apply,LinearMap.compr₂_apply,glint_once,map_add,map_smul,L,ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply]
  simp only [smul_eq_mul]
  rw [zpow_neg,show ↑k.fst + (2:ℤ)=(mass k:ℤ) from by unfold mass; push_cast; rfl,zpow_natCast]
  have eh (R s : ℝ) : (↑(Nat.factorial 2):ℝ)⁻¹ • s • (↑R:ℂ)=↑(s*((1/4)*(R+R))) := by simp [Complex.real_smul,Nat.factorial]; ring
  rw [eh]
  unfold A; rfl
open Pert.First
lemma roll_one (j : ℕ) (x : Four X) (A : Wind G X) : iteratedDeriv 1 (fun r:ℝ=> Bare.diffU j (pointU A r) x) 0= Bare.wideCore G j x A := by
  funext i a p
  let L : Bare.Response G j →ₗ[ℝ] G.Color := LinearMap.proj p ∘ₗ LinearMap.proj a ∘ₗ LinearMap.proj i
  change L (iteratedDeriv (F:=Bare.Response G j) 1 _ _)= _; rw [←First.iterated_linear (E:=Bare.Response G j) (D:=G.Color) L _ (shine _ x A)]
  dsimp only [L,LinearMap.comp_apply,LinearMap.proj_apply]; simp only [Bare.diffU]; erw [iteratedDeriv_fun_const_smul_field]
  have e (w): ContDiffAt ℝ (1:ℕ) (fun r:ℝ=>Bare.sign w • Bare.plateU (pointU A r) x (Bare.walk p w) i a) 0 := by
    simp only [←trace_ride,recover_group]; exact (((recoverL G).contDiff.comp (g:=recoverL G) (scan_road _ _ A)).const_smul _).contDiffAt.of_le (by decide)
  rw [iteratedDeriv_fun_sum (fun _ _ => e _)]
  rw [Bare.wideCore_apply]
  exact congrArg _ (Finset.sum_congr rfl fun w _=> by erw [iteratedDeriv_fun_const_smul_field]; rw [echo_once,patched,Bare.displaced])
lemma tensor_front (A : Wind G X) (h : ℝ) (x) (j) : iteratedDeriv 1 (fun r:ℝ=> Bare.tensorJet h (pointU A r) x j) 0 = Bare.wideLinear G j h x A := by
  unfold Bare.tensorJet; erw [iteratedDeriv_fun_const_smul_field, iteratedDeriv_fun_sum (fun s _ => (oval_blip A s h x j).1.contDiffAt.of_le (by decide))]
  unfold Bare.wideLinear; rw [LinearMap.smul_apply,LinearMap.sum_apply]; refine congrArg _ (Finset.sum_congr rfl fun s _=>?_)
  let L : Bare.Response G j→ₗ[ℝ] Labels.Taylor G j := Labels.Taylor.turn s.ortho ∘ₗ (h ^ (-(j+2:ℤ)) • Bare.radialMap)
  have he := iterated_linear (E:=Bare.Response G j) (D:=Labels.Taylor G j) L 0 (d:=1) (shine j (affine s⁻¹ 0 x) (Bare.wideLink G s A)); simp only [Bare.oval,←point_pull,Bare.rawJet]; rw [roll_one] at he; exact he
lemma crossHr {Z : Type*} [AddCommGroup Z] {b c d e f g : Z} (hx : b+d+(c+g)=b+f+(e+g)) : c+d=e+f := by grind
lemma glints_symm (t : Signed) (A B : Wind G X) (x) (j) :
    glint x j (Bare.wideLink G t A) (Bare.wideLink G t B)=Labels.Taylor.turn t⁻¹.ortho (glint (affine t 0 x) j A B) := by
  let F:=glint (affine t 0 x) (G:=G) j; let Q:=glint (G:=G) x j
  let S : Wind G X→ₗ[ℝ] Wind G X := Bare.wideLink G t; let L : Labels.Taylor G j→ₗ[ℝ] Labels.Taylor G j := Labels.Taylor.turn t⁻¹.ortho
  have hh (A : Wind G X) : sheer G j x (S A) (S A) = L (sheer G j (affine t 0 x) A A) := by
    have He := (tensor_ride (S A) 1 x j).2; unfold S at He; simp_rw [point_pull,Bare.tensor_move,one_zpow,one_smul] at He
    rw [← He]; have ht := tensor_ride A 1 (affine t 0 x) j; have H:=iterated_linear (E:=Labels.Taylor G j) (D:=Labels.Taylor G j) L 0 (d:=2) ht.1; rw [ht.2,one_zpow,one_smul] at H; exact H
  have h := hh (A+B); have he := hh A; have hu := hh B; simp only [map_add,LinearMap.add_apply] at h
  rw [he,hu] at h
  simp only [glint_once,map_smul,map_add]
  have hh2 := crossHr h
  unfold S L at hh2; rw [hh2]
lemma linear_symm (t : Signed) (A : Wind G X) (x) (j) (h : ℝ) : Bare.wideLinear G j h x (Bare.wideLink G t A) = Labels.Taylor.turn t⁻¹.ortho (Bare.wideLinear G j h (affine t 0 x) A) := by
  rw [←tensor_front,←tensor_front]; simp only [point_pull,Bare.tensor_move]; exact iterated_linear (E:=Labels.Taylor G j) (D:=Labels.Taylor G j) _ _ (tensor_ride ..).1
end YM.RG11.FirstW

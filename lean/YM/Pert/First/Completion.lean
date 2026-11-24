import YM.Pert.First.ActionVertex
/-! First nonlinear corrections of the undifferentiated curvature stencils (physical length -2 per slot). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 320000
set_option maxRecDepth 8000
noncomputable section
namespace YM.Pert.First
open Filter Lattice Function Orb Labels Set Bare
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {N : Side} {X : Type*} [AddCommGroup X] [One X]
lemma response_face (U : Links X G.El) (x : Four X) (i j r) : diffU 0 U x i j r=plateU U x [] i j := by
  simp only [diffU,Nat.factorial_zero,Nat.cast_one,inv_one,one_smul]
  rw [Finset.sum_eq_single_of_mem (∅ : Finset (Fin 0)) (Finset.mem_univ _)]
  · simp [sign,walk]
  exact fun b _ hb=> False.elim (hb (Subsingleton.elim b _))
lemma iterated_clm {E D : Type*} [NormedAddCommGroup E] [NormedAddCommGroup D] [NormedSpace ℝ E] [NormedSpace ℝ D]
    (L : E →L[ℝ] D) {f : ℝ→ E} {d : ℕ} (t) (hf : ContDiff ℝ ∞ f) : iteratedDeriv d (fun r:ℝ=> L (f r)) t = L (iteratedDeriv d f t) := by
  have e : (fun r => L (f r)) = L ∘ f := rfl
  simp only [e,iteratedDeriv_eq_iteratedFDeriv, ContinuousLinearMap.iteratedFDeriv_comp_left L (f:=f) hf.contDiffAt (show (d:WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)];rfl
lemma iterated_linear {E D : Type*} [NormedAddCommGroup E] [NormedAddCommGroup D] [NormedSpace ℝ E] [NormedSpace ℝ D] [FiniteDimensional ℝ E]
    (L : E →ₗ[ℝ] D) {f : ℝ→ E} {d : ℕ} (t) (hf : ContDiff ℝ ∞ f) : iteratedDeriv d (fun r => L (f r)) t = L (iteratedDeriv d f t) := iterated_clm (LinearMap.toContinuousLinearMap L) t hf
lemma rawPlate (x : Site N) (i j) (a : Potential G N) : plateU (positiveLinks a) x [] i j = G.curvature (plaquette a x i j) := by simp [plateU, square_links, plaquette,travel,stop]
lemma plus_path (x : Site N) : ContDiff ℝ ∞ (fun a : Potential G N=> diffU 0 (positiveLinks a) x) := contDiff_pi.mpr fun i=> contDiff_pi.mpr fun j=>contDiff_pi.mpr (fun r=> (by simp_rw [response_face,rawPlate]; exact (curve_diff (pos_sqDiff ..)).of_le le_top))
lemma diff_second (v : Potential G N) (x : Site N) : iteratedDeriv 2 (fun t:ℝ=> diffU 0 (positiveLinks (t • v)) x) 0=fun i j r=> bracketAt x i j v.val := by
  let e i j (r : Fin 0→Axis): Response G 0 →ₗ[ℝ] G.Color := LinearMap.proj r ∘ₗ LinearMap.proj j ∘ₗ LinearMap.proj i
  funext i j r
  let f := fun t:ℝ => diffU 0 (positiveLinks (t•v)) x
  have hc : ContDiff ℝ ∞ f := (plus_path x).comp (g:=fun a=> diffU 0 (positiveLinks a) x) (f:=fun t:ℝ=>t • v) (contDiff_id.smul contDiff_const)
  change e i j r (iteratedDeriv 2 f 0)=_
  rw [← iterated_linear (E:=Response G 0) (e i j r) 0 hc]
  dsimp only [f,e,LinearMap.comp_apply,LinearMap.proj_apply]; simp_rw [response_face]; exact curvature_second_on ..
lemma raw_intact (h : ℝ) (o : Site N) : ContDiff ℝ ∞ (fun v:Potential G N=> rawJet h (positiveLinks v) o 0) := by
  let L : Response G 0 →L[ℝ] Labels.Taylor G 0 := radialMap.toContinuousLinearMap
  let f := (fun v:Potential G N=> diffU 0 (positiveLinks v) o)
  exact ContDiff.const_smul (E:=Potential G N) (F:=Labels.Taylor G 0) (𝕜:=ℝ) ((h:ℝ)^(-(0+2:ℤ))) (ContinuousLinearMap.contDiff (F:=Labels.Taylor G 0) (𝕜:=ℝ) L |>.comp (f:=f) (g:=(L:Response G 0→_)) (plus_path o))
def blade (o : Four X) (r : Signed) (A : Links X G.Color) : Response G 0 := fun i j _ => bracketAt (affine r⁻¹ 0 o) i j (wideLink G r A)
def mixedJet (h : ℝ) (o : Four X) (r : Signed) (A : Links X G.Color) : Labels.Taylor G 0 := Labels.Taylor.turn r.ortho (h^(-(2:ℤ)) • radialMap (blade o r A))
variable (v : Potential G N) (h : ℝ) (o : Site N) (r : Signed)
lemma raw_first (a : Potential G N) : iteratedDeriv 2 (fun t:ℝ => rawJet h (positiveLinks (t • a)) o 0) 0 = h^(-(2:ℤ)) • radialMap (fun i j _=> bracketAt o i j a.val) := by
  unfold rawJet; erw [iteratedDeriv_fun_const_smul_field]
  let f := fun t:ℝ=> diffU 0 (positiveLinks (t • a)) o
  have he := iterated_linear (d:=2) (E:=Response G 0) (D:=Labels.Taylor G 0) (radialMap (G:=G) (j:=0)) (f:=f) 0 ((plus_path o).comp (g:=fun a=>diffU 0 (positiveLinks a) o) (f:=fun t:ℝ=>t • a) (contDiff_id.smul contDiff_const))
  exact congrArg (fun x : Labels.Taylor G 0 => h^(-(2:ℤ)) • x) (he.trans ( congrArg _ (diff_second a o)))
lemma rotate_comp (r : Signed) (v : Potential G N) : (rotation r v).val = wideLink G r v.val := rfl
lemma oval_intact : ContDiff ℝ ∞ (fun v:Potential G N=> oval r h (positiveLinks v) o 0) := by
  simp_rw [oval,← rotation_links]
  exact ContDiff.comp (g:=((Labels.Taylor.turn r.ortho).toContinuousLinearMap : Labels.Taylor G 0 →L[ℝ] Labels.Taylor G 0)) (ContinuousLinearMap.contDiff ..) ((raw_intact h (affine r⁻¹ 0 o)).comp (f:=fun v=>rotation r v) ((LinearMap.toContinuousLinearMap (rotation r)).contDiff (𝕜:=ℝ)))
lemma oval_quadratic : iteratedDeriv 2 (fun t:ℝ=> oval r h (positiveLinks (t•v)) o 0) 0=mixedJet h o r v.val := by
  unfold mixedJet oval; simp only [←rotation_links, LinearMap.map_smul,rotate_comp]
  let U := fun t:ℝ=> rawJet h (positiveLinks (t•(rotation r v))) (affine r⁻¹ 0 o) 0
  have he := iterated_linear (E:=Labels.Taylor G 0) (D:=Labels.Taylor G 0) (d:=2) (Labels.Taylor.turn r.ortho) (f:=U) (0:ℝ) ((raw_intact h ..).comp (f:=fun t:ℝ=> t • rotation r v) (contDiff_id.smul contDiff_const))
  exact he.trans ((congrArg (Labels.Taylor.turn r.ortho) (raw_first h (affine r⁻¹ 0 o) (rotation r v))).trans (LinearMap.map_smul (Labels.Taylor.turn (G:=G) (j:=0) r.ortho) _ _))
lemma tensor_intact : ContDiff ℝ ∞ (fun v:Potential G N=> tensorJet h (positiveLinks v) o 0) := ContDiff.const_smul (𝕜:=ℝ) (E:=Potential G N) (F:=Labels.Taylor G 0) ((Fintype.card Signed:ℝ)⁻¹) (ContDiff.sum (s:=Finset.univ) (fun r _=>oval_intact h (G:=G) o r))
lemma tensor_quadratic : iteratedDeriv 2 (fun t:ℝ=> tensorJet h (positiveLinks (t•v)) o 0) 0=(Fintype.card Signed:ℝ)⁻¹ • ∑ r, mixedJet h o r v.val := by
  let f:= fun (r : Signed) (t : ℝ) => oval r h (positiveLinks (t•v)) o 0
  have he r : ContDiffAt ℝ (2:ℕ) (f r) 0 := ((oval_intact h (G:=G) o r).comp (f:=fun t:ℝ=>t•v) (contDiff_id.smul contDiff_const)).contDiffAt.of_le (by decide)
  unfold tensorJet; erw [iteratedDeriv_fun_const_smul_field]; rw [iteratedDeriv_fun_sum (I:=Finset.univ) (f:=f) (fun r _ => he r)]; simp only [f, oval_quadratic]
def legK (i : Fin (dim G 0)) : Labels.Taylor G 0 →L[ℝ] ℂ := Complex.ofRealCLM ∘L ((axes G 0).coord i).toContinuousLinearMap
def completion (h : ℝ) (o : Four X) (i : Fin (dim G 0)) (A : Links X G.Color) := legK i ((1/2:ℝ) • (Fintype.card Signed:ℝ)⁻¹ • (∑ r, mixedJet h o r A))
def scalarDatum (h : ℝ) (o : Site N) (i : Fin (dim G 0)) := datum h o (⟨0,i⟩:Labels.Key G)
lemma scalarDatum_one (i : Fin (dim G 0)) : scalarDatum h o i v = legK i (tensorJet h (positiveLinks v) o 0) := rfl
lemma precise_line (i : Fin (dim G 0)) (c : Coords G N) : ContDiff ℝ ∞ (fun t:ℝ=>tensorJet h (positiveLinks (t•expand G N c)) o 0) := by
  have hc t : (t:ℝ) • (expand G N c) = (ContinuousLinearMap.id ℝ ℝ).smulRight (expand G N c) t := rfl
  simp_rw [hc]; exact (tensor_intact h o).comp (g:=_) (f:=(ContinuousLinearMap.id ℝ ℝ).smulRight (expand G N c)) (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=ℝ) (F:=(Potential G N)) (n:=∞) _)
lemma datum_intact (i : Fin (dim G 0)) : ContDiff ℝ ∞ (scalarDatum h o i):= (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Labels.Taylor G 0) (F:=ℂ) (legK (G:=G) i)).comp (g:=legK i) (tensor_intact h o)
lemma completion_exact (i : Fin (dim G 0)) (c : Coords G N) : PowerSeries.coeff 1 (seriesLex h o c (⟨0,i⟩:Key G)) = completion h o i (expand G N c).val := by
  unfold seriesLex; rw [PowerSeries.coeff_mk]
  change scaleJet (scalarDatum h o i) 2 c=_; have Hd:=datum_intact h (G:=G) o i
  rw [lineJet _ _ _ Hd]
  simp_rw [scalarDatum_one]; change ((2).factorial:ℝ)⁻¹ • iteratedDeriv 2 (fun t:ℝ=>legK i (tensorJet h (positiveLinks (t•expand G N c)) o 0)) 0 = _
  let f := fun t:ℝ=>tensorJet h (positiveLinks (t•expand G N c)) o 0
  have he := precise_line h o i c
  rw [iterated_clm (legK (G:=G) i) 0 he]; change _ • (legK i (iteratedDeriv 2 f 0)) = _; refine (congrArg (fun u : Labels.Taylor G 0 => (((2).factorial:ℝ)⁻¹) •(legK i u)) (tensor_quadratic _ _ _)).trans ?_ ; norm_num [completion, map_smul, Nat.factorial, one_div]
end YM.Pert.First

import YM.RG11Scheme.Stencil.Detector

/-! Binding the full *finite-regulator formal* curvature jets on every derivative order to native cover slots. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 4500
set_option synthInstance.maxHeartbeats 32000
namespace YM.RG11Scheme.Stencil.Cell
open Function Set Filter Maxwell Lattice Mesh Pert Orb Pert.First Labels Spark Bare
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G:Gauge} {X:Type} [AddCommGroup X] [One X] {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {N:Side} {j:ℕ}
local notation "Δ" => Spark.tensor X G
local notation "Σ!" => (Fintype.card Signed)
-- all components in links are finite-coordinate functions
variable (f:E→ Lattice.Links X G.El) (hf:∀ l, ContDiff ℝ ω (fun z:E=>G.mat (f z l)))
include hf
lemma rule_pull (s:Signed) (l) : ContDiff ℝ ω (fun z:E=> G.mat (pull s 0 (f z) l)) := by
   unfold pull Step.read; split
   · exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp (hf _)
   exact hf _
lemma rule_trip (τ:Walk)(x:Four X) : ContDiff ℝ ω (fun z:E=>G.mat (travel (f z) x τ)) := by
   induction τ generalizing x with
   | nil => exact contDiff_const
   | cons t τ ih => simp only [travel,G.mat_mul]; apply ContDiff.mul _ (ih _); unfold Step.read; split
                    exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp (hf _)
                    exact hf _
lemma rule_plate (x:Four X)(τ:Walk)(i k) : ContDiff ℝ ω (fun z:E=> plateU (f z) x τ i k) := by
   simp_rw [plateU, ← G.curvature_conjugate]
   apply curve_diff; simp only [G.mat_mul]
   exact ((rule_trip f hf τ x).mul (rule_trip f hf _ _)).mul ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp (rule_trip f hf τ x))
lemma rule_diff (x:Four X)(j) : ContDiff ℝ ω (fun z:E=> diffU j (f z) x) := contDiff_pi.mpr (fun i=>contDiff_pi.mpr (fun k=> contDiff_pi.mpr (fun _=> (ContDiff.sum (fun s _=> (rule_plate f hf x _ i k).const_smul (Bare.sign s))).const_smul (F:=G.Color) (((j.factorial):ℝ)⁻¹))))
lemma rule_oval (s:Signed) (x:Four X)(j) (h:ℝ) : ContDiff ℝ ω (fun z:E=> oval s h (f z) x j) := by
   let d (z:E):= diffU j (pull s 0 (f z)) (affine s⁻¹ 0 x)
   have hd := rule_diff (fun z:E=>pull s 0 (f z)) (rule_pull f hf s) (affine s⁻¹ 0 x) j
   rw [show (fun z:E=> oval s h (f z) x j)=(outside h s j) ∘ d from funext fun z=>rfl]
   let K := (outside (G:=G) h s j).toContinuousLinearMap
   exact (ContinuousLinearMap.contDiff (F:=Labels.Taylor G j) (n:=ω) (𝕜:=ℝ) (E:=Response G j) K).comp (f:=d) (g:=K) hd
lemma rule_spot (x:Four X) (j) (h:ℝ) : ContDiff ℝ ω (fun z:E=> tensorJet h (f z) x j) := ContDiff.const_smul (𝕜:=ℝ) (E:=E) (F:=Labels.Taylor G j) ((Σ!:ℝ)⁻¹) (ContDiff.sum (fun s _=> rule_oval f hf s x j h))
omit hf
omit [AddCommGroup X] [One X] in
lemma rule_ride (A:Δ)(l) : ContDiff ℝ ω (fun r:ℝ => G.mat (ride (r • A) l)) := G.exp_jet.comp (show ContDiff ℝ ω (fun r:ℝ=>r • A l) from contDiff_id.smul contDiff_const)
abbrev hrank (i: Axis)(k:Axis)(γ : Fin j→Axis) : Response G j →ₗ[ℝ] G.Color := LinearMap.proj γ ∘ₗ LinearMap.proj k ∘ₗ LinearMap.proj i
lemma counted (A:Δ)(x:Four X) (j) : iteratedDeriv 2 (fun t:ℝ=> diffU j (Spark.ride (t • A)) x) 0= expander j x A A := by
   funext i k γ; let v:= fun t:ℝ=> Spark.ride (t • A)
   let r s (t:ℝ):= Bare.sign s • Bare.plateU (v t) x (Bare.walk γ s) i k
   have hs := rule_diff _ (rule_ride A) x j
   have hr (s) : ContDiffAt ℝ (2:ℕ) (r s) 0 := ((rule_plate v (rule_ride A) x _ _ _).contDiffAt.const_smul (E:=ℝ) (F:=G.Color) (Bare.sign s)).of_le le_top
   rw [active]
   change hrank i k γ (iteratedDeriv 2 (fun t:ℝ=>diffU j (v t) x) 0)=_
   rw [← iterated_linear (E:=Response G j) (hrank i k γ) (f:=fun t:ℝ=>diffU j (v t) x) 0 (hs.of_le le_top)]
   dsimp only [hrank,LinearMap.comp_apply,LinearMap.proj_apply,diffU]; erw [iteratedDeriv_fun_const_smul_field]; rw [iteratedDeriv_fun_sum (f:=r) (fun s _=>hr s)]
   congr 1; apply Finset.sum_congr rfl; intro s _; unfold r v; erw [iteratedDeriv_fun_const_smul_field]; rw [twin_second]
lemma first_counted (A:Δ)(x:Four X)(j) : iteratedDeriv 1 (fun t:ℝ=> diffU j (Spark.ride (t • A)) x) 0= wideCore G j x A := by
   funext i k γ; let v:=fun t:ℝ=>Spark.ride (t • A)
   let r s (t:ℝ):= Bare.sign s • Bare.plateU (v t) x (Bare.walk γ s) i k
   have hs := rule_diff _ (rule_ride A) x j
   have hr (s) : ContDiffAt ℝ (1:ℕ) (r s) 0 := ((rule_plate v (rule_ride A) x _ _ _).contDiffAt.const_smul (E:=ℝ) (F:=G.Color) (Bare.sign s)).of_le le_top
   rw [shear]; change hrank i k γ (iteratedDeriv 1 (fun t:ℝ=>diffU j (v t) x) 0)=_
   rw [← iterated_linear (E:=Response G j) (hrank i k γ) (f:=fun t:ℝ=>diffU j (v t) x) 0 (hs.of_le le_top)]
   dsimp only [hrank,LinearMap.comp_apply,LinearMap.proj_apply,diffU]; erw [iteratedDeriv_fun_const_smul_field]; rw [iteratedDeriv_fun_sum (f:=r) (fun s _=>hr s)]
   congr 1;apply Finset.sum_congr rfl;intro s _; unfold r v; erw [iteratedDeriv_fun_const_smul_field]; rw [iteratedDeriv_one,twin_first]

lemma rotated_path (A:Δ)(t:ℝ)(s:Signed) : pull s 0 (Spark.ride (t • A))=Spark.ride (t • wideLink G s A) := by
   funext l; rw [pull, signed_read]; unfold Spark.ride
   cases e : ((posDir l.2).rotate s).neg <;> simp [wideLink,Spark.went,Spark.take,e]
lemma track (s:Signed)(A:Δ)(x:Four X)(j)(h:ℝ) : (fun t:ℝ=> oval s h (Spark.ride (t • A)) x j)= (fun t:ℝ=> outside h s j (diffU j (Spark.ride (t • wideLink G s A)) (affine s⁻¹ 0 x))) := funext (fun t=>by rw [oval,rotated_path]; exact rfl)
private lemma curve_agg {d:ℕ}{f:Signed→ℝ→E}(J:ℝ)(hf:∀ i,ContDiffAt ℝ (d:ℕ) (f i) 0)(g:Signed→E)(he:∀ i,iteratedDeriv d (f i) 0=g i) : iteratedDeriv d (fun t=>J • ∑ s:Signed, f s t) 0= J • ∑ s:Signed,g s :=
   (iteratedDeriv_fun_const_smul_field (F:=E) (𝕝:=ℝ) (𝕜:=ℝ) (x:=0) (n:=d) J (fun t:ℝ=>∑ s:Signed,f s t)).trans (congrArg (fun x:E => J • x) ((iteratedDeriv_fun_sum (F:=E) (I:=Finset.univ) (n:=d) (x:=0) (fun s _ => hf s)).trans (Finset.sum_congr rfl (fun s _=> he s))))
lemma raw_squares (h:ℝ)(v:Four X)(A:Δ) (j): iteratedDeriv 2 (fun t:ℝ=> tensorJet h (Spark.ride (t • A)) v j) 0= full2 h v j A A := by
   let f (s:Signed):= fun t:ℝ=> oval s h (Spark.ride (t • A)) v j
   have hf (s : Signed) : ContDiffAt ℝ (2:ℕ) (f s) 0 := (rule_oval _ (rule_ride A) s v j h).contDiffAt.of_le le_top
   have he (s : Signed) : iteratedDeriv 2 (f s) 0= (outside h s j) (expander j (affine s⁻¹ 0 v) (wideLink G s A) (wideLink G s A)):= by
     unfold f
     rw [track]
     let l:=affine s⁻¹ 0 v
     let B:=wideLink G s A
     let g t:=diffU j (Spark.ride ((t:ℝ) • B)) l
     have hg : ContDiff ℝ ∞ g := (rule_diff _ (rule_ride B) l j).of_le le_top
     have hk := First.iterated_linear (D:=Labels.Taylor G j) (E:=Response G j) (outside (G:=G) h s j) (d:=2) (f:=g) 0 hg
     apply Eq.trans hk
     refine congrArg _ ?_
     exact counted B l j
   rw [rung]
   unfold tensorJet
   have hk := curve_agg (E:=Labels.Taylor G j) (d:=2) (f:=f) ((Fintype.card Signed:ℝ)⁻¹) hf _ he
   dsimp only [f] at hk
   set_option pp.instances true in with_reducible exact hk
lemma raw_one (h:ℝ)(v:Four X)(A:Δ) (j): iteratedDeriv 1 (fun t:ℝ=> tensorJet h (Spark.ride (t • A)) v j) 0= wideLinear G j h v A := by
   let f (s:Signed):= fun t:ℝ=> oval s h (Spark.ride (t • A)) v j
   have hf (s : Signed) : ContDiffAt ℝ (1:ℕ) (f s) 0 := (rule_oval _ (rule_ride A) s v j h).contDiffAt.of_le le_top
   have he (s : Signed) : iteratedDeriv 1 (f s) 0= (outside h s j) (wideCore G j (affine s⁻¹ 0 v) (wideLink G s A)):= by
     unfold f
     rw [track]
     let l:=affine s⁻¹ 0 v
     let B:=wideLink G s A
     let g t:=diffU j (Spark.ride ((t:ℝ) • B)) l
     have hg : ContDiff ℝ ∞ g := (rule_diff _ (rule_ride B) l j).of_le le_top
     have hk := First.iterated_linear (D:=Labels.Taylor G j) (E:=Response G j) (outside (G:=G) h s j) (d:=1) (f:=g) 0 hg
     apply Eq.trans hk
     refine congrArg _ ?_
     exact first_counted B l j
   rw [sided]
   unfold tensorJet
   have hk := curve_agg (E:=Labels.Taylor G j) (d:=1) (f:=f) ((Fintype.card Signed:ℝ)⁻¹) hf _ he
   dsimp only [f] at hk
   set_option pp.instances true in with_reducible exact hk

lemma scale_detail (i:Key G)(h:ℝ)(x:Site N) : ContDiff ℝ ∞ (datum h x i) := by
    let L := Complex.ofRealCLM ∘L ((axes G i.1).coord i.2).toContinuousLinearMap
    exact L.contDiff.comp ((rule_spot (positiveLinks (G:=G)) (pos_mDiff (G:=G)) x i.1 h).of_le le_top)
lemma coefficients (i:Key G)(h:ℝ)(x:Site N) (v:Coords G N) : PowerSeries.coeff 1 (seriesLex h x v i) = (((1/2:ℝ) • (axes G i.1).coord i.2 (full2 h x i.1 (expand G N v).val (expand G N v).val) : ℝ):ℂ) := by
    let A := (expand G N v).val
    unfold seriesLex; rw [PowerSeries.coeff_mk, First.lineJet _ _ _ (scale_detail i h x)]
    let L := Complex.ofRealCLM ∘L ((axes G i.1).coord i.2).toContinuousLinearMap
    let f := fun t:ℝ=> tensorJet h (Spark.ride (t • A)) x i.1
    have e := iterated_clm (d:=2) (E:=Labels.Taylor G i.1) (D:=ℂ) L (f:=f) (0:ℝ) ((rule_spot _ (rule_ride A) x i.1 h).of_le le_top)
    change ((2:ℕ).factorial:ℝ)⁻¹ • iteratedDeriv 2 (fun t=>L (f t)) 0 = _
    rw [e]; unfold f; rw [raw_squares]
    norm_num [Nat.factorial, A, L, one_div, smul_eq_mul,Complex.real_smul]
end YM.RG11Scheme.Stencil.Cell

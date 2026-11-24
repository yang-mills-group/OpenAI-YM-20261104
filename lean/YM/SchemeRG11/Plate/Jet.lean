import YM.SchemeRG11.Plate.Arc
/-! All slots finite. -/
set_option maxRecDepth 8000
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Bark
open Lattice Function Filter Asymptotics Haze Pert Bare
open scoped Classical ContDiff Matrix.Norms.Frobenius
variable {L : Type*} [AddCommGroup L] [One L] {G : Gauge}
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U : E→Links L G.El} (hU : ∀ e, ContDiff ℝ ω (fun v:E=> G.mat (U v e)))
include hU
lemma travelC (x: Four L)(s:Walk): ContDiff ℝ ω (fun p=>G.mat (travel (U p) x s)):=by
 induction s generalizing x with
 | nil=> exact contDiff_const
 | cons d s ih=>
    simp only [travel,Step.read,G.mat_mul]; split
    · simp_rw [G.mat_inv]; exact ((starL ℝ).contDiff.comp (f:=fun v:E=> G.mat (U v _)) (hU _)).mul (ih _)
    exact (hU _).mul (ih _)
lemma diffC (x : Four L)(j:ℕ): ContDiff ℝ ω (fun p=>diffU j (U p) x):=by
 apply contDiff_pi.mpr; intro i; apply contDiff_pi.mpr; intro k; apply contDiff_pi.mpr; intro r
 simp_rw [diffU,turn_path]; exact ContDiff.const_smul (𝕜:=ℝ) _ (ContDiff.sum (s:=Finset.univ) fun s _=> ContDiff.const_smul (𝕜:=ℝ) _ (Bare.curve_diff (f:=fun p=>travel (U p) x _) (travelC hU x (turn _ _ _))))
lemma rawC (v:ℝ)(x:Four L)(j:ℕ): ContDiff ℝ ω (fun p=>rawJet v (U p) x j):= by
 unfold rawJet; let R:Response G j→L[ℝ] Labels.Taylor G j:= radialMap.toContinuousLinearMap
 exact ContDiff.const_smul (𝕜:=ℝ) (E:=E) (F:=Labels.Taylor G j) _ ((ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Response G j) (F:=Labels.Taylor G j) R).comp (g:=(R:Response G j→_)) (f:=fun p=> diffU j (U p) x) (diffC hU x j))
lemma pivotC (q:Signed)(v:ℝ)(x:Four L)(j:ℕ): ContDiff ℝ ω (fun p=> oval q v (U p) x j):=by
 let S:Labels.Taylor G j →L[ℝ] Labels.Taylor G j:=(Labels.Taylor.turn q.ortho).toContinuousLinearMap
 refine ContDiff.comp (g:=(S:Labels.Taylor G j→_)) (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Labels.Taylor G j) (F:=Labels.Taylor G j) S) (f:=fun p=> rawJet v (pull q 0 (U p)) (affine q⁻¹ 0 x) j) (rawC (U:=fun p=>pull q 0 (U p)) ?_ _ _ _)
 intro e; unfold pull Step.read; split
 · simp_rw [G.mat_inv]; exact (starL ℝ).contDiff.comp (f:=fun v:E=> G.mat (U v _)) (hU _)
 exact hU _
lemma tensorC (v : ℝ)(x:Four L)(j:ℕ): ContDiff ℝ ω (fun p=>tensorJet v (U p) x j):=by
 unfold tensorJet; exact ContDiff.const_smul (𝕜:=ℝ) (E:=E) (F:=Labels.Taylor G j) _ (ContDiff.sum (s:=Finset.univ) (fun s _=> pivotC hU s v x j))
end
omit [AddCommGroup L] [One L] in
lemma rollsC (A:trunk G L) (e : Edge (Four L)): ContDiff ℝ ω (fun p:ℝ=>G.mat (unroll A p e)):=by apply G.exp_jet.comp (f:=fun p:ℝ => p • A e); exact contDiff_id.smul contDiff_const
lemma steering (s : Signed)(A:trunk G L)(u:ℝ): unroll (wideLink G s A) u = pull s 0 (unroll A u):=by
 funext e; unfold pull Step.read unroll; rw [wideLink_apply]
 split
 · simp [smul_neg, ←Work.F03.exp_neg_color,affine]
 simp [affine]
lemma operations (s:Signed)(e:Four L→G.Color)(A:trunk G L) :
    wideLink G s (ascent e)=ascent (fun x=>e (affine s 0 x)) ∧ wideLink G s (spur e A)=spur (fun x=>e (affine s 0 x)) (wideLink G s A):=by
 have he (l:Edge (Four L)) : affine s 0 (l.1+step l.2)=(affine s 0 l.1)+((posDir l.2).rotate s).vec:=by simp [affine, Step.vec_rotate]
 constructor
 · funext a
   have hw:=heel_up (affine s 0 a.1) ((posDir a.2).rotate s) e
   change wideLink G s (ascent e) a = e (affine s 0 (a.1+step a.2))-e (affine s 0 a.1) -- abbrev
   rw [he,←hw]; unfold heel; rw [wideLink_apply]; split <;> simp [affine]
 funext a; change wideLink G s (spur e A) a = G.ad (wideLink G s A a) (e (affine s 0 (a.1+step a.2))+e (affine s 0 a.1))
 rw [he, show wideLink G s A a=heel ((posDir a.2).rotate s) (affine s 0 a.1) A from by rw [wideLink_apply]; unfold heel; split <;> simp [affine],← heel_stamp,wideLink_apply]; unfold heel; split <;> simp [affine]

abbrev angle (t : Bool)(x:Four L)(w:Walk)(A B:trunk G L): G.Color:= if t then cohort x w A B else mileage x w A
variable (t : Bool)(h:ℝ)(x:Four L) (j:ℕ)
def part(A B:trunk G L) : Response G j:=fun i k γ=> (j.factorial:ℝ)⁻¹ • ∑ s, sign s • angle t x (turn (walk γ s) i k) A B
def style(s:Signed)(A B:trunk G L): Labels.Taylor G j:= Labels.Taylor.turn s.ortho (h^(-(j+2:ℤ)) • radialMap (part t (affine s⁻¹ 0 x) j (wideLink G s A) (wideLink G s B)))
def starJet (A B:trunk G L): Labels.Taylor G j:= (Fintype.card Signed:ℝ)⁻¹ • ∑ s,style t h x j s A B
abbrev point (t:Bool):ℕ:=if t then 2 else 1
lemma detent (A:trunk G L): iteratedDeriv (point t) (fun r:ℝ=> diffU j (unroll A r) x) 0=part t x j A A:=by
 let F(r:ℝ):=diffU j (unroll A r) x
 let f (i k:Axis)(γ: Fin j→Axis):Response G j→ₗ[ℝ] G.Color := LinearMap.proj γ ∘ₗ LinearMap.proj k ∘ₗ LinearMap.proj i
 funext i k γ; change f i k γ (iteratedDeriv _ F 0)=_
 rw [← First.iterated_linear (E:=Response G j) (f i k γ) 0 ((diffC (rollsC A) x j).of_le le_top)]
 let W(s: Finset (Fin j)):=turn (walk γ s) i k
 let K(s:Finset (Fin j))(r:ℝ):=sign s • G.curvature (travel (unroll A r) x (W s))
 dsimp only [f, LinearMap.comp_apply, LinearMap.proj_apply,F,part,diffU]; simp_rw [turn_path]; erw [iteratedDeriv_fun_const_smul_field]; rw [iteratedDeriv_fun_sum (f:=K) (fun i _=> ?_)]
 · congr 1; apply Finset.sum_congr rfl; intro s _
   dsimp [K]; erw [iteratedDeriv_fun_const_smul_field]; cases t
   · exact congrArg _ (log_arc x (W s) A).1
   exact congrArg _ (log_arc x (W s) A).2
 exact (ContDiff.const_smul (𝕜:=ℝ) (E:=ℝ) (F:=G.Color) _ (Bare.curve_diff (f:=fun r=> travel (unroll A r) x (W i)) (travelC (rollsC A) x (W i)))).contDiffAt.of_le le_top
lemma stakes (A:trunk G L) (s:Signed): iteratedDeriv (point t) (fun r:ℝ=> oval s h (unroll A r) x j) 0=style t h x j s A A:=by
 let V:=wideLink G s A;let u:=affine s⁻¹ 0 x; simp_rw [style,oval,← steering]
 change iteratedDeriv _ (fun r=>Labels.Taylor.turn s.ortho (rawJet h (unroll V r) u j)) 0=_
 rw [First.iterated_linear (E:=Labels.Taylor G j) (D:=Labels.Taylor G j) (Labels.Taylor.turn s.ortho) (0:ℝ) ((rawC (rollsC V) h u j).of_le le_top)]
 apply congrArg; unfold rawJet; erw [iteratedDeriv_fun_const_smul_field]; rw [First.iterated_linear (E:=Response G j) (D:=Labels.Taylor G j) (radialMap (j:=j)) 0 ((diffC (rollsC V) u j).of_le le_top),detent]
lemma accord (A:trunk G L): iteratedDeriv (point t) (fun r=> tensorJet h (unroll A r) x j) 0=starJet t h x j A A:=by
 unfold tensorJet starJet; erw [iteratedDeriv_fun_const_smul_field]; rw [iteratedDeriv_fun_sum (f:=fun s r=>oval s h (unroll A r) x j) (fun s _=>(pivotC (rollsC A) s h x j).contDiffAt.of_le le_top)]; simp_rw [stakes]
end YM.SchemeRG11.Bark

import YM.Contacts.Loom.Chasm
/-! # Direct stationary cleavage and qualification using radar. Canon kin.
 F can be chosen arbitrarily here; for Sight choose planted.
 At each large finite period separately. -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree
open Exterior Push.Uniform Milling ConnectedActivityE6 Blaze Shield Poll Lapis
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{P : ChartRatio G} {Λ σ C v b:ℝ}{n k:ℕ}
abbrev Anchor (G:Gauge)(c:Side):= Positions (Push.Uniform.Primary c G)
abbrev Truck (G:Gauge) (F:Forest S.ratio):= Poll.Body (Key F G)
section quadratic
variable {E V : Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup V][NormedSpace ℝ V]
    {p:E×V→ℝ}{u:E→V}
def levelL (L:E→L[ℝ] V) : E×V→L[ℝ]E×V:= let X:=ContinuousLinearMap.fst ℝ E V; X.prod (L.comp X + ContinuousLinearMap.snd ℝ E V)
def camber (p:E×V→ℝ)(L:E→L[ℝ] V)(x:E) := jet p 2 (x,L x)
lemma behold (L:E→L[ℝ] V)  {X:E} {Y:V}: levelL L (X,Y)=(X,L X + Y):=rfl
lemma bend_bank (hp:AnalyticAt ℝ p 0)(hu:u 0=0)(h:DifferentiableAt ℝ u 0)(he:∀ᶠ x in 𝓝 0,∀ y:V, fderiv ℝ p (x,u x) (0,y)=0)(x:E)(y:V): let L:=fderiv ℝ u 0; let T:=p∘ levelL L; jet T 2 (x,y)=camber p L x + Lantern.scratch (0,y) p 0 /2:= by
   let L:= fderiv ℝ u 0; let f:=fderiv ℝ p; let F:=fderiv ℝ f 0; let w:E×V:=(x,L x); let v:E×V:=(0,y); let g(z:E):=(z,u z); have hz:g 0=0:= by simp [g,hu]
   have hd:= (hasFDerivAt_id (E:=E) (𝕜:=ℝ) 0).prodMk h.hasFDerivAt; have hF : DifferentiableAt ℝ f 0:= (hp.contDiffAt.fderiv_right (m:=1) (by exact le_top)).differentiableAt (by decide)
   let H:= ContinuousLinearMap.apply ℝ ℝ v; have ha : HasFDerivAt (f ∘ g) (F.comp ((ContinuousLinearMap.id ℝ E).prod L)) 0:= (HasFDerivAt.comp _ (hz.symm ▸ hF.hasFDerivAt) hd); have hA:= H.hasFDerivAt.comp _ ha
   have hv : F w v=0 := congr_arg (fun d:E→L[ℝ] ℝ=> d x) ((hA.congr_of_eventuallyEq (f₁:=fun _=>0) (he.mono fun x hx=> (hx y).symm)).unique (hasFDerivAt_const ..)); have hh : F v w=0 := (hp.contDiffAt.isSymmSndFDerivAt_of_omega v w).trans hv;
   intro L' T; have he z: jet p 2 z= F z z/2:= by unfold jet; rw [iteratedFDeriv_two_apply]; norm_num [Nat.factorial]; ring -- z F not unfolded
   rw [show jet T 2 (x,y)=jet p 2 (levelL L (x,y)) from Garf.woven hp (levelL L) _ _, show levelL L (x,y)=w+v from Prod.ext (add_zero _).symm rfl, he]; unfold camber; rw [he]; unfold Lantern.scratch; change _= F w w/2+ F v v/2; simp_rw [map_add,_root_.add_apply,hv,hh]; ring
end quadratic
variable (F:Forest S.ratio)(T: Tube G S)(j:S.Choices) {ρ:Bid.Dir G c → AxisChart G F}
local notation "Y" => Truck G F
local notation "E" => Anchor G c
def gram (A:Matrix (Key F G) (Key F G) ℝ)(x:Y):= dotProduct (WithLp.ofLp x) (A *ᵥ WithLp.ofLp x) /2
local notation "p" => (Lapis.table F j T.up T.high)
def seam (ρ:Bid.Dir G c → AxisChart G F): E→L[ℝ] Y := fderiv ℝ (orbit F ρ) 0
variable {A:Push.Uniform.Before G σ C S.patch.J S.kernel (n+3)} (h:A.Service F T.high T.up ρ)(hp:T.up.Bounds T.high σ C Λ)(hg:Larger (G:=G) S)
include hp hg
lemma kernelCost : AnalyticAt ℝ p 0 ∧ Radial.Stationary p := by
   let Z:= (combineH (G:=G) F); let U:= priced F j T.high T.up; let k:= uncurry (tested F j T.high T.up); obtain ⟨hU,hp₀,hf,-⟩:=Push.Uniform.price_identity F j hp hg.1; let L : E × Y →L[ℝ] _ := (paint F G).toContinuousLinearMap.comp Z.toContinuousLinearMap -- paint?
   have hK : p=k ∘ L:=rfl; have he : AnalyticAt ℝ p 0:=by rw [hK]; exact Milling.Forge.starts _ hU.analyticAt L
   refine ⟨he, he.contDiffAt,?_,?_⟩; · rw [hK, Function.comp_apply,map_zero]; exact hp₀
   intro x; rw [hK,Milling.Garf.woven hU.analyticAt]; unfold jet; rw [iteratedFDeriv_one_apply,hf]; simp
include h
lemma cleavage (x:E)(y:Y): let q:=Lapis.gram F T.up T.high ρ j 0; let t:=seam F ρ; jet (p ∘ levelL t) 2 (x,y)= camber p t x + gram F q y:= by
   intro q t; have hz:= Lapis.zeroO F T.up T.high ρ σ C A h -- likely args order
   let d:=(A.tables T.high S.patch); let u:=Lapis.orbit F ρ; have ht:0<d.horizon:= h.x_pos; have he:= Lapis.luminous F j T.up T.high ρ σ C Λ A hg hp h (1+ Fintype.card (Joint F G)) (le_add_of_nonneg_right (Nat.cast_nonneg _)) (le_add_of_nonneg_left zero_le_one) _ (show (0:E)∈ ball 0 d.horizon from mem_ball_self ht);
   have hy:∀ᶠ x in 𝓝 (0:E), ‖x‖ < d.horizon:= Metric.mem_nhds_iff.mpr ⟨_,ht,fun _ hx=> mem_ball_zero_iff.mp hx⟩; refine Eq.trans (bend_bank (kernelCost F T j hp hg).1 hz (he.smooth.differentiableAt (by norm_cast)) (hy.mono fun x hx y=> Lapis.heart F j T.up T.high ρ _ _ _ A hg hp h x hx y) x y) ?_; unfold gram; have ht:= (Lapis.wakes F j T.up T.high ρ _ _ _ A hg hp h 0 (by rw [norm_zero]; exact ht)).2.2.2 y; rw [hz] at ht; erw [← ht]; rfl
section metrology
variable {ι:Type}[Fintype ι][DecidableEq ι]
omit h hp hg
def law (A: Matrix ι ι ℝ):= (Shield.lens₀ A⁻¹ 0)⁻¹
lemma lens (A : Matrix (Key F G) (Key F G) ℝ)(h:A.PosDef)(x:Y) : Real.exp (- gram F A x)= law A * lens₀ A⁻¹ x := by -- ambiguity
    unfold gram; let k:= Shield.lens₀ A⁻¹; change _=(k 0)⁻¹*k x; have hk :0<k 0:= Shield.fullFuel _ _; apply mul_left_cancel₀ hk.ne'; rw [←mul_assoc,mul_inv_cancel₀ hk.ne',one_mul]; unfold k Shield.lens₀; rw [mul_assoc,← Real.exp_add,Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr h.det_pos.ne')]; apply congr_arg; apply congr_arg; simp; ring -- pow add
include h hp hg
omit h hp hg
private lemma jet_y0 {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V](F:V→ℝ): jet F 2 0=0:= by simpa using jet_smul F 2 0 0
lemma pillow {J V:Type}[NormedAddCommGroup V][NormedSpace ℝ V] [NormedAddCommGroup J][NormedSpace ℝ J][FiniteDimensional ℝ V][FiniteDimensional ℝ J] {F:J×V→ℝ}{u:J→ℝ}{Q:V→ℝ}(h:AnalyticAt ℝ F 0)(hu:u 0=0)(hv: ∀ x:V,x≠0 →0< Q x)(he:∀ x y,jet F 2 (x,y)=u x + Q y)(R:ℝ): ∃ c>(0:ℝ),∃ C,Hilly F (c+c) R C:= by
   let f:= F ∘ ContinuousLinearMap.inr ℝ J V; let g:= F ∘ ContinuousLinearMap.inl ℝ J V;
   have ht y: jet f 2 y= Q y := by rw [show jet f 2 y=_ from Milling.Garf.woven h (ContinuousLinearMap.inr ℝ J V) y 2]; change jet _ _ (0,y)=_; rw [he, hu,zero_add]
   obtain ⟨b,hb,H⟩:= Radial.quadratic_min f (fun y hy=> (ht y).symm ▸ hv y hy); have hw x:jet g 2 x=u x:= by rw [show jet g 2 x=_ from Milling.Garf.woven h (ContinuousLinearMap.inl ℝ J V) x 2]; change jet F 2 (x,0)=_; rw [he,← ht,jet_y0,add_zero]
   obtain ⟨K,hK⟩: BddBelow ((jet g 2) '' closedBall (0:J) R):= ((isCompact_closedBall _ _).image (continuous_iff_continuousAt.mpr (fun i=> (Ion.jet_ana _ _ i).continuousAt))).bddBelow; refine ⟨b/2, half_pos hb,b*R^2-K,fun x h y=>?_⟩; rw [he, ← hw,← ht]; have hv:= mem_closedBall_zero_iff.mp h; have ha:= hK ⟨x,h,rfl⟩; change K≤ jet g 2 x at ha
   rcases le_total ‖x‖ ‖y‖ with he|he; · rw [Prod.norm_def,max_eq_right he]; nlinarith only [ha,H y,mul_nonneg hb.le (sq_nonneg R)]
   rw [Prod.norm_def,max_eq_left he]; nlinarith only [mul_nonneg hb.le (sq_nonneg ‖y‖),mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv 2) hb.le,ha,H y]
lemma gram_pos (A: Matrix (Key F G) (Key F G) ℝ)(h:A.PosDef)(y:Y)(hy:y≠0): 0<gram F A y:= by
   have he : WithLp.ofLp y ≠0 := (weld (Key F G)).map_ne_zero_iff.mpr hy; apply div_pos (show 0 < _ from ?_) zero_lt_two; have ht:= h.dotProduct_mulVec_pos he; rwa [star_trivial] at ht
lemma cam_zero (L:E→L[ℝ] Y): camber p L 0=0:= by unfold camber; rw [map_zero]; exact jet_y0 _
end metrology
end YM.Contacts.Junction

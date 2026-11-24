import YM.WilsonCoeffUV.Emit.NoiseLaw
import YM.WilsonCoeffUV.Emit.Expense
/-!
# Fk/A port (unmarked; one real test included to pin denominators)

Read on all ordinary tori at patch P. Value `Φ` for coarse passed-density
means the **log-coordinate formal** density against *group* probability Haar,
still EXCLUDING a possible extensive vacuum-power prefactor and the
unperturbed, g-independent precision exp(-orbC(B)). The prefactor has the
powers of g from BOTH the fine-axis Jacobian and ζ-link Jacobian, and
contiguous determinants; never call `actionW` or iterate ANY gates as a
bound on that. We keep the conditional measure of fine variables at fixed B
only inside the step; two denominator sorts, with this ratio and the prior
invariants as here. Log taken AFTER tag-sum, necessary even when tags
symbolically collapse at the zero-background germ. The back map goes from
the coarse-reset coupling variable.

This port describes equations BEFORE doing output-to-link-density conversions,
not the E→A real theorem. Use `Bank.story` with `season` and these same
coefficients and kernels, then `VacuumUV`. Do not plug the running REAL g or
use this as an approximate push proof.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Fk
open Filter Function Matrix MeasureTheory Set Lattice FreeResolvent Metric RG Wilson Tree Precision
open Bank Bank.Bloom Blue Power PowerSeries
open scoped BigOperators Topology ContDiff
variable {G:Gauge}{A:Levels G}{m N:ℕ}{Ñ:ChartRatio G}

section convention
open Gauge
lemma top_exact (A:Levels G)(n:Side)(Ñ:ChartRatio G)(N : ℕ) :
    (PowerSeries.X :Ink (Woods G n))^2* flash ((story A Ñ N N).1 n) = Blue.jet (fun v:TreeVars G n=> Wilson.energy (mantle v)) := by
  rw [story_top]
  have h : ∀ i:ℕ, sprig (eWilson (G:=G) (c:=n)) 2 i 0=0 := fun i=> shine_dark (by omega)
  have hz:(tale G).1 n=sprig (eWilson (G:=G)) 2:=by
    change lop (sprig (eWilson (G:=G) (c:=n)) 2)=_
    ext1 i; ext1 r; by_cases H:r=0; · subst r; exact (h i).symm
    rw [lop,if_neg H]
  rw [hz]
  have hp:= w_jets (drawTop A n N) (G:=G)
  exact sprouts_move hp.1 hp.2.1

section
variable {n f:Side}
private lemma raiseUnit (x : PowerSeries ℝ)(hp:constantCoeff x=1)(n:ℕ): raiseE (n • logOf x)=x^n := by
  induction n with
  | zero=> rw [zero_smul,pow_zero,raise_still]
  | succ k h=> rw [add_smul,one_smul, raise_add (by rw [map_nsmul,constantCoeff_logOf hp]; simp) (constantCoeff_logOf hp), h, raising_log hp,pow_succ]

/-- Denote Φ. Equals unmarked push after removing the g^0 coarse quadratic and
scale-dependent scalar constants; we have NOT yet dropped scalar coefficients
at positive g-orders. `plugζ` comes only from kernel side. -/
def residualUnmarked (H:FaceRow)(P:PChart G n) : Ink (Woods G n) :=
  raiseE (orbC (precisionC G n H)-flash P)

lemma log_output (S:StepData n f)(K Y:FaceRow)(F:Forest S.ratio)(P:PChart G f) (Q:Matrix (Exterior.Body 1 f) (Exterior.Body 1 n) ℝ)(h:LocalRatio Ñ)(e:Interlace K P)(p:S.patch.Branches S.kernel G)(u:(K.acts f).transpose=K.acts f):
    residualUnmarked Y (winter S F K Y Q Ñ P) * (soil (ζ Ñ S.kernel.penalty))^(Fintype.card (Edge (Site n))) = inside S F K Q Ñ P:=by
   rw [residualUnmarked,winter_read S F K Y Q e.lamp h p u e.shape]
   let X:=orbC (precisionC G n Y); let Z:= plugζ S Ñ; let U:=inside S F K Q Ñ P
   let d:=Fintype.card (Edge (Site n))
   have hf: raiseE (soil (U:=Woods G n) Z) =(soil (U:=Woods G n) (ζ Ñ S.kernel.penalty))^d:=by
       have he: constantCoeff Z=0:=by unfold Z plugζ; rw [map_nsmul,constantCoeff_logOf (ζ_one _ h),smul_zero]
       rw [← raise_map _ (by simp [soil]) he, show raiseE Z=ζ Ñ S.kernel.penalty^d from raiseUnit _ (ζ_one _ h) d, map_pow]
   have hZ:constantCoeff (soil (U:=Woods G n) Z)=0:=by
       unfold Z plugζ; rw [← coeff_zero_eq_constantCoeff,soil, coeff_map,coeff_zero_eq_constantCoeff_apply,map_nsmul,constantCoeff_logOf (ζ_one _ h),smul_zero,map_zero]
   have hu : constantCoeff U=1:= inside_mass S F K Q h
   change raiseE (X-(X-logOf U+soil Z)) * _= U
   rw [← hf, show X-(X-logOf U+soil Z)=logOf U-soil Z from by ring, ← raise_add _ hZ,sub_add_cancel,raising_log hu]
   rw [map_sub,hZ,constantCoeff_logOf hu]; simp

end

structure ThermalLaw (A:Levels G)(Ñ:ChartRatio G) (N m:ℕ) (n : Side): Prop where
   pinned : m<N
   prescription :
     let L:= loose A m
     let K:= freeForms A N (m+1)
     let Y:= freeForms A N m
     let S:= mStep A n m
     let F:= repeatF S
     let J := A.clock.kernel
     let R: PChart G (n*L.L):= (story A Ñ N (m+1)).1 (n*L.L)
     let Q:= roam A N m n
     let D:= unripe A Ñ N m (story A Ñ N (m+1)).1 n
     -- log height count and W_n on ALL DOF, then precision
     Interlace K R ∧
       (D=winter S F K Y Q Ñ R)∧
       (story A Ñ N m).1 n = Blue.mix (back (pitch A Ñ N m)) (lop D) ∧
       (treeMatrix G S F K).PosDef ∧
       (shot S F Q Ñ R = loom (camSlice G S F (extractV G S F Q)) (jet (unhaar Ñ)) - unscaled S F Q R + (holdUp (Active G F) (orbC (precisionC G n Y))+ bodyQ (Woods G n) (treeMatrix G S F K))) ∧
       constantCoeff (inside S F K Q Ñ R)=1 ∧ Warded (flash D) ∧
       residualUnmarked Y D * (soil (ζ Ñ J.penalty))^(Fintype.card (Edge (Site n)))= inside S F K Q Ñ R ∧
       (∀ᶠ x:TreeVars G (n*L.L) in 𝓝 0, ∀ β:ℝ,∀ v, S.density β (mantle x) v= S.noise β (S.prediction (mantle x) (tac S)) v) ∧
       ∀ (k:ℕ)(P:PChart G (n*L.L)), shellK k P → (∀ i,Pure (P i)) →
          insideMark S F K Q Ñ R P = inside S F K Q Ñ R * flash (reed S F K Q Ñ R k P)

theorem finite_sampler (p:G.Simple)(h:LocalRatio Ñ)(v:m<N) (n:Side) :
    ThermalLaw A Ñ N m n := by
  let L:=loose A m; let S:=mStep A n m; let F:=repeatF S
  have hp := (old A Ñ p h N (m+1) v).basis (n*L.L)
  have he:= S.patch; have hB:S.patch.Branches S.kernel G:= (A.blocks m 0).branches
  have hv:= age_sym A N (m+1) (n*L.L)
  have hx := horizon_step A m N v n (n*L.L) rfl
  have hi:= (cond_laws A m N).1 n (n*L.L) rfl
  refine ⟨v,hp,rfl,?_,Convention.tree_pos A m N (n:=n) (f:=n*L.L) rfl, shot_bill S F _ _ _ hp.lamp hp.stem hB hx hv, inside_mass S F _ _ h, survives S F _ _ _ hp.lamp hp.stem hB h hi hx hv hp.valid hp.shape, log_output S _ _ _ _ _ h hp hB hv, ?_, fun k P g e=> inside_reed S F _ _ k hp.lamp h g hB hv hp.shape e⟩
  · conv_lhs=>rw [story_stride A Ñ v]
    rfl
  filter_upwards [penalty_same S hB] with x hx β w
  change S.density _ _ _=_; unfold StepData.density; simp_rw [hx,← Finset.sum_mul,S.chosen hB,one_mul]; rfl

/-- Fixed cutoff mesh **period limit** of this thermodynamic sampler (sewn): kernel,
transfer, Ward, no-finite-volume-cost Yields proof and reset equations. Per-site for the
extra scalar powers, none propagated. `Yields.cover` is on ALL slots;
constants here at fixed N,m, no uniform torus estimates. -/
theorem bulk_from_tori (p:G.Simple)(h:LocalRatio Ñ)(v:m<N) :
    let P:= (story A Ñ N (m+1)).1
    (∀ i r,Yields (fun n=>(story A Ñ N m).1 n i r) (actionW A Ñ N m i r)) ∧
    (∀ i r, Yields (fun n=>unripe A Ñ N m P n i r) (freshet A Ñ N m i r)) ∧
    (actionW A Ñ N m=Blue.mix (ratioHigh A Ñ N m) (lop (freshet A Ñ N m))) ∧
    (pitch A Ñ N m * (pace (pitch A Ñ N m))^2=1) ∧ BulkP (freeForms A N m) (actionW A Ñ N m):=by
  intro P; exact ⟨(old A Ñ p h N m v.le).patch,(perch A Ñ p h v).growth,conduct A Ñ v, pace_tax (angle_tilt p h v), catchment A Ñ p h v.le⟩
end convention
end YM.WilsonCoeffUV.Fk

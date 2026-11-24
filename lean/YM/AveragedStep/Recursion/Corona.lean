import YM.AveragedStep.Rank.Seal
/-!
# Continuum wall-free CONDITIONAL Wilson program — tree-pinned internal SD recursion
(StepData grammar, finite torus). `wall-free` = no plastic pointwise chart gate in the
coefficient program itself; analytic grafts there (physical grafts in Parcel/Plea etc.)
Continuum conversion NOT provided here. This step supplies local slot coefficients of the
coefficient program and full Cauchy budgets. No suppressing coincident or trivial slots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
open Matrix Push.Uniform
open PertExtension.Series.Radial
variable {c f:Side}{G:Gauge}{S:StepData c f}
section basic
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]
/-- Symplectic factors / permutation sums NOT included: 1/n! calculus library convention. -/
def threads (f:X→ℝ)(n:ℕ): ContinuousMultilinearMap ℝ (fun _ : Fin n=>X) ℝ :=
   ((n.factorial:ℝ)⁻¹) • iteratedFDeriv ℝ n f 0
lemma sewn (f:X→ℝ)(n:ℕ)(x:X):threads f n (fun _=>x)=jet f n x:=rfl
end basic
/-- Projection CLM exact in product Euclidean/pi norm of Hand. No lattice size into budgets later. -/
def dart (i:Ink G c f):Hand G c f:=Pi.single i.1 (fingers G i.2)
lemma dart_sum (Y:Hand G c f):
    ∑ i : Ink G c f,dashMark (Y i.1) i.2 • dart i = Y := by
 rw [Fintype.sum_prod_type]
 funext j
 simp_rw [Finset.sum_apply,Pi.smul_apply,dart]
 rw [Finset.sum_eq_single j]
 · simp_rw [Pi.single_eq_same]
   let B:=(EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis
   have h(i:G.ColorIndex): B.repr (Y j) i = dashMark (Y j) i:=by unfold B;simp [dashMark]
   exact (Finset.sum_congr rfl fun i _ =>congrArg₂ _ (h i).symm rfl).trans (B.sum_repr (Y j))
 · intro i hi he; rw [Finset.sum_eq_zero]
   intro n hn; simp [Pi.single_eq_of_ne he.symm]
 · simp
lemma mon_seq {k} (w: Fin k→Ink G c f)(Y):mon (List.ofFn w) Y = ∏ i,dashMark (Y (w i).1) (w i).2 := by
 induction k with
 | zero=> simp
 | succ n ih=> rw [List.ofFn_succ,mon_cons,ih,Fin.prod_univ_succ]
lemma mon_expand {n} (T:ContinuousMultilinearMap ℝ (fun _:Fin n=>Hand G c f) ℝ) (Y):
    T (fun _=>Y) = ∑ u : Fin n → Ink G c f,T (fun i=> dart (u i))*mon (List.ofFn u) Y:=by
 let L(u : Ink G c f):=dashMark (Y u.1) u.2
 have he:=T.map_sum (α:=fun _=>Ink G c f) (fun _ u=> L u • dart u)
 simp only [L,dart_sum] at he
 apply he.trans; exact Finset.sum_congr rfl (fun u _=>by simp_rw [mon_seq,mul_comm (T _)]; exact T.map_smul_univ ..)

/-- Local coefficient arrays at a pin direction. Use full Ink sequences with
zeros OFF touched home (DO NOT pay their count, only l1 in the home). -/
def trinity (S:StepData c f)(z:Ink G c f)(n:ℕ):ContinuousMultilinearMap ℝ (fun _:Fin n=>Hand G c f) ℝ :=
    ∑ p∈owners S z.1,(threads (fun y=> fderiv ℝ (chip S.patch S.kernel (sort p) (canon S.patch)) y (pick (S:=S) p (dart z))) n).compContinuousLinearMap (fun _=>bridge (S:=S) p)
def tuft (A:ChartRatio G)(z:Ink G c f)(n:ℕ):ContinuousMultilinearMap ℝ (fun _:Fin n=>Hand G c f) ℝ :=
    (threads (fun y=>Cuff.haarScore (A:=A) y (fingers G z.2)) n).compContinuousLinearMap (fun _=> ContinuousLinearMap.proj z.1)
def canopy (S:StepData c f)(z:Ink G c f){n:ℕ}(u:Fin n→Ink G c f):ℝ:=trinity S z n (fun i=>dart (u i))
def elm (A:ChartRatio G)(z:Ink G c f){n:ℕ}(u:Fin n→Ink G c f):ℝ:=tuft A z n (fun i=>dart (u i))
lemma backbone_tabs (S:StepData c f)(z:Ink G c f)(n:ℕ)(Y): backbone S z.1 (fingers G z.2) n Y=
    trinity S z (n+1) fun _=> Y := by
 unfold backbone trinity
 rw [_root_.sum_apply]
 refine Finset.sum_congr rfl fun i _=>?_ ; rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,sewn]; rfl
lemma gum_tabs (A:ChartRatio G)(z:Ink G c f)(n:ℕ)(Y:Hand G c f):gum A (fingers G z.2) n (Y z.1)= tuft A z n (fun _=>Y):=rfl
lemma duplicate {n:ℕ}(hn:n≠0)(S:StepData c f)(A:ChartRatio G)(z:Ink G c f)(Y):tier S A z.1 (fingers G z.2) n Y =
    ∑ u: Fin (n+1)→Ink G c f,canopy S z u *mon (List.ofFn u) Y - ∑ u:Fin (n-1)→Ink G c f,elm A z u *mon (List.ofFn u) Y:=by
 rw [tier,backbone_tabs,gum_tabs (z:=z),mon_expand _,mon_expand _,if_neg hn]; rfl
lemma canopy_keeps (S:StepData c f)(z:Ink G c f){n:ℕ}(u:Fin n→Ink G c f)(h:canopy S z u ≠ 0)(i:Fin n) : (u i).1 ∈ home S z.1:=by
 by_contra! hn
 unfold canopy trinity at h; rw [_root_.sum_apply] at h
 apply h; apply Finset.sum_eq_zero
 intro p hp; rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]; apply ContinuousMultilinearMap.map_coord_zero (i:=i)
 exact pick_zero p (fun he=>hn (home_owner S hp (own_need S he))) (fingers G _)
lemma elm_keeps (A:ChartRatio G)(z:Ink G c f){n:ℕ}(u:Fin n→Ink G c f)(h:elm A z u≠0)(i:Fin n) :(u i).1=z.1:=by
 by_contra! hn
 unfold elm tuft at h; rw [ContinuousMultilinearMap.compContinuousLinearMap_apply] at h
 exact h (ContinuousMultilinearMap.map_coord_zero _ i (Pi.single_eq_of_ne hn.symm _))

lemma dart_unit (z:Ink G c f)(j:Rim c f):‖dart z j‖ ≤ 1:= by
 unfold dart; by_cases he:j=z.1; · subst j; simp [fingers]
 simp [he]
private lemma sword (P:Patch)(K:KernelChoices)(n:ℕ)(G:Gauge):∃ B:ℝ,0≤B∧∀(v:G.ColorIndex)(p:Mold)(d:Finset (Interior P))(u:Fin n→Vectors P G), (∀ i,‖u i‖≤1)→
    |threads (fun y=> fderiv ℝ (chip P K p (canon P)) y (bits d (fingers G v))) n u| ≤ B:=by
 let A(v:G.ColorIndex×Mold×Finset (Interior P)):=threads (fun y=> fderiv ℝ (chip P K v.2.1 (canon P)) y (bits v.2.2 (fingers G v.1))) n
 refine ⟨∑ v,‖A v‖,Finset.sum_nonneg (fun i _=>norm_nonneg _),fun v p d u he=>?_⟩
 let i0:G.ColorIndex × Mold × Finset (Interior P):=(v,p,d)
 have h:‖A i0 u‖ ≤ ‖A i0‖*(∏ i,‖u i‖):=(A _).le_opNorm _
 exact h.trans ((mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun i _=>norm_nonneg _) (fun i _=>he i))).trans (Finset.single_le_sum (fun i _=>norm_nonneg (A i)) (Finset.mem_univ _)))
lemma pick_darts (S:StepData c f)(p:Parcel c f)(z:Ink G c f):‖pick (S:=S) p (dart z)‖ ≤ 1:=by
 refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i=>?_); unfold pick; cases hook S p i; · simp [Option.elim]
 exact dart_unit ..
lemma canopy_bound (P:Patch)(K:KernelChoices)(n:ℕ)(G:Gauge):∃ B:ℝ,0≤B∧∀{c f:Side}(S:StepData c f),S.patch=P→S.kernel=K→∀ (z:Ink G c f)(u:Fin n→Ink G c f), |canopy S z u|≤B:=by
 let m:=cap (aperture P) parcelCount
 obtain ⟨B,hB,h⟩:= sword P K n G; refine ⟨m*B,by positivity,fun {c f} S hP hK z u=>?_⟩
 unfold canopy trinity; rw [_root_.sum_apply]; subst P K
 refine (Finset.abs_sum_le_sum_abs ..).trans <| le_trans (Finset.sum_le_sum (g:=fun _=>B) (fun p hp=>?_)) ?_
 · rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]; conv_lhs=> arg 1; arg 1; arg 1; intro y; rw [dart,bits_eq]
   exact h _ _ _ _ (fun i=> pick_darts ..)
 rw [Finset.sum_const,nsmul_eq_mul]; gcongr; exact owned S z.1
lemma elm_bound (A:ChartRatio G)(n:ℕ):∃ B:ℝ,0≤B∧∀{c f:Side}(z:Ink G c f)(u:Fin n→Ink G c f), |elm A z u|≤B:=by
 let L(i:G.ColorIndex):=threads (fun y=>Cuff.haarScore (A:=A) y (fingers G i)) n
 refine ⟨∑ i,‖L i‖,Finset.sum_nonneg (fun i _=>norm_nonneg _),fun {c f} z u=>?_⟩
 unfold elm tuft; rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]; change ‖L z.2 (fun i=>dart _ _)‖ ≤ _
 refine ((L _).le_opNorm _).trans ?_
 apply (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun i _=> norm_nonneg _) (fun i _=> dart_unit ..))).trans (Finset.single_le_sum (fun i _=>norm_nonneg (L i)) (Finset.mem_univ _))
end YM.AveragedStep

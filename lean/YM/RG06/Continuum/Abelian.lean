import YM.RG06.Continuum.SmoothQuot

/-! g=0 radial fixing, compatibility with accepted Maxwell kinematics at tree level. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
open Maxwell Labels Function Analysis
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G : Gauge} (A:Connection G)

def freeStage (k:ℕ): Connection G:= fun i=> A i-par i (obstacle k A)
lemma smoothFree (h:Smooth A)(k:ℕ):Smooth (freeStage A k):=fun i=> ContDiff.sub (h i) ((obstacle_smooth k A).par i)
lemma curvature_free (h:Smooth A)(k:ℕ)(i j:Axis)(x:E4): curvature 0 (freeStage A k) i j x= curvature 0 A i j x:=by
  unfold freeStage curvature
  simp only [sub_eq_add_neg, par_add (h _) (g:=-par _ (obstacle k A)) (ContDiff.neg ((obstacle_smooth _ _).par _)), zero_smul, par_neg,Pi.add_apply,Pi.neg_apply,par_cross (obstacle_smooth k A) i j]; abel

lemma free_curve_price (h:Smooth A)(k:ℕ)(he:killed k A)(i:ℕ)(hi:i≤k)(z:E4):
    iteratedDeriv i (radTest (freeStage A k) z) 0=0:=by
  have hx(t:ℝ): (∑ i:Axis,z i • par i (obstacle k A) (t • z)) = ((k+1:ℕ):ℝ) • t^k • obstacle k A z:=by
    let x0:=t • z
    have hk : HasDerivAt (fun t:ℝ=>t • z) z t:=by simpa using! (hasDerivAt_id' t).smul_const z
    have ht:= ((obstacle_smooth k A).germ x0).hasFDerivAt.comp_hasDerivAt t hk
    change HasDerivAt (fun t :ℝ=> obstacle k A (t • z)) ((fderiv ℝ (obstacle k A) x0) z) t at ht
    simp_rw [obstacle_power] at ht
    have he:= (((hasDerivAt_id' t).pow (k+1)).smul_const (obstacle k A z))
    have hu : ((fderiv ℝ (obstacle k A) x0) z) = ((k+1:ℕ):ℝ) • t^k • obstacle k A z:=by simpa only [Nat.add_sub_cancel, mul_one, ← smul_smul] using! ht.unique he
    unfold par D; rw [show t • z=x0 from rfl,← hu]
    have hZ: ∑ i:Axis,z i • basis i=z:=by ext i; simp [WithLp.ofLp_sum,Finset.sum_apply,basis,Pi.single_apply,mul_ite]
    conv_rhs=> arg 2; rw [← hZ]
    rw [map_sum]; simp only [map_smul]
  unfold radTest freeStage
  simp only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib,hx]
  rw [iteratedDeriv_fun_sub]
  let m:= ((k+1:ℕ):ℝ) • obstacle k A z
  rw [show (fun t:ℝ=> ((k+1:ℕ):ℝ) • t^k • obstacle k A z)=(fun t:ℝ=> t^k • m) from funext (fun t=>smul_comm ..), iteratedDeriv_smul_const, iteratedDeriv_fun_pow_zero]; split
  next hI=> subst i; change iteratedDeriv _ (radTest A z) _ - _ = _; rw [← charge k A h, sub_eq_zero, show m=((k+1:ℕ):ℝ) • obstacle k A z from rfl,smul_smul,mul_comm]; push_cast;rfl
  next hI=> rw [Nat.cast_zero, zero_smul]; exact sub_eq_zero.mpr (he _ (by omega) z)
  · exact contDiffAt_id.pow _
  · exact ContDiffAt.sum (fun i _=> ContDiffAt.const_smul _ (((ContDiff.contDiffAt (h i)).comp (f:=fun t:ℝ=> t • z) 0 (contDiffAt_id.smul contDiffAt_const)).of_le (WithTop.coe_le_coe.mpr le_top)))
  · exact ContDiffAt.const_smul _ ((contDiffAt_id.pow k).smul contDiffAt_const)

lemma eval_free (h:Smooth A)(k:ℕ): Form.evaluate 0 (freeStage A k) 0 = Form.evaluate 0 A 0 := by
  have he(A B:Connection G)(j:ℕ)(w:Fin j→ Axis)(f:Section G): nablas 0 A w f= nablas 0 B w f:=by
    induction j with
    | zero=>rfl
    | succ j H=>rw [nablas,nablas,H]; simp [covariant]
  funext j i a w
  unfold Form.evaluate covJet; rw [show curvature 0 _ i a = _ from funext (fun x=>curvature_free A h k i a x), he _ A j]
lemma orbit_free (h:Smooth A)(k:ℕ):∃ B:Connection G, Smooth B ∧ killed k B ∧ Form.evaluate 0 B 0=Form.evaluate 0 A 0:=by
  induction k with
  | zero=> exact ⟨A,h,(fun _ hk=>False.elim (Nat.not_lt_zero _ hk)),rfl⟩
  | succ k H=>obtain ⟨B,hs,hv,hB⟩:=H; exact ⟨freeStage B k,smoothFree B hs k,(fun i hi z=>free_curve_price B hs k hv i (Nat.lt_succ_iff.mp hi) z),(eval_free B hs k).trans hB⟩

theorem solved {A:Connection G}(g:ℝ)(h:Smooth A)(d:ℕ):∃ J:Labels.Jet G,∀ p:Form.Field G d,
    Form.actual g A 0 p.val=Form.actual g (radField d J) 0 p.val:=by
  by_cases hc:g≠0
  · exact cov_orbit g A hc h d
  have he:g=0:=Classical.byContradiction fun q=>hc q; subst g
  obtain ⟨B,s,q,v⟩:= orbit_free A h d
  refine ⟨snapshot d B s q,fun p=>?_⟩; apply Eq.trans _ (snapshot_eval _ s q p); exact congrArg (fun x=>Form.applyTo x p.val) v.symm

end YM.RG06.Continuum

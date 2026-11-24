import YM.Contacts.Loom.Area
/-! Arbitrary point/seam evaluation markets. Clock after.Stage.Star. Uniformly weighted relative spaces.
 A Motion r charges scale‐normalized `cap` using actual n.Point Metrics. -/
namespace YM.Contacts.Loom
open Function Filter Set Finset Metric
open Lattice RG Wilson PhysicalNext.Repeat Pressure ConnectedActivityE6 Blaze
open MeasureTheory Meter
open scoped Topology InnerProductSpace NNReal BigOperators ContDiff Matrix.Norms.Frobenius Interval Classical
set_option linter.unusedVariables false
noncomputable section
variable {E F V Y α γ:ℕ→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (F i)] [∀ i,NormedSpace ℝ (F i)] [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] [∀ i,NormedAddCommGroup (Y i)][∀ i,NormedSpace ℝ (Y i)]
variable {N:Meter}{p q r s Z:ℝ}{k j l:ℕ}{f:ℕ→ℝ}
section weights
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]
private def sym (X:Type)[NormedAddCommGroup X][NormedSpace ℝ X](j:ℕ):Submodule ℝ (Tensor.T X ℝ j) where
  carrier:= {u | Tensor.Sym u}
  zero_mem' := fun _ _=>rfl
  add_mem' {u v} p q x y:=by simp only [add_apply,p x y,q x y]
  smul_mem' a u h x y:= by simp only [smul_apply,h x y] -- smul implicit
private lemma mercury (U : Fin j →(Fin j→ℝ)) : ∃ z:ℝ,0≤z ∧ ∀ w:ℝ,0≤w→ ∀ F : sym (Fin j →ℝ) j,(∀ x: Fin j→ℝ, ‖Tensor.diagonal F.val x‖≤w*‖x‖^j)→ ‖F.val U‖ ≤ z*w:= by
   let V:= Fin j→ℝ; let A(u:Fin j→V):= (ContinuousMultilinearMap.apply ℝ (fun _:Fin j=> V) ℝ u).toLinearMap.comp (sym V j).subtype; let Y:= ↥(sym V j); let l(z:V):=A (fun _=> z); have hv: A U ∈ Submodule.span ℝ (Set.range l):= by
      refine FiniteDimensional.mem_span_of_iInf_ker_le_ker ?_; intro y hy; have hZ:y=0:=by
         refine Subtype.ext (Tensor.ext_diag _ _ y.2 (fun _ _=> rfl) (funext fun x=> (Submodule.mem_iInf _).1 hy x))
      rw [hZ]; exact Submodule.zero_mem _
   let P(f:Y→ₗ[ℝ] ℝ):=∃ z:ℝ,0≤z ∧ ∀ w:ℝ,0≤w→ ∀ F : Y,(∀ x: V, ‖Tensor.diagonal F.val x‖≤w*‖x‖^j)→ ‖f F‖ ≤ z*w
   refine Submodule.span_induction (p:=fun v _=>P v) ?_ ?_ ?_ ?_ hv;
   · rintro f ⟨v,rfl⟩; exact ⟨_,pow_nonneg (norm_nonneg v) j, fun u h F p=> (p v).trans_eq (mul_comm ..)⟩
   · exact ⟨0,le_rfl,fun w h F _=> by simp⟩
   · intro a b _ _ ⟨s,hs,H⟩ ⟨t,ht,K⟩; exact ⟨_,add_nonneg hs ht,fun w hw F h=> (norm_add_le ..).trans ((add_le_add (H _ hw F h) (K _ hw F h)).trans_eq (add_mul _ _ _).symm)⟩
   intro c f _ ⟨s,hs,H⟩; refine ⟨_, mul_nonneg (norm_nonneg c) hs,fun w hw F hh=>?_ ⟩; erw [LinearMap.smul_apply,norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (H _ hw F hh) (norm_nonneg _)
private lemma mercury' (z:X): ‖‖z‖⁻¹ • z‖ ≤ 1 ∧ ‖z‖ • (‖z‖⁻¹ • z)=z := by
   by_cases hz:z=0; · subst z; simp
   simp [norm_inv, norm_smul, smul_inv_smul₀ (show ‖z‖ ≠ 0 from (norm_pos_iff.mpr hz).ne')]; field_simp; exact le_rfl
lemma poly_rent (j:ℕ): ∃ a≥(0:ℝ),∀ (X:Type)[NormedAddCommGroup X][NormedSpace ℝ X](S:Tensor.T X ℝ j), Tensor.Sym S→∀ z:ℝ,0≤z→(∀ x:X, ‖Tensor.diagonal S x‖≤z*‖x‖^j)→ ‖S‖≤ a*z:= by
   let I:= Fin j; let V:= Fin j→ℝ; let f (i:I):V:= Pi.single i (1:ℝ); obtain ⟨a,ha,hx⟩:=mercury f; refine ⟨a*(j:ℝ)^j,by positivity,fun E _ _ S h z hz he=>?_⟩; apply ContinuousMultilinearMap.opNorm_le_bound (by positivity); intro y
   let p(i:I):=‖y i‖; let u(i:I):=(p i)⁻¹ • y i; have hp i:0≤p i:= norm_nonneg _; have hy':(fun i=>p i• u i)=y:= funext fun i=>(mercury' _).2
   let L: V →L[ℝ] E:= ∑ i:I,(ContinuousLinearMap.proj i).smulRight (u i); have hL x: L x=∑ i:I,(x i) • u i:= by simp [L]; rfl
   have hg i:L (f i)=u i:= by rw [hL]; simp [f,Pi.single_apply,ite_smul]; simp [I]
   have ht x:‖L x‖ ≤ (j:ℝ)*‖x‖:= by rw [hL]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun i=>‖x‖) fun i _=>?_).trans_eq (by simp [I])); rw [norm_smul]; exact (mul_le_of_le_one_right (norm_nonneg _) (mercury' _|>.1)).trans (norm_le_pi_norm x i)
   let m:Tensor.T V ℝ j:= S.compContinuousLinearMap (fun _=>L); let Q:=sym V j; have hh:m∈Q:=by
      intro v a; change S ( (L∘v) ∘ a)= S _; exact h (L ∘ v) a
   have hx': ‖S u‖ ≤ a*(z*(j:ℝ)^j):= by
      refine (Eq.trans_le (by unfold m; simp [hg]: ‖S u‖=‖m f‖) (hx _ (by positivity) ⟨m,hh⟩ ?_)); intro x; change ‖Tensor.diagonal S (L x)‖ ≤ _; exact (he _).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (ht x) j) hz).trans_eq (by rw [mul_pow, ← mul_assoc]))
   rw [show S y=_ from ((show S y=S _ from congr_arg _ hy'.symm).trans (S.map_smul_univ p u)), norm_smul]; apply le_trans (mul_le_mul_of_nonneg_left hx' (norm_nonneg _)); change _ ≤ a*_ *_ *∏ i,p i; rw [Real.norm_of_nonneg (prod_nonneg fun i _=> hp _)]; apply le_of_eq; ring
-- truncated at fixed height. `Budget` eventual only
open PertExtension.Series Radial Milling
lemma jet_s (a:X→ℝ) (k:ℕ) (x:X): AnalyticAt ℝ (jet a k) x:= by unfold jet; exact ContDiffAt.analyticAt (contDiffAt_const.mul ((iteratedFDeriv ℝ k a 0).contDiff.contDiffAt.comp (f:=fun i=>fun _:Fin k=>i) _ (by fun_prop)))
-- reminder Renew.tth uses only enough derivatives at origin. choose analytic hypothesis OR CtD.Der lemma even-order symmetric equality analyticAt when analyt all. Later used. scalar coeff universal
variable [FiniteDimensional ℝ X]
def skel (a:X→ℝ)(k:ℕ): X→ℝ:= fun x=>∑ i∈Finset.range k,jet a i x
lemma skel_analytic (a:X→ℝ)(k:ℕ)(x:X): AnalyticAt ℝ (skel a k) x:= by unfold skel; apply ContDiffAt.analyticAt; exact ContDiffAt.sum fun i _=> (jet_s a i x).contDiffAt
lemma peel (a:X→ℝ)(k:ℕ)(x:X) : jet (skel a k) l x= if l<k then jet a l x else 0:= by
   unfold skel; rw [Milling.Ion.loan_sum _ (fun i _=> jet_s _ i _)]; simp_rw [Milling.radiant (jet_s ..) _ _ (fun x t=> jet_smul _ _ _ x)]; simp
lemma cords (a:X→ℝ)(k:ℕ)(h: AnalyticAt ℝ a 0): YM.Stationary.Rays k (a-skel a k):= Ion.valued k h (skel_analytic ..) fun x i hi=> ((peel a k x).trans (if_pos hi)).symm
end weights
open PertExtension.Series Radial Milling
variable {x: Frame α E}{f:Shelf E α F} {y :ℕ→ℝ}
lemma Budget.jetcap {w:Lamp F}(h: Budget N x k p f)(hx:N.Rush r (fun i=> normJ j (w i) 0)) : Budget N x k (r+p*j) (fun i u x'=> jet (w i) j (f i u x')):= by
   let S i : Tensor.T (F i) ℝ j:= iteratedFDeriv ℝ j (w i) 0; have hp:Budget N x k r (fun i (_:α i) (_:E i)=> S i):= Budget.value S hx
   exact (hp.sheet h).scale _ -- scalar j!
variable [∀ i, FiniteDimensional ℝ (F i)]
lemma Budget.skew {w:Lamp F}(h: Budget N x k p f)(hp:p≤0)(hx:∀ i<j,N.Rush r (fun x=> normJ i (w x) 0)) : Budget N x k r (fun i v x'=> skel (w i) j (f i v x')):= by
   unfold skel; exact Budget.spike (a:=fun u i j x=> jet (w i) u (f i j x)) (fun i (hi:i∈Finset.range j) => Arms.lo (h.jetcap (hx i (mem_range.mp hi))) (by have he:= mul_nonpos_of_nonpos_of_nonneg hp (Nat.cast_nonneg i); linarith) le_rfl)
end
end YM.Contacts.Loom

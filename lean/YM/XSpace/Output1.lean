import YM.XSpace.Sightline
/-!
# First ORDER succeeds in physical position

Tests & point geometry representative. Retain order-cost sense. **Prior to coupling
registration** uses the nonlinear bare parameter. Higher estimates not claimed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Photo
open Function Set Filter Structure1 Cirrus Normalize PowerSeries Retirement MeasureTheory Maxwell Fray
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n:ℕ} (W:Initialize G)(V:Store G)(d:ℕ)(p:Tags G d n)(c:Shade.Cut)
def calibrate (x: Points n): Point G d n:= Mix (Normalize.scene x d) (orderBasic W d c x) 1 (fallFee W V d c).val
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4600 in
lemma profile_limit (H:Granted V d c): Senses (Good c n) (fun i=> Positioned W V d i p) (fun x=> calibrate W V d c x p):=by
  intro x hx
  let f i:= grab (n:=n) i; let F:= fallFee W V d c
  let b i:= adjustment W V d c (f i); let a i:= visor W V (f i) d; let o:= fun i:Sample n=> fallRecords W d c i
  have he(j:Fin n):Reads d (F:=Gate x) (fun i=> a i (p j)) (p j):= by have hh:=cue_cost W V d (p j); unfold Reads at *; exact hh.comp (liftG x)
  have hp(j): Tendsto (fun i=> o i j) (Gate x) (𝓝 (orderBasic W d c x j)):= maturation d j (Good c n) (structures W d c) x hx
  simp_rw [show ∀ i: Cirrus.Sample n,Positioned W V d i= Mix (live W d i 0) (o i) (a i) (b i).val from fun i=> adapt .., calibrate,mixer]; change Tendsto _ _ (𝓝 (orderBasic W d c x p+∑ i:Fin n,scene x d (update p i (F.val (p i)))))
  refine (lights d p (fun i=> a i ∘ p) he _ _ hp).add (tendsto_finsetSum Finset.univ fun i _=>?_); refine lights d _ _ ?_ _ _ (fun p=> notices W d p x (beyond_conf c hx))
  intro j; by_cases hy:j=i; subst j; simp_rw [update_self]; exact light_cost d ((board_paid W V d c H).comp (liftG x)) _
  simp_rw [update_of_ne hy]; exact he j

lemma reached : Positive d (conf n) (Positioned W V d):=by
  intro p x hx; obtain ⟨c,hc,H⟩:= small_cut V d (K:={x}) (isCompact_singleton) (singleton_subset_iff.mpr hx); exact ⟨_,profile_limit W V d p c H x (hc (mem_singleton _))⟩

-- continuum definition inferior/orders per future; no perturbative-orders swap

def checked1 (x:Points n): Point G d n:= mature d (conf n) (Positioned W V d) (reached W V d) x
lemma reaches1 : Senses (conf n) (fun i=> Positioned W V d i p) (fun x=> checked1 W V d x p):= maturation d _ _ (reached W V d)
theorem independent (H:Granted V d c) (x:Points n)(hx:x∈Good c n): checked1 W V d x= calibrate W V d c x:=by ext1 p; exact tendsto_nhds_unique (reaches1 W V d p x (beyond_conf c hx)) (profile_limit W V d p c H x hx)
theorem continuously : ContinuousOn (fun x:Points n=> checked1 W V d x p) (conf n):=(reaches1 W V d p).priced
open TestBudget Function Fray

-- Test view with horizon. Uniform e across all profiles on compact set with only one derivative.
def readings (f:Test n) : Point G d n:= MultilinearMap.mk' (fun p=> f.applyTo fun x=> checked1 W V d x p)
 (fun p i a b=> by simp_rw [Test.applyTo,MultilinearMap.map_update_add,mul_add]; exact integral_add (f.smearing (continuously W V d _)) (f.smearing (continuously W V d _)))
 (fun p i a b=> by unfold Test.applyTo; simp_rw [MultilinearMap.map_update_smul,smul_eq_mul,mul_left_comm (f _) a]; exact integral_const_mul a _)
-- importable G expectation first jets. Later coupling first tangent must ≠0 and normalization sends.
def kernel1 : Prediction G d:= fun n=>
 { toFun f:= readings W V d f
   map_add' a b := by ext1 p; simp only [readings,MultilinearMap.mk'_apply, add_apply,Test.applyTo,add_mul]; exact integral_add (a.smearing (continuously W V d _)) (b.smearing (continuously W V d _))
   map_smul' c v:= by ext1 p; simp only [Test.applyTo,readings,MultilinearMap.mk'_apply,smul_apply,smul_eq_mul,mul_assoc,RingHom.id_apply]; rw [integral_const_mul] }

theorem reads1 (f:Test n): Tendsto (fun i=> V.opens W i d 1 n f p) Front (𝓝 (kernel1 W V d n f p)):= (sees_test (conf n) f _ (conf_open n) (reaches1 W V d p) (fun _ _ _=>rfl) f.tsupport_subset).congr fun i=> deposit_normal ..
theorem uniform1 {K:Set (Points n)}(H:IsCompact K)(h: K⊆ conf n)(e:ℝ)(he:0<e): ∀ᶠ m in Front,∀ f:Test n, tsupport f ⊆ K→∀ b:ℝ,Bound f b→ ‖V.opens W m d 1 n f p-kernel1 W V d n f p‖≤ b*e:=by simp_rw [← deposit_normal W V p _]; exact graduate _ _ (conf_open _) (continuously W V d p) h H (reaches1 W V d p) (fun _ _ _=>rfl) e he

lemma horizon_test {k:ℕ}(h:d≤k): recruit (Normalize.up h) (kernel1 W V k)=kernel1 W V d:=by ext1 n; ext1 f; ext1 p; apply tendsto_nhds_unique (f:=fun i=> V.opens W i d 1 n f p) _ (reads1 W V d p f); exact (reads1 W V k (fun i=> up h (p i)) f).congr' ((V.cumulative W frontier h).mono fun i hi=> by apply Eq.trans _ (show recruit (up h) (V.opens W i k 1) n f p= _ from congr_arg (fun X:Prediction G d=> X n f p) (hi 1)); rfl)
lemma horizon_point {k:ℕ}(h:d≤k){x:Points n}(hx:x∈conf n): checked1 W V k x (up h ∘ p)= checked1 W V d x p:=by
  exact (Test.unique_kernel (continuously W V k _) (continuously W V d p)).mp (fun f=> by change recruit (up h) (kernel1 W V k) _ _ _=_; rw [horizon_test]; rfl) hx
lemma bills : (V.measure d).D (kernel1 W V d)=0:=by
  let D:=V.measure d; let u:= V.survey d; let v:= u.stamps; let t(i:Mesh):=V.opens W i d 1; have h(P: Prediction G d): guide G d (D.D P)= v (fun i=>watch (u.scope i) P):=by rw [← u.equal]; rfl
  apply (guide G d).injective; rw [map_zero]; change guide G d (D.D _)=_; apply tendsto_nhds_unique (f:=fun i=> guide G d (D.D (t i))) (l:=Front); swap
  · apply tendsto_const_nhds.congr'; filter_upwards [(V.nested_solution W d frontier).2] with i hi; change (0:MoveSpace G d)= _; rw [show D.D (t i)=0 from (hi.1.2.1 1).trans (if_neg one_ne_zero), map_zero]
  simp_rw [h]; exact v.continuous.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (fun i=> reads1 ..))
lemma slots1 : recruit (hinge d) (kernel1 W V d)= -(kernel1 W V d):=by
  ext1 n; ext1 f; ext1 p; apply tendsto_nhds_unique (reads1 W V d (hinge d ∘ p) f); let u(i:Mesh):= V.opens W i d 1; apply (reads1 W V d p f).neg.congr'; filter_upwards [(V.nested_solution W d frontier).2] with i hi
  have ht:= hi.1.2.2.2.1 1; rw [pow_one] at ht; change -u i n f p = _; rw [← recruits, show recruit (hinge d) (V.opens W i d 1)=(-1:ℝ) • V.opens W i d 1 from ht]; exact (neg_one_smul ℝ (u i n f p)).symm
lemma reals1 : RealFields (kernel1 W V d):=by intro n p t; exact tendsto_nhds_unique (reads1 W V d (reel d ∘ p) (inverted t)) ((reads1 W V d p t).star.congr' (((V.nested_solution W d frontier).2).mono fun i hi=> (hi.1.2.2.2.2.1 1 n p t).symm))
end YM.XSpace.Photo

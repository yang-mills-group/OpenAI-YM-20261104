import YM.Contact.Junction
import YM.Contact.Orbits

/-! Full Euclidean rotations and slot permutations on the normal variables. They act by genuine
linear isometries of the fixed Jacobi space, not by a per-label choice of different cutoffs. -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts
open Set Function Filter MeasureTheory ContinuousLinearMap
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {k n:ℕ}
def moveList (g:Ortho) : Points n ≃ₗᵢ[ℝ] Points n where
    toFun:= Points.move g
    invFun:= Points.move g⁻¹
    map_add' x y:=by ext1 i; exact (g.motion).map_add (x i) (y i)
    map_smul' r x:=by ext1 i; exact (g.motion).map_smul r (x i)
    left_inv x:=by ext1 i; exact Ortho.inv_move _ _
    right_inv x:=by ext1 i; exact Ortho.move_inv ..
    norm_map' x:=by apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp; rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]; change (∑ i,‖(Points.move g x) i‖^2) = _; simp only [Points.move_coord,Ortho.move_norm]

def permuteList (p:Equiv.Perm (Fin n)): Points n ≃ₗᵢ[ℝ] Points n where
    toFun := Points.rearrange p
    invFun := Points.rearrange p⁻¹
    map_add' _ _:=rfl
    map_smul' _ _:=rfl
    left_inv x:=by ext1 i; simp only [Points.rearrange_at,Equiv.Perm.inv_def, p.apply_symm_apply]
    right_inv x:=by ext1 i; simp only [Points.rearrange_at,Equiv.Perm.inv_def, p.symm_apply_apply]
    norm_map' x:= (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by
       rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]; exact Equiv.sum_comp p (fun i=> ‖x i‖^2))

def placed (g:Ortho)(p:Equiv.Perm (Fin n)) := (permuteList p⁻¹).trans (moveList g)
lemma placed_apply (g:Ortho)(p:Equiv.Perm (Fin n))(x:Points n):placed g p x=Points.move g (Points.rearrange p⁻¹ x):=rfl

lemma placed_mul (g h: Ortho)(p q:Equiv.Perm (Fin n))(x:Points n):placed (g*h) (p*q) x = placed g p (placed h q x):=by
    ext1 i; simp only [placed_apply,Points.move_coord,Points.rearrange_at,Ortho.move_mul,mul_inv_rev, Equiv.Perm.coe_mul,Function.comp_apply]
lemma placed_id(x:Points n):placed 1 1 x=x:=by ext1 i; simp only [placed_apply,Points.move_coord,inv_one,Points.rearrange_at,Equiv.Perm.one_apply,Ortho.move_one]

lemma centroid_placed (g:Ortho)(p:Equiv.Perm (Fin n))(x:Points n):
    centroid n (placed g p x)=g.motion (centroid _ x):=by
   simp only [centroid_apply,placed_apply,Points.rearrange_at,Points.move_coord]
   change (n:ℝ)⁻¹ • (∑ i,g.motion (x (p⁻¹ i)))= _
   rw [Equiv.sum_comp p⁻¹ (fun i=>g.motion (x i)),map_smul,map_sum]
lemma ker_invariant(g:Ortho)(p:Equiv.Perm (Fin n))(x : LinearMap.ker (centroid n)): placed g p x ∈ LinearMap.ker (centroid n):=
    (centroid_placed g p x).trans ((congrArg (fun y=>g.motion y) (LinearMap.mem_ker.mp x.property)).trans (g.motion.map_zero))
private def kerAction (g:Ortho)(p:Equiv.Perm (Fin n)) : ((centroid n).ker) ≃ₗᵢ[ℝ] ((centroid n).ker) where
    toFun x:= ⟨placed g p (x:Points n),ker_invariant ..⟩
    invFun x:= ⟨placed g⁻¹ p⁻¹ (x:Points n),ker_invariant ..⟩
    map_add' _ _:= Subtype.ext ((placed g p).map_add ..)
    map_smul' _ _:=Subtype.ext ((placed g p).map_smul ..)
    left_inv x:=Subtype.ext (by change placed g⁻¹ p⁻¹ (placed g p x)=x.val; rw [← placed_mul,inv_mul_cancel,inv_mul_cancel]; exact placed_id _)
    right_inv x:=Subtype.ext (by change placed g p (placed g⁻¹ p⁻¹ x)=x.val; rw [← placed_mul,mul_inv_cancel,mul_inv_cancel]; exact placed_id _)
    norm_map' x:= (placed g p).norm_map x

def normalAction (g:Ortho)(p:Equiv.Perm (Fin (k+1))) : Points k ≃ₗᵢ[ℝ] Points k:= ((stair k).trans (kerAction g p)).trans (stair k).symm
lemma normal_def (g:Ortho)(p:Equiv.Perm (Fin (k+1)))(x): normalAction g p x=(stair k).symm (⟨placed g p (differences k x),ker_invariant g p (stair k x)⟩):=rfl
lemma image_normal (g:Ortho)(p:Equiv.Perm (Fin (k+1)))(x):
    differences k (normalAction g p x)=placed g p (differences k x):= congrArg Subtype.val ((stair k).apply_symm_apply (kerAction g p (stair k x)))
lemma normal_mul (g h:Ortho) (p q:Equiv.Perm (Fin (k+1))) (x:Points k): normalAction g p (normalAction h q x) = normalAction (g*h) (p*q) x:=(stair k).injective (Subtype.ext (by change differences k _=differences k _; rw [image_normal,image_normal,image_normal,placed_mul]))
lemma normal_id (x:Points k): normalAction 1 1 x=x:=(stair k).injective (Subtype.ext (by change differences k _=differences k _;rw [image_normal,placed_id]))
lemma normal_inv (g:Ortho)(p:Equiv.Perm (Fin (k+1))): (normalAction g p).symm= normalAction g⁻¹ p⁻¹:=LinearIsometryEquiv.ext fun x=>(normalAction g p).injective (by rw [LinearIsometryEquiv.apply_symm_apply,normal_mul,mul_inv_cancel,mul_inv_cancel,normal_id])

lemma combo_movable : Continuous (fun z:Ortho × Points n=> Points.move z.1 z.2):= by
   change Continuous ((WithLp.toLp 2) ∘ (fun z:Ortho×Points n=> fun i=>z.1.move (z.2 i)))
   refine (PiLp.continuous_toLp 2 _).comp (continuous_pi_iff.mpr fun i=> ortho_movable.comp (continuous_fst.prodMk ((PiLp.continuous_apply 2 _ i).comp continuous_snd)))
lemma normal_movable (p: Equiv.Perm (Fin (k+1))): Continuous (fun z: Ortho × Points k=> normalAction z.1 p z.2):=by
    simp only [normal_def]; apply (stair k).symm.continuous.comp
    apply Continuous.subtype_mk
    exact combo_movable.comp (continuous_fst.prodMk ((permuteList p⁻¹).continuous.comp (differencesCLM.continuous.comp continuous_snd)))

-- Test transformation with inverse pullback (Jacobian modulus one), for arbitrary linear isometry.
abbrev Motion (k:ℕ) := Points k ≃ₗᵢ[ℝ] Points k
variable (L:Motion k)
def pose : Trial (Points k) →ₗ[ℂ] Trial (Points k) where
   toFun φ:= ⟨⇑φ ∘ L.symm, φ.contDiff.comp ((L.symm.toContinuousLinearEquiv: Points k ≃L[ℝ] Points k).contDiff),
       (φ.hasCompactSupport.image L.continuous).of_isClosed_subset (isClosed_tsupport _) (fun x hx=>by
           have he := tsupport_comp_subset_preimage (φ:Points k→ℂ) L.symm.continuous hx
           exact ⟨L.symm x,he, L.apply_symm_apply _⟩), fun _ _=>trivial⟩
   map_add' _ _:=TestFunction.ext (fun _=>rfl)
   map_smul' _ _:=TestFunction.ext (fun _=>rfl)

lemma pose_apply (φ : Trial (Points k)) (x : Points k):pose L φ x=φ (L.symm x):=rfl

lemma pose_comp (φ : Trial (Points k))(x) : iteratedFDeriv ℝ n (pose L φ) x =
    (iteratedFDeriv ℝ n φ (L.symm x)).compContinuousLinearMap fun _=> L.symm.toContinuousLinearEquiv.toContinuousLinearMap:= by exact ContinuousLinearMap.iteratedFDeriv_comp_right L.symm.toContinuousLinearEquiv.toContinuousLinearMap (φ.orders n) _ le_rfl

lemma pose_major (φ:Trial (Points k)){b:ℝ}(h:Major n φ b): Major n (pose L φ) b := fun i hi x=>by
   rw [pose_comp]; apply ContinuousMultilinearMap.opNorm_le_bound h.nonneg; intro u;rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]; apply (ContinuousMultilinearMap.le_opNorm ..).trans
   change ‖iteratedFDeriv ℝ i (φ:Points k→ℂ) _‖ * (∏ j, ‖L.symm (u j)‖) ≤ _
   simpa only [LinearIsometryEquiv.norm_map] using! mul_le_mul_of_nonneg_right (h i hi (L.symm x)) (show 0 ≤ (∏ i,‖u i‖) from Finset.prod_nonneg fun _ _=>norm_nonneg _)
lemma pose_shrink (r : ℝ) (φ : Trial (Points k)) : shrinking r (pose L φ) = pose L (shrinking r φ) :=TestFunction.ext fun x=>by simp only [pose_apply,shrinking_apply,shrink_apply,L.symm.map_smul]

lemma pose_support (φ : Trial (Points k))(R:ℝ)(hR:support ⇑φ ⊆ Metric.closedBall 0 R) : support ⇑(pose L φ) ⊆ Metric.closedBall 0 R:=by intro x hx;exact mem_closedBall_zero_iff.mpr ((L.symm.norm_map x) ▸ mem_closedBall_zero_iff.mp (hR hx))
lemma pose_live (g:Ortho)(p:Equiv.Perm (Fin (k+1))) {φ : Trial (Points k)} (h:tsupport ⇑φ ⊆ airborne k):tsupport ⇑(pose (normalAction g p) φ) ⊆ airborne k:=by
    intro y hy; let e:=normalAction g p
    have hf := h ((tsupport_comp_subset_preimage (φ:Points k→ℂ) e.symm.continuous) hy); have he:= Points.move_in g (Points.rearrange_in p⁻¹ hf)
    rw [← placed_apply,← image_normal,e.apply_symm_apply] at he;exact he
lemma pose_join (g h:Ortho) (p q:Equiv.Perm (Fin (k+1)))(φ : Trial (Points k)):
    pose (normalAction g p) (pose (normalAction h q) φ) = pose (normalAction (g*h) (p*q)) φ := TestFunction.ext fun x=> by simp only [pose_apply,normal_inv,normal_mul,mul_inv_rev]

end YM.Contacts

import YM.Contact.Orbits

/-! Homogeneous splitting of the physical filtration preserved by rotations. Choices once on
each actual hierarchy/inclusion plan. We use algebraic finite-dimensional norms here, no UV
calibrations. -/
noncomputable section
set_option autoImplicit false
open LinearMap Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators ComplexConjugate
namespace YM.Contacts
open scoped Contacts
variable {G:Gauge} {L:Register G} {S:Table L} {R:S.Rotation} {d d':ℕ}

def fieldBar (H:S.RealSpin) (i:ℕ) : S.Field i →ₗ[ℝ] S.Field i where
  toFun :=S.conj H i
  map_add' := map_add _
  map_smul' r v:=by
    change S.conj H i (r • v)=r • _
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),LinearMap.map_smulₛₗ]; exact_mod_cast (congrArg (· • S.conj H i v) (Complex.conj_ofReal r)).trans
        (Eq.trans rfl (RCLike.real_smul_eq_coe_smul _ _).symm)

variable {W:DiffPlan S} (H:S.RealSpin)
/-- Average a map with its real conjugate, staying complex-linear. -/
def parity (q : S.Field d→ₗ[ℂ] S.Field d') : S.Field d→ₗ[ℂ] S.Field d' where
  toFun v:=((1/2:ℝ):ℂ) • (q v + S.conj H _ (q (S.conj H _ v)))
  map_add' v w:=by rw [map_add, map_add, map_add, map_add]; module
  map_smul' z v:=by rw [q.map_smul,LinearMap.map_smulₛₗ,q.map_smul,LinearMap.map_smulₛₗ]; simp only [starRingEnd_apply,star_star]; change (_:ℂ) • _= z•_; module

lemma parity_real (q : S.Field d→ₗ[ℂ] S.Field d')(v):
    S.conj H _ (parity H q v)=parity H q (S.conj H _ v):=by
  unfold parity; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [LinearMap.map_smulₛₗ,map_add,S.reflect_star,S.reflect_star]
  rw [show (starRingEnd ℂ) ((1/2:ℝ):ℂ) = _ from Complex.conj_ofReal _,add_comm]


/-- A splitting for a supplied inclusion plan; exact covariance with respect to the actual
continuous rotations and real structure, not an isometric identification with the free theory. -/
structure Graded (W:DiffPlan S) (R:S.Rotation) (h:S.RealSpin) where
  restrict (i:ℕ): S.Field (i+1)→ₗ[ℂ] S.Field i
  left i (v:S.Field i): restrict i (W.rise (Nat.le_succ i) v)=v
  rotate i k (v:S.Field (i+1)): restrict i (R.act _ k v)=R.act _ k (restrict i v)
  real i (v:S.Field (i+1)): S.conj h i (restrict i v)=restrict i (S.conj h _ v)

namespace Graded

def averageStep (h:R.Laws W H) (q:S.Field (d+1)→ₗ[ℂ] S.Field d) : S.Field (d+1)→ₗ[ℂ] S.Field d where
  toFun v := ∫ g:Ortho,R.act d g (q (R.act _ g⁻¹ v)) ∂spins
  map_smul' z v:= by have he(g:Ortho): R.act d g (q (R.act _ g⁻¹ (z•v)))= z • R.act d g (q (R.act _ g⁻¹ v)):=by rw [LinearEquiv.map_smul, q.map_smul,LinearEquiv.map_smul]
                     change (∫ g, R.act d g (q (R.act _ g⁻¹ (z•v)))∂spins)=z• ∫ g:Ortho,R.act d g (q (R.act _ g⁻¹ v)) ∂spins; simp_rw [he]; exact integral_smul (G:=S.Field d) z _
  map_add' v w:=by
    have hf (v:S.Field (d+1)) : Continuous (fun g:Ortho=>R.act d g (q (R.act _ g⁻¹ v))):=
       (label_movable h d).comp (continuous_id.prodMk (q.continuous_of_finiteDimensional.comp ((h.spin _ v).comp continuous_inv)))
    simp_rw [map_add]; exact integral_add (integrate_orbit _ (hf _)) (integrate_orbit _ (hf _))

lemma average_left (h:R.Laws W H) (q:S.Field (d+1)→ₗ[ℂ] S.Field d)
    (hq:(q.comp (W.rise (Nat.le_succ d)))=LinearMap.id)(v): averageStep H h q (W.rise (Nat.le_succ d) v)=v:=by
  unfold averageStep; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; simp_rw [h.filtered _ _ (Nat.le_succ d)]
  have ht(g:Ortho):q ((W.rise (Nat.le_succ d)) (R.act _ g v))=R.act _ g v:= LinearMap.congr_fun hq _
  simp [ht, ← h.group,h.fixes]

lemma average_rotate (h:R.Laws W H) (q:S.Field (d+1)→ₗ[ℂ] S.Field d) (k:Ortho)(v:S.Field (d+1)):
    averageStep H h q (R.act (d+1) k v)=R.act _ k (averageStep H h q v):=by
  let f(g:Ortho):= R.act d g (q (R.act (d+1) (g⁻¹) (R.act _ k v)))
  change (∫ g,f g ∂spins)=R.act d k (∫ g,R.act d g (q (R.act (d+1) g⁻¹ v)) ∂spins)
  rw [← left_mean k f]
  have he(g:Ortho): f (k*g) = R.act d k (R.act _ g (q (R.act (d+1) g⁻¹ v))):=by dsimp only [f]; rw [h.group d,mul_inv_rev, ← h.group (d+1), mul_assoc, inv_mul_cancel, mul_one]
  simp_rw [he]
  exact ((LinearMap.toContinuousLinearMap (R.act d k).toLinearMap).integral_comp_comm
       (integrate_orbit _ ((label_movable h d).comp (continuous_id.prodMk (q.continuous_of_finiteDimensional.comp ((h.spin _ v).comp continuous_inv))))))

lemma available (H':S.Symmetric)(hW:W.Inclusions S)(h:R.Laws W H)(hO:W.Orientation H): Nonempty (Graded W R H):=by
  choose q hq using fun i=> (W.rise (Nat.le_succ i)).exists_leftInverse_of_injective (ker_eq_bot.mpr (W.inject H' hW _))
  refine ⟨⟨fun i=>parity H (averageStep H h (q i)),fun i v=>?_,fun i k v=>?_,fun i=>parity_real H _⟩⟩
  · simp [parity,hO.realInc,average_left H h (q i) (hq i),S.reflect_star]; module
  · simp [parity,h.real,average_rotate H h (q i)]

variable (s:Graded W R H)
def grade:∀ i:ℕ,Submodule ℂ (S.Field i)
 | 0=>⊤
 | i+1 => LinearMap.ker (s.restrict i)
abbrev Pure (i:ℕ) := ↥(s.grade H i)

def high (i:ℕ):S.Field i→ₗ[ℂ] s.Pure H i:= match i with
 | 0 => (LinearMap.id).codRestrict ⊤ (fun _=>trivial)
 | i+1 => (LinearMap.id-(W.rise (Nat.le_succ i)).comp (s.restrict i)).codRestrict
     (grade H s (i+1)) (fun v=> by change s.restrict i (v-_)=0;rw [map_sub,LinearMap.comp_apply,s.left]; exact sub_self _)

/-- Projection to exact filtration weight, before injection back into a larger horizon. -/
def readGrade (j:ℕ) : ∀ i:ℕ, S.Field i→ₗ[ℂ] s.Pure H j
 | 0 => if h:j=0 then h.symm ▸ s.high H 0 else 0
 | i+1 => if h:j=i+1 then h.symm ▸ s.high H (i+1) else if _h:i+1<j then 0 else (readGrade j i).comp (s.restrict i)

lemma read_last (i:ℕ) : readGrade H s i i=high H s i:=by cases i <;> simp [readGrade]

lemma read_larger {j i:ℕ} (h:i<j): readGrade H s j i=0:=by
  have hj:j≠i:= ne_of_gt h
  cases i <;> simp [readGrade,hj,h]

lemma read_lt {j i:ℕ}(h:j ≤ i): readGrade H s j (i+1)=(s.readGrade H j i).comp (s.restrict i):=by
  have ht:j≠i+1:= by omega
  simp [readGrade,ht,Nat.not_lt.mpr (le_of_lt (lt_of_le_of_lt h (Nat.lt_succ_self _)))]

def extend (i j:ℕ) (v : S.Field j) : S.Field i :=
    if h:j ≤ i then W.rise h v else 0
lemma extend_with (i j:ℕ) (h:j ≤ i) (v:S.Field j): extend (W:=W) i j v=W.rise h v:=dif_pos h -- name collides? namespace okay

lemma expand (H':S.Symmetric)(hW:W.Inclusions S) (i:ℕ) (v:S.Field i):
    (∑ j∈Finset.range (i+1),extend (W:=W) i j ((readGrade H s j i v:S.Field j)))=v:=by
  induction i with
  | zero=> simp [extend,read_last,H',hW,W.arrival,high]; rfl
  | succ i ih=>
    rw [Finset.sum_range_succ,read_last, extend_with _ _ (Nat.le_refl _) _,W.arrival H' hW]
    suffices ∑ j∈Finset.range (i+1),extend (W:=W) (i+1) j ((readGrade H s j (i+1) v:S.Field j))=W.rise (Nat.le_succ _) (s.restrict i v) by rw [this]; change _ + (v-_) = _; rw [LinearMap.comp_apply]; abel
    rw [← ih (s.restrict _ v),map_sum]
    refine Finset.sum_congr rfl fun j hm=>?_; have ht:=Finset.mem_range_succ_iff.mp hm
    rw [extend_with _ _ ht, extend_with _ _ (Nat.le_trans ht (Nat.le_succ _)),W.transit H' hW,read_lt _ _ ht]
    rfl

lemma restrict_compat (H':S.Symmetric)(hW:W.Inclusions S){j i:ℕ}(h:j ≤ i)(v:S.Field j): s.restrict i (W.rise (Nat.le_trans h (Nat.le_succ _)) v)=W.rise h v:=by rw[← W.transit H' hW h (Nat.le_succ _),s.left]
lemma read_compat (H':S.Symmetric)(hW:W.Inclusions S)(k:ℕ) {j i:ℕ}(h:j ≤ i)(v:S.Field j):s.readGrade H k i (W.rise h v)=s.readGrade H k j v:=by
  induction i with
  | zero=> have hv:j=0:= Nat.eq_zero_of_le_zero h;subst j;rw [W.arrival H' hW]
  | succ i ih=>
    by_cases hv:j=i+1
    · subst j; rw [W.arrival H' hW]
    have ht:j ≤ i:=by omega
    rw [readGrade]
    split_ifs with hh hhh
    · subst k; have hk:= show j < i+1 by omega
      rw [read_larger _ _ hk]; change s.high H _ _=0; apply Subtype.ext; change W.rise h v-W.rise (Nat.le_succ i) (s.restrict i (W.rise _ v))=0; rw [restrict_compat H s H' hW ht, W.transit H' hW,sub_self]
    · rw [read_larger _ _ (lt_of_le_of_lt h hhh)]; rfl
    change s.readGrade H k i (s.restrict i (W.rise _ v))=_; rw [restrict_compat H s H' hW ht, ih ht]

lemma read_rotate (g:Ortho) (j i:ℕ)(x:S.Field i) (h:R.Laws W H) : R.act j g (s.readGrade H j i x)=s.readGrade H j i (R.act i g x):=by
  induction i with
  | zero=> by_cases hv:j=0; · subst j; rw [read_last]; rfl
           rw [read_larger _ _ (by omega:0<j)];change R.act j g 0=0;rw [map_zero]
  | succ i ih=>
    by_cases hv:j=i+1
    · subst j; rw [read_last]; change R.act _ g (x-_) = _ - W.rise _ (s.restrict _ _);rw [map_sub,LinearMap.comp_apply,_root_.YM.Table.Rotation.Laws.filtered h, s.rotate]; rfl
    by_cases hk:j ≤ i
    · rw [read_lt H s hk]; change R.act j g (s.readGrade H j i (s.restrict i _))=s.readGrade H j i (s.restrict i _); rw [s.rotate, ih]
    rw [read_larger _ _ (by omega:i+1<j)];change R.act j g 0=0;rw [map_zero]

lemma read_real (j i:ℕ)(x:S.Field i) (h:W.Orientation H) : S.conj H j (s.readGrade H j i x)=s.readGrade H j i (S.conj H i x):=by
  induction i with
  | zero=> by_cases hv:j=0; · subst j; rw [read_last]; rfl
           rw [read_larger _ _ (by omega:0<j)];change S.conj H j 0=0;rw [map_zero]
  | succ i ih=>
    by_cases hv:j=i+1
    · subst j; rw [read_last]; change S.conj _ _ (x-_) = _ - W.rise _ (s.restrict _ _);rw [map_sub,LinearMap.comp_apply,h.realInc, s.real]; rfl
    by_cases hk:j ≤ i
    · rw [read_lt H s hk]; change S.conj H j (s.readGrade H j i (s.restrict i _))=s.readGrade H j i (s.restrict i _); rw [← s.real, ih]
    rw [read_larger _ _ (by omega:i+1<j)];change S.conj H j 0=0;rw [map_zero]
end Graded
end YM.Contacts

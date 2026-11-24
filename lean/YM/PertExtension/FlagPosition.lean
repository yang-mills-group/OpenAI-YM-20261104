import YM.PertExtension.MomentFrame

/-! Real unit-, signed-coordinate- and filtration-preserving position solves
on the common field quotient. Scoped to one field horizon; compatibility
when restricting needs the nested choices. No assumed scalar stabilizer
absence for the physical comparator.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace YM.PertExtension.Physical
open Set Filter Function Table Labels Extraction Climb Position Next.UVStress Ward
open MeasureTheory
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {G : Gauge}{C : Family G}{f : Order}{S : Table C.book}{L:Register G}
variable {d : ℕ}{J : Type*}[Fintype J]{P : Type*}{arity : P→ℕ}

def operator (b : Module.Basis J ℂ ((Bel L).Field d))(K : FrameAt J ℝ) : Module.End ℂ ((Bel L).Field d) :=
  (Finsupp.linearCombination ℂ (columns b K)).comp b.repr.toLinearMap
@[simp] lemma operator_basis (b : Module.Basis J ℂ ((Bel L).Field d))(K) (i) :
    operator b K (b i) = columns b K i := by simp [operator]

lemma operator_add (b : Module.Basis J ℂ ((Bel L).Field d))(K A) : operator b (A+K)=operator b A+operator b K :=
  b.ext fun j=>by simp [columns,add_smul,Finset.sum_add_distrib]
lemma operator_scale (b : Module.Basis J ℂ ((Bel L).Field d))(K)(x:ℝ) :
    operator b (x•K)=(x:ℂ) • operator b K :=
  b.ext fun j=>by simp [columns,smul_eq_mul,Finset.smul_sum,mul_smul]

abbrev diag (J:Type*) := (fun i j:J=>if i=j then (1:ℝ) else 0)
@[simp] lemma operator_identity (b : Module.Basis J ℂ ((Bel L).Field d)) :
    operator b (diag J) = LinearMap.id :=
  b.ext fun j=>by simp only [operator_basis,LinearMap.id_coe,id_eq]; simp [columns,diag]

def matrixOp (b : Module.Basis J ℂ ((Bel L).Field d)) :
    FrameAt J ℝ →ₗ[ℝ] Module.End ℂ ((Bel L).Field d) where
  toFun := operator b
  map_add' := fun x y=>operator_add b y x
  map_smul' := fun a x=> (operator_scale b x a).trans (RCLike.real_smul_eq_coe_smul a (operator b x)).symm

variable (b : Module.Basis J ℂ ((Bel L).Field d)) (V : DiffPlan (Bel L))(H : (Bel L).Hierarchy)

def respects (K : FrameAt J ℝ) := (∀ k:Signed,(operator b K).comp ((Bel L).mirror H.spin d k)=((Bel L).mirror H.spin d k).comp (operator b K)) ∧
    (∀ e (he:e≤d), LinearMap.range ((operator b K).comp (V.rise he)) ≤ LinearMap.range (V.rise he))
structure AtUnit (K : FrameAt J ℝ) : Prop where
  unit : operator b K ((Bel L).unit d)=(Bel L).unit d
  filters : respects b V H K

lemma identity_respects : AtUnit b V H (diag J) := by
  constructor <;> simp [respects]

/-- H- and filtration preserving real Lie variations in this basis.
Use a real-label basis on the physical quotient. -/
def variations : Submodule ℝ (FrameAt J ℝ) where
  carrier := {K | operator b K ((Bel L).unit d)=0 ∧ respects b V H K }
  add_mem' {x y} := by
    intro ⟨hx,hm,hl⟩ ⟨hy,hn,hr⟩
    change _ ∧ _ ∧ _
    simp_rw [operator_add];
    constructor; · simp [hx,hy]
    refine ⟨fun k=> LinearMap.ext fun v=>by
             simp only [LinearMap.comp_apply,LinearMap.add_apply,_root_.map_add]
             exact congr_arg₂ _ (DFunLike.congr_fun (hm k) v) (DFunLike.congr_fun (hn k) v),?_⟩
    intro e he v hp;obtain ⟨v,rfl⟩:=hp
    exact Submodule.add_mem _ (hl e he (LinearMap.mem_range_self _ _)) (hr e he (LinearMap.mem_range_self _ _))
  zero_mem' := by
    have he : operator b (0 : FrameAt J ℝ)=0:= b.ext fun i=>by simp [columns]
    simp only [respects,Set.mem_setOf, he, LinearMap.zero_apply,true_and]
    exact ⟨by simp,by simp⟩
  smul_mem' {K A} := by
    rintro ⟨hu,hs,hf⟩
    change (operator b (K • A) _ = 0) ∧ _
    simp_rw [respects,operator_scale,LinearMap.smul_apply,hu,smul_zero,true_and]
    refine ⟨fun k=>LinearMap.ext fun v=>?_,?_⟩
    · simp_rw [LinearMap.comp_apply,LinearMap.smul_apply, map_smul]; exact congr_arg _ (congr($(hs k) v))
    intro e he v hv;obtain ⟨v,rfl⟩:=hv
    exact Submodule.smul_mem _ _ (hf e he (LinearMap.mem_range_self _ _))

include H V b in
lemma add_variation {K A} (hK : AtUnit b V H K)(hA : A∈variations b V H) :
    AtUnit b V H (K+A) := by
  obtain ⟨h,hs,hf⟩:=hA
  constructor
  · rw [operator_add,LinearMap.add_apply,h,hK.unit,add_zero]
  unfold respects; simp_rw [operator_add]
  obtain ⟨ht,hv⟩:= hK.filters
  refine ⟨fun s=>(LinearMap.ext fun x=>by simpa using congr_arg₂ (·+·) (DFunLike.congr_fun (ht s) x) (DFunLike.congr_fun (hs s) x)),?_⟩
  intro e he v hp; obtain ⟨v,hp⟩:=hp
  rw [←hp,LinearMap.comp_apply,LinearMap.add_apply]
  exact Submodule.add_mem _ (hv e he (LinearMap.mem_range_self _ _)) (hf e he (LinearMap.mem_range_self _ _))

lemma columns_reality {K} (hb:∀ i,(Bel L).conj H.spin d (b i)=b i) :
    ((Bel L).conj H.spin d).comp (operator b K)=(operator b K).comp ((Bel L).conj H.spin d) :=
   b.ext fun i=>by simp only [LinearMap.comp_apply,operator_basis,hb,columns,_root_.map_sum, map_smulₛₗ]; simp

lemma sampled_flag (A : Actual C f S)(c:Module.Basis J ℂ ((Bel C.book).Field d))(D : TestSystem J Profile Profile.n)
    (hb:∀ i,(Bel C.book).conj A.M.hT.spin d (c i)=c i) (hk : AtUnit c A.M.T.W A.M.hT D.baseline)
    (hV : D.Z ≤ variations c A.M.T.W A.M.hT) {y:FrameAt J ℝ}
    (hy : y-D.baseline∈D.Z) :
   ∀ᶠ k : ℕ in atTop,
      let f := ((A.curve.U k d).toLinearMap.comp (operator c y))
      f ((Bel C.book).unit d) = S.unit d ∧
      (∀ s,LinearMap.comp (S.mirror A.F.room.kernel.spin d s) f=f.comp ((Bel C.book).mirror A.M.hT.spin d s)) ∧
      (S.conj A.F.room.kernel.spin d).comp f=f.comp ((Bel C.book).conj A.M.hT.spin d) ∧
      (∀ e (he:e≤d),LinearMap.range (f.comp (A.M.T.W.rise he)) ≤ LinearMap.range (A.E.rise he)) := by
  have hj : AtUnit c A.M.T.W A.M.hT y:= by simpa using add_variation c A.M.T.W A.M.hT hk (hV hy)
  have hv : ∀ᶠ k in atTop,∀ e∈Finset.range (d+1),∀ h : e≤d,∀ v_, A.curve.U k d (A.M.T.W.rise h v_)=A.E.rise h (A.curve.U k e v_) :=
     (eventually_all_finset (Finset.range (d+1))).mpr fun e he=>
       (A.aligned.rises e d (Nat.le_of_lt_succ (Finset.mem_range.mp he))).mono (fun i hi _=>hi)
  filter_upwards [A.aligned.units d,A.aligned.hsym d,hv] with k hu hr he
  intro f
  constructor
  · exact (by change (A.curve.U k d) (operator c y _) = _; rw [hj.unit,hu])
  refine ⟨?signed,?realCase,?_⟩
  case signed =>
    intro s; exact LinearMap.ext fun v=> by
      change (S.mirror A.F.room.kernel.spin d s) ((A.curve.U k d) _) = (A.curve.U k d) _
      rw [← hr.1 s]
      exact congr_arg _ (DFunLike.congr_fun (hj.filters.1 s) v).symm
  case realCase =>
    exact LinearMap.ext fun v=>by
      change S.conj A.F.room.kernel.spin d ((A.curve.U k d) _)=(A.curve.U k d) _
      rw [← hr.2]; exact congr_arg (A.curve.U k d) (DFunLike.congr_fun (columns_reality c A.M.hT hb (K:=y)) v)
  intro e hev v hv
  obtain ⟨v,rfl⟩:=hv
  obtain ⟨p,hp⟩:= hj.filters.2 e hev (LinearMap.mem_range_self _ v)
  exact ⟨A.curve.U k e p, ((he e (Finset.mem_range.mpr (Nat.lt_succ_of_le hev)) hev p).symm.trans (congr_arg (A.curve.U k d) hp))⟩

variable {b}
lemma eventual_basis {D:TestSystem J P arity} {x : ℕ→FrameAt J ℝ} (h : Tendsto x atTop (𝓝 D.baseline))(hk : Bijective (operator b D.baseline)):
    ∀ᶠ k in atTop,Bijective (operator b (x k)) := by
  let f := ((LinearMap.toContinuousLinearMap : Module.End ℂ ((Bel L).Field d) ≃ₗ[ℂ] ((Bel L).Field d →L[ℂ] _)).toLinearMap.restrictScalars ℝ).comp (matrixOp b)
  have he : IsUnit (f D.baseline) := ContinuousLinearMap.isUnit_iff_bijective.mpr hk
  letI : ContinuousSMul ℝ ((Bel L).Field d →L[ℂ] (Bel L).Field d) := IsScalarTower.continuousSMul ℂ
  have hz : ∀ᶠ x in 𝓝 (f D.baseline),x∈{y|IsUnit (y : (Bel L).Field d →L[ℂ] (Bel L).Field d)}:= (Units.isOpen (R:= (Bel L).Field d →L[ℂ] (Bel L).Field d)).mem_nhds he
  filter_upwards [(f.continuous_of_finiteDimensional.continuousAt.tendsto.comp h).eventually hz] with k (hk:IsUnit (f (x k)))
  exact ContinuousLinearMap.isUnit_iff_bijective.mp hk

end YM.PertExtension.Physical

import YM.WilsonCoeffUV.Test.Measure
/-!
# Integral-address currency (distinct markers)

The Banach object is the *dual of the tensor table* on the stipulated
closed address cells. Products in distinct markers naturally have these
budgets (not just a testwise lim sup). See measure adapters in this run.
No assertion about realignment on interacting masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Wheel
open Filter Function Set Lattice RG Embroider Embroider.Canvas
open scoped Topology BigOperators ContDiff
variable {ι:Type} {D d : ι→ℕ}
variable {j i d':ι} {J K S T R:Finset ι}

abbrev Plot (D : ι→ℕ) := ∀ i : ι, Knob (D i) × Chamber
abbrev Case (D : ι→ℕ):= ∀ i : ι, Volume (D i)
abbrev Pier (D : ι→ℕ):= C(Plot D,ℝ)
open ContinuousMap

def slice (v:Volume (D d')) (x:Knob (D d') × Chamber) :ℝ:= v.val x.1 x.2
lemma slice_ct (v:Volume (D i)) : Continuous (slice v):= by
    unfold slice
    refine continuous_iff_continuousAt.mpr fun x=>?_
    have he: (fun y:Knob (D i) × Chamber=> v.val y.1 y.2)=ᶠ[𝓝 x] fun y=> v.val x.1 y.2 := by
       filter_upwards [(continuous_fst.tendsto x).eventually (show ∀ᶠ u in 𝓝 x.1,u=x.1 by rw [nhds_discrete]; simp)] with y hy; simp_rw [show y.1=x.1 from hy]
    exact ((map_continuous (v.val x.1)).comp continuous_snd).continuousAt.congr he.symm

def folio (A:Case D) (J:Finset ι) : Pier D := ⟨fun x=>∏ i∈J, slice (A i) (x i), continuous_finsetProd J fun i _=> (slice_ct _).comp (continuous_apply i)⟩
lemma folio_split[DecidableEq ι] (A:Case D)(h:J⊆S)(x:Plot D) : folio A S x = folio A J x*folio A (S\J) x:= by rw [mul_comm]; exact (Finset.prod_sdiff h).symm
lemma folio_norm [Fintype ι](A:Case D): ‖folio A J‖≤∏ i∈J,‖A i‖:=by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr; intro x
    rw [show folio A J x=∏ i∈J,slice (A i) (x i) from rfl,norm_prod]; exact Finset.prod_le_prod (fun i _=>norm_nonneg _) fun i _=> registry _ _ _

def area (D:ι→ℕ)(J:Finset ι) := Submodule.span ℝ (range (fun A:Case D=> folio A J))
abbrev Table (D:ι→ℕ)(J:Finset ι):= ↥(Submodule.span ℝ (range (fun A:Case D=> folio A J)))
scoped instance : NormedAddCommGroup (Table D S):= inferInstance
scoped instance : NormedSpace ℝ (Table D S):= inferInstance
abbrev Pen (D:ι→ℕ)(J:Finset ι):= Table D J →L[ℝ]ℝ

def seaMark (A:Case D)(J:Finset ι): Table D J:= ⟨_,Submodule.subset_span (mem_range_self A)⟩
def touch {D}(A:Case D)(J:Finset ι) : Pen D J →L[ℝ]ℝ:= (ContinuousLinearMap.apply ℝ ℝ) (seaMark A J)
@[simp] lemma hit_leaf {A:Case D}(x:Pen D J): touch A J x=x (seaMark A J):= rfl
lemma pen_inj (x y : Pen D J)(h:∀ A,touch A J x=touch A J y): x=y:=by
    apply ContinuousLinearMap.ext; rintro ⟨v,hv⟩
    refine Submodule.span_induction (fun w hw => ?_) ?_ (fun _ _ ha hb a b=>?_) (fun i w e f=>?_) hv
    · obtain ⟨A,rfl⟩:= hw; exact h A
    · change x 0 = y 0; rw [map_zero, map_zero]
    · change x ((⟨_,ha⟩: Table D J)+⟨_,hb⟩)=y ((⟨_,ha⟩: Table D J)+⟨_,hb⟩); rw [map_add,map_add,a,b]
    change x (i • ⟨w,e⟩) = y (i • ⟨w,e⟩); rw [map_smul,map_smul,f]
variable [DecidableEq ι]

private def marks (J:Finset ι)(y x:Plot D)(i:ι):= if i∈J then x i else y i
private lemma mark_ct (J:Finset ι)(p: Plot D): Continuous (marks J p):=continuous_pi fun i => by
   by_cases t:i∈J
   · simpa only [marks,t, ↓reduceIte] using (continuous_apply i: Continuous (fun u : Plot D=> u i))
   simp only [marks,t,↓reduceIte]; exact continuous_const

private def boxL (J:Finset ι)(x:Plot D): Pier D →ₗ[ℝ] Pier D where
   toFun f:= ContinuousMap.comp f ⟨_,mark_ct J x⟩
   map_add' _ _:=rfl
   map_smul' _ _:=rfl

lemma boxL_single (A:Case D)(h:J⊆S)(x:Plot D) : boxL J x (folio A S)= folio A (S\J) x • folio A J:=by
    ext y; change folio A S (marks J x y)= _* _; rw [folio_split _ h,mul_comm]; congr 1
    · exact Finset.prod_congr rfl fun i hi => by simp [marks,(Finset.mem_sdiff.mp hi).2]
    exact Finset.prod_congr rfl fun i hi=>by simp [marks,hi]
lemma boxL_area (h:J⊆S)(x:Plot D) (v:Pier D) (hv:v∈ area D S): boxL J x v∈ area D J:=by
    induction hv using Submodule.span_induction with
    | mem z e=> obtain ⟨A,rfl⟩:=e; rw [boxL_single _ h]; exact Submodule.smul_mem _ _ ((seaMark A J).property)
    | zero=> rw [map_zero]; apply Submodule.zero_mem
    | add u v hu hv ih hp=> rw [map_add]; exact Submodule.add_mem _ ih hp
    | smul a z h hb=> rw [map_smul]; exact Submodule.smul_mem _ a hb

def boxC {D}(h:J⊆S)(x: Plot D): Table D S →ₗ[ℝ]Table D J where
    toFun v:=⟨boxL J x v.val,boxL_area h x v.val v.property⟩
    map_add' _ _:= Subtype.ext rfl
    map_smul' _ _:= Subtype.ext rfl

lemma boxC_norm (h:J⊆S)(x:Plot D)(p:Table D S): ‖boxC h x p‖ ≤ ‖p‖:= (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun y=> ContinuousMap.norm_coe_le_norm (p.val) (marks J x y)
lemma boxC_leaf (h:J⊆S)(x:Plot D)(v:Case D): boxC h x (seaMark v S)=folio v (S\J) x • seaMark v J:= Subtype.ext (boxL_single v h x)

lemma sliced_area (h:J⊆S)(p: Pen D J) (u:Table D S):∃ v:Table D (S\J),∀ x : Plot D,p (boxC h x u)=v.val x:=by
    cases u with
    | mk u he=>
        refine Submodule.span_induction ?_ ?_ ?_ ?_ he
        · rintro _ ⟨v,rfl⟩
          refine ⟨p (seaMark v J) • seaMark v (S\J),fun x=>?_⟩; change p (boxC h x (seaMark v S))= p (seaMark v J)*folio v (S\J) x; rw [boxC_leaf,map_smul]; exact mul_comm ..
        · refine ⟨0,fun x=>?_⟩; change p (boxC h x 0)=0; rw [map_zero,map_zero]
        · rintro a b ha hb ⟨A,he⟩ ⟨B,hf⟩; refine ⟨A+B,fun x=>?_⟩; change p (boxC h x ((⟨_,ha⟩: Table D S)+⟨_,hb⟩))= _+_; rw [map_add,map_add,he,hf]
        rintro c a ha ⟨A,hA⟩; refine ⟨c • A,fun x=>?_⟩; change p (boxC h x (c • (⟨_,ha⟩:Table D S)))= _*_; rw [map_smul,map_smul,hA]; rfl

def stone (h:J⊆ S)(p: Pen D J)(u:Table D S): Table D (S\J):=(sliced_area h p u).choose
lemma stone_v (h:J⊆ S)(p: Pen D J)(u:Table D S)(x): (stone h p u).val x=p (boxC h x u):=((sliced_area h p u).choose_spec x).symm
private def slate (h:J⊆S)(p: Pen D J): Table D S→ₗ[ℝ]Table D (S\J) where
   toFun:=stone h p
   map_add' a b:= Subtype.ext (ContinuousMap.ext fun x=> by change (stone _ _ _).val _= (stone _ _ _).val _+(stone _ _ _).val _; rw [stone_v,map_add,map_add, stone_v,stone_v])
   map_smul' a b:=Subtype.ext (ContinuousMap.ext fun x=> by change (stone _ _ _).val _= a • (stone _ _ _).val _; rw [stone_v,map_smul,map_smul,stone_v])
lemma slate_norm (h:J⊆ S)(p: Pen D J)(u:Table D S): ‖slate h p u‖≤‖p‖*‖u‖:=by
   change ‖(stone h p u).val‖ ≤_; apply (ContinuousMap.norm_le _ (by positivity)).mpr; intro y; rw [stone_v]; exact (p.le_opNorm _).trans (mul_le_mul_of_nonneg_left (boxC_norm h y u) (norm_nonneg _))

def rock (h:J⊆ S)(p: Pen D J): Table D S→L[ℝ] Table D (S\J):= (slate h p).mkContinuous ‖p‖ (slate_norm h p)
lemma rock_norm (h:J⊆ S)(p: Pen D J): ‖rock h p‖≤‖p‖:= LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
lemma rock_leaf (h:J⊆ S)(p: Pen D J)(x:Case D): rock h p (seaMark x S)=p (seaMark x J) • seaMark x (S\J):=Subtype.ext (ContinuousMap.ext fun y => by change (stone _ _ _).val _=p (seaMark x J)*folio _ (S\J) y; rw [stone_v,boxC_leaf,map_smul]; exact mul_comm ..)

def joy (h:J ⊆ S)(p:Pen D J)(q:Pen D (S\J)): Pen D S:= q.comp (rock h p)
lemma joy_norm (h:J⊆ S)(p:Pen D J)(q:Pen D (S\J)): ‖joy h p q‖≤ ‖p‖*‖q‖:=by rw [mul_comm]; exact (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_mul_of_nonneg_left (rock_norm h p) (norm_nonneg _))
lemma joy_p (h:J⊆ S)(p:Pen D J)(q:Pen D (S\J))(x:Case D): touch x S (joy h p q)= touch x J p * touch x (S\J) q:=by rw [hit_leaf,joy,ContinuousLinearMap.comp_apply,rock_leaf,map_smul]; rfl

end YM.WilsonCoeffUV.Wheel

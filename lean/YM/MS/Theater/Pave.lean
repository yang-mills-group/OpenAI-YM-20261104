import YM.MS.Theater.Scale
/-!
# Linearized variations by homogeneous jets with the physical metric. Unconstrained.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset MeasureTheory Real Maxwell
open Analysis Tensor Koszul Plane Landau Detect Local.BV InnerProductSpace
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {J E K:Type}[Fintype J]{G:Gauge}{h r n:ℕ}
   [NormedAddCommGroup E][NormedSpace ℝ E]
abbrev Feet (G:Gauge)(n:ℕ):= LightC Axis G n
abbrev Head (G:Gauge)(n:ℕ):= LightC Unit G n
-- derivative in axis
variable (G J) in
def snow (n:ℕ)(u:E4): LightC J G (n+1) →ₗ[ℝ] LightC J G n where
    toFun X:= ⟨fun i=>( (n+1:ℝ) • ( X.val i ).curryLeft u ), fun i x σ=> by change (( n+1:ℝ ) • (X.val i).curryLeft u) _=_; rw [smul_apply,smul_apply,freeze_sym _ (X.property i)] ⟩
    map_add' X Y:= by apply Subtype.ext; ext1 i; apply ContinuousMultilinearMap.ext; intro l; exact smul_add ..
    map_smul' c X:= by apply Subtype.ext; ext1 i; apply ContinuousMultilinearMap.ext; intro l; exact smul_comm (n+1:ℝ) c ( X.val i ( Fin.cons u l ) )
abbrev stepL (G:Gauge)(J:Type)(n:ℕ)(i:Axis):= snow J G n (basis i) -- variable order?
lemma workL (u:E4)(X:LightC J G (h+1))(i:J): diagonal ( ( snow J G h u X ).val i )= Analysis.D u ( diagonal ( X.val i ) ):= by
    funext x; rw [Analysis.D,differential_diagonal _ ( X.property i )]; change (h+1:ℝ) • ((X.val i).curryLeft u (fun _=>x))=_; norm_cast -- maybe no goals
lemma rot (i:J)(u p:E4)(v:G.Color): snow J G h u ( planeC i (h+1) p v )=(inner ℝ p u) • planeC i h p v:= by
    classical
    apply Subtype.ext; ext1 j; apply ContinuousMultilinearMap.ext; intro x; change (h+1:ℝ) • (planeC i (h+1) p v).val j (Fin.cons u x)=inner ℝ p u • ((planeC i h p v).val j x); by_cases he:j=i
    · rw [ he ]; change _= inner ℝ p u • ((planeC i h p v).val i _); rw [ wearing,wearing ]; rw [ Fin.prod_univ_succ ]; simp_rw [Fin.cons_zero,Fin.cons_succ ]; rw [ smul_smul ( h+1:ℝ ) ( amount _ ),periodC, mul_smul,smul_comm ]
    rw [ away (h+1) p v he, away h p v he ]; rw [ContinuousMultilinearMap.zero_apply,ContinuousMultilinearMap.zero_apply,smul_zero,smul_zero] -- change RHS notation map.PeQ
lemma step_at (i:J)(p: FourP)(a:Axis)(v:G.Color): stepL G J h a (speak (h+1) i p v)= (p a) • speak h i p v:= by unfold stepL speak; rw [ rot, lean_axis ]
lemma plane_x (i:J)(p: FourP)(a:ℝ)(v:G.Color): speak h i (a • p) v=a^h • speak h i p v:= by
    classical
    apply Subtype.ext; ext1 j; apply ContinuousMultilinearMap.ext; intro l; unfold speak; change _= a^h • ((planeC i h _ v).val j l); by_cases he:j=i; · rw [he]; rw [wearing,wearing,map_smul]; simp_rw [real_inner_smul_left,Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ,Fintype.card_fin,mul_smul,smul_comm (amount _)]
    rw [away h _ _ he,away h _ _ he]; simp
variable (G) in
def gradS (h:ℕ): Head G (h+1) →ₗ[ℝ] Feet G h where
    toFun X:= ⟨ fun i=> ( stepL G Unit h i X ).val (), fun i=> ( stepL G Unit h i X ).property () ⟩
    map_add' X Y:= by apply Subtype.ext; ext1 i; apply ContinuousMultilinearMap.ext; intro l; exact congr_arg (fun p:Head G h=> p.val () l) ( map_add ( stepL G Unit h i ) X Y )
    map_smul' c X:= by apply Subtype.ext; ext1 i; apply ContinuousMultilinearMap.ext; intro l; exact congr_arg (fun p:Head G h=> p.val () l ) ( map_smul ( stepL G Unit h i ) c X )
lemma grad_at(p:FourP)(v:G.Color): gradS G h ( speak (h+1) () p v )= ∑ i:Axis,(p i) • speak h i p v:= by
    apply Subtype.ext; ext1 i; rw [AddSubmonoidClass.coe_finsetSum,Finset.sum_apply]; rw [ Finset.sum_eq_single_of_mem i ( Finset.mem_univ _ ) ]; · change ( stepL G Unit h i _ ).val ()= _; rw [step_at]; apply ContinuousMultilinearMap.ext; intro l; change p i • ((speak h () p v).val () l) = p i • ((speak h i p v).val i l); simp_rw [ speak,wearing ];
    intro j hj ht; rw [ Submodule.coe_smul,Pi.smul_apply, speak,away h _ _ (Ne.symm ht),smul_zero]
-- contraction.Collar total coordinate x · form.S
omit [Fintype J] in
lemma light_ext (X Y:LightC J G h)(H:∀ i p,Tensor.diagonal ( X.val i ) p=Tensor.diagonal ( Y.val i ) p): X=Y:= by apply Subtype.ext; ext1 i; apply ext_diag _ _ ( X.property i ) ( Y.property i ) ( funext (H i) )
private def flatX (h:ℕ)(X:Feet G h): Head G (h+1):= ⟨ fun _=> ∑ a:Axis,added ( X.val a ) ( compAxis a ),fun i v σ=> by simp_rw [_root_.sum_apply, added_sym _ _ v σ]⟩
private lemma diagX (X:Feet G h)(i:E4): diagonal ( ( flatX h X ).val () ) i=∑ a:Axis,i a • diagonal ( X.val a ) i:= by unfold Tensor.diagonal; change (∑ a:Axis,added (X.val a) (compAxis a)) _=_; rw [_root_.sum_apply]; exact Finset.sum_congr rfl fun j _=>added_diag ..
def radialX (G:Gauge)(h:ℕ): Feet G h →ₗ[ℝ] Head G (h+1) where
    toFun := flatX h
    map_add' X Y:= by apply light_ext; rintro ⟨ ⟩ p; change _= diagonal ((flatX h X).val ()) p+diagonal ((flatX h Y).val ()) p; simp_rw [diagX]; simp [Finset.sum_add_distrib,Tensor.diagonal,smul_add]; -- omega
    map_smul' c X:= by apply light_ext; rintro ⟨ ⟩ p; change _= c • diagonal ((flatX h X).val ()) p; simp_rw [diagX, Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> smul_comm ( M:=ℝ ) _ c _ -- check field
lemma tBudget (X:Feet G h)(i:E4): diagonal ( ( radialX G h X ).val () ) i=∑ a:Axis,i a • diagonal ( X.val a ) i:= diagX ..
lemma depart (X:Head G (h+1)): radialX G h ( gradS G h X )=( h+1:ℝ ) • X:= by
    apply light_ext; rintro ⟨ ⟩ p; rw [ tBudget ]; change ∑ i:Axis,p i • diagonal ((stepL G Unit h i X).val ()) p=(h+1:ℝ) • _; simp_rw [stepL,workL]; change (∑ i,p i • grad i ( diagonal _ ) p)=_; rw [grad_euler (X.val ()) ( X.property () )]; push_cast; rfl
end YM.MS.Theater

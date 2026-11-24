import YM.WilsonCoeffUV.Marked.Step.Plot
/-!
# Address contraction, singles. The Engineering prefactor supplied separately.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Wheel
open Filter Function Set Lattice RG Embroider Embroider.Canvas
open scoped Topology BigOperators ContDiff
variable {ι:Type}{D : ι→ℕ}{J S:Finset ι}

section
variable (P:Patch)(p:ι→ Site P.L)
private def dent {i}(u:Knob (D i) × Chamber) := speck P ^ (u.1.1 : ℕ)
private def dentC (x:Plot D)(i:ι):= dent P (x i)
private lemma dentT {j:ι}: Continuous (fun v:Plot D=> dentC P v j) :=by
    let f (x: Knob (D j)) := speck P ^(x.1:ℕ)
    show Continuous (f ∘ Prod.fst ∘ _); exact continuous_of_discreteTopology.comp (continuous_fst.comp (continuous_apply j))
private lemma dent_bound (x:Plot D)(i): ‖dentC P x i‖≤ 1:=by unfold dentC dent; rw [norm_pow,Real.norm_eq_abs,abs_of_pos (speck_pos _)]; exact pow_le_one₀ (speck_pos P).le (speck_le P)
private def pointM (x:Plot D)(i:ι) : Knob (D i) × Chamber:=((x i).1,⟨_,tucks_enter P (p i) (x i).2⟩)
private lemma pointM_ct: Continuous (pointM P p (D:=D)):=by unfold pointM tucks; apply continuous_pi; intro v; fun_prop (disch:= intros; apply continuous_apply)
private def beams (J:Finset ι): Pier D →ₗ[ℝ] Pier D where
    toFun f:=⟨fun u=> (∏ i∈J,dentC P u i) • f (pointM P p u), (continuous_finsetProd J fun _ _ => dentT _).smul (f.continuous.comp (pointM_ct ..))⟩
    map_add' a b:= ContinuousMap.ext fun x=> smul_add ..
    map_smul' a b:=ContinuousMap.ext fun x=>by change (∏ i∈J,dentC P x i)*(a*b (pointM P p x))=a*((∏ i∈J,dentC P x i)*_); ring

def laid (A:Case D)(i:ι): Volume (D i) := foldWord P (p i) (D i) (A i)
lemma beams_v (J:Finset ι)(A: Case D) : beams P p J (folio A J)=folio (laid P p A) J:=by
    ext x; change (∏ i∈J, dentC _ x i)*(∏ i∈J, slice (A i) (pointM P p x i))=∏ i∈J,slice _ _; rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro i _
    unfold laid; obtain ⟨f,h⟩:=submitted (A i); rw [← h,observed]; exact (narrow P _ f (x i).1.snd (by have he: ((x i).1.1:ℕ)<D i+1:=(x i).1.1.isLt; omega) (x i).2.val).symm
private lemma beams_area {x:Pier D}(h:x∈area D J): beams P p J x∈area D J:=by
   induction h using Submodule.span_induction with
   | mem s e => obtain ⟨A,rfl⟩:=e; rw [beams_v]; exact (seaMark _ _).property
   | zero=> rw [map_zero]; apply Submodule.zero_mem
   | add a b ha hb h t=> rw [map_add]; exact Submodule.add_mem _ h t
   | smul a b hb h=> rw [map_smul]; exact Submodule.smul_mem _ _ h
private def beads (J:Finset ι)(D:ι→ℕ): Table D J →ₗ[ℝ] Table D J where
    toFun a:= ⟨_,beams_area P p a.property⟩
    map_add' a b:= Subtype.ext (map_add (beams P p J) a.val b.val)
    map_smul' c b:= Subtype.ext (map_smul (beams P p J) c b.val)
private lemma beads_bound (x:Table D J): ‖beads P p J D x‖≤1*‖x‖:=by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr; intro y
    change ‖(∏ i∈J,dentC P y i)* x.val (pointM P p y)‖ ≤ _; rw [norm_mul,norm_prod]
    exact mul_le_mul (Finset.prod_le_one (fun _ _=>norm_nonneg _) (fun _ _=> dent_bound ..)) (ContinuousMap.norm_coe_le_norm x.val _) (norm_nonneg _) zero_le_one

def beenL (D:ι→ℕ)(J:Finset ι) : Table D J→L[ℝ]Table D J:= (beads P p J D).mkContinuous 1 (beads_bound P p)
def mend (D:ι→ℕ)(J:Finset ι): Pen D J →L[ℝ] Pen D J := ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ (Table D J) (Table D J) ℝ) (beenL P p D J)
lemma mend_v (x:Pen D J)(A:Case D) : touch A J (mend P p D J x)= touch (laid P p A) J x:=congr_arg x (show beenL P p D J (seaMark A J)=seaMark (laid P p A) J from Subtype.ext (beams_v ..))
lemma mend_norm (D:ι→ℕ)(J:Finset ι): ‖mend P p D J‖≤1:=by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; rw [one_mul]
    change ‖x.comp (beenL P p D J)‖ ≤ ‖x‖; exact (ContinuousLinearMap.opNorm_comp_le x _).trans (mul_le_of_le_one_right (norm_nonneg _) (LinearMap.mkContinuous_norm_le _ zero_le_one _))
end

-- Singleton equivalence, rendered full ledger
private def dotV (D:ι→ℕ):Plot D:= fun _=> (⟨0,fun _=>0⟩,zeroC)
lemma folio_single {D}(i:ι)(p:Case D) : ‖folio p {i}‖=‖p i‖:=by
    apply le_antisymm
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr; intro x; simp only [folio,ContinuousMap.coe_mk,Finset.prod_singleton]; exact registry ..
    apply vote_cap _ (norm_nonneg _); intro j x; classical
    let p': Plot D:= update (dotV D) i (j,x); have h:=ContinuousMap.norm_coe_le_norm (folio p {i}) p'
    simpa only [folio,ContinuousMap.coe_mk,Finset.prod_singleton,p',update_self,slice] using h
section
variable [DecidableEq ι] (D:ι→ℕ) (i:ι)
def singlesL : Volume (D i) →ₗ[ℝ] Table D {i} where
    toFun X:=seaMark (update (0:Case D) i X) {i}
    map_add' a b:= by
        apply Subtype.ext; ext x; change folio _ _ _=folio _ _ _+folio _ _ _; simp [folio,slice]
    map_smul' a b:=by apply Subtype.ext; ext x; change folio _ _ _=_*folio _ _ _; simp [folio,slice]
lemma loneC (x: Volume (D i)): ‖singlesL D i x‖=‖x‖:=by change ‖folio _ _‖=_; rw [folio_single,update_self]
lemma loneA (x:Case D) : singlesL D i (x i)=seaMark x {i}:=Subtype.ext (ContinuousMap.ext fun y=>by change folio _ _ _=_; change _ = folio _ _ _; simp [folio])
lemma loneS : Surjective (singlesL D i):=by
    rintro ⟨x,h⟩; induction h using Submodule.span_induction with
    | mem s e=> obtain ⟨A,rfl⟩:=e; exact ⟨_,loneA D i A⟩
    | zero=> exact ⟨0,map_zero _⟩
    | add a b ha hb h t=> obtain ⟨w,hw⟩:= h; obtain ⟨x,hx⟩:=t; exact ⟨w+x,Eq.trans (map_add ..) (congr_arg₂ (·+·) hw hx)⟩
    | smul p a he h=> obtain ⟨x,hx⟩:=h; exact ⟨p•x,Eq.trans (map_smul _ p _) (congr_arg (p • ·) hx)⟩

def singletonL : Volume (D i) ≃ₗᵢ[ℝ] Table D {i}:= .ofSurjective (show Volume _ →ₗᵢ[ℝ] _ from ⟨singlesL ..,loneC D i⟩) (loneS D i)
private abbrev pav := (singletonL D i).symm.toContinuousLinearEquiv.toContinuousLinearMap

def petal : Vote (D i)→L[ℝ] Pen D {i}:= ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ (Table D {i}) (Volume (D i)) ℝ) (pav D i)
lemma petal_hit (v: Vote (D i))(A:Case D): touch A {i} (petal D i v)= v (A i):=congr_arg v ((singletonL D i).symm_apply_eq.mpr (loneA D i A).symm)
lemma petal_bound : ‖petal D i‖ ≤1:=by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; rw [one_mul]
    change ‖x.comp (pav D i)‖ ≤ ‖x‖; refine le_trans (ContinuousLinearMap.opNorm_comp_le ..) (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_)); intro x; rw [one_mul]; exact ((singletonL ..).symm.norm_map x).le
end

def ochre (D:ι→ℕ): Pen D ∅:=(ContinuousMap.evalCLM ℝ (dotV D)).comp (Submodule.subtypeL _)
lemma ochre_v {D:ι→ℕ}(A:Case D): touch A ∅ (ochre D)=1:=by change folio A ∅ (dotV D)=1; simp [folio]

end YM.WilsonCoeffUV.Wheel

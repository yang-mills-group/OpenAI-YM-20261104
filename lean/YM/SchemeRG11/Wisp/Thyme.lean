import YM.SchemeRG11.Wisp.Dart
import YM.SchemeRG11.Cover.Table
/-! Soft budget χ integration of Ward. Compact support. Exact before Taylor. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.North
open Function Lattice Pert Maxwell Flock Bare Tree Bark Haze Pile Atoll Crest Labels MvPolynomial RawLabels
open scoped Classical Pointwise
variable {G:Gauge}
variable (χ:Cover→ℝ)(s:Finset Cover)
def parade : Finset (Shaft G):=(s ×ˢ Finset.univ) ×ˢ Finset.univ
def brim (p:Shaft G):Touch G:= ∑ i:Axis,(χ (p.1.1-step i)-χ p.1.1) • intake (p.1.1-step i) i p.1.2 p.2
def edgeT(p:Shaft G):= χ p.1.1 • radius p + brim χ p
def escort : vellum G:= ∑ z∈s,χ z • ∑ i:Axis,∑ j:Axis, Tree.cost z i j
lemma fearless (x:Cover)(i j:Axis): (land G).heat (Tree.cost x i j)=Tree.cost x i j:=by apply Acorn.vapid; rintro a b h; exact if_neg (fun w=>h w.1)
lemma warm : (land G).heat (escort χ s)=escort χ s:=by unfold escort; simp only [_root_.map_sum,map_smul,fearless]
lemma billT(p:Shaft G)(A:Bevy G.Color): sense (cant (linkup A)) (edgeT χ p) = ∑ i:Axis,(χ (p.1.1-step i)*Flock.bend A i p.1.2 (p.1.1-step i) p.2-χ p.1.1* Flock.bend A i p.1.2 p.1.1 p.2):=by
 unfold edgeT radius brim; simp only [map_add,map_smul,map_neg,map_sum,map_sub,speak,intake_g,smul_eq_mul, mul_neg]; rw [Finset.mul_sum,← Finset.sum_neg_distrib,←Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; ring
def covers:Prop:=∀ x∉s, χ x=0∧∀i:Axis,χ (x-step i)=0
lemma billTotal(A B:Bevy G.Color)(h:covers χ s):∑ p∈parade (G:=G) s,sense (cant (linkup A)) (edgeT χ p)*cant (linkup B) p = ∑x∈s,χ x *(∑ i:Axis,∑ j:Axis,if i<j then inner ℝ (Flock.bend A i j x) (Flock.bend B i j x) else 0):=by
 rw [groove_i χ s h]; simp_rw [billT,parade, Finset.sum_product, color_inner]; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro j _; simp_rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro k _; rw [sub_mul,mul_assoc,mul_assoc];rfl
lemma tariff(θ: Cover→ G.Color)(h:covers χ s): vent (cant (ascent θ)) (escort χ s)=-(1/2:ℝ) • ∑ p∈parade s, leaf (edgeT χ p)*leaf (drift θ p):=by
 apply viewers; intro A; let f:= linkup.symm A; let g:= linkup.symm (spur θ A)
 have he (x i j): aeval (cant A) (vent (cant (ascent θ)) (Tree.cost x i j))= -(1/2:ℝ) * (if i<j then inner ℝ (Flock.bend f i j x) (Flock.bend g i j x) else 0):=by
   by_cases h:i<j
   · rw [wardFace _ _ _ A θ h, if_pos h,signFace]
     have hh(x i j)(A:trunk G ℤ): First.curlAt x i j A=Flock.bend (linkup.symm A) i j x:=by have w:= intake_g x i j (linkup.symm A); rw [LinearEquiv.apply_symm_apply] at w; exact w -- def?
     rw [hh,hh]
   rw [Tree.cost, if_neg h,if_neg h,map_zero,map_zero,mul_zero]
 unfold escort; simp only [map_smul,(vent (cant (ascent θ))).map_smul,map_sum,map_mul,Haze.realTaste, drifts, smul_eq_mul,he, ← Finset.mul_sum]
 simp_rw [mul_left_comm _ (-(1/2):ℝ),← Finset.mul_sum]; rw [←billTotal χ s f g h]; simp only [f,g,LinearEquiv.apply_symm_apply]
abbrev basisU {I:Type*}[DecidableEq I](i:I):I→ℝ:=Pi.single i 1
lemma itinerary {I:Type*}[DecidableEq I] (q:Paper I ℝ): ∃ s:Finset I, ∀ t:Finset I,s ⊆ t → ∀(χ:I→ℝ), (∀i∈s,χ i=1)→∀ x:I→ℝ, vent x q= ∑ i ∈ t,(χ i*x i) • vent (basisU i) q:=by
 induction q using MvPolynomial.induction_on with
 | C c=> refine ⟨∅,fun t _ χ h x=>?_⟩; simp only [vent_C,smul_zero,Finset.sum_const_zero]
 | add a b ha hb=>
   obtain ⟨s,H⟩:=ha; obtain ⟨u,R⟩:=hb
   refine ⟨s ∪ u,fun t w χ k x=>?_⟩; rw [map_add, H t (Finset.subset_union_left.trans w) χ (fun i hi=>k i (Finset.mem_union_left _ hi)) x,R t (Finset.subset_union_right.trans w) χ (fun i hi=>k i (Finset.mem_union_right _ hi)) x,←Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _=>by simp only [map_add,smul_add]
 | mul_X q i hp=>
   obtain ⟨s,h⟩:=hp; refine ⟨insert i s,fun t w χ k x=>?_⟩
   have ht:i∈t:=w (Finset.mem_insert_self ..); have hu:= k i (Finset.mem_insert_self ..)
   rw [vent_x]; simp_rw [vent_x,smul_add]; rw [Finset.sum_add_distrib]; apply congrArg₂
   · rw [Finset.sum_eq_single_of_mem i ht, basisU,Pi.single_eq_same,hu]; simp
     intro b _ hb; rw [basisU,Pi.single_eq_of_ne (Ne.symm hb),zero_smul,smul_zero]
   rw [h t (Finset.subset_insert _ _ |>.trans w) χ (fun i hi=> k i (Finset.mem_insert_of_mem hi)) x, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> mul_smul_comm ..
lemma marked (p:pLabel G): ∃ v: Finset (Shaft G),∀ (χ:Cover→ℝ)(s:Finset Cover),v⊆parade s → (∀i∈v,χ i.1.1=1)→∀θ:Cover→G.Color,θ 0=0→ vent (cant (ascent θ)) (castFirst 1 p)= -(1/2:ℝ) • ∑ i∈parade s,χ i.1.1 • (leaf (drift θ i) * vent (splinter i) (castZero 1 p)):=by
 obtain ⟨v,H⟩:= itinerary (castZero 1 p); refine ⟨v,fun χ s hs ht θ he =>?_⟩
 apply viewers; intro A; rw [(sailing _ _ _ _ he).2, H _ hs _ ht (cant (spur θ A)),_root_.map_sum]; rw [map_smul,_root_.map_sum]; apply congrArg ((-(1/2):ℝ) * ·); apply Finset.sum_congr rfl; intro i _; rw [_root_.map_smul (aeval _),map_smul,map_mul,Haze.realTaste,drifts]; simp only [smul_eq_mul]; rw [mul_assoc]
end YM.SchemeRG11.North

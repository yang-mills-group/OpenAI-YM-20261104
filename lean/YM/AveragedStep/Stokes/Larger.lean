import YM.AveragedStep.Stokes.Cover

/-! Push prediction costs to the actual two-level tori, including equal
centers and seams. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.Loops
open Lattice Wilson RG Function
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}(S:StepData c f)
abbrev faceAt (x:Site f)(p:Face ℤ):Face (Per f):=(wrap f p.1+x,p.2)
lemma expand_bill (x:Site f)(U:Config G f)(l:List (Face ℤ)):bill (expandAt x U) l=bill U (l.map (faceAt x)):=by
  unfold bill; simp [faceValue,travel_at,Function.comp_def]

private lemma prediction_read (U:Config G f)(t:S.Choices)(e:Edge (Site c)):
    S.prediction U t e=coverQ S.patch S.kernel (t.1 e.1) (t.1 (e.1+step e.2)) (t.2 e) e.2 (expandAt (S.ratio.embed e.1) U):=by
 unfold coverQ StepData.prediction
 apply congr_arg (fun X:S.patch.Connector G=>S.patch.predict S.kernel X _)
 funext q
 unfold coverY StepData.connector StepData.frames
 rw [S.leap, show expandAt (S.ratio.embed e.1+S.patch.L.val • step e.2) U = translate (S.patch.L.val • step e.2) (expandAt (S.ratio.embed e.1) U) from ?_]
 funext i; simp only [expandAt,translate,map_add,map_nsmul,wrap_step,add_right_comm,add_assoc] -- simp loops add

-- Uniform in local tags, group but not patch
lemma native_price (P:Patch)(K:KernelChoices)(h:P.Branches K G):∃ D:ℝ,0≤D ∧ ∃ m:ℕ,∀ (c f:Side) (S:StepData c f), S.patch=P → S.kernel=K → ∀ (e:Edge (Site c)),∃ L:List (Face (Per f)), L.length≤m ∧
    ∀ (U:Config G f) (t:S.Choices),G.chord (S.prediction U t e*(travel U (S.ratio.embed e.1) (List.replicate P.L.val (posDir e.2)))⁻¹) ≤ D*bill U L:=by
  let X:=fun (p:P.FrameTag × P.FrameTag × P.Points × Axis) (U:CoverConfig G)=>coverQ P K p.1 p.2.1 p.2.2.1 p.2.2.2 U *(travel U 0 (List.replicate P.L.val (posDir p.2.2.2)))⁻¹
  obtain ⟨l,D,hD,H⟩:=together X fun i=>straight_difference P K h ..
  refine ⟨D,hD,l.length,?_⟩
  intro c f S h₁ h₂ e
  refine ⟨l.map (faceAt (S.ratio.embed e.1)),by simp,?_⟩
  subst P K
  intro U t; rw [←expand_bill,prediction_read]
  have he:=H (t.1 e.1,t.1 (e.1+step e.2),t.2 e,e.2) (expandAt (S.ratio.embed e.1) U)
  unfold X at he; dsimp only at he; simpa only [travel_at, map_zero,zero_add] using! he

lemma chord_prod (a b c d:G.El):G.chord ((a*b)*(c*d)⁻¹) ≤ G.chord (a*c⁻¹)+G.chord (b*d⁻¹):=by
  rw [show (a*b)*(c*d)⁻¹=(a*(b*d⁻¹)*a⁻¹)*(a*c⁻¹) by group]
  calc
    _ ≤ _ := G.chord_triangle _ _
    _ = _:=by rw [G.chord_conj,add_comm]
lemma chord_inv_pair (a b:G.El):G.chord (a⁻¹*(b⁻¹)⁻¹)=G.chord (a*b⁻¹):=by
  rw [←G.chord_inv (a*b⁻¹), show (a*b⁻¹)⁻¹=a*(a⁻¹*(b⁻¹)⁻¹)*a⁻¹ by group,G.chord_conj]

def lay (L:ℕ)(w:Walk):Walk:=w.flatMap (fun i=>List.replicate L i)
lemma lay_size (L:ℕ)(w:Walk) : List.length (lay L w)=L*w.length:=by
 induction w with
 | nil=>simp [lay]
 | cons a w ih=>rw [show lay L (a::w)=List.replicate L a++lay L w from rfl,List.length_append,List.length_replicate,ih,List.length_cons,Nat.mul_succ,Nat.add_comm]

lemma path_stop (x:Site c)(a:Step):
    stop (S.ratio.embed x) (List.replicate S.patch.L.val a)=S.ratio.embed (x+a.vec):=by
  rcases a with ⟨z,h|h⟩
  · rw [show List.replicate S.patch.L.val {dir:=z, neg:=false}=S.repath z from rfl,S.stop_repath,show Step.vec ⟨z,false⟩=(step z:Site c) from rfl]; exact (S.leap ..).symm
  let a:=negDir z
  let b:=x+a.vec (R:=Per c)
  have he:x=b+step z:=by unfold b a; rw [Step.vec_neg]; abel
  nth_rw 1 [he]; rw [S.leap]
  have hv : List.replicate S.patch.L.val (negDir z)=Lattice.reverse (S.repath z):=by simp [Lattice.reverse,StepData.repath]
  change stop (S.ratio.embed b+S.patch.L.val • step z) (List.replicate S.patch.L.val (negDir z))=S.ratio.embed b
  rw [←S.stop_repath,hv,reverse_stop]

variable {P:Patch}{K:KernelChoices} (hk:P.Branches K G)
include hk
omit S in
lemma step_price:∃ D:ℝ,0≤D ∧ ∃ m:ℕ,∀ (c f:Side) (S:StepData c f), S.patch=P→ S.kernel=K→∀ (x:Site c) (a:Step),∃ L:List (Face (Per f)),L.length≤m ∧∀ (U:Config G f)(t:S.Choices),G.chord (a.read (S.prediction U t) x*(travel U (S.ratio.embed x) (List.replicate S.patch.L.val a))⁻¹)≤D*bill U L:=by
  obtain ⟨D,hD,m,H⟩:=native_price P K hk
  refine ⟨D,hD,m,?_⟩
  intro c f S hP hK x a
  obtain ⟨z,h|h⟩:=a
  · change ∃ _,_ ∧ ∀ _ _,G.chord ((posDir z).read .. * _) ≤ _
    exact hP ▸ H c f S hP hK (x,z) -- cast?
  obtain ⟨L,hL,H⟩:= H c f S hP hK (x-step z,z)
  refine ⟨L,hL,?_⟩
  change ∀ (U:Config G f) (t:S.Choices),G.chord ((negDir z).read _ _ * (travel U _ (List.replicate S.patch.L.val (negDir z)))⁻¹) ≤ _
  intro U t; rw [Step.neg_read]
  have hv : List.replicate S.patch.L.val (negDir z)=Lattice.reverse (S.repath z):=by simp [Lattice.reverse,StepData.repath]
  have hx:= travel_reverse (S.repath z) U (S.ratio.embed (x-step z))
  rw [S.stop_repath,← S.leap,sub_add_cancel] at hx
  rw [hv,hx,chord_inv_pair]; subst P; exact H U t

omit S in
lemma predictor_walk:∃ D:ℝ,0≤D ∧ ∃ m:ℕ,∀ (c f:Side) (S:StepData c f), S.patch=P→ S.kernel=K→∀ (x:Site c)(w:Walk),∃ L:List (Face (Per f)), L.length≤m*w.length ∧
    ∀ (U:Config G f)(t:S.Choices),G.chord (travel (S.prediction U t) x w*(travel U (S.ratio.embed x) (lay S.patch.L.val w))⁻¹) ≤ D*bill U L:=by
  obtain ⟨D,hD,m,H⟩:=step_price hk
  refine ⟨D,hD,m,?_⟩
  intro c f S hP hK x w
  induction w generalizing x with
  | nil=>exact ⟨[],by simp,fun U t=>by simp [travel,lay,bill]⟩
  | cons a w ih=>
    obtain ⟨l,hl,h⟩:= H c f S hP hK x a; obtain ⟨q,hq,J⟩:=ih (x+a.vec)
    refine ⟨l++q, by rw [List.length_append,List.length_cons,Nat.mul_succ]; omega,fun U t=>?_⟩
    rw [show lay S.patch.L.val (a::w)=List.replicate _ _++lay _ w from rfl,travel_append,path_stop S,travel]
    rw [bill_append,mul_add]; exact (chord_prod ..).trans (add_le_add (h U t) (J U t))
omit hk S in
private lemma lay_rect (A:ℕ)(i j:Axis):stop (0:Cover) (lay A (square i j))=0:=by
  have he (x:Cover)(a:Step):stop x (List.replicate A a)=x+A • a.vec:=by
    induction A generalizing x with
    | zero=>simp [stop]
    | succ d ih=> rw [List.replicate_succ,stop,ih,succ_nsmul]; abel
  unfold lay square
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,stop_append,he,Step.vec_pos,Step.vec_neg,smul_neg]; abel
omit S in
lemma plaquette_prediction : ∃ D:ℝ,0≤D∧∃ m:ℕ,∀ (c f:Side)(S:StepData c f), S.patch=P→S.kernel=K→∀ p:Face (Per c),∃ L:List (Face (Per f)), L.length≤m ∧ ∀ (U:Config G f)(t:S.Choices),G.chord (faceValue (S.prediction U t) p) ≤ D*bill U L:=by
  obtain ⟨D,hD,m,H⟩:=predictor_walk hk
  refine ⟨max D 1,by positivity,m*4+(P.L.val*4)^2,?_⟩
  intro c f S hP hK p
  let w:=square p.2.val.1 p.2.val.2
  obtain ⟨l,hl,h⟩:= H c f S hP hK p.1 w
  obtain ⟨q,hq,J⟩:=closed (lay S.patch.L.val w) (lay_rect ..) (S.ratio.embed p.1)
  refine ⟨l++q,?_ ,?_⟩
  · rw [lay_size,hP] at hq; exact (List.length_append.le.trans (Nat.add_le_add hl hq))
  intro U t
  let a:=faceValue (S.prediction U t) p; let b:=travel U (S.ratio.embed p.1) (lay S.patch.L.val w)
  change G.chord a≤_; rw [show a=(a*b⁻¹)*b from by group]
  have hp:max D 1 * bill U q ≥ bill U q:=le_mul_of_one_le_left (bill_pos ..) (le_max_right ..)
  rw [bill_append,mul_add]; apply (G.chord_triangle _ _).trans
  exact add_le_add ((h U t).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (bill_pos ..))) ((J G U).trans hp)

end YM.AveragedStep.Loops

import YM.MSbar.Pole.Symbol.Rights
/-! # Lorentz-index δ in complex dimension
This contraction must be prior to specializing to a low embedding dimension. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Symbol
open Set Function Filter MeasureTheory Ambient Momentum Age Mellin place
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {I : Type} [Fintype I] {n : ℕ}
variable (a b : I)
def joint (x : External I n) (v w : place n) : External I n:= update (update x b w) a v
lemma joint_pad (x:External I n) (v w:place n) : joint a b (pad n ∘ x) (pad n v) (pad n w)=pad n ∘ joint a b x v w:=by
  ext1 i; by_cases hh:i=a; subst i; simp only [joint,Function.comp_apply,update_self];
  by_cases hg:i=b; subst i; simp only [joint,Function.comp_apply,update_of_ne hh,update_self];
  simp only [joint,Function.comp_apply,update_of_ne hh,update_of_ne hg]
lemma joint_turn (J : place n≃ₗᵢ[ℝ] place n) (x:External I n) (v w:place n) : joint a b (J ∘ x) (J v) (J w)=J ∘ joint a b x v w:=by
  ext1 i; by_cases hh:i=a; subst i; simp only [joint,Function.comp_apply,update_self];
  by_cases hg:i=b; subst i; simp only [joint,Function.comp_apply,update_of_ne hh,update_self];
  simp only [joint,Function.comp_apply,update_of_ne hh,update_of_ne hg]
abbrev ortho (n):= EuclideanSpace.basisFun (Fin (2*n)) ℝ

def horizontal (H : Cloud I) (x : External I n): ℂ:=∑ i,H n (joint a b x (ortho n i) (ortho n i))
def vertical (H:Cloud I) (x:External I n) : ℂ:= H (n+1) (joint a b (pad n ∘ x) (room n 1) (room n 1))
def stroke (w:ℂ)(H : Cloud I): Cloud I:=fun n x=>horizontal a b H x+(w- 2*n)*vertical a b H x

variable {a b} {H : Cloud I}
lemma horizontally {J:Type}[Fintype J] (B : OrthonormalBasis J ℝ (place n))
    (hn:a≠b) (h: Tone H a)(p:Tone H b) (x : External I n) : horizontal a b H x=∑ i,H n (joint a b x (B i) (B i)):=by
  let D := ortho n
  let F (v:place n)(w:place n):= H n (joint a b x v w)
  let X(w:place n):= Along.lift (show Along (fun v=>F v w) from h n (update x b w))
  have he (v): Along (F v) := by
    unfold F joint; simp_rw [update_comm hn.symm]; exact p n (update x a v)
  let Y (v:place n):= Along.lift (he v)
  have hf i:F (D i) (D i)= ∑ j, inner ℝ (B j) (D i) • F (B j) (D i):=by
    change X (D i) (D i) = _; nth_rw 2 [← B.sum_repr' (D i)]; rw [map_sum]; apply Finset.sum_congr rfl; intro u _; exact map_smul (X _) ..
  have hg i:F (B i) (B i)= ∑ j, inner ℝ (D j) (B i) • F (B i) (D j):=by
    change Y (B i) (B i) = _; nth_rw 2 [← D.sum_repr' (B i)]; rw [map_sum]; apply Finset.sum_congr rfl; intro u _; exact map_smul (Y _) ..
  change ∑ i,F (D i) (D i)=∑ j,F (B j) (B j)
  simp_rw [hf,hg]; rw [Finset.sum_comm]; simp_rw [real_inner_comm (D _) (B _)]

variable (h:Tensor H)
include h
lemma band {u:ℂ} (hu: ‖u‖=1) (a b:I) (x:External I n) : vertical a b H x= H (n+1) (joint a b (pad n ∘ x) (room n u) (room n u)):=by
  obtain ⟨J,hJ,hx⟩ := sphere (x:=room n 1) (y:=room n u) (by simp [squared,hu])
  · have hl : J ∘ (pad n ∘ x) = pad n ∘ x:= funext fun i=>hx _ (by simp)
    unfold vertical; rw [← h.moves (n+1) J,← joint_turn,hJ,hl]

lemma next (a b:I) (x:External I n) : vertical a b H (pad n ∘ x)=vertical a b H x:=by
  let U:= pad (n+1) (room n 1); let V:=room (n+1) 1
  let Z:=pad (n+1) ∘ (pad n ∘ x)
  obtain ⟨J,hJ,he⟩:= sphere (x:=U) (y:=V) (by unfold U V; simp [squared])
  · have hz : J ∘ Z= Z:=funext fun i => he _ (by simp [U,V,Z])
    unfold vertical
    rw [← h.agrees (n+1), ← joint_pad, ← h.moves (n+2) J (joint a b _ U U), ← joint_turn]; rw [hJ,hz]
lemma extra (hn:a≠b) (ha: Tone H a)(hb:Tone H b)(x:External I n): horizontal a b H (pad n ∘ x)=horizontal a b H x+2*vertical a b H x:=by
  let C:= ortho n; let B := (C.prod Complex.orthonormalBasisOneI).map (globe n)
  rw [horizontally B hn ha hb,Fintype.sum_sum_type]
  have hh i: B (Sum.inl i)= pad n (C i):= by simp [B]
  have ht i: B (Sum.inr i)= room n (Complex.orthonormalBasisOneI i):= by simp [B]
  simp_rw [hh,ht,joint_pad,h.agrees]; simp_rw [← band h (Complex.orthonormalBasisOneI.norm_eq_one _)]; congr 1; simp
lemma trace_style (w:ℂ)(hn:a≠b)(ha:Tone H a)(hb:Tone H b): Tensor (stroke a b w H):=by
  constructor
  · intro n J x; unfold stroke
    rw [horizontally ((ortho n).map J) hn ha hb (J ∘ x)]
    have hh : pad n ∘ (J ∘ x)=grow J ∘ (pad n ∘ x):= funext fun i=>by simp
    have hv: vertical a b H (J ∘ x) = vertical a b H x:= by unfold vertical; rw [hh,show joint a b (grow J ∘ (pad n ∘ x)) _ _=grow J ∘ joint a b (pad n ∘ x) (room n 1) (room n 1) from ?_, h.moves];
                                                                              rw [← joint_turn]; simp
    simp only [OrthonormalBasis.map_apply, joint_turn, h.moves, hv,horizontal]
  intro n x; unfold stroke; rw [next h,extra h hn ha hb]; push_cast; ring
end YM.MSbar.Pole.Symbol

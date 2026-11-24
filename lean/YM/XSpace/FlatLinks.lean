import YM.XSpace.Tree

/-!
# No zero mode left after tree gauge fixing

Alternative to Fourier resolution for the regulator check in §orbpt. For any
finite period, translating a closed link field changes it by a coboundary. Average over
all translations. The constant remainder vanishes by inversion symmetry. Then symmetrize
the primitive in the same geometry and test it on the tree.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Period
open Lattice Function Set
open scoped BigOperators
variable (R : XSpace.Period) {E : Type*} [AddCommGroup E] [Module ℝ E]

def extend (u : R.Link → E) (e : R.Bonds) := if R.Chosen e then u (R.rep e) else -u (R.rep e)
omit [Module ℝ E] in
lemma extend_at (u : R.Link → E) (e : R.Link) : R.extend u e = u e := by simp [extend,e.property]
omit [Module ℝ E] in
@[simp] theorem extend_reflect (u : R.Link → E) (e : R.Bonds) : R.extend u (R.reflect e) = - R.extend u e := by
  by_cases he:R.Chosen e <;> simp [extend,he]

def translate (a : R.Sites) : (R.Bonds → E) →ₗ[ℝ] (R.Bonds → E) where
  toFun u e:=u (e.1+a,e.2)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
lemma translate_apply (A : R.Bonds → E) (a : R.Sites) (e : R.Bonds) : R.translate a A e = A (e.1+a,e.2) := rfl
lemma translate_zero (A : R.Bonds → E) : R.translate 0 A=A:=funext fun e=> by simp [translate]
lemma translate_add (a b : R.Sites) (A : R.Bonds → E) : R.translate a (R.translate b A)=R.translate (a+b) A :=
    funext fun e=> by simp [translate,add_assoc]

def derivative : (R.Sites → E) →ₗ[ℝ] (R.Bonds → E) where
  toFun v e:= v (e.1+step e.2)-v e.1
  map_add' v w:= funext fun e=> by simp; abel
  map_smul' t v:= funext fun e=> by simp [smul_sub]
lemma derivative_at (v : R.Sites → E) (e : R.Bonds) : R.derivative v e=v (e.1+step e.2)-v e.1 := rfl

lemma translate_exact (u : R.Bonds → E) (v : R.Sites) (h : u∈ LinearMap.range R.derivative) :
    R.translate v u∈ LinearMap.range R.derivative := by
  obtain ⟨p,rfl⟩:=h
  exact ⟨fun x=> p (x+v),funext fun e=> by simp [translate,derivative,add_right_comm]⟩

/-- The Hessian only uses this curl. Use positive-coordinate faces with `i < j`.
(This is on the covering torus, with invariant fields extended.) -/
def curlIJ (A : R.Bonds → E) (x : R.Sites) (i j : Axis) :=
  A (x,i) + A (x+step i,j)- A (x+step j,i)-A (x,j)
omit [Module ℝ E] in
lemma curlJI (A : R.Bonds → E) (x : R.Sites) (i j : Axis) : R.curlIJ A x j i = - R.curlIJ A x i j := by unfold curlIJ; abel

def curl : (R.Bonds → E) →ₗ[ℝ] (Face (Per R.side) → E) where
  toFun A p:= R.curlIJ A p.1 p.2.val.1 p.2.val.2
  map_add' A B:= funext fun p=> by simp [curlIJ]; abel
  map_smul' t A:= funext fun p=> by simp [curlIJ,smul_add,smul_sub]
lemma curl_at (A : R.Bonds → E) (p : Face (Per R.side)) : R.curl A p=R.curlIJ A p.1 p.2.val.1 p.2.val.2:=rfl
@[simp] theorem curl_derivative (v : R.Sites → E) : R.curl (R.derivative v)=0:=
  funext fun p=> by simp [curl, derivative, curlIJ, add_right_comm]

private def Translates (A : R.Bonds → E) (x : R.Sites) := R.translate x A - A∈LinearMap.range R.derivative

private lemma translated_step (A : R.Bonds → E) (h : R.curl A=0) (i : Axis) : R.Translates A (step i) := by
  have H x j : R.curlIJ A x i j=0 := by
    rcases lt_trichotomy i j with a|a|a
    · exact congr_fun h (x,⟨(i,j),a⟩)
    · simp [curlIJ,a]
    rw [curlJI,show R.curlIJ A x j i=0 from congr_fun h (x,⟨(j,i),a⟩),neg_zero]
  refine ⟨fun x => A (x,i),?_⟩; ext1 ⟨x,j⟩
  change A (_,i)-A (x,i)= A (_,j)-A (x,j)
  have ht:= H x j; unfold curlIJ at ht
  rw [sub_eq_zero,sub_eq_iff_eq_add] at ht
  rw [sub_eq_iff_eq_add]
  apply sub_eq_zero.mp
  rw [show _ - _ = -(A (x,i)+A (x+step i,j) - (A (x,j)+ A (x+step j,i))) by abel, ht, sub_self,neg_zero]

private lemma translates_add (A : R.Bonds → E) (x y : R.Sites) (hx : R.Translates A x) (hy : R.Translates A y) :
    R.Translates A (x+y) := by
  unfold Translates
  rw [← R.translate_add, show _-_ = R.translate x (R.translate y A-A)+(R.translate x A-A) by rw [map_sub]; abel]
  exact Submodule.add_mem _ (R.translate_exact _ x hy) hx
private lemma translates_neg (A : R.Bonds → E) (x : R.Sites) (hx : R.Translates A x) : R.Translates A (-x) := by
  unfold Translates; rw [← Submodule.neg_mem_iff, neg_sub]
  have h := R.translate_exact _ (-x) hx; rw [map_sub,R.translate_add,neg_add_cancel,translate_zero] at h; exact h
private lemma any_translated (A : R.Bonds → E) (h : R.curl A=0) (x : R.Sites) : R.Translates A x := by
  have hp (w : Walk) (x : R.Sites) (he : R.Translates A x) : R.Translates A (stop x w) := by
    induction w generalizing x with
    | nil => exact he
    | cons d w ih =>
      refine ih _ (R.translates_add A _ d.vec he ?_)
      unfold Step.vec; split
      · exact R.translates_neg A (step d.dir) (R.translated_step A h _)
      exact R.translated_step A h _
  obtain ⟨w,hw⟩:=R.exists_walk 0 x; rw [← hw]; exact hp w 0 (by unfold Translates; rw [translate_zero,sub_self]; exact Submodule.zero_mem _)

lemma sum_inverted_zero (A : R.Bonds → E) (h : ∀ e, A (R.reflect e) = -A e) (i : Axis) : ∑ x:R.Sites, A (x,i) = 0 := by
  let f (x : R.Sites):= (R.reflect (x,i)).1
  have he : Function.Involutive f:= fun x=> congr_arg Prod.fst (R.reflect_invol (x,i))
  let e:= he.toPerm f
  have ht x : A (e x,i) = -A (x,i) := h (x,i)
  let z:= ∑ x:R.Sites,A (x,i)
  have hz : z = -z := (Equiv.sum_comp e (fun x => A (x,i))).symm.trans (by unfold z; simp_rw [ht,Finset.sum_neg_distrib])
  have hb : (2:ℝ) • z=0:= by rw [two_smul]; nth_rw 2 [hz]; rw [add_neg_cancel]
  exact (smul_eq_zero.mp hb).resolve_left (by norm_num)

lemma sum_translate (A : R.Bonds → E) (e : R.Bonds) : (∑ x:R.Sites, R.translate x A) e= ∑ x:R.Sites,A (x,e.2):=by
  rw [Finset.sum_apply]; exact Equiv.sum_comp (Equiv.addLeft e.1) (fun x => A (x,e.2))

theorem exact_of_odd (A : R.Bonds → E) (h : ∀ e, A (R.reflect e) = -A e) (hA : R.curl A=0) :
    ∃ v : R.Vertex → E, A = R.derivative (v ∘ R.vertex) := by
  have hh := Submodule.sum_mem (p:=LinearMap.range R.derivative) (t:=Finset.univ) (f:=fun x=> R.translate x A-A) (fun x _=> R.any_translated A hA x)
  have he : (∑ x:R.Sites, R.translate x A)=0:= funext fun e=> (R.sum_translate A e).trans (R.sum_inverted_zero A h e.2)
  rw [Finset.sum_sub_distrib, he, Finset.sum_const, Finset.card_univ, zero_sub,Submodule.neg_mem_iff,← Nat.cast_smul_eq_nsmul ℝ] at hh
  have hc: (Fintype.card R.Sites:ℝ)≠0:=by positivity
  obtain ⟨v,hv⟩:= ((LinearMap.range (R.derivative (E:=E))).smul_mem_iff hc).mp hh
  let f x:= (2:ℝ)⁻¹ • (v x + v (-x))
  let V : R.Vertex → E:=Quotient.lift f (by intro x y (H : y=x ∨ y= -x); rcases H with he|he <;> simp [he,f,add_comm])
  refine ⟨V,Eq.symm ?_⟩; funext e; change f _ - f _ = A e
  have hp:= (R.derivative_at v e).symm.trans (congr_fun hv e)
  have hq:= ((R.derivative_at v (R.reflect e)).symm.trans (congr_fun hv (R.reflect e))).trans (h e); rw [reflect_axis,reflect_dest,reflect_base] at hq
  unfold f; rw [← smul_sub,show (v _ + _)-(v _ + _) = R.derivative v e - R.derivative v (R.reflect e) by rw [derivative_at,derivative_at,reflect_axis,reflect_dest,reflect_base]; abel, hv,h, sub_neg_eq_add, ← two_smul ℝ, inv_smul_smul₀ (by norm_num)]

variable {R}
namespace Tree
variable (T : R.Tree)

def prolong (u : T.Free → E) (e : R.Link) := if h:e∈T.edges then 0 else u ⟨e,h⟩
omit [Module ℝ E] in
@[simp] lemma prolong_free (u : T.Free → E) (i : T.Free) : T.prolong u i = u i := by simp [prolong,i.property]

def covering : (T.Free → E) →ₗ[ℝ] (R.Bonds → E) where
  toFun u:= R.extend (T.prolong u)
  map_add' u v := by
    funext i
    have he e : T.prolong (u+v) e = T.prolong u e+ T.prolong v e:= by unfold prolong; split <;> simp [*]
    unfold Period.extend; rw [he]; simp only [Pi.add_apply]; split_ifs <;> abel
  map_smul' t u := by
    funext i
    have he e : T.prolong (t • u) e = t • T.prolong u e:= by unfold prolong; split <;> simp [*]
    unfold Period.extend; rw [he]; simp only [RingHom.id_apply,Pi.smul_apply]; split_ifs <;> simp
lemma covering_at (u : T.Free → E) (i : R.Link) : T.covering u i = T.prolong u i := R.extend_at _ i
@[simp] lemma covering_reflect (u : T.Free → E) (i : R.Bonds) : T.covering u (R.reflect i) = -T.covering u i := R.extend_reflect _ _

theorem no_modes (u : T.Free → E) (h : R.curl (T.covering u)=0) : u=0 := by
  obtain ⟨v,hv⟩:= R.exact_of_odd _ (fun e=> covering_reflect T _ e) h
  have ht (x : R.Vertex) (hx : x≠T.root) : v (T.parent x)=v x := by
    let e:=T.edge x hx
    have hp := (T.covering_at u e).symm.trans (congr_fun hv e.val)
    rw [prolong, dif_pos ((T.mem_edges _).2 ⟨_,hx,rfl⟩)] at hp
    change 0=v (R.dst e)-v (R.src e) at hp
    rcases T.joins x hx with ⟨a,b⟩|⟨a,b⟩ <;> unfold e at hp <;> rw [a,b] at hp
    · exact sub_eq_zero.mp hp.symm
    exact (sub_eq_zero.mp hp.symm).symm
  have he (m : ℕ) : ∀ x,T.rank x=m → v x=v T.root := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hm; by_cases h:x=T.root; exact h ▸ rfl
      exact (ht x h).symm.trans (ih _ (hm ▸ T.closer x h) _ rfl)
  funext i; change u i=0
  rw [← T.prolong_free u i, ← T.covering_at u i.val, hv, derivative_at,comp_apply,comp_apply,he _ _ rfl,he _ (R.vertex i.val.val.1) rfl,sub_self]
lemma curl_injective : Function.Injective (R.curl ∘ₗ (T.covering (E:=E))) := by
  intro a b h; exact sub_eq_zero.mp (T.no_modes _ (show (R.curl ∘ₗ T.covering) _=0 by rw [map_sub,h,sub_self]))
end Tree
end YM.XSpace.Period

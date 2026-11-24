import YM.XSpace.Curled

/-!
# The free (curl) covariance used inside the bare diagrams: inversion projector

With exactly the lift/fixed spanning tree of XSpace.Bare (unscaled log insertions,
Native units). Do this on curl Hilbert spaces, keeping all top orbit constraints. No
spurious constant mode or removal of a mode on the unconditioned Wilson path, and no
pretended translation invariance of this free kernel. Used to handle the peculiar large
inversion-quotient regulator even to leading order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Period
open Lattice Filter Set Function Exterior Matrix
open scoped Topology InnerProductSpace BigOperators
variable (R : Period) {G : Gauge} {E : Type*} [AddCommGroup E] [Module ℝ E]

def mirrorLink : (R.Bonds → E) →ₗ[ℝ] (R.Bonds → E) := LinearMap.pi (fun i=> -LinearMap.proj (R.reflect i))
lemma mirror_apply (u : R.Bonds → E) (i : R.Bonds): R.mirrorLink u i= -u (R.reflect i):=rfl
@[simp] lemma mirror_link_twice (u : R.Bonds → E): R.mirrorLink (R.mirrorLink u)=u:= funext fun i=> by rw [mirror_apply,mirror_apply,reflect_invol,neg_neg]
lemma mirror_derivative (v : R.Vertex → E) : R.mirrorLink (R.derivative (v ∘ R.vertex))=R.derivative (v ∘ R.vertex):= funext fun i=> by rw [mirror_apply,derivative_at,derivative_at,reflect_axis,reflect_dest,reflect_base]; simp only [Function.comp_apply,R.vertex_neg,neg_sub]

omit [Module ℝ E] in
lemma extend_injective (u w : R.Link → E) (h : R.extend u= R.extend w): u=w:= by funext i; rw [← R.extend_at u i, ← R.extend_at w i,h]
lemma mirror_reps (u v : R.Bonds→E) (h : R.mirrorLink u=u) (p : R.mirrorLink v=v) (ht : ∀ i : R.Link, u i=v i): u=v:= funext fun i=> by
  by_cases hb:R.Chosen i
  · exact ht ⟨i,hb⟩
  calc _ = -u (R.reflect i) := (congr_fun h i).symm
       _ = -v (R.reflect i) := congr_arg Neg.neg (ht ⟨_,(R.choice_reflect i).mpr hb⟩)
       _ = _ := congr_fun p i

def reflectedFace (p : Top.Faces R.side) : Top.Faces R.side:= (-p.1-step p.2.val.1-step p.2.val.2,p.2)
@[simp] lemma axis_reflectedFace (p : Top.Faces R.side) : (R.reflectedFace p).2=p.2:=rfl
@[simp] lemma face_invol (p : Top.Faces R.side): R.reflectedFace (R.reflectedFace p) = p := by refine Prod.ext ?_ rfl; unfold reflectedFace; dsimp only; abel

lemma curl_mirror (A : R.Bonds → E) (x : Top.Faces R.side): R.curl (R.mirrorLink A) x = R.curl A (R.reflectedFace x):= by
  rw [curl_at,curl_at]; rcases x with ⟨x,i⟩; let k:=i.val.1; let l:=i.val.2
  simp only [curlIJ,reflectedFace, mirror_apply,reflect]
  rw [show -(x+step k)-step l= -x-step i.val.1-step i.val.2 by abel,
      show -(x+step l)-step k = -x-step i.val.1-step i.val.2 by abel,
      show -x-step k-step l+step k= -x-step i.val.2 by abel,
      show -x-step k-step l+step l= -x-step i.val.1 by abel]; abel

def mirrorFace : Top.Forms G R.side →ₗ[ℝ] Top.Forms G R.side where
  toFun x:= WithLp.toLp 2 fun i => x (R.reflectedFace i)
  map_add' _ _:= rfl
  map_smul' _ _:=rfl
lemma face_apply (x : Top.Forms G R.side) (i : Top.Faces R.side): R.mirrorFace x i=x (R.reflectedFace i):=rfl
@[simp] lemma mirror_face_twice (x : Top.Forms G R.side): R.mirrorFace (R.mirrorFace x)=x:=by
  ext i j; rw [face_apply,face_apply,face_invol]
lemma symmetric (x y : Top.Forms G R.side): inner ℝ (R.mirrorFace x) y=inner ℝ x (R.mirrorFace y):= by
  rw [PiLp.inner_apply,PiLp.inner_apply]; simp only [face_apply]; let e:=(show Involutive R.reflectedFace from R.face_invol).toPerm _; rw [← Equiv.sum_comp e (fun i=> inner ℝ (x i) (y (R.reflectedFace i)))]; exact Finset.sum_congr rfl fun i _=> by change _=inner ℝ _ (y (R.reflectedFace (R.reflectedFace i))); rw [face_invol]; rfl
lemma mirror_at_face (i : Top.Faces R.side) (j : G.ColorIndex): R.mirrorFace (Top.unitFace i j)=Top.unitFace (R.reflectedFace i) j:=by
  apply ext_inner_right ℝ; intro x; rw [symmetric, Top.atFace,Top.atFace,face_apply]

-- Identify the range of projected invariant-link curls.
def arrange (A : R.Bonds→G.Color) : Top.Input G R.side:= fun i=> A (i.1,axisEquiv.symm i.2)
lemma cover_curl (x : Top.Input G R.side) (i : Top.Faces R.side): Top.curl G R.side x i= R.curl (collect G x) i:=by
  ext j; rw [Top.curl_val,curl_at,curlIJ]
  change ((((Exterior.d 1 R.side) *ᵥ parts G 1 x j) (i.1,plaquette i.2)) : ℝ)=_
  rw [d_plaquettes]; unfold parts collect; simp only [PiLp.sub_apply, PiLp.add_apply]; abel
lemma rearrange (u : R.Bonds→G.Color): collect G (R.arrange u)=u:=by
  funext i; change u (i.1,axisEquiv.symm (axisEquiv i.2))=u i; rw [Equiv.symm_apply_apply]
lemma cover_mirror (x : Top.Input G R.side) : Top.curl G R.side (R.arrange (R.mirrorLink (collect G x)))= R.mirrorFace (Top.curl G R.side x):=by
  ext i j; rw [face_apply,R.cover_curl,R.rearrange,R.curl_mirror,R.cover_curl]
lemma mirror_mem (x : Top.Forms G R.side) (h : x∈Top.Curled G R.side): R.mirrorFace x ∈ Top.Curled G R.side:= by obtain ⟨u,rfl⟩:=h; exact ⟨_,R.cover_mirror u⟩
lemma mirror_star (x : Top.Forms G R.side): (Top.Curled G R.side).starProjection (R.mirrorFace x) = R.mirrorFace ((Top.Curled G R.side).starProjection x):=by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (R.mirror_mem (G:=G) _ (Submodule.starProjection_apply_mem ..)) ?_
  intro w hw
  rw [inner_sub_left,symmetric,symmetric,Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr (R.mirror_mem _ hw),sub_self]

def evenForms (G : Gauge):= LinearMap.ker (R.mirrorFace (G:=G)-LinearMap.id)
lemma mem_even (x : Top.Forms G R.side) : x∈R.evenForms G↔R.mirrorFace x=x:= by unfold evenForms; simp [sub_eq_zero]

abbrev Equivariant (G : Gauge):= R.evenForms G ⊓ Top.Curled G R.side

def evenPart (G : Gauge):=(2:ℝ)⁻¹ • (LinearMap.id+R.mirrorFace (G:=G))
lemma even_apply (x : Top.Forms G R.side): R.evenPart G x = (2:ℝ)⁻¹ • (x+R.mirrorFace x):=rfl
lemma hits_even (x : Top.Forms G R.side) : R.evenPart G x∈R.evenForms G:= by rw [R.mem_even,even_apply,map_smul,map_add,mirror_face_twice,add_comm (R.mirrorFace x)]
lemma fixes_even (x : Top.Forms G R.side) (h : x∈R.evenForms G): R.evenPart G x=x:= by rw [even_apply,(R.mem_even _).1 h,← two_smul ℝ,inv_smul_smul₀ two_ne_zero]

/-- The range with its *actual* Hessian normalization will read `2 • starProjection` here.
This is exactly the image sum. -/
lemma invariant_projection (x : Top.Forms G R.side) : (R.Equivariant G).starProjection x = R.evenPart G ((Top.Curled G R.side).starProjection x) :=by
  let P:= Top.Curled G R.side; have he : P.starProjection x∈ P:= Submodule.starProjection_apply_mem ..
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ⟨R.hits_even _,P.smul_mem _ (P.add_mem he (R.mirror_mem _ he))⟩ ?_
  intro w hw
  rw [inner_sub_left,R.even_apply,real_inner_smul_left, inner_add_left,symmetric]
  rw [(R.mem_even w).mp hw.1,Submodule.inner_starProjection_left_eq_right,Submodule.starProjection_eq_self_iff.mpr hw.2]; ring
lemma projection_formula (x : Top.Forms G R.side): (2:ℝ) • (R.Equivariant G).starProjection x = (Top.Curled G R.side).starProjection x+ (Top.Curled G R.side).starProjection (R.mirrorFace x):=by rw [R.invariant_projection,even_apply,smul_inv_smul₀ (by norm_num), R.mirror_star]

namespace Tree
variable {R} (T : R.Tree)
lemma mirrors (x : T.Free → E) : R.mirrorLink (T.covering x)= T.covering x:=funext fun i=> by rw [mirror_apply,T.covering_reflect,neg_neg]

def absorb (T : R.Tree) (A : R.Bonds→E) (x : R.Vertex) : E:= if hx:x=T.root then 0 else
  let e:= T.edge x hx
  T.absorb A (T.parent x) + if R.dst e=x then A e.val else -A e.val
termination_by T.rank x
decreasing_by exact T.closer x hx

omit [Module ℝ E] in
lemma absorb_derivative (A : R.Bonds→E) (e : R.Link) (he:e∈T.edges):T.absorb A (R.dst e)-T.absorb A (R.src e)= A e.val:=by
  obtain ⟨x,hx,rfl⟩:=(T.mem_edges e).1 he
  have h:T.parent x≠x:= by intro ha; have h:=T.closer x hx; rw [ha] at h; omega
  rcases T.joins x hx with ⟨a,b⟩|⟨a,b⟩ <;> rw [a,b,absorb.eq_1 T A x,dif_neg hx] <;> simp [*]

lemma complete (A : R.Bonds→E) (h : R.mirrorLink A=A) : ∃ x:T.Free→E, R.curl (T.covering x)= R.curl A:=by
  let B:= R.derivative ((T.absorb A) ∘ R.vertex)
  have he:∀ i:R.Link, i∈T.edges→ B i.val=A i.val:=fun i hi=> T.absorb_derivative A i hi
  let x (i : T.Free) := (A-B) i.val.val
  refine ⟨x, ?_⟩
  have hh : T.covering x=A-B:=R.mirror_reps _ _ (T.mirrors x) (by rw [map_sub,h]; exact congr_arg _ (R.mirror_derivative (T.absorb A))) fun i=> by
    by_cases H:i∈ T.edges
    · rw [T.covering_at,Pi.sub_apply,prolong,dif_pos H,he _ H,sub_self]
    rw [T.covering_at,prolong,dif_neg H]
  rw [hh,map_sub,show R.curl B=0 from R.curl_derivative ..,sub_zero]

def compass : T.Field G→ₗ[ℝ] Top.Forms G R.side:= Top.curl G R.side ∘ₗ T.logdir
lemma compass_at (u : T.Field G) (i : Top.Faces R.side):T.compass u i=T.linearCurl u i:= by rw [compass,LinearMap.comp_apply,R.cover_curl,T.collected]; rfl
lemma even_compass (u : T.Field G):T.compass u∈R.Equivariant G := by
  refine ⟨(R.mem_even _).2 ?_,⟨_,rfl⟩⟩; change R.mirrorFace (Top.curl G R.side _) = Top.curl G R.side _
  rw [← R.cover_mirror,T.collected,T.mirrors]; rfl
lemma compass_onto (x : Top.Forms G R.side) (h : x∈R.Equivariant G): ∃ u,T.compass u=x:= by
  obtain ⟨u,hu⟩:=h.2
  let A:= collect G u
  let B:= (2:ℝ)⁻¹ • (A+R.mirrorLink A)
  have he : R.mirrorLink B=B:=by dsimp only [B]; rw [map_smul,map_add, mirror_link_twice,add_comm (R.mirrorLink A)]
  have hh (i : Top.Faces R.side): R.curl B i=x i:= by
    dsimp only [B]; rw [map_smul,map_add,Pi.smul_apply, Pi.add_apply, R.curl_mirror]; unfold A
    simp only [← R.cover_curl,hu, ← R.face_apply x i, (R.mem_even _).1 h.1,← two_smul ℝ,inv_smul_smul₀ (two_ne_zero (α:=ℝ))]
  obtain ⟨v,hv⟩:=T.complete B he
  refine ⟨v,?_⟩; ext i j; rw [compass_at,linearCurl,LinearMap.comp_apply,hv,hh]
lemma compass_bilinear (x y : T.Field G): inner ℝ (T.compass x) (T.compass y)= (2:ℝ)*T.quadratic G x y:= by rw [PiLp.inner_apply,T.quadratic_val]; simp only [T.compass_at]; ring
end Tree
end YM.XSpace.Period

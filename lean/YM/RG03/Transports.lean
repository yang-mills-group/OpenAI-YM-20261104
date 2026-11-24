import YM.Next.SCHEDULE.TensorCost

/-!
# Re-expression on the actual link fields: elementary curvature moves

Exact group and matrix identities before any mask or integration, and their left-derivative costs on the
common plaquette-healthy domain. No linearized-field substitution in the density. Intermediate higher
terms use defects of the *transported plaquette matrices* (positive curvature valuation); apply the
continuous real-linear curvature projector as the last operation. Generalizes the group's forward-cube
idea in `YM.Trace2.BareEquation` and uses the `YM.Next.SCHEDULE` path calculus, here for signed steps, RG
`Healthy`, and arbitrarily many (fixed finite) ordered derivatives. Everything holds on the actual torus,
even for wrapping paths, without a gauge choice. There is no cost from periodization in the estimates.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG03
open Wilson RG Lattice
open Next.Scheduling.Wages Work.G07
open scoped ContDiff Matrix.Norms.Frobenius Topology BigOperators Classical
variable {G : Gauge} {n : Side}

/-- Positivity/smallness gate of the path estimate: true support includes the incident base of the
canonical positive face (or parallel axes whose circuit cancels). -/
structure Circuit where
  prefix' : Walk
  a : Step
  b : Step

namespace Circuit

def path (w : Circuit) := (w.prefix' ++ oriented w.a w.b) ++ Lattice.reverse w.prefix'
def turn (w : Circuit) : Circuit := ⟨w.prefix',w.b,w.a⟩
def start (w : Circuit) (o : Site n) := stop o w.prefix'
def location (w : Circuit) (o : Site n) := atFace (w.start o) w.a w.b
def supply (w : Circuit) (o : Site n) (X : Support n) : Prop := w.a.dir=w.b.dir ∨ w.location o ∈ X

def holonomy (w : Circuit) (o : Site n) (U : Config G n) := travel U o w.path
def raw (w : Circuit) (o : Site n) (U : Config G n) := G.mat (w.holonomy o U)
def defect (w : Circuit) (o : Site n) (U : Config G n) := w.raw o U - 1
def curvature (w : Circuit) (o : Site n) (U : Config G n) := G.curvature (w.holonomy o U)

lemma holonomy_eq (w : Circuit) (o : Site n) (U : Config G n) :
    w.holonomy o U = travel U o w.prefix' * travel U (w.start o) (oriented w.a w.b) * (travel U o w.prefix')⁻¹ := by
  rw [holonomy,path,travel_append,travel_append,stop_append, stop_oriented,travel_reverse]
  rfl
lemma holonomy_turn (w:Circuit) (o:Site n) (U:Config G n) : w.turn.holonomy o U = (w.holonomy o U)⁻¹ := by
  simp_rw [holonomy_eq]; unfold turn; simp only [start]
  rw [oriented_swap w.a w.b]; group
lemma raw_turn (w:Circuit)(o:Site n)(U:Config G n) : w.turn.raw o U = G.mat (w.holonomy o U)⁻¹ := by rw [raw,holonomy_turn]

lemma conjugation (w:Circuit)(o:Site n)(k: Site n → G.El)(U:Config G n) :
    w.holonomy o (gauge k U) = (k o) * w.holonomy o U * (k o)⁻¹ := by
  have hs : stop o w.path = o := by rw [path,stop_append,stop_append,stop_oriented,reverse_stop]
  rw [holonomy,travel_gauge,hs]; rfl
lemma holonomy_local (w:Circuit)(o:Site n) : LocalOn (visits o w.path).toFinset (w.holonomy (G:=G) o) := by
  intro U V h
  exact travel_local o w.path _ _ fun i hi hi'=> h i (List.mem_toFinset.mpr hi) (List.mem_toFinset.mpr hi')

lemma chord_of_healthy (w:Circuit)(t:ℝ)(ht:0≤t)(o:Site n)(U:Config G n){X:Support n}
    (hx : w.supply o X) (hu : Healthy t X U) : G.chord (w.holonomy o U) ≤ t := by
  rw [holonomy_eq,G.chord_conj]
  rw [price_shift_pos G.chord U G.chord_inv (fun k g=>G.chord_conj g k)]
  have hz (p:PlaqAxes) (hp:w.location o ∈ X) : G.chord (faceValue U (w.location o,p)) ≤ t := by
    by_contra hc
    have hh : w.location o ∈ flags t U := (flags_spec ..).2 ⟨(w.location o,p),by exact List.mem_toFinset.mpr List.mem_cons_self,by simpa only [not_le] using hc⟩
    exact Finset.disjoint_left.mp hu hp hh
  rcases lt_trichotomy w.a.dir w.b.dir with h|h|h
  · exact hz ⟨(w.a.dir,w.b.dir),h⟩ (Or.resolve_left (id hx : w.a.dir=w.b.dir ∨ _) h.ne)
  · rw [h]
    suffices travel U (atFace (w.start o) w.a w.b) (square w.b.dir w.b.dir) = 1 by rw [this,G.chord_one]; exact ht
    simp only [square,travel,Step.pos_read,Step.neg_read,Step.vec_pos,Step.vec_neg,mul_one]
    simp [sub_eq_add_neg,add_assoc]
  rw [show square w.a.dir w.b.dir=oriented (posDir w.a.dir) (posDir w.b.dir) from rfl, oriented_swap,G.chord_inv]
  exact hz ⟨(w.b.dir,w.a.dir),h⟩ (Or.resolve_left (id hx : w.a.dir = w.b.dir ∨ _) (Ne.symm h.ne))

lemma curvature_eq (w:Circuit)(o:Site n)(U:Config G n) : w.curvature o U = projector G (w.defect o U) := by
  have h1 : projector G (1:G.Mat) = G.curvature 1 := rfl
  rw [defect,map_sub,h1,G.curvature_unit,sub_zero]; rfl
lemma defect_small (w:Circuit)(t:ℝ)(ht:0≤t)(o:Site n)(U:Config G n){X:Support n}
    (hx : w.supply o X) (hu : Healthy t X U) : ‖w.defect o U‖ ≤ t * G.colorScale := by
  rw [defect,raw]
  have h := w.chord_of_healthy t ht o U hx hu
  change ‖_‖ / G.colorScale ≤ _ at h
  exact (div_le_iff₀ G.colorScale_pos).mp h

end Circuit

/-- Positive path exchange AND its full nonlinear replacement with common endpoint at finite period. -/
theorem exchange (U:Config G n)(x:Site n)(a b:Step) :
    travel U x [a,b] = travel U x (oriented a b) * travel U x [b,a] := by
  rw [oriented]; simp only [travel]
  have hx : x+a.vec+b.vec = x+b.vec+a.vec := add_right_comm ..
  rw [show (x+a.vec+b.vec+a.rev.vec : Site n)=x+b.vec by rw [hx,a.vec_rev]; simp]
  rw [hx,b.read_rev U x,a.read_rev U (x+b.vec)]; group

private theorem swapped (U:Config G n)(o:Site n)(r s:Walk)(a b: Step) :
    travel U o ((r++[a,b])++s) = (Circuit.mk r a b).holonomy o U * travel U o ((r++[b,a])++s) := by
  simp_rw [Circuit.holonomy_eq,travel_append,stop_append,Circuit.start]
  rw [exchange U (stop o r) a b]
  rw [show stop (stop o r) [a,b] = stop (stop o r) [b,a] from add_right_comm ..]
  group

def afterSwap (r s : Walk) (a b c d : Step) : Circuit := ⟨((r ++ [a,b])++s),c,d⟩

theorem holonomy_align (r s : Walk) (a b c d : Step) (U:Config G n) (o:Site n) :
    (afterSwap r s a b c d).holonomy o U = (Circuit.mk r a b).holonomy o U *
      (afterSwap r s b a c d).holonomy o U * (Circuit.mk r b a).holonomy o U := by
  rw [Circuit.holonomy_eq (w:=afterSwap r s a b c d),Circuit.holonomy_eq (w:=afterSwap r s b a c d), afterSwap,afterSwap]
  simp only [Circuit.start,stop_append]
  rw [show stop (stop o r) [a,b] = stop (stop o r) [b,a] from add_right_comm ..]
  rw [swapped U o r s a b]
  rw [show Circuit.mk r b a = Circuit.turn (Circuit.mk r a b) from rfl,Circuit.holonomy_turn]; group

/-- The three terms added by one swap have degree ≥2, on actual holonomies. -/
def incrementMat {A:Type*} [NonUnitalNonAssocRing A] (x y z : A) := z*x + x*y + z*x*y

theorem defect_align (r s : Walk) (a b c d : Step) (U:Config G n)(o:Site n) :
    (afterSwap r s a b c d).defect o U = (afterSwap r s b a c d).defect o U +
      incrementMat ((afterSwap r s b a c d).defect o U) ((Circuit.mk r b a).defect o U) ((Circuit.mk r a b).defect o U) := by
  let h := (Circuit.mk r a b).raw o U; let j := (Circuit.mk r b a).raw o U; let z := (afterSwap r s b a c d).raw o U
  have he : h*j=1 := by
    unfold h j; rw [Circuit.raw,show Circuit.mk r b a = (Circuit.mk r a b).turn from rfl,Circuit.raw_turn,←G.mat_mul]; simp
  have hx : (afterSwap r s a b c d).defect o U = h*z*j - 1 := by
    unfold Circuit.defect Circuit.raw h z j; rw [holonomy_align]; simp only [Circuit.raw,G.mat_mul]
  rw [hx]; change _ = (z-1) + incrementMat (z-1) (j-1) (h-1)
  calc _ = h*z*j - h*j := by rw [he]
       _ = _ := by unfold incrementMat; noncomm_ring

def block1 (a b:Step) : Circuit := ⟨[],a,b⟩
def block2 (x a b: Step) : Circuit := ⟨[x],a,b⟩

theorem holonomy_braid (a b c : Step)(U:Config G n)(o:Site n) :
    (block1 a b).holonomy o U * (block2 b a c).holonomy o U * (block1 b c).holonomy o U =
      (block2 a b c).holonomy o U * (block1 a c).holonomy o U * (block2 c a b).holonomy o U := by
  have he (x y z : Step) : (block1 x y).holonomy o U=travel U o [x,y,z]*(travel U o [y,x,z])⁻¹ := by
    rw [show [x,y,z]=([]++[x,y])++[z] from rfl, swapped]; simp [block1]
  have hf (x y z : Step) : (block2 z x y).holonomy o U=travel U o [z,x,y]*(travel U o [z,y,x])⁻¹ := by
    rw [show [z,x,y]=([z]++[x,y])++[] from rfl, swapped]; simp [block2]
  rw [he a b c,hf a c b,he b c a,hf b c a,he a c b,hf a b c]; group

/-- Higher terms of a cube triple (distinct from the swap `incrementMat`). -/
def higher {A:Type*} [NonUnitalNonAssocRing A] (x y z : A) := x*y+y*z+x*z+x*y*z

def cubeClosure (o:Site n) (a b c : Step) (U:Config G n) := let f(w:Circuit):=w.curvature o U
   f (block1 a b)+f (block2 b a c)+f (block1 b c)-f (block2 a b c)-f (block1 a c)-f (block2 c a b)

/-- Exact Bianchi correction as a polynomial starting at degree two. -/
theorem bianchi (o:Site n)(a b c:Step)(U:Config G n) : cubeClosure o a b c U = (let f(w:Circuit):=w.defect o U
    projector G (higher (f (block2 a b c)) (f (block1 a c)) (f (block2 c a b)) -
      higher (f (block1 a b)) (f (block2 b a c)) (f (block1 b c)))) := by
  simp only [cubeClosure]
  simp_rw [Circuit.curvature_eq,← map_add,← map_sub]
  congr 1
  have h := congr_arg G.mat (holonomy_braid a b c U o)
  simp only [G.mat_mul] at h
  let A:=(block1 a b).raw o U; let B:=(block2 b a c).raw o U; let C:=(block1 b c).raw o U
  let D:=(block2 a b c).raw o U; let E:=(block1 a c).raw o U; let F:=(block2 c a b).raw o U
  let e: G.Mat → G.Mat := fun z=>z-1
  change e A+e B+e C-e D-e E-e F= higher (e D) (e E) (e F) - higher (e A) (e B) (e C)
  suffices (e A+e B+e C-e D-e E-e F)+higher (e A) (e B) (e C) - higher (e D) (e E) (e F)=0 by rw [←sub_eq_zero]; rw [←this]; abel
  convert sub_eq_zero.mpr (show A*B*C=D*E*F from h) using 1; unfold higher e; noncomm_ring

end YM.RG03

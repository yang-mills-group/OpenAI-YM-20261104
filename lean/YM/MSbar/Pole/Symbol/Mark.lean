import YM.MSbar.Pole.Scale.Counter

/-!
# Momentum and tensor slot usage in MS counterterms
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Filter Set MeasureTheory Ambient Momentum Age Mellin Curtain
open scoped Topology ContDiff BigOperators Classical
namespace Symbol
variable {I : Type} {J : Type} [Fintype I] [Fintype J] {n : ℕ}
-- univariate linear test; use before quotient or angular traces.
structure Along {E : Type} [AddCommGroup E] [Module ℝ E] (f : E → ℂ) : Prop where
  add : ∀ a b : E, f (a+b)=f a+f b
  smul : ∀ (r:ℝ) a, f (r • a)=r • f a

namespace Along
variable {E : Type} [AddCommGroup E] [Module ℝ E] {f g:E→ℂ}

def lift (h:Along f) : E →ₗ[ℝ] ℂ:= ⟨⟨f,h.add⟩,h.smul⟩
lemma plus (h:Along f) (p:Along g) : Along (fun u=> f u +g u):=by
  constructor
  · intro a b; rw [h.add,p.add]; ring
  intro r a; rw [h.smul,p.smul,smul_add]
lemma scale (h:Along f) (c:ℂ): Along (fun u=>c*f u):=
  ⟨fun a b=>by rw [h.add,mul_add],fun r a=>by rw [h.smul,mul_smul_comm]⟩
lemma zero : Along (fun _ : E=> (0:ℂ)):=⟨by intros; simp,by intros; simp⟩
lemma sum {Z : Type*} (s : Finset Z) (F : Z → E → ℂ) (h : ∀ v∈s,Along (F v)):Along (fun u=>∑ v∈s,F v u):= by
  induction s using Finset.induction_on with
  | empty=> simpa using (zero (E:=E))
  | @insert i s hi ih=> simpa only [Finset.sum_insert hi] using (h i (Finset.mem_insert_self ..)).plus (ih fun z hz=>h z (Finset.mem_insert_of_mem hz))
end Along

-- coherent add and multiply not assumed from single-ε families; let CT analysis preserve.
def Listen (J:Finset I) (F : Cloud I):= ∀ n (x y : External I n), (∀ i∈J,x i=y i)→F n x=F n y

def Tone (C : Cloud I) (i:I):=∀ n (x:External I n),Along fun v=> C n (update x i v)

structure Shape (read angles : Finset I) (F : Cloud I) : Prop where
  sees : Listen read F
  angle : ∀ i∈angles,Tone F i
namespace Shape
variable {U V:Finset I} {F G:Cloud I} (h:Shape U V F)
include h
lemma add (g:Shape U V G) : Shape U V (F+G) := ⟨fun n x y hx=> congr_arg₂ (· + ·) (h.sees n x y hx) (g.sees n x y hx),fun i hi n x=>Along.plus (h.angle i hi n x) (g.angle i hi n x)⟩
lemma scale (c:ℂ): Shape U V (c•F):= ⟨fun n x y hx=> congr_arg (c*·) (h.sees n x y hx),fun i hi n x=>(h.angle i hi n x).scale c⟩
omit h
lemma zero : Shape U V (0:Cloud I):=⟨fun _ _ _ _=>rfl,fun i _ n _=> Along.zero⟩
lemma sum {Z:Type*} (s:Finset Z)(F:Z→Cloud I)(h : ∀ i∈s,Shape U V (F i)):Shape U V (∑ i∈s,F i):=by
  induction s using Finset.induction_on with
  | empty=> simpa using zero (I:=I) (U:=U) (V:=V)
  | @insert i s hi ih=>rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add (ih fun _ hv => h _ (Finset.mem_insert_of_mem hv))
lemma transmitted {Z : Type*} {t : Filter Z} [t.NeBot] {f : Z→Cloud I} (h : ∀ᶠ z in t, Shape U V (f z)) (hp : ∀ n x,Tendsto (fun z=> f z n x) t (nhds (F n x))) : Shape U V F:=by
  refine ⟨fun n x y he=>tendsto_nhds_unique_of_eventuallyEq (hp n x) (hp n y) (h.mono fun z hz => hz.sees n x y he),fun i hi n x=>?_⟩
  refine ⟨fun a b=>tendsto_nhds_unique_of_eventuallyEq (hp n _) ((hp n _).add (hp n _)) (h.mono fun z hz=>(hz.angle i hi n x).add a b), fun r a=>?_⟩
  exact tendsto_nhds_unique_of_eventuallyEq (hp n _) (tendsto_const_nhds.smul (hp n _)) (h.mono fun z hz=>(hz.angle i hi n x).smul r a)
include h
lemma move_by (D:Finset I) (he:Disjoint D V) (t:ℝ) : Shape U V (fun n x=> F n (move D t x)):= by
  constructor
  · intro n x y hh; exact h.sees n _ _ (fun i hi=> by simp_rw [move,hh i hi])
  intro i hi n x; have hj:i∉D:=fun hh=>Finset.disjoint_left.1 he hh hi
  have hh z: move D t (update x i z)=update (move D t x) i z:=by
    ext1 v; by_cases hv:v=i
    · subst v; simp [hj,move]
    simp [hv,move]
  simp_rw [hh]; exact h.angle i hi ..

omit h
/-- read an MS local pole graph before projection; residues inherit finite
label and per-polarization direction identities. -/
lemma residue {k:ℕ} {C:ℕ→Cloud I} {F : ℂ→Cloud I} (h : Vortex 0 (F - purePolar k C))
    (hp : ∀ᶠ z in approaching, Shape U V (F z)) (j:ℕ)(hj:j<k) : Shape U V (C j):=by
  obtain ⟨R,G,hr,H,h⟩:= h
  have ht (n : ℕ) (x : External I n) : Tendsto (fun z => G z n x) approaching (nhds (G 0 n x)) := ((H.budget _).region _ (zone_zero hr) _).continuousAt.continuousWithinAt
  have hm z (hz:z∈slit R) n x : F z n x= (∑ i∈Finset.range k, z⁻¹^(i+1)*C i n x)+G z n x := by
    rw [← h _ hz]; simp only [purePolar,pow_zero,one_mul,Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; ring
  constructor
  · intro n x y hh; apply sub_eq_zero.mp
    refine (point_pole (k:=k) (fun i=> C i n x-C i n y) _ (( (ht n y).sub (ht n x)).congr' ?_)) j hj
    filter_upwards [neighborhood hr,hp] with z hz hw; have hP:=hw.sees n x y hh; rw [hm z hz,hm z hz] at hP
    simp_rw [mul_sub,Finset.sum_sub_distrib]; linear_combination hP * (-1)
  intro i hi n x
  let X(j:ℕ)(v) := C j n (update x i v); let A z v:= G z n (update x i v)
  have h₀ v: Tendsto (fun z => A z v) approaching (nhds (A 0 v)):=ht n _
  constructor
  · intro a b; apply sub_eq_zero.mp
    refine point_pole (k:=k) (fun j=> X j (a+b)-(X j a+X j b)) _ ((( (h₀ a).add (h₀ b)).sub (h₀ (a+b))).congr' ?_) j hj
    filter_upwards [neighborhood hr,hp] with z hz hw
    have hP: F z n (update x i (a+b))=F z n (update x i a)+F z n (update x i b):=(hw.angle i hi n x).add a b
    rw [hm z hz,hm z hz,hm z hz] at hP
    unfold A X; simp_rw [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]; linear_combination -hP
  intro r a; apply sub_eq_zero.mp
  refine point_pole (k:=k) (fun j=> X j (r • a) - r • X j a) _ ((((tendsto_const_nhds (x:=r)).smul (h₀ a)).sub (h₀ (r • a))).congr' ?_) j hj
  filter_upwards [neighborhood hr,hp] with z hz hw
  have hP: F z n (update x i (r • a))=r • F z n (update x i a):=(hw.angle i hi n x).smul r a
  rw [hm z hz,hm z hz, smul_add,Finset.smul_sum] at hP
  unfold X A; simp_rw [mul_sub,mul_smul_comm,Finset.sum_sub_distrib]; linear_combination -hP
end Shape
end Symbol
end YM.MSbar.Pole

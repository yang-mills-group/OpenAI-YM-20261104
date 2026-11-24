import YM.SchemeConversionRG11.Maxwell.Cone

/-! # Geometry for a bi-residue. One moving point and an arbitrary but finite
number of distinct non-null real spectators. -/

set_option autoImplicit false
noncomputable section

namespace YM.SchemeConversionRG11.Corona
open Function Filter Maxwell Set MvPolynomial
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {n : ℕ} {x : Fin n → Space} {a y : Fin n}

def Dispersed (x : Fin n → Space) : Prop := ∀ i j, i ≠ j → sq (x i-x j)≠0

def rayScale (v z : Space) := sq v/(2 * dot z v)

def endpoint (v z : Space) := rayScale v z • z

def flight (v z : Space) := dot z v
lemma ray_ne {z v : Space} (hw : sq v≠0) (hx : dot z v ≠ 0) : rayScale v z≠0 := div_ne_zero hw (mul_ne_zero (by norm_num) hx)
lemma endpoint_null (v : Space) {z : Space} (h : sq z=0) : sq (endpoint v z)=0 := by rw [endpoint,sq_scale,h,mul_zero]
lemma endpoint_dot {z v : Space} (hx : dot z v ≠ 0) : 2*dot (endpoint v z) v = sq v := by
  rw [endpoint,dot_scale,rayScale]; field_simp
lemma endpoint_both {z v : Space} (h : sq z=0) (hx : dot z v ≠ 0) : sq (endpoint v z-v)=0 := by
  rw [sq_sub,endpoint_null v h,endpoint_dot hx]; ring
lemma endpoint_self {v z : Space} (hp : sq v≠0) (hq : sq z=0) (hx : sq (z-v)=0) : dot z v≠0 ∧ endpoint v z=z := by
  rw [sq_sub,hq,zero_add] at hx
  have hs := sub_eq_zero.mp hx
  have hn : dot z v≠0 := by intro h; exact hp (hs.trans (by rw [h,mul_zero]))
  refine ⟨hn,?_⟩; unfold endpoint rayScale; rw [hs,div_self (mul_ne_zero (by norm_num) hn),one_smul]

/-- At two chosen non-null separated points xa,xy. Coordinates d=b-xa.
Other pairs from b must be non-null. -/
structure Blip (x : Fin n → Space) (a y : Fin n) (d : Space) : Prop where
  first : sq d=0
  second : sq (d-(x y-x a))=0
  across (i : Fin n) : i≠a → i≠y → sq (d-(x i-x a))≠0

lemma Blip.sharp {d : Space} (h : Blip x a y d) (hp : Dispersed x) (hy : y≠a) : dot d (d-(x y-x a))≠0 := by
  rw [dot_comm,dot_sub,dot_self,h.first,zero_sub]; exact neg_ne_zero.mpr (by rw [dot_comm]; exact (endpoint_self (hp y a hy) h.first h.second).1)

def shield (v w : Space) := plot (sq w • v - sq v • w)

lemma shield_read {z v w : Space} (hz : sq z=0) (hd : dot z v ≠0) :
    aeval z (shield v w) = dot z v * sq (endpoint v z-w) := by
  unfold shield; rw [plot_at, dot_comm,dot_sub,dot_scale,dot_scale,dot_comm v,dot_comm w,
    sq_sub, endpoint_null v hz,endpoint,dot_scale,rayScale]; field_simp; ring
lemma shield_ok {v w : Space} (hv : sq v≠0) (hw : sq w≠0) (h : v ≠ w) : ¬Obstructs (shield v w) := by
  apply plots
  intro ht
  rw [sub_eq_zero] at ht
  have hh := congrArg sq ht; rw [sq_scale,sq_scale] at hh
  have he : sq v=sq w := by
    apply mul_right_cancel₀ (mul_ne_zero hv hw : sq v*sq w≠0); linear_combination -hh
  apply h; rw [← he] at ht; exact smul_right_injective Space hv ht

abbrev Stray (a y : Fin n) := {i : Fin n//i≠a ∧ i≠y}

def shields (x : Fin n → Space) (a y : Fin n) := plot (x y-x a) * ∏ i : Stray a y, shield (x y-x a) (x i-x a)
lemma cone_prod {ι : Type*} (s : Finset ι) (f : ι → Script) (h : ∀ i∈s, ¬Obstructs (f i)) : ¬Obstructs (∏ i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; intro h; exact one_ne_zero ((map_one (aeval (R:=ℂ) (0:Space))).symm.trans (h _ sq_zero))
  | @insert i s hi ih => rw [Finset.prod_insert hi]; exact cone_ok (h i (by simp)) (ih (fun i hi ↦ h i (by simp [hi])))
lemma shields_ok (hp : Dispersed x) (ha : a≠y) : ¬Obstructs (shields x a y) := by
  let T := hp y a (Ne.symm ha)
  refine cone_ok (plots (fun he ↦ T (he ▸ sq_zero))) (cone_prod _ _ ?_)
  intro i _; apply shield_ok T (hp i a i.property.1)
  exact fun h ↦ hp i y i.property.2 (by rw [sub_left_inj.mp h]; exact (by simp [sq,dot]))
lemma shields_have (x : Fin n → Space) {a y d} (hd : sq d=0) (h : aeval d (shields x a y)≠0) :
    dot d (x y-x a)≠0 ∧ Blip x a y (endpoint (x y-x a) d) := by
  rw [shields,map_mul,plot_at,map_prod,mul_ne_zero_iff,Finset.prod_ne_zero_iff] at h
  refine ⟨h.1,endpoint_null _ hd, endpoint_both hd h.1,fun i hi he ↦ ?_⟩
  have hv := h.2 ⟨i, hi, he⟩ (Finset.mem_univ _); rw [shield_read hd h.1] at hv
  exact (mul_ne_zero_iff.mp hv).2

def hyper (P : Script) (r : ℕ) : Prop := ∀ x : Space, ∀ t : ℂ, aeval (t • x) P=t^r * aeval x P

def parabel (v : Space) : Script →ₐ[ℂ] Script := aeval fun i ↦ C (sq v/2)*X i - C (v i)*plot v
lemma parabel_at (v z : Space) (hz : dot z v≠0) (P : Script) :
    aeval z (parabel v P) = aeval ((dot z v) • (endpoint v z-v)) P := by
  induction P using MvPolynomial.induction_on with
  | C => simp [parabel]
  | add _ _ hp hg => rw [map_add,map_add,map_add,hp,hg]
  | mul_X p i hp =>
    rw [map_mul,map_mul,map_mul,hp]; congr 1
    unfold parabel
    simp only [aeval_X, map_sub,map_mul,aeval_C, Algebra.algebraMap_self,RingHom.id_apply,plot_at,Pi.smul_apply,Pi.sub_apply]
    simp only [endpoint,rayScale, Pi.smul_apply,smul_eq_mul]
    field_simp
lemma parabel_ok (v : Space) (h : sq v≠0) {P : Script} {r : ℕ} (hp : ¬Obstructs P) (he : hyper P r) :
    ¬Obstructs (parabel v P) := by
  intro ht; apply hp
  have hv : sq (-v)≠0 := by rw [sq_neg]; exact h
  apply pierce (plots (x:= -v) (fun h ↦ hv (h ▸ sq_zero)))
  intro z hz hw; rw [plot_at] at hw
  let d := endpoint (-v) z+v
  have hD : sq (d-v)=0 := by simp only [d,add_sub_cancel_right]; exact endpoint_null _ hz
  have hd : sq d=0 := by simpa [d,sub_neg_eq_add] using endpoint_both hz hw
  have hh := ht d hd; obtain ⟨hF,hG⟩ := endpoint_self h hd hD
  rw [parabel_at v _ hF,he,hG,show d-v=endpoint (-v) z by simp only [d,add_sub_cancel_right],endpoint,he] at hh
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ hF))).resolve_left (pow_ne_zero _ (ray_ne hv hw))

theorem cone_extend {u r : ℕ} {p q : Script} (hx : Dispersed x) (ha : a≠y) (hp : hyper p u) (hq : hyper q r) (he : ¬Obstructs p)
    (h : ∀ d : Space, Blip x a y d → aeval (d-(x y-x a)) p≠0 → aeval d q=0) : Obstructs q := by
  let v := x y-x a
  have hv : sq v≠0 := hx y a (Ne.symm ha)
  apply pierce (cone_ok (parabel_ok v hv he hp) (shields_ok hx ha)) -- order?
  intro z hz hV
  rw [map_mul,mul_ne_zero_iff] at hV
  obtain ⟨hN,hB⟩ := shields_have x hz hV.2
  have he := hV.1; rw [parabel_at v _ hN,hp] at he
  have hw := h _ hB (mul_ne_zero_iff.mp he).2
  rw [endpoint,hq] at hw
  exact (mul_eq_zero.mp hw).resolve_left (pow_ne_zero _ (ray_ne hv hN))

end YM.SchemeConversionRG11.Corona

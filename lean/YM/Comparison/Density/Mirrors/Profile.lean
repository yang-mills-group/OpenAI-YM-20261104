import YM.Comparison.Density.Mirrors.Pull
/-!
# Boundary stencil types

Centred local evaluation of a site inside the repeated mirror volume
depends only on its `shade`: which axes have a boundary within the
stencil window, and on such axes which boundary and at what distance.
This is an exact statement on group fields. It uses reflection symmetry
of the **whole** unmarked vacuum stencil, not of an arbitrary term
before oriented averaging.
-/
set_option autoImplicit false
namespace YM.Comparison.Density.Mirrors
open Lattice Function Finset

abbrev Wall (r : Side) := Option (Bool × Fin r.val)

/-- `none` denotes the full interior; `.some (false,d)` the low end. -/
def shade (r k : Side) (x : Per (quad k)) : Wall r :=
  let a := wave k x
  let l := (a+k.val).natAbs
  let h := ((k.val : ℤ)-a).natAbs
  if hh : l < r.val then some (false,⟨l,hh⟩)
  else if ht : h < r.val then some (true,⟨h,ht⟩)
  else none

lemma shade_none (r k : Side) (x : Per (quad k)) :
    shade r k x=none ↔ -(k.val:ℤ)+r.val≤wave k x ∧ wave k x≤(k.val:ℤ)-r.val := by
  have he:= wave_range k x
  dsimp only [shade]
  split_ifs <;> simp <;> omega

lemma shade_false (r k : Side) (x : Per (quad k)) (q : Fin r.val) :
    shade r k x = some (false,q) ↔ wave k x = -(k.val:ℤ)+q.val := by
  have he:= wave_range k x
  have hq:= q.isLt
  dsimp only [shade]
  split_ifs <;> simp [Fin.ext_iff] <;> omega

lemma shade_true (r k : Side) (hr : r.val ≤ k.val) (x : Per (quad k)) (q : Fin r.val) :
    shade r k x = some (true,q) ↔ wave k x = (k.val:ℤ)-q.val := by
  have he:= wave_range k x
  have hq:= q.isLt
  dsimp only [shade]
  split_ifs <;> simp [Fin.ext_iff] <;> omega

def localWave {r : Side} (s : Wall r) (i : ℤ) : ℤ := match s with
  | none=>i
  | some (false,d)=> if i< -(d.val:ℤ) then -(2*(d.val:ℤ))-i else i
  | some (true,d) => if i> (d.val:ℤ) then 2*(d.val:ℤ)-i else i

lemma shade_local (r k : Side) (hr : r.val ≤ k.val) (x : Per (quad k)) (u : ℤ)
    (hl : -(r.val:ℤ) ≤ u) (hu : u ≤ r.val) :
    wave k (((wave k x+u:ℤ):Per (quad k)))=wave k x+localWave (shade r k x) u := by
  cases he:shade r k x with
  | none=>
    obtain ⟨ht,hx⟩ := (shade_none r k x).1 he
    exact wave_core _ _ (by omega) (by omega)
  | some v=>
    obtain ⟨b,d⟩:=v; have h:= d.isLt
    cases b
    · have hz:= (shade_false r k x d).1 he
      rw [localWave]; split
      · rw [wave_lower k _ (by omega) (by omega)]; omega
      exact wave_core _ _ (by omega) (by omega)
    have hz:= (shade_true r k hr x d).1 he
    rw [localWave]; split
    · rw [wave_upper k _ (by omega) (by omega)]; omega
    exact wave_core _ _ (by omega) (by omega)

abbrev Sky (r : Side) := Axis → Wall r
def sky (r k : Side) (x : Site (quad k)) : Sky r := shade r k ∘ x

def localPlace {r : Side} (s : Sky r) (z : Cover) : Cover := fun i => localWave (s i) (z i)

def localStep {r : Side} (s : Sky r) (z : Cover) (i : Axis) : Step :=
  if localPlace s (z+step i) i=localPlace s z i+1 then posDir i else negDir i

variable {K : Type*} [Group K]

/-- Local stencil near a reflected boundary. Input already based at
   the reflected point in the old lattice. -/
def profile {r : Side} (s : Sky r) (U : Links ℤ K) : Links ℤ K := fun e =>
  (localStep s e.1 e.2).read U (localPlace s e.1)

@[simp] lemma profile_clear (r : Side) (U : Links ℤ K) : profile (r:=r) (fun _ => none) U = U := by
  funext e; obtain ⟨x,i⟩:=e
  rw [profile]; simp only [localStep,localPlace,Pi.add_apply,localWave,step_apply,↓reduceIte]; rfl

/-- Reflect coordinates out of the mirror region to the chosen
representative by a signed affine symmetry ABOUT THE ENDPOINTS. -/
lemma mirrors (k : Side) (x : Site (quad k)) :
    ∃ (s : Signed) (b : Site (quad k)), (∀ z, reflectAt k (affine s b z)=reflectAt k z) ∧
        affine s b x=wrap (quad k) (reflectAt k x) := by
  let s : Signed := ⟨Equiv.refl _,fun i=>decide (x i ≠ (wave k (x i): Per (quad k)))⟩
  let b : Site (quad k) := fun i=> if s.flip i then ((2*(k.val:ℤ):ℤ) : Per (quad k)) else 0
  have he (z : Site (quad k)) (i : Axis) : affine s b z i =
      if x i = (wave k (x i) : Per (quad k)) then z i else ((2*(k.val:ℤ):ℤ) : Per (quad k)) - z i := by
    by_cases hx : x i=(wave k (x i) : Per (quad k))
    · simp only [affine,Signed.act,Pi.add_apply,b,s,Equiv.refl_symm,Equiv.refl_apply,decide_eq_true_eq]; rw [if_neg (not_not.mpr hx), if_neg (not_not.mpr hx), if_pos hx, add_zero]
    simp only [affine, Signed.act, Pi.add_apply, s,Equiv.refl_symm, Equiv.refl_apply, b,decide_eq_true_eq]
    rw [if_pos hx,if_pos hx,if_neg hx]; abel
  refine ⟨s,b,fun z=>?_,?_⟩
  · funext j; change wave k _=wave k _; rw [he]; split; rfl
    exact wave_reflect k _
  funext j; change affine s b x j = (↑(wave k (x j)) : Per _); rw [he]; split
  · assumption
  rename_i hh
  have hb := (wave_period k (x j)).resolve_left hh
  let a:= wave k (x j)
  change x j = ((2*(k.val:ℤ)-a:ℤ):Per (quad k)) at hb
  change _ = (a:Per (quad k))
  rw [hb,← Int.cast_sub,sub_sub_cancel]

lemma reflect_local (r k : Side) (hr : r.val ≤ k.val) (x : Site (quad k)) {z : Cover} (hz : z∈box r.val) :
    reflectAt k (wrap (quad k) z+wrap (quad k) (reflectAt k x))=localPlace (sky r k x) z+reflectAt k x := by
  rw [add_comm,←map_add,add_comm (localPlace (sky r k x) z)]
  funext i
  exact shade_local r k hr (x i) (z i) (box_test.mp hz|>.1 i) (box_test.mp hz|>.2 i)

lemma local_agrees (r k : Side) (hr : r.val ≤ k.val) (x : Site (quad k)) (U : Links ℤ K) :
    Agrees (box r.val)
      (expandAt (wrap (quad k) (reflectAt k x)) (field k U))
      (profile (sky r k x) (translate (reflectAt k x) U)) := by
  rintro ⟨z,i⟩ hz hv
  let p:= wrap (quad k) z + wrap (quad k) (reflectAt k x)
  let s:= sky r k x
  have he : reflectAt k p=localPlace s z + reflectAt k x:= reflect_local r k hr x hz
  have hg : reflectAt k (p+step i)=localPlace s (z+step i)+reflectAt k x := by 
    rw [show p + step i=wrap (quad k) (z+step i) + wrap (quad k) (reflectAt k x) by simp only [p,map_add,wrap_step]; abel]; exact reflect_local r k hr x hv
  have hf : wave k (p i+1)=localPlace s (z+step i) i + reflectAt k x i := by
    have ht:= congr_fun hg i
    simpa only [reflectAt,Function.comp_apply,Pi.add_apply,step_apply,↓reduceIte] using ht
  have hl : wave k (p i)=localPlace s z i + reflectAt k x i := congr_fun he i
  have hm : risen k p i=localStep s z i := by
    unfold risen localStep; rw [hf,hl]; split_ifs <;> first | rfl | omega
  change (risen k p i).read U (reflectAt k p)=_
  rw [hm,he,profile]
  change _ = (localStep s z i).read (translate _ U) _
  rw [← pull_one, Step.pull_read, Step.rotate_one, affine, Signed.act_one]

lemma evaluate_profile {Y : Type*} (f : Links ℤ K → Y) (r k : Side) (hr : r.val ≤ k.val)
    (hs : ∀ U s, f (pull s 0 U)=f U) (h : LocalOn (box r.val) f) (U : Links ℤ K) (x : Site (quad k)) :
    f (expandAt x (field k U))= f (profile (sky r k x) (translate (reflectAt k x) U)) := by
  obtain ⟨s,b,hq,hw⟩:= mirrors k x
  rw [← field_fixed k s b hq U,expandAt_pull,hs,hw]
  exact h _ _ (local_agrees r k hr x U)
end YM.Comparison.Density.Mirrors

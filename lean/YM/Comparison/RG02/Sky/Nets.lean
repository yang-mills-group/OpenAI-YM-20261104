import YM.Next.STATIONARY.Loops.Fourier
import YM.Push.FREE_RESOLVENT.Torus
import YM.Pert.Bulk.Sites
/-!
# Connected cover diagrams: winding calculus on coarse lattice sites

Roots fix translation. Factor tensor slots each specify a displacement. Take the standard period
sum before contracting for a torus calculation, so even if two slot endpoints in the complete
contraction happen to coincide they are **not** tied to the same winding instruction in that
periodization. Cover evaluation instead requires mutual compatibility. External displacements to
hold fixed when reading the calculation aren't used to recognize winding cost. In particular no
nearest-image denominator here and NO application on the inversion quotient. Cells/distances use
`c`, same as the actual coarse site geometry. Can encode carries or further native rescaling in
factor values as needed (don't conflate costs). Any coarse torus size. In applying to ideal Fk/A
use same translation-repeated forest and branch and the actual unmasked/no-hole Cover prescription
primitive inputs; price only via corresponding genuine estimates there. No price on choice of this
gauge, real locality or representation here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Sky
open Lattice RG Precision Laurent Function Finset
open scoped BigOperators Classical

variable {P F : Type*} {D : F→ Type*}

-- A tensor uses offsets recorded at *that* placement. Similar factors can have many instances.
structure Net (P : Type*) {F : Type*} (D : F→ Type*) where
  base : F→P
  sees : ∀ i, D i→ P
namespace Net
variable (K : Net P D)

abbrev Plan (D : F→ Type*) (A : Type*) := ∀ i, D i→A

variable {R : Type*} [AddCommGroup R]
def meter (a : P → R) : Plan D R := fun v j=> a (K.sees v j)-a (K.base v)
def Slot (x y : P) := (∃ i j,K.base i=x ∧ K.sees i j=y) ∨ (∃ i j,K.base i=y ∧ K.sees i j=x)

/-! `Route` needn't be geodesic; allow ANY finite exposure, no period dependence. -/
inductive Rail : P→ P → Type (max (max (u_1) (u_2)) u_3)
| stay (x : P) : Rail x x
| read {x y} (v) (h : y=K.base v) (j : D v) : Rail x y → Rail x (K.sees v j)
| ret {x y} (v) (j : D v) (h : y= K.sees v j) : Rail x y → Rail x (K.base v)

namespace Rail
variable {K} {x y z : P}
def thenRide (f : Rail K x y) : {z : P} → Rail K y z → Rail K x z
| _, .stay _ => f
| _, .read v h j r=> .read v h j (thenRide f r)
| _, .ret v j h r=> .ret v j h (thenRide f r)
def reverse : {y : P} → Rail K x y → Rail K y x
| _, .stay _=> .stay _
| _, .read v h j r=> thenRide (ret v j rfl (.stay _)) (cast (by rw [h]) (reverse r))
| _, .ret v j h r=> thenRide (read v rfl j (.stay _)) (cast (by rw [h]) (reverse r))

def tally (ds : Plan D R) : {y:P} → Rail K x y → R
| _, .stay _=>0
| _, .read v _ j r=>tally ds r + ds v j
| _, .ret v j _ r=>tally ds r - ds v j
def marks : {y:P} → Rail K x y → ℕ
| _, .stay _=>0
| _, .read _ _ _ r=> marks r+1
| _, .ret _ _ _ r=> marks r+1
lemma charges (f : Rail K x y) (a : P → R) : f.tally (K.meter a) = a y-a x := by
   induction f with
   | stay=> simp [tally]
   | read v h j r ih=> unfold tally; rw [ih]; unfold meter; subst_vars; abel
   | ret v j h r ih=> unfold tally; rw [ih]; unfold meter; subst_vars; abel
lemma map (f : Rail K x y) {R' : Type*} [AddCommGroup R'] (A : R →+ R') (ds : Plan D R) :
    f.tally (fun v=> A ∘ ds v) = A (f.tally ds) := by
   induction f with
   | stay=> simp [tally]
   | read v h j r ih=> simp only [tally,ih, map_add,comp_apply]
   | ret v j h r ih=>simp only [tally,ih, map_sub,comp_apply]
end Rail

variable {K} {x y z o : P}
lemma step_slot (h:Slot K x y) : Nonempty (Rail K x y) := by
   rcases h with ⟨i,j,rfl,rfl⟩|⟨i,j,rfl,rfl⟩
   · exact ⟨Rail.read i rfl j (.stay _)⟩
   exact ⟨Rail.ret i j rfl (.stay _)⟩
abbrev Reaches (o x : P) := Nonempty (Rail K o x)
lemma slips : Reaches (K:=K) x x := ⟨Rail.stay _⟩
lemma spans (v : F) (j : D v) : Reaches (K:=K) (K.base v) (K.sees v j) := step_slot (.inl ⟨v,j,rfl,rfl⟩)
lemma through (h : Reaches (K:=K) x y) (h' : Reaches (K:=K) y z) : Reaches (K:=K) x z := h.elim fun X=> h'.map fun q=> Rail.thenRide X q
lemma again (h : Reaches (K:=K) x y) : Reaches (K:=K) y x := h.map Rail.reverse

-- called when a connected contraction plan is chosen before positions.
structure Guide (K : Net P D)(o : P) where
   ride : ∀ p, Rail K o p
   start : ride o=Rail.stay _
variable (K o)
def Open := ∀ x, Reaches (K:=K) o x
variable {K o}
lemma Open.any (h:Open K o) (x y:P) : Reaches (K:=K) x y := through (again (h x)) (h y)
def Open.guide (h : Open K o) : Guide K o where
   ride x:= if he : x=o then cast (by rw [he]) (Rail.stay (K:=K) o) else Classical.choice (h x)
   start:=by simp
variable (Y : Guide K o)

def circuit (ds : Plan D R) : P→ R := fun p=> (Y.ride p).tally ds
lemma circuit_self (ds : Plan D R): circuit Y ds o=0:= by rw [circuit,Y.start]; rfl
lemma circuit_origin (x : P→R)(h : x o=0): circuit Y (K.meter x)=x := funext fun z=> by rw [circuit,(Y.ride z).charges,h,sub_zero]
-- coords anchored on any pivot, all in one orientation.
abbrev Options (P R : Type*)(o : P)[Zero R] := {x:P → R// x o=0}
namespace Guide
variable {Y} (Z : Options P R o)
def arrive (Y : Guide K o) (ds : Plan D R) : Options P R o := ⟨circuit Y ds,circuit_self Y ds⟩
lemma landed (Y : Guide K o): Y.arrive (K.meter Z.val)=Z := Subtype.ext (circuit_origin Y Z.val Z.property)
end Guide

def Coherent (d : Plan D R) := K.meter (circuit Y d)=d
lemma coherence (x : Options P R o) : Coherent Y (K.meter x.val) := by rw [Coherent,circuit_origin Y x.val x.property]

-- winding
variable (c:Side) (d:Plan D Cover)
def page : Plan D (Site c) := fun i=> wrap c ∘ d i
def toTorus (x:Options P Cover o) : Options P (Site c) o:=⟨wrap c ∘ x.val,by simp only [comp_apply,x.property,map_zero]⟩
lemma Guide.transport : Y.arrive (page c d) = toTorus c (Y.arrive d) := Subtype.ext (funext fun p=> (Y.ride p).map _ _)
lemma Guide.binder (h:K.meter (Y.arrive d).val=d) : K.meter (toTorus c (Y.arrive d)).val = page c d:= by
   funext i j; unfold meter toTorus page; dsimp only; simp only [comp_apply, ← map_sub]; exact congrArg (wrap c) (congr_fun (congr_fun h i) j)
lemma Guide.stay (h : Coherent Y d) : Coherent Y (page c d) := by
   change K.meter (Y.arrive _).val = _
   rw [Guide.transport]; exact Guide.binder _ _ _ h

variable [Fintype F] [∀ i, Fintype (D i)]

def mileage {S : Type*}[Fintype S] (d:S→Cover) := ∑ s, Pert.Bulk.length (d s)
lemma mileage_cost {S : Type*}[Fintype S] (w:S→Cover) : 0≤ mileage w:= Finset.sum_nonneg (fun _ _=> by dsimp [Pert.Bulk.length]; positivity)
def toll := ∑ i,mileage (d i)
lemma toll_nonneg : 0 ≤ toll d := sum_nonneg fun i _ => mileage_cost (d i)
lemma toll_here (v : F)(j : D v) : Pert.Bulk.length (d v j) ≤ toll d:= le_trans (b:=mileage (d v)) (Finset.single_le_sum (f:=fun k=> Pert.Bulk.length (d v k)) (fun _ _=>by unfold Pert.Bulk.length; positivity) (Finset.mem_univ j)) (Finset.single_le_sum (fun i _=> mileage_cost (d i)) (Finset.mem_univ v))
namespace Rail
lemma overhead (f: Rail K x y) : Pert.Bulk.length (f.tally d) ≤ f.marks * toll d := by
   induction f with
   | stay=> simp [tally,marks,Pert.Bulk.length,size]
   | read v h j r ih=> simp only [tally,marks,Nat.cast_add,Nat.cast_one,add_mul,one_mul]; exact le_trans (Pert.Bulk.length_add ..) (add_le_add ih (toll_here d v j))
   | ret v j h r ih=>
       simp only [tally,marks,Nat.cast_add,Nat.cast_one,add_mul,one_mul]; rw [sub_eq_add_neg]; apply le_trans (Pert.Bulk.length_add ..); rw [Pert.Bulk.length_neg]; gcongr; apply toll_here
end Rail

namespace Guide
variable [Fintype P]
def rate := (2:ℝ) * ∑ i,(Y.ride i).marks -- sum coercion clarify
omit [Fintype F] [∀ i, Fintype (D i)] in
lemma enough : 0 ≤ rate Y:= by unfold rate; positivity
omit [Fintype F] [∀ i, Fintype (D i)] in
lemma singly (p:P): (↑(Y.ride p).marks:ℝ) ≤ rate Y/2:= by
   simp only [rate,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)]
   exact_mod_cast (Finset.single_le_sum (f:=fun i=> (Y.ride i).marks) (fun i _=>Nat.zero_le _) (Finset.mem_univ p))
lemma cap (p:P): Pert.Bulk.length ((Y.arrive d).val p) ≤ rate Y /2 * toll d:= le_trans ((Y.ride p).overhead d) (mul_le_mul_of_nonneg_right (singly Y p) (toll_nonneg d))
lemma all (p q:P): Pert.Bulk.length ((Y.arrive d).val p-(Y.arrive d).val q) ≤ rate Y*toll d := by
   have h:= Pert.Bulk.length_add ((Y.arrive d).val p) (-((Y.arrive d).val q)); rw [Pert.Bulk.length_neg] at h; rw [sub_eq_add_neg]; nlinarith [cap Y d p,cap Y d q]

lemma odd (h : Coherent Y (page c d)) (he : ¬ Coherent Y d) : (c.val:ℝ) ≤ (Y.rate+1)* toll d := by
   change K.meter (Y.arrive (page c d)).val= _ at h
   rw [Y.transport] at h
   obtain ⟨i,hi⟩:=Function.ne_iff.mp he; obtain ⟨j,hj⟩:=Function.ne_iff.mp hi
   let x:Options P Cover o := Y.arrive d
   have hb : wrap c (K.meter x.val i j-d i j)=0:= by
      rw [map_sub, sub_eq_zero]; have hy := congr_fun (congr_fun h i) j
      change wrap c (x.val (K.sees i j))- wrap c (x.val _) = _ at hy
      exact (map_sub _ _ _).trans hy
   apply le_trans (b:=Pert.Bulk.length (K.meter x.val i j-d i j)) (by exact_mod_cast Stationary.winds_size _ hb (sub_ne_zero.mpr hj))
   have hy := Pert.Bulk.length_add (K.meter x.val i j) (-(d i j)); rw [Pert.Bulk.length_neg] at hy
   exact le_trans (b:=Pert.Bulk.length (K.meter x.val i j) + Pert.Bulk.length (d i j)) (by rw [sub_eq_add_neg]; exact hy) (by rw [add_mul,one_mul]; exact add_le_add (Y.all d (K.sees i j) (K.base i)) (toll_here d i j))
end Guide
end Net
end YM.Comparison.RG02.Sky

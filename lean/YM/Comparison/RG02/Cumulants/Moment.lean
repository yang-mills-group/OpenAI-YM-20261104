import YM.Comparison.RG02.Cumulants.Split

/-!
# Shared-state moments

Exact coefficients on arbitrary test/source names. The state is a *single* linear functional.
For genuine measure versions see also the integrability & trajectory adapters (in other files).
Take conditional-normalized or tag probabilities, or polynomial Gaussian blend against one &
any covariance. No positivity needed here; only normalization by weight AT THE WHOLE TABLE;
examples include computing a formal coefficient with subtractions. `FactorsAt` criterion for
zero joint cumulant. Derivation, linear-in-one-mark, and mixing of states.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Comparison.RG02.Cumulants
open YM.Marker YM.Multi YM.Primitives.GCC.Anchor
open YM.Extra.Trajectories (connected connected_quiet pass_connected)
open Finset
open scoped BigOperators Classical

variable {V : Type*} [DecidableEq V] {R : Census V}

-- Root identity with GCC's fused calculus
lemma quotient_singleton [Fintype V] (t : R.Mode) (i : V) (m : Poly R)
    (hm : m.part R.quiet = 1) (hi : i∈t.val) :
    (quotient t.val {i} m).part t = (connected m).part t := by
  -- split in closed t zone
  let H := withinSet t.val m
  have hH : H.part R.quiet=1 := by unfold H; rwa [begin_inner_part,if_pos (by simp [Census.quiet])]
  have hx : (connected H).part t=(connected m).part t := by rw [conn_inside t.val m hm, begin_inner_part, if_pos (Subset.refl _)]
  have he : YM.Primitives.GCC.Anchor.root t.val {i} m = highlight i H := rfl
  let L := without {i} H
  change (root t.val {i} m *inverseMass L).part t = _
  rw [← hx, ← show (highlight i (connected H)).part t=_ from (highlight_part i (connected H) t).trans (if_pos hi),connected_root i H hH,← he]
  apply congrArg (fun x : Poly R=> x.part t)
  -- may use UpTo inverses
  apply contains_mul_congr (root_contains t.val {i} m); intro j hj
  refine UpTo.pass (T:=j.val) ?_ j (Subset.refl _)
  have hv : UpTo j.val L H := fun s hs => Eq.trans (begin_outer_part _ _ s) (if_pos (hj.mono_left hs))
  exact fun s hs => by rw [Poly.part_neg, Poly.part_neg, hv.conn s hs]

section
variable {A : Type*} [CommMonoid A]

/-- Moment at any allowed combination. `f` is e.g. a linear functional on all
    polynomials, or an integral (validity on the admitted moments checked separately;
    nothing excludes costs where some other reads are undefined). -/
def moments (R : Census V) (f : A → ℂ) (w : V → A) : Poly R :=
  Poly.inject fun s => f (∏ i∈s.val,w i)
lemma moments_part (f : A → ℂ) (w : V → A) (s : R.Mode) :
    (moments R f w).part s = f (∏ i∈s.val,w i) := rfl
lemma moments_quiet (f : A → ℂ) (w : V → A) :
    (moments R f w).part R.quiet = f 1 := by simp [moments_part,Census.quiet]

variable [Fintype V]
theorem cumulant_formula (f : A → ℂ) (w : V → A) (s : R.Mode) (h : f 1 = 1) :
    (connected (moments R f w)).part s = ∑ t∈shards R s,
      mobiusTop t.val.card * ∏ i∈t.val, f (∏ j∈i.sites,w j) := log_partition _ (by rwa [moments_quiet]) s

theorem equal_occurrences (f : A → ℂ) (v w : V → A) (s : R.Mode) (h : ∀ i∈s.val,v i=w i) :
    (connected (moments R f v)).part s = (connected (moments R f w)).part s := by
  have he : UpTo s.val (moments R f v) (moments R f w) := fun u hu =>
    congrArg f (Finset.prod_congr rfl (fun i hi => h i (hu hi)))
  exact he.conn s (Subset.refl _)

omit [Fintype V] in
/-- Identity used only when *all products*, e.g. those under a Haar or conditional Gaussian
    integral, really factor. `t.val` locations/marker occurrences are indices, not a claim of
    locality wrt physical distance. -/
def FactorsAt (f : A → ℂ) (w : V → A) (t : R.Mode) (U : Finset V) : Prop :=
  ∀ s : R.Mode, s.val ⊆ t.val → f (∏ i∈s.val,w i) =
      f (∏ i∈s.val∩U,w i) * f (∏ i∈s.val\U,w i)

theorem cumulant_split (f : A → ℂ) (w : V → A) (t : R.Mode)
    (hf : f 1=1) {U : Finset V} (hi : (t.val∩U).Nonempty) (ho : (t.val\U).Nonempty)
    (h : FactorsAt f w t U) :
    (connected (moments R f w)).part t = 0 :=
  conn_crossing U _ ((moments_quiet f w).trans hf) t h hi ho

end

section Multilinear
variable {A : Type*} [CommSemiring A] [Algebra ℂ A] -- unnecessary ℚ etc avoid
variable (f : A →ₗ[ℂ] ℂ) (h : f 1=1)
open Function

-- multilinearity in a block (first identity for additive and scalar, then sum extension).
-- Keep the same pinned Census and same value v.
lemma moment_with_root (w : V → A) {s:R.Mode} (i : V) (hi : i∈s.val) (x : A) :
    (moments R f (update w i x)).part s = f (x * ∏ j∈s.val.erase i,w j) := by
  rw [moments_part,← mul_prod_erase _ _ hi,update_self,
    Finset.prod_congr rfl (g:=w) (fun j hj => update_of_ne (ne_of_mem_erase hj) ..)]

lemma moment_without_root (w : V → A) {s:R.Mode} (i : V) (hi : i∉s.val) (x : A) :
    (moments R f (update w i x)).part s = (moments R f w).part s := by
  exact congrArg (fun a : A=>f a) (Finset.prod_congr rfl (s₁:=s.val) (s₂:=s.val) (fun j hj => update_of_ne
    (fun (he : j=i)=>hi (he ▸ hj)) x w))

lemma invariant_denominator (w : V → A) {s:R.Mode} (i : V) (x : A) :
    outer s.val {i} (moments R f (update w i x)) = outer s.val {i} (moments R f w) := by
  ext t; simp only [outer_part]
  split_ifs with h; exact moment_without_root f w i (Finset.disjoint_singleton_right.mp h.2) x
  rfl

variable [Fintype V]
include h
lemma cumulant_add (w : V → A) {s:R.Mode} (i : V) (hi : i∈s.val) (x y : A) :
    let m (a : A) := (connected (moments R f (update w i a))).part s
    m (x+y)=m x+m y := by
  intro m
  let r (a:A):=root s.val {i} (moments R f (update w i a))
  let M := inverseMass (outer s.val {i} (moments R f w))
  have hm a : m a=(r a*M).part s := by
    unfold m; rw [← quotient_singleton s i _ ( (moments_quiet (⇑f) _).trans h) hi, quotient, invariant_denominator]
  have hr : r (x+y)=r x+r y := by
    ext t; simp only [r, root_part, singleton_subset_iff, Poly.part_plus]; split_ifs with h
    · simp_rw [moment_with_root f w i h.2, add_mul, map_add]
    simp
  rw [hm,hr,hm,hm,add_mul,Poly.part_plus]

lemma cumulant_smul (w : V → A) {s:R.Mode} (i : V) (hi : i∈s.val) (x : A) (z : ℂ) :
    let m (a : A) := (connected (moments R f (update w i a))).part s
    m (z•x)=z*m x := by
  intro m
  let r (a:A):=root s.val {i} (moments R f (update w i a))
  let M := inverseMass (outer s.val {i} (moments R f w))
  have hm a : m a=(r a*M).part s := by
    unfold m; rw [← quotient_singleton s i _ ( (moments_quiet (⇑f) _).trans h) hi, quotient, invariant_denominator]
  have hr : r (z • x)=z • r x := by
    ext t; simp only [r, root_part, singleton_subset_iff, Poly.part_smul]; split_ifs with h
    · simp only [moment_with_root f w i h.2, smul_mul_assoc, map_smul, smul_eq_mul]
    simp
  rw [hm,hr, hm, smul_mul_assoc, Poly.part_smul]

def rootCumulant (w : V → A) {s:R.Mode} (i : V) (hi : i∈s.val) : A →ₗ[ℂ] ℂ where
  toFun x := (connected (moments R f (update w i x))).part s
  map_add' := cumulant_add f h w i hi
  map_smul' c x := cumulant_smul f h w i hi x c

lemma cumulant_sum {ι:Type*} (L : Finset ι) (u : ι→A) (w : V→A) {s:R.Mode} {i : V}
    (hi : i∈s.val) :
    (connected (moments R f (update w i (∑ a∈L,u a)))).part s=
      ∑ a∈L, (connected (moments R f (update w i (u a)))).part s :=
  map_sum (rootCumulant f h w i hi) ..

end Multilinear

section Drivers

variable {A : Type*} [CommMonoid A]

/-- **All** exponent entries, not necessarily singleton insertions. Real exponent
    may use additional gas & quiet entries; these are not mixed in this `pass` identity. -/
def driven (f : A → ℂ) (d : Hot R → A) : Poly R :=
  substitute R (moments (parts R) f d)

lemma driven_quiet (f : A → ℂ) (d : Hot R → A) : (driven f d).part R.quiet=f 1 := by
  rw [driven,substitute_quiet,moments_quiet]
lemma driven_part (f : A → ℂ) (d : Hot R → A) (s : R.Mode) :
    (driven f d).part s=∑ t∈shards R s, f (∏ i∈t.val, d i) := substituted ..

variable [Fintype V]
lemma log_driven (f : A → ℂ) (d : Hot R → A) (s : R.Mode) (hf : f 1=1) :
    (connected (driven f d)).part s = ∑ t∈shards R s,
      (connected (moments (parts R) f d)).part t := by
  rw [driven, ← log_map (substitute R) substitute_quiet (show (moments (parts R) f d).part (parts R).quiet=1 from
    (moments_quiet f _).trans hf),substituted]

lemma driven_pass (d : Hot R → ℂ) : driven id d = Poly.pass (lit R d) := by
  ext s; rw [driven_part,pass_partition _ (part_lit_quiet _)]; simp_rw [part_lit,id]
end Drivers

section Mixing

variable {K : Type*} [Fintype K]

/-- Use also with complex/polarized counterpart when valid. `w` may have signed/zero terms. -/
def tagAverage (w : K → ℂ) : (K → ℂ) →ₗ[ℂ] ℂ where
  toFun a := ∑ i,w i*a i
  map_add' a b := by simp only [Pi.add_apply,mul_add, Finset.sum_add_distrib]
  map_smul' c b := by simp only [Pi.smul_apply, smul_eq_mul,RingHom.id_apply,Finset.mul_sum,mul_left_comm (w _)]
lemma averaged (w : K→ℂ) (hw : ∑ a,w a=1) : tagAverage w 1=1 := by
  unfold tagAverage; simp [hw]

/-- Coefficientwise coherent weight. Summing BEFORE any further logarithm. Signed weights
    allowed; if computing a conditional tilt via tagged likelihood and energy, the weight used
    should match that reference and the *later* normalization/quotient. -/
def mix (w : K → ℂ) (m : K → Poly R) := ∑ a, w a • m a
lemma mix_part (w : K→ℂ) (m : K→Poly R) (t : R.Mode) :
    (mix w m).part t=∑ a, w a*(m a).part t := by
  simp only [mix,Poly.part_sum,Poly.part_smul]

/-- Different insertions may use the same `d` and the same underlying random variable even
    when (in applications) the block of predictor reads overlaps. -/
lemma mix_moments {A : K→Type*} [∀ a,CommMonoid (A a)] (f : ∀ a,A a→ℂ)
    (w : K→ℂ) (d : V→∀ a,A a) (s : R.Mode) :
    (mix w (fun a=> moments R (f a) (fun i=>d i a))).part s =
      (moments R (fun g:∀ a,A a=>∑ a,w a*f a (g a)) d).part s := by
  simp only [mix_part,moments_part,Finset.prod_apply]

lemma substitute_mix (w : K→ℂ) (m : K → Poly (parts R)) :
    mix w (fun a=> substitute R (m a))=substitute R (mix w m) := by simp [mix]

lemma mix_driven {A : K→Type*} [∀ a, CommMonoid (A a)] (f : ∀ a,A a→ℂ)
    (w : K→ℂ) (d : Hot R→∀ a,A a) :
    mix w (fun a=> driven (f a) (fun i=>d i a)) =
      driven (fun g:∀ a,A a=>∑ a,w a*f a (g a)) d := by
  change mix w (fun a => substitute R _) = substitute R _
  rw [substitute_mix]; apply congrArg (substitute R) (Poly.ext fun s => mix_moments ..)

variable [Fintype V]

/-- **Law of total cumulance** at any admissible marker grade. `m(a)` can be itself the
 formal moment polynomial in coupling and markers. The joint mixed cumulant is exactly the
 sum of outer tag cumulants of the conditional connected blocks. Connection across those
 blocks is again required (use `cumulant_split`), and is *not* merely by the conditional
 covariance. Useful also when the conditional Gaussian depends on these tags. -/
lemma total_log (t : R.Mode) (m : K → Poly R) (w : K→ℂ)
    (hw : ∑ a,w a=1) (hm : ∀ a,(m a).part R.quiet=1) :
    (connected (mix w m)).part t = ∑ s∈shards R t,(connected (moments (parts R)
      (tagAverage w) (fun i a=> (connected (m a)).part i.val))).part s := by
  let d (i : Hot R) (a : K) := (connected (m a)).part i.val
  have he : m=fun a=>driven id (fun i=>d i a) := funext fun a=> by
    unfold d; rw [driven_pass,lit_identity _ (connected_quiet (hm a)),pass_connected (hm a)]
  calc
    _ = (connected (mix w (fun a=>driven id (fun i=>d i a)))).part t := congrArg (fun v => (connected (mix w v)).part t) he
    _ = _ := by rw [mix_driven]; apply log_driven; exact averaged w hw
end Mixing
end YM.Comparison.RG02.Cumulants

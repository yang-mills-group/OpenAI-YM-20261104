import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
/-!
# Marker coefficient as insertion differentiation *at zero*

Works for general Census incl excluded products, at fixed V (`Poly.pass`
and contributions evaluate only after truncation). Identify the actual
mixed partial of the full evaluated marked polynomial on independent complex
amplitude variables at zero. Not derivatives of arbitrary post-truncation
`square` formula at general x (drop jumps outside ideal before every such
use) nor derivatives in configuration/threshold. No Taylor-in-mask
justification. Ordinary coefficient on distinct slots, no factorial. Re-using
one differential source in a list requires distinct slots encoded first if
one wants powers; differentiated twice in THIS same variable in the stored
polynomial always vanishes. Same applies to forbidden partner sets. These
are important source corrections after any density identity on this algebra
and before comparison to a possibly untruncated analytic prescription.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Law
open Marker Function Finset
open scoped Topology BigOperators ContDiff
variable {V : Type} [DecidableEq V] {R : Census V}

-- squarefree interpolant (NOT a multiplicative evaluation). Include quiet.
def assess (d : Marker.Poly R) (z : V→ℂ) := ∑ i,d.part i * ∏ x∈i.val,z x

/-- dropping terms whose key after differentiation doesn't exist in a
formal ideal derivative would lead to zero for everything if one promoted
before differentiating. Here differentiate **after** restrictions as actual
polynomial representative. Product rule on `*` in Marker.Poly thereby gains
a projector; NOT a derivation internal to the ring, see `asymmetric`. -/
def below (i : V) (f : V → ℂ) (x : ℂ) := update f i x

def spring (i : V) (s : R.Mode) : R.Mode := ⟨s.val.erase i,R.down s.property _ (erase_subset ..)⟩

def single (i : V) (q : Marker.Poly R) := ∑ s : R.Mode, if i∈s.val then Poly.send (spring i s) (q.part s) else 0

def leaves (f : (V → ℂ)→ℂ) : List V→ (V → ℂ) → ℂ
  | [] => f
  | i::l => fun z => deriv (fun t => leaves f l (update z i t)) (z i)

lemma surface_apply (s : R.Mode) (c : ℂ) (z : V → ℂ) : assess (Poly.send s c) z=c*∏ x∈s.val,z x := by
  rw [assess, sum_eq_single s]
  · simp
  · intro b _ hh; rw [Poly.part_send,if_neg hh,zero_mul]
  simp
lemma surface_sum {I} (s : Finset I) (q : I→Marker.Poly R) (z) : assess (∑ i∈s,q i) z=∑ i∈s,assess (q i) z := by
  unfold assess; simp_rw [Poly.part_sum,sum_mul]; exact sum_comm

lemma rises (d : Marker.Poly R) (i : V) (z : V→ℂ) (t : ℂ) :
    HasDerivAt (fun t' => assess d (below i z t')) (assess (single i d) z) t := by
  have hx (s : Finset V) : HasDerivAt (fun t' => ∏ x∈s, below i z t' x) (if i∈s then ∏ x∈(s.erase i),z x else 0) t := by
    split
    next h =>
      have H (r : ℂ) : ∏ x∈s,below i z r x = r * ∏ x∈s.erase i,z x := by
        rw [← mul_prod_erase s _ h,below,update_self]; congr 1
        exact prod_congr rfl (fun j hj => update_of_ne (ne_of_mem_erase hj) ..)
      simp_rw [H]; simpa using (hasDerivAt_id' t).mul_const (∏ x∈s.erase i,z x)
    next h =>
      have H (r : ℂ) : ∏ x∈s,below i z r x = ∏ x∈s,z x := prod_congr rfl (fun j hj => update_of_ne (fun (he : j=i) => h (he ▸ hj)) ..)
      simp_rw [H]; exact hasDerivAt_const _ _
  unfold assess
  simp_rw [single,Poly.part_sum,sum_mul]
  conv in ∑ i : R.Mode,∑ j : R.Mode,_ => rw [sum_comm]
  -- sum identity and HasDerivAt.fun_sum
  convert HasDerivAt.fun_sum (u:=(univ : Finset R.Mode)) (fun s _ => (hx s.val).const_mul (d.part s)) using 1
  · rfl
  · rfl
  refine sum_congr rfl (fun s _ => ?_)
  split
  next h => exact surface_apply (spring i s) (d.part s) z
  simp

lemma neigh_add (i : V) (q r : Marker.Poly R) : single i (q+r)=single i q + single i r := by
  apply Marker.Poly.ext; intro s
  simp only [single,Poly.part_plus,Poly.part_sum,← sum_add_distrib]
  refine sum_congr rfl (fun j _ => ?_)
  split; simp only [Poly.part_send]; split <;> simp
  simp
lemma neigh_zero (i : V) : single i (0:Marker.Poly R)=0 := by
  apply Marker.Poly.ext; intro s; simp [single]
lemma neigh_unit (i : V) : single i (1:Marker.Poly R)=0 := by
  apply Marker.Poly.ext; intro s; rw [single, Poly.part_sum]
  refine (sum_eq_zero (fun j _ => ?_)).trans ?_
  · by_cases he : j=R.quiet
    · subst j; simp [Census.quiet]
    simp [he]
  rfl
lemma neigh_send (s : R.Mode) (i : V) (c : ℂ) : single i (Poly.send s c) = if i∈ s.val then Poly.send (spring i s) c else 0 := by
  rw [single,sum_eq_single s]
  · simp
  · intro b _ hb
    simp [hb]
  simp

def literal (f : Marker.Poly R) : List V → Marker.Poly R
  | [] => f
  | i::l => single i (literal f l)

lemma literal_fact (q : Marker.Poly R) (l : List V) (z : V→ℂ) :
    leaves (assess q) l z=assess (literal q l) z := by
  induction l generalizing z with
  | nil => rfl
  | cons i l ih =>
    rw [leaves]; simp_rw [ih,literal]
    exact (rises (literal q l) i z (z i)).deriv

-- explicit authorized monomial capture
lemma literal_send (s : R.Mode) (l : List V) (c : ℂ) :
    literal (Poly.send s c) l = if _H : l.Nodup ∧ l.toFinset ⊆ s.val then
      Poly.send (⟨s.val\l.toFinset,R.down s.property _ (sdiff_subset)⟩ : R.Mode) c else 0 := by
  induction l with
  | nil => simp [literal]
  | cons i l ih =>
    rw [literal,ih]
    by_cases he : l.Nodup ∧ l.toFinset ⊆s.val
    · rw [dif_pos he,neigh_send]
      by_cases h : i∈s.val\l.toFinset
      · rw [if_pos h,dif_pos (show (i::l).Nodup ∧ (i::l).toFinset⊆ s.val from ?_)]
        · apply congrArg (fun u:R.Mode => Poly.send u c)
          apply Subtype.ext; change (s.val\l.toFinset).erase i=s.val\(i::l).toFinset
          ext; simp; tauto
        obtain ⟨h1,h2⟩ := mem_sdiff.mp h
        simp only [List.nodup_cons,List.toFinset_cons,insert_subset_iff]; exact ⟨⟨by simpa using h2,he.1⟩,h1,he.2⟩
      rw [if_neg h,dif_neg (show ¬((i::l).Nodup ∧ (i::l).toFinset⊆ s.val) from ?_)]
      simp only [List.nodup_cons,List.toFinset_cons,insert_subset_iff]
      exact fun h' => h (mem_sdiff.mpr ⟨h'.2.1,by simpa using h'.1.1⟩)
    rw [dif_neg he,neigh_zero,dif_neg (show ¬((i::l).Nodup ∧ (i::l).toFinset⊆ s.val) from by simp only [List.nodup_cons,List.toFinset_cons,insert_subset_iff]; tauto)]

lemma literal_sum {I : Type*} (s : Finset I) (q : I → Marker.Poly R) (l : List V) :
    literal (∑ i∈s,q i) l=∑ i∈s,literal (q i) l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [literal,ih]
    let g : Marker.Poly R →+ Marker.Poly R := { toFun := single i, map_zero' := neigh_zero i,map_add' := neigh_add i }
    exact map_sum g ..

lemma at_send (s : R.Mode) (l : List V) (c : ℂ) :
    assess (literal (Poly.send s c) l) 0=if l.Nodup ∧ l.toFinset=s.val then c else 0 := by
  rw [literal_send]; split
  next h =>
    rw [surface_apply]
    split
    next he => simp [he]
    next he =>
      obtain ⟨i,hi⟩ : (s.val\l.toFinset).Nonempty := nonempty_iff_ne_empty.mpr (fun hg => he ⟨h.1,Subset.antisymm h.2 (sdiff_eq_empty_iff_subset.mp hg)⟩)
      rw [prod_eq_zero hi rfl,mul_zero]
  next h => simp only [if_neg (show ¬(l.Nodup ∧ l.toFinset=s.val) from fun hh => h ⟨hh.1,hh.2.le⟩)]; simp [assess]

/-- Repeated-key and prohibited terms are zero in the **stored law**,
not a claim about an unrestricted smooth functional supplied separately.
Use this for derivatives of d.density in `Checked` and in every
`Forms.Adjust` consumer. -/
theorem derivatives (q : Marker.Poly R) (l : List V) :
    leaves (assess q) l 0=if h : l.Nodup ∧ l.toFinset∈R.choices then q.part ⟨l.toFinset,h.2⟩ else 0 := by
  rw [literal_fact]
  conv_lhs => rw [← Poly.studs q,literal_sum,surface_sum]
  simp_rw [at_send]
  split
  next h =>
    rw [sum_eq_single (⟨l.toFinset,h.2⟩ : R.Mode)]
    · rw [if_pos ⟨h.1,rfl⟩]
    · intro b _ hb; exact if_neg (fun he => hb (Subtype.ext he.2.symm))
    simp
  next h => apply sum_eq_zero; intro s _; exact if_neg (fun (he : l.Nodup ∧ l.toFinset = s.val) => h ⟨he.1,he.2.symm ▸ s.property⟩)
end YM.RG3.Law

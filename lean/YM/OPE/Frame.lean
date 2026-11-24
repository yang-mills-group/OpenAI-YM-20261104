import YM.Euclid.Union
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# A fixed homogeneous-complement basis on the physical filtered union

Physical spaces and pin throughout are the all-spectator quotient of the given
Table. Construction assumes the same `DiffPlan.Inclusions` as in the transport
of `Spec.Final`; no choice of a new basis when increasing an output horizon.
-/
set_option autoImplicit false
noncomputable section

namespace YM.OPE
open Function Set
open scoped BigOperators

variable {G : Gauge} {L : Register G} (S : Table L) (P : DiffPlan S)

/-- One grading-compatible basis convention (no scalar product normalization
or rotational covariance of the particular splitting is a prerequisite for
its existence as this object). `channels` are finite in each degree. -/
structure Frame where
  channels : ℕ → ℕ
  field {d : ℕ} : Fin (channels d) → S.Field d
  basis : Module.Basis ((d : ℕ) × Fin (channels d)) ℂ S.Union
  placed (d : ℕ) (i : Fin (channels d)) : basis ⟨d,i⟩ = S.pin d (field i)
  exhaust (d : ℕ) : Submodule.span ℂ (basis '' {j | j.1 ≤ d}) = LinearMap.range (S.pin d)

/-- Step complement chosen without any later length, horizon or phase. -/
private def increment : (n : ℕ) → Submodule ℂ (S.Field n)
  | 0 => ⊤
  | n+1 => (LinearMap.range (P.rise (Nat.le_succ n))).exists_isCompl.choose

private lemma forms_step (n) : IsCompl (LinearMap.range (P.rise (Nat.le_succ n))) (increment S P (n+1)) :=
    Submodule.exists_isCompl _ |>.choose_spec

local notation "R" n => increment S P n
local notation "E" => increment S P
private abbrev Slots (d) := Fin (Module.finrank ℂ (increment S P d))
private abbrev TotalSlots := Sigma (Slots S P)

private def spelling (j : TotalSlots S P) : S.Union := S.pin j.1 (Module.finBasis ℂ ↥(R j.1) j.2).val

variable (hs : S.Symmetric) (hp : P.Inclusions S)
include hs hp

private lemma ranges_mono : Monotone (fun d => LinearMap.range (S.pin d)) := by
  intro i j hij y hy
  obtain ⟨x,rfl⟩ := LinearMap.mem_range.mp hy
  exact LinearMap.mem_range.mpr ⟨P.rise hij x, P.stays hs hp _ _⟩

private lemma contained {d} (y : S.Field d) : S.pin d y ∈ Submodule.span ℂ (spelling S P '' {j | j.1 ≤ d}) := by
  let A (d : ℕ) := Submodule.span ℂ (spelling S P '' {j | j.1 ≤ d})
  change _ ∈ A d
  have h (n) (y : S.Field n) (he : y ∈ R n) : S.pin n y ∈ A n := by
    let b := Module.finBasis ℂ ↥(R n)
    let W := (S.pin n).comp (R n).subtype
    change W ⟨y,he⟩ ∈ A n
    rw [← b.sum_repr ⟨y,he⟩,map_sum]
    simp_rw [map_smul]
    exact (A n).sum_mem fun i _ => (A n).smul_mem _ (Submodule.subset_span ⟨⟨n,i⟩, show n ≤ n from le_rfl, rfl⟩)
  induction d with
  | zero => exact h _ _ trivial
  | succ n ih =>
    have hy : y ∈ LinearMap.range (P.rise (Nat.le_succ n)) ⊔ R (n+1) := by
      rw [(forms_step S P n).sup_eq_top]; trivial
    obtain ⟨a,⟨v,rfl⟩,z,hz,rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add,P.stays hs hp]
    exact (A _).add_mem ((Submodule.span_mono (by apply Set.image_mono; rintro j hj; exact Nat.le_succ_of_le hj)) (ih v)) (h _ z hz)

private lemma basic_independent : LinearIndependent ℂ (spelling S P) := by
  classical
  refine linearIndependent_iff'.mpr fun t c h => ?_
  let n := t.sup Sigma.fst
  have ht (j) (hj : j ∈ t) : j.1 ≤ n := Finset.le_sup (s:=t) hj
  have hu (j) (hj : j ∈ t) : j.2 ∈ (Finset.univ : Finset (Slots S P j.1)) := Finset.mem_univ _
  let φ i j := (Module.finBasis ℂ ↥(R i) j)
  let b' (i : ℕ) (j : Slots S P i) := if (⟨i,j⟩ : TotalSlots S P) ∈ t then c ⟨i,j⟩ else 0
  let b (i : ℕ) (j : Slots S P i) := b' i j • φ i j
  let y (i) := ∑ j, S.pin i ((b i j).val)
  let p (i : Σ d, Slots S P d) := S.pin i.1 ((b i.1 i.2).val)
  have he : ∑ i ∈ Finset.range (n+1), y i = 0 := by
    have he' : t ⊆ (Finset.range (n+1)).sigma (fun i => (Finset.univ : Finset (Slots S P i))) := by
      intro j hj; rw [Finset.mem_sigma]; exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (ht j hj)),hu _ hj⟩
    change (∑ i ∈ Finset.range (n+1), ∑ j, p ⟨i,j⟩) = 0
    rw [← Finset.sum_sigma,
      ← Finset.sum_subset he' (by rintro ⟨i,j⟩ _ hi; dsimp only [p,b,b']; rw [if_neg hi,zero_smul]; exact map_zero _)]
    rw [← h]; apply Finset.sum_congr rfl
    rintro ⟨i,j⟩ hj
    dsimp only [p,b,b']; rw [if_pos hj]; exact map_smul _ _ _
  have hv i : y i ∈ LinearMap.range (S.pin i) := (LinearMap.range (S.pin i)).sum_mem fun j _ => LinearMap.mem_range.mpr ⟨_,rfl⟩
  have hz : ∀ m : ℕ, ∑ i ∈ Finset.range (m+1), y i = 0 → ∀ i ≤ m, y i = 0 := by
    intro m; induction m with
    | zero => intro h j hj; obtain rfl : j=0 := Nat.eq_zero_of_le_zero hj; simpa using h
    | succ m ih =>
      intro he i hi
      let f := S.pin (m+1)
      let q := P.rise (Nat.le_succ m)
      let z : R (m+1) := ∑ j, b (m+1) j
      have h₁ : f z = y (m+1) := by
        change (f.comp (R (m+1)).subtype) z = _
        dsimp only [y,z]; rw [map_sum]; rfl
      have hw : f z ∈ LinearMap.range (S.pin m) := by
        rw [Finset.sum_range_succ,h₁.symm] at he
        rw [eq_neg_of_add_eq_zero_right he]
        exact (LinearMap.range (S.pin m)).neg_mem ((LinearMap.range (S.pin m)).sum_mem fun j hj =>
          (ranges_mono S P hs hp (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) (hv j)))
      obtain ⟨w,hw⟩ := LinearMap.mem_range.mp hw
      have hx : q w = z := S.pin_inj _ ((P.stays hs hp _ _).trans hw)
      have hy : (z:S.Field (m+1)) = 0 :=
        Submodule.disjoint_def.mp (forms_step S P _).disjoint _ (LinearMap.mem_range.mpr ⟨_,hx⟩) z.property
      have hm : y (m+1)=0 := h₁.symm.trans (hy ▸ f.map_zero)
      rw [Finset.sum_range_succ,hm,add_zero] at he
      rcases lt_or_eq_of_le hi with h'|rfl; exact ih he i (Nat.le_of_lt_succ h'); exact hm
  have hx (i) (hi : i ≤ n) := hz n he i hi
  rintro ⟨i,j⟩ hj
  have hy : ∑ l, b i l = 0 := by
    apply Subtype.val_injective
    apply S.pin_inj
    change (S.pin i) _ = (S.pin i) 0
    rw [(S.pin i).map_zero]
    change (LinearMap.comp (S.pin i) (Submodule.subtype _)) (∑ l, b i l) = 0
    rw [map_sum]
    exact hx i (ht _ hj)
  have hL : LinearIndependent ℂ (φ i) := Module.Basis.linearIndependent _
  simpa only [b',if_pos hj] using (linearIndependent_iff'.mp hL Finset.univ (b' i) hy j (Finset.mem_univ _))

private lemma basis_exists :
    ∃ b : Module.Basis (TotalSlots S P) ℂ S.Union, ⇑b = spelling S P := by
  have hs' := basic_independent S P hs hp
  have ht : ⊤ ≤ Submodule.span ℂ (Set.range (spelling S P)) := by
    intro v _
    obtain ⟨d,x,rfl⟩ := P.covered hs hp v
    exact Submodule.span_mono (Set.image_subset_range _ _) (contained S P hs hp x)
  exact ⟨Module.Basis.mk hs' ht, funext (Module.Basis.mk_apply hs' ht)⟩

private def basis' := (basis_exists S P hs hp).choose

variable {P} in
/-- A frame is fixed from the physical filtration alone, before any scale or
finite-arity request. -/
def newFrame : Frame S where
  channels d := Module.finrank ℂ (increment S P d)
  field := fun {d} i => (Module.finBasis ℂ ↥(increment S P d) i).val
  basis := basis' S P hs hp
  placed d i := congr_fun (basis_exists S P hs hp).choose_spec ⟨d,i⟩
  exhaust d := by
    change Submodule.span ℂ ((basis' S P hs hp) '' {j | j.fst ≤ d}) = _
    unfold basis'; rw [(basis_exists S P hs hp).choose_spec]
    refine le_antisymm (Submodule.span_le.mpr ?_) (fun x hx => ?_)
    · rintro x ⟨j,hj,rfl⟩
      exact ranges_mono S P hs hp hj (LinearMap.mem_range.mpr ⟨_,rfl⟩)
    obtain ⟨x,rfl⟩ := LinearMap.mem_range.mp hx
    exact contained S P hs hp x
end YM.OPE

namespace YM.OPE.Frame
open Function Set
open scoped BigOperators

variable {G : Gauge} {L : Register G} {S : Table L} (P : DiffPlan S) (F : Frame S)

abbrev Index := Sigma (fun d => Fin (F.channels d))

/-- Coefficient in the fixed graded convention of a genuine local field
vector (as element of the physical union). -/
def readout (j : F.Index) : S.Union →ₗ[ℂ] ℂ := (Finsupp.lapply j).comp F.basis.repr.toLinearMap

variable {F}
lemma readout_self (j : F.Index) (i : F.Index) : F.readout j (F.basis i) = if i=j then 1 else 0 := by
  classical
  change F.basis.repr (F.basis i) j = _
  rw [Module.Basis.repr_self]
  by_cases hi : i=j
  · subst i; rw [Finsupp.single_eq_same,if_pos rfl]
  rw [Finsupp.single_eq_of_ne (Ne.symm hi),if_neg hi]

lemma readout_entry {d} (i : Fin (F.channels d)) (j : F.Index) : F.readout j (S.pin _ (F.field i)) = if j = ⟨d,i⟩ then 1 else 0 := by
  rw [← F.placed d i, F.readout_self]; simp only [eq_comm]

lemma readout_cut {d} (B : S.Field d) {j : F.Index} (h : d < j.1) : F.readout j (S.pin _ B) = 0 := by
  let l : S.Union →ₗ[ℂ] ℂ := 0
  refine LinearMap.eqOn_span (s:=(F.basis '' {j | j.1 ≤ d})) (f:=F.readout j) (g := l) ?_ (F.exhaust d ▸ LinearMap.mem_range.mpr ⟨_,rfl⟩)
  rintro _ ⟨i,hi,rfl⟩
  change i.1 ≤ _ at hi
  have hne : i ≠ j := fun he => h.not_ge (he.symm ▸ hi)
  rw [F.readout_self,if_neg hne]; rfl

variable (F)

/-- The finite channel set through the indicated horizon. -/
def keep (d : ℕ) : Finset F.Index := (Finset.range (d+1)).sigma (fun _ => Finset.univ)

@[simp] lemma keeps {i : F.Index} {d} : i ∈ F.keep d ↔ i.1 ≤ d := by
  classical
  simp only [keep,Finset.mem_sigma,Finset.mem_range,Finset.mem_univ,and_true]
  omega

lemma represent_sum {V : Type*} [AddCommGroup V] [Module ℂ V] (H : S.Union →ₗ[ℂ] V) (d) (x : S.Field d) :
    ∑ i ∈ F.keep d, F.readout i (S.pin d x) • H (F.basis i) = H (S.pin d x) := by
  classical
  have hv := F.basis.linearCombination_repr (S.pin d x)
  rw [Finsupp.linearCombination_apply,Finsupp.sum] at hv
  let u := F.basis.repr (S.pin d x)
  change (∑ i ∈ u.support, u i • F.basis i) = _ at hv
  rw [← hv,map_sum]
  simp only [map_smul,hv]
  rw [← Finset.sum_subset (s₁:=u.support)] -- check
  · rfl
  · intro i hi; rw [Finsupp.mem_support_iff] at hi
    exact (keeps _).mpr (le_of_not_gt (fun h => hi (readout_cut x h)))
  intro i _ hi; change u i • _ = _; rw [Finsupp.notMem_support_iff.mp hi]; exact zero_smul _ _

/-- Finite synthesis (also defined for arbitrary coefficient arrays since only
`F.keep d` enters). -/
def lift (d) (C : F.Index → ℂ) : S.Field d := ∑ i ∈ F.keep d, C i • (if h : i.1 ≤ d then P.rise h (F.field i.2) else 0)

variable (hs : S.Symmetric) (hp : P.Inclusions S)
include hs hp
lemma lifted (d C) : S.pin d (F.lift P d C) = ∑ i ∈ F.keep d, C i • (F.basis i) := by
  classical
  unfold lift; rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [dif_pos (keeps _|>.1 hi), map_smul,P.stays hs hp,← F.placed _ _]

lemma lift_through (d) (x : S.Field d) : F.lift P d (fun i => F.readout i (S.pin d x)) = x := by
  apply S.pin_inj; rw [lifted _ _ hs hp]; exact F.represent_sum (LinearMap.id : S.Union →ₗ[ℂ] S.Union) _ _

lemma truncates (d C) (i : F.Index) : F.readout i (S.pin d (F.lift P d C)) = if i.1 ≤ d then C i else 0 := by
  classical
  rw [lifted _ _ hs hp,map_sum]
  simp_rw [← F.keeps]
  simp only [map_smul,readout_self]
  by_cases h : i ∈ F.keep d
  · rw [if_pos h,Finset.sum_eq_single i]
    · simp
    · rintro j _ hj; rw [if_neg hj]; exact smul_zero _
    exact fun h' => (h' h).elim
  rw [if_neg h]; exact Finset.sum_eq_zero fun j hj => by rw [if_neg (fun he : j=i => h (he ▸ hj))]; exact smul_zero _

end YM.OPE.Frame

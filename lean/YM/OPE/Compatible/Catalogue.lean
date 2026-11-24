import YM.OPE.Compatible.Tower

/-!
# Real homogeneous complement basis

At each finite horizon these vectors (included with the actual `rise`)
form a complex basis of `Field n`, fixed by the *real* involution,
not the OS time adjoint. Equivalently this is a basis on the real forms,
as displayed also in the coordinate theorem `conj_coord`. Rotations may
mix channels at the same weight. They do not mix our graded spaces.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov
open Function Set Filter Table Survey Submodule
open MultipleContact (Splitting)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L} {T : Table L}
  {I J : Type} [Fintype I] [Fintype J] {P : DiffPlan S} {R : S.Rotation}

section
variable (B : Splitting P) {ρ : S.RealSpin}

def totalRanks (d : ℕ) : ℕ := Module.finrank ℂ (B.stratum d)
-- `Colour` is fixed across kinds of words, horizons, scales and phases
abbrev Hue (d : ℕ) := Fin (totalRanks B d)
abbrev Colour := (d : ℕ) × Hue B d
def shades (n : ℕ) : Finset (Colour B) := (Finset.range (n+1)).sigma fun _ => Finset.univ
lemma shadows (a : Colour B) (n : ℕ) : a ∈ shades B n ↔ a.1 ≤ n := by
  simp [shades]

/- Proofs for this splitting. -/
lemma crown (w h : ℕ) (hw : w=h) (v : B.stratum w) : B.top w v.val = v.val := by
  cases w
  · rfl
  next w =>
    have he : B.down _ v.val = 0 := v.property
    simp [MultipleContact.Splitting.top,he]
lemma crystal (w : ℕ) (v : B.stratum w) : B.part w w v.val = v.val := by
  rw [B.top_part,crown B w w rfl]
lemma notRead (w h : ℕ) (hh : w≠h) (v : B.stratum h) : B.part w h v.val = 0 := by
  rw [← crown B h h rfl v]
  change (B.part w h ∘ₗ B.top h) v.val = _; rw [B.part_top hh,LinearMap.zero_apply]

lemma uses_conj (hb : B.Covariant R ρ) (w : ℕ) (v : B.stratum w) : S.conj ρ w v.val ∈ B.stratum w := by
  cases w with
  | zero => exact Submodule.mem_top
  | succ j =>
    have h : B.down _ v.val = 0 := v.property
    change B.down _ (S.conj _ _ _) = 0
    rw [← hb.real,h,map_zero]
lemma uses_rot (hb : B.Covariant R ρ) (w : ℕ) (v : B.stratum w) (K : Ortho) :
    R.act w K v.val ∈ B.stratum w := by
  cases w with
  | zero => exact Submodule.mem_top
  | succ j =>
    have h : B.down _ v.val = 0 := v.property
    change B.down _ (R.act _ K _) = 0
    rw [← hb.act,h,map_zero]

lemma conj_part (hb : B.Covariant R ρ) (ho : P.Orientation ρ) (w k : ℕ) (hw : w≤k)
    (v : S.Field k) : S.conj ρ w (B.part w k v) = B.part w k (S.conj ρ k v) := by
  induction k,hw using Nat.le_induction with
  | base =>
    rw [B.top_part]; cases w with
    | zero => rfl
    | succ n =>
      unfold MultipleContact.Splitting.top; simp only [LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.comp_apply,map_sub,ho.realInc,hb.real]
  | succ k he ih =>
    rw [MultipleContact.Splitting.part,dif_neg (by omega : k+1≠w),LinearMap.comp_apply,LinearMap.comp_apply,
      ih,hb.real]
lemma rot_part (hb : B.Covariant R ρ) (H : R.Laws P ρ) (w k : ℕ) (hw : w ≤ k)
    (v : S.Field k) (K : Ortho) : R.act w K (B.part w k v) = B.part w k (R.act k K v) := by
  induction k,hw using Nat.le_induction with
  | base =>
    rw [B.top_part]; cases w with
    | zero => rfl
    | succ n =>
      unfold MultipleContact.Splitting.top; simp only [LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.comp_apply,map_sub,H.filtered,hb.act]
  | succ k he ih =>
    rw [MultipleContact.Splitting.part,dif_neg (by omega : k+1≠w),LinearMap.comp_apply,LinearMap.comp_apply,
      ih,hb.act]

def Preserve (ρ : S.RealSpin) (w : ℕ) : Set (B.stratum w) := {v | S.conj ρ w v.val = v.val}

/-- Fixed basis on the *complexification* of the real filtration, using
real vectors. Include unital normalization. -/
structure Catalogue (ρ : S.RealSpin) where
  axisSet (w : ℕ) : Module.Basis (Hue B w) ℂ (B.stratum w)
  isReal (w) : range (axisSet w) ⊆ Preserve B ρ w
  unit_in : ∃ u, (axisSet 0 u).val = S.unit 0

variable (hb : B.Covariant R ρ)
include hb
lemma preserve_spans (w : ℕ) : ⊤ ≤ span ℂ (Preserve B ρ w) := by
  intro x _
  let y : B.stratum w := ⟨_,uses_conj B hb w x⟩
  have he : x+y ∈ Preserve B ρ w := by
    change S.conj ρ w (x.val + S.conj ρ w x.val) = x.val + S.conj ρ w x.val
    rw [map_add,S.reflect_star,add_comm]
  have hh : Complex.I • (x-y) ∈ Preserve B ρ w := by
    change S.conj ρ w (Complex.I • (x.val - S.conj ρ w x.val)) = Complex.I • (x.val - S.conj ρ w x.val)
    rw [map_smulₛₗ,map_sub,S.reflect_star]; simp [smul_sub]; abel
  refine (show (1/2:ℂ) • ((x+y) + (-Complex.I) • (Complex.I • (x-y))) = x from ?_) ▸
    smul_mem _ _ (add_mem (subset_span he) (smul_mem _ _ (subset_span hh)))
  rw [smul_smul, neg_mul, Complex.I_mul_I,neg_neg,one_smul,show (x+y) + (x-y) = (2:ℂ) • x from by rw [two_smul]; abel,
    smul_smul,div_mul_cancel₀ _ (by norm_num),one_smul]

private lemma vivid (w : ℕ) {U : Set (B.stratum w)} (hs : LinearIndepOn ℂ id U)
    (hu : U ⊆ Preserve B ρ w) : ∃ b : Module.Basis (Hue B w) ℂ (B.stratum w),
        range b ⊆ Preserve B ρ w ∧ U ⊆ range b := by
  let t := hs.extend hu
  let b := Module.Basis.extendLe hs hu (preserve_spans B hb w)
  haveI : Finite t := Module.Finite.finite_basis b
  letI := Fintype.ofFinite (t:Type)
  let f : t ≃ Hue B w := (Fintype.equivFin _).trans (finCongr (Module.finrank_eq_card_basis b).symm)
  have he : range (b.reindex f) = range b := by
    simp only [Module.Basis.coe_reindex]; exact f.symm.surjective.range_comp _
  refine ⟨b.reindex f,?_⟩
  rw [he]; exact ⟨Module.Basis.extendLe_subset ..,Module.Basis.subset_extendLe ..⟩

lemma palette (hs : S.Hierarchy) : Nonempty (Catalogue B ρ) := by
  let y : B.stratum 0 := ⟨S.unit 0,Submodule.mem_top⟩
  have hy : y ≠ 0 := fun e => S.alive 0 hs.laws (congr_arg (fun v:B.stratum 0 => v.val) e)
  have he : y ∈ Preserve B ρ 0 := S.conj_unit ..
  obtain ⟨Z,hZ,hE⟩ := vivid B hb 0 ((linearIndepOn_singleton_iff ..).mpr hy)
    (singleton_subset_iff.mpr he)
  choose X hX hY using fun w : ℕ => vivid B hb w (linearIndepOn_empty ℂ id) (empty_subset _)
  let A (w : ℕ) : Module.Basis (Hue B w) ℂ (B.stratum w) := match w with
    | 0 => Z
    | i+1 => X (i+1)
  obtain ⟨u,hu⟩ := hE (mem_singleton _)
  exact ⟨A,fun w => by cases w <;> first| exact hZ| exact hX _, u,congr_arg _ hu⟩
end

variable {B : MultipleContact.Splitting P} {ρ : S.RealSpin} (A : Catalogue B ρ)
namespace Catalogue

def axis (a : Colour B) : S.Field a.fst := (A.axisSet a.1 a.2).val

def readIn (n : ℕ) (a : Colour B) : S.Field n →ₗ[ℂ] ℂ :=
  ((A.axisSet a.fst).coord a.snd).comp
    ((B.part a.fst n).codRestrict (B.stratum a.fst) (fun _ => B.top_mem _))
lemma readIt (n : ℕ) (a : Colour B) (v : S.Field n) :
  A.readIn n a v = (A.axisSet a.fst).coord a.snd ⟨B.part a.fst n v,B.top_mem v⟩ := rfl

lemma star_axis (a : Colour B) : S.conj ρ a.1 (A.axis a) = A.axis a :=
  A.isReal _ (mem_range_self _)

def there (n : ℕ) (a : Colour B) : S.Field n := if h : a.fst≤n then P.rise h (A.axis a) else 0
lemma present (n : ℕ) (a : Colour B) (h : a.fst ≤ n) : A.there n a = P.rise h (A.axis a) := dif_pos h

lemma piece_code (w k : ℕ) (v : S.Field k) :
    ∑ i : Hue B w, A.readIn k ⟨w,i⟩ v • A.axis ⟨w,i⟩ = B.part w k v := by
  let p : B.stratum w := ⟨B.part w k v,B.top_mem v⟩
  have he (i : Hue B w) : A.readIn k ⟨w,i⟩ v = (A.axisSet w).repr p i := rfl
  have hp := congr_arg ((B.stratum w).subtype) ((A.axisSet w).sum_repr p)
  simp_rw [map_sum,map_smul] at hp
  simp_rw [he]
  exact hp

variable (h : S.Symmetric) (hr : P.Inclusions S)
include h hr
lemma encode (k : ℕ) (v : S.Field k) : ∑ a ∈ shades B k, A.readIn k a v • A.there k a = v := by
  have he := B.recombine h hr k v
  unfold shades
  rw [Finset.sum_sigma, ← Fin.sum_univ_eq_sum_range]; refine Eq.trans (b:=_) ?_ he
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : i.val ≤ k := Nat.le_of_lt_succ i.isLt
  have hh (j : Hue B i.val) : A.there k ⟨i.val,j⟩ = P.rise hi (A.axis ⟨i.val,j⟩) := A.present k _ hi
  simp_rw [hh, ← map_smul]; rw [← map_sum,A.piece_code]

lemma one_grade (n : ℕ) (a c : Colour B) (ha : a ∈ shades B n) (hc : c∈ shades B n) :
    A.readIn n a (A.there n c) = if a=c then 1 else 0 := by
  have he : c.fst≤n := (shadows ..).mp hc
  rw [A.present n c he]
  rcases a with ⟨w,i⟩; rcases c with ⟨k,j⟩
  by_cases hz : w=k
  · subst w; rw [A.readIt]
    let G := A.axisSet k
    have ht : B.part k n (P.rise he (A.axis ⟨k,j⟩)) = (G j).val :=
      (B.part_rise h hr he _).trans (crystal B k (G j))
    have hy (v:B.stratum k) : G.coord i v=G.repr v i:=rfl
    change G.coord i ⟨B.part k n _,_⟩ = _
    rw [show (⟨_,_⟩:B.stratum k)=G j from Subtype.ext ht]
    by_cases hh:i=j
    · subst j; rw [hy]; simp
    rw [hy]; simp [hh]
  have ht : B.part w n (P.rise he (A.axis ⟨k,j⟩)) = 0 :=
    (B.part_rise h hr he _).trans (notRead B w k hz (A.axisSet k j))
  rw [A.readIt, if_neg (show Sigma.mk w i ≠ Sigma.mk k j from fun e => hz (congr_arg Sigma.fst e))]
  exact Eq.trans (congr_arg ((A.axisSet w).coord i) (Subtype.ext ht)) (map_zero _)

lemma conj_coord (ho : P.Orientation ρ) (k : ℕ) (v : S.Field k) (a : Colour B) (ha : a∈shades B k) :
    A.readIn k a (S.conj ρ k v) = star (A.readIn k a v) := by
  conv_lhs => rw [← A.encode h hr k v,map_sum, map_sum]
  have he (b:Colour B) (hb : b∈shades B k) : A.readIn k a
      (S.conj ρ k (A.readIn k b v • A.there k b)) =
      star (A.readIn k b v) • A.readIn k a (A.there k b) := by
    rw [map_smulₛₗ,map_smul,A.present k b ((shadows ..).mp hb),ho.realInc,star_axis]; rfl
  rw [Finset.sum_eq_single_of_mem _ ha,he a ha,A.one_grade h hr k a a ha ha,if_pos rfl]; simp
  intro c hc e; rw [he c hc, A.one_grade h hr k a c ha hc,if_neg e.symm, smul_zero]
end Catalogue
end YM.OPE.Cov

import YM.OPE.Splitting.Observe
import YM.MultipleContact.Detector
import Mathlib.LinearAlgebra.Multilinear.Curry
/-!
# Products of fields (on the Final quotients)

`sense T x A` is the actual T value on fields of S using the same
physical hierarchy throughout (T is S or a T respecting S). Finite
names rather than `Fin`; quotiented (possibly inhomogeneous) labels.
As with `observe`, **only interpreted on Config** (matches
`Table.useAt`, is multilinear even with the junk values kept).
-/
set_option autoImplicit false
noncomputable section

open Set Function Filter Fintype
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
namespace YM.OPE.Frame
open Table
variable {G : Gauge} {L : Register G} {S T : Table L} {I J : Type} [Fintype I] [Fintype J]
variable {P : DiffPlan S} {X : Rotation S} {x : I → E4} {o : E4} {y : J → E4} {d h : ℕ}

def deploy (A : S.Tag) : L.Token := ⟨A.fst, S.representative _ A.snd⟩
@[simp] lemma classify (A : S.Tag) : S.classTokens (deploy A) = A := by
  change (⟨A.fst,S.project _ (S.representative _ A.snd)⟩ : S.Tag) = A; rw [S.rep]

def sense (T : Table L) (x : I → E4) (A : I → S.Tag) : ℂ := observe T x (deploy ∘ A)
lemma as_use (A : I → S.Tag) : sense T x A = S.useAt T (points (x ∘ runNames I)) (A ∘ runNames I) := by
  unfold sense observe worded; rw [T.readAt]; rfl
lemma as_token (A : I → L.Token) (h : T.Symmetric) (hT : T.respects S) (hx : Injective x) :
    sense T x (S.classTokens ∘ A) = observe T x A := by
  rw [as_use]; exact (observe_exact T A h hT hx).symm
lemma same_read (A : I → S.Tag) (e : J ≃ I) (h : T.Symmetric) (hx : Injective x) :
    sense T (x ∘ e) (A ∘ e) = sense T x A := perm_observe T h e (deploy ∘ A) hx
lemma same_shift (A : I → S.Tag) (a : E4) (h : T.Homogeneous) (hx : Injective x) :
    sense T (fun i => x i + a) A = sense T x A := observe_carry T h (deploy ∘ A) hx a
lemma same_spin (A : I → S.Tag) (K : Ortho) (h : X.Oriented T) (hx : Injective x) :
    sense T (Ortho.move K ∘ x) (X.label K ∘ A) = sense T x A := by
  simp_rw [as_use]; exact h _ (A ∘ runNames I) _ (runs_conf.mpr hx) _

def bar (ρ : S.RealSpin) (A : S.Tag) : S.Tag := ⟨A.fst,S.conj ρ _ A.snd⟩
@[simp] lemma bar_project (ρ : S.RealSpin) (A : L.Token) :
    bar ρ (S.classTokens A) = S.classTokens (L.conjugate A) := rfl
@[simp] lemma bar_bar (ρ : S.RealSpin) (A : S.Tag) : bar ρ (bar ρ A) = A := by
  change (⟨A.fst,S.conj ρ _ (S.conj ρ _ A.snd)⟩ : S.Tag) = A; rw [S.reflect_star]
lemma same_real (A : I → S.Tag) (ρ : S.RealSpin) (h : T.RealSpin) (hS : T.Symmetric)
    (hT : T.respects S) (hx : Injective x) : sense T x (bar ρ ∘ A) = star (sense T x A) := by
  rw [show bar ρ ∘ A = S.classTokens ∘ (L.conjugate ∘ (deploy ∘ A)) by
    ext1 i; simp only [Function.comp_apply]; rw [← bar_project ρ, classify], as_token _ hS hT hx]
  unfold sense observe worded; simp_rw [T.readAt]; exact h.real (runs_conf.mpr hx) _
lemma raised [DecidableEq I] (A : I → S.Tag) (i : I) (hz : d ≤ h) (v : S.Field d) (hS : T.Symmetric)
    (hT : T.respects S) (hp : P.Inclusions T) (hx : Injective x) :
    sense T x (update A i ⟨h,P.rise hz v⟩) = sense T x (update A i ⟨d,v⟩) := by
  have he (a : S.Tag) : deploy ∘ update A i a = update (deploy ∘ A) i (deploy a) := by
    funext j; by_cases h : j = i <;> simp [h]
  rw [sense,he,sense,he]; refine observe_replace T _ hS hT hp hx i hz ?_; change P.rise hz (S.project _ (S.representative _ v)) = S.project _ (S.representative _ _); rw [S.rep,S.rep]

variable (S T)
abbrev insertField (o : E4) (y : J → E4) (B : J → S.Tag) (d : ℕ) : S.Field d →ₗ[ℂ] ℂ :=
  observeOne S T o y (deploy ∘ B) d
variable {S T}
lemma inserted (B : J → S.Tag) (v : S.Field d) (hS : T.Symmetric) (hT : T.respects S)
    (hy : Injective (beside (sole o) y)) : insertField S T o y B d v =
      sense T (beside (sole o) y) (beside (sole (⟨d,v⟩ : S.Tag)) B) := by
  have hh := projectedOne T (deploy ∘ B) d (S.representative _ v) hS hT hy; rw [S.rep] at hh
  rw [sense, beside_commutes]; exact hh
lemma insert_hold (B : J → S.Tag) (v : S.Field d) (hS : T.Symmetric) (hT : T.respects S) (hp : P.Inclusions T) (hz : d ≤ h)
    (hy : Injective (beside (sole o) y)) : insertField S T o y B h (P.rise hz v) = insertField S T o y B d v :=
  lowerOne T (deploy ∘ B) d v hp hS hy hz hT
lemma insert_detect (e : Exterior L) (v : S.Field d) (h : S.Hierarchy) : insertField S S 0 (bearing e) (S.classTokens ∘ e.letter) d v =
    YM.MultipleContact.response S d e v := by
  rw [YM.MultipleContact.response_self]
  let A : L.Token := ⟨d,S.representative _ v⟩; have he : (⟨d,v⟩ : S.Tag)=S.classTokens A := by change _ = (⟨d,S.project d (S.representative _ _)⟩ : S.Tag); rw [S.rep]
  rw [inserted _ _ h.laws.toSymmetric (fun _ => le_rfl) (bearing_clear _), he,
    show sole (S.classTokens A) = S.classTokens ∘ sole A from rfl, ← beside_commutes,
    as_token _ h.laws.toSymmetric (fun _ => le_rfl) (bearing_clear _)]
  have hx := Prescription.one_test d e (S.representative _ v) h
  simp only [S.rep, Prescription.reading, sub_zero, if_pos (bearing_clear e)] at hx
  exact hx

variable (S T) in
/-- Named multilinear version. -/
def sensed (x : I → E4) (n : I → ℕ) : MultilinearMap ℂ (fun i => S.Field (n i)) ℂ :=
  (MultilinearMap.domDomCongrLinearEquiv' ℂ ℂ (fun i => S.Field (n i)) ℂ (runNames I).symm).symm
    (S.classMoment T (n ∘ runNames I) (points (x ∘ runNames I)))
lemma sensed_eq (A : I → S.Tag) : sensed S T x (fun i => (A i).fst) (fun i => (A i).snd) = sense T x A := by
  rw [as_use]; rfl
lemma sensed_apply {n : I → ℕ} (A : ∀ i, S.Field (n i)) :
    sensed S T x n A = sense T x (fun i => (⟨n i,A i⟩ : S.Tag)) := sensed_eq (fun i => ⟨n i,A i⟩)
lemma beside_sensed {x : I⊕J → E4} (A : I → S.Tag) {n : J → ℕ} (v : ∀ i, S.Field (n i)) :
    let F := sensed S T x (beside (fun i => (A i).fst) n); F.currySum (fun i => (A i).snd) v =
      sense T x (beside A (fun i => ⟨n i, v i⟩)) := by
  intro F; rw [MultilinearMap.currySum_apply, sensed_apply]
  congr 1; ext1 (i|i) <;> rfl

lemma flds_sum {K : Type*} {Y : K → Type*} [DecidableEq K] [Fintype K]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    {σ : K → Type*} [∀ i, Fintype (σ i)] (A : ∀ i, Y i) (F : MultilinearMap ℂ Y Z)
    (B : ∀ i, Module.Basis (σ i) ℂ (Y i)) :
    F A = ∑ a : ∀ i, σ i, (∏ j, (B j).coord (a j) (A j)) • F (fun i => B i (a i)) := by
  conv_lhs => rw [show A = fun i => ∑ a, (B i).coord a (A i) • B i a from funext fun i => ((B i).sum_repr (A i)).symm]
  rw [F.map_sum]; exact Finset.sum_congr rfl fun a _ => F.map_smul_univ _ _

private lemma sense_fixed_smooth (A : I → S.Tag) (h : T.Smooth) (hx : Injective x) :
    ContDiffAt ℝ ∞ (fun p => sense T (S := S) p A) x := by
  simp_rw [as_use]
  let f (x : I → E4) := points (x ∘ runNames I); have hu : ContDiff ℝ ∞ f := by unfold f points; fun_prop
  exact ((S.class_smooth T h _ _ (runs_conf.mpr hx)).contDiffAt ((conf_open _).mem_nhds (runs_conf.mpr hx))).comp (f := f) _ hu.contDiffAt
lemma sense_vary_ext_smooth (A : I → S.Tag) {x : I⊕J → E4} (h : T.Smooth) {n : J → ℕ} (v : ∀ i, S.Field (n i))
    (hx : Injective x) : ContDiffAt ℝ ∞ (fun p : (I⊕J → E4) × (∀ i, S.Field (n i)) =>
      sense T p.1 (beside A (fun i => ⟨n i,p.2 i⟩))) (x, v) := by
  let B i := Module.finBasis ℂ (S.Field (n i))
  have he (x : I⊕J → E4) (v : ∀ i, S.Field (n i)) : sense T x (beside A (fun i => ⟨n i,v i⟩)) =
      ∑ a : ∀ i, Fin (Module.finrank ℂ (S.Field (n i))), (∏ j, (B j).coord (a j) (v j)) •
        sense T x (beside A (fun i => ⟨n i,B i (a i)⟩)) := by
    let F := (sensed S T x (beside (fun i => (A i).fst) n)).currySum (fun i => (A i).snd)
    have hf (v : ∀ i, S.Field (n i)) : F v = sense T x (beside A (fun i => ⟨n i,v i⟩)) := beside_sensed A v
    simp_rw [← hf]; exact flds_sum v F B
  conv in sense T _ _ => rw [he]
  apply ContDiffAt.sum; intro a _
  refine ContDiffAt.mul ?_ ((sense_fixed_smooth (beside A _) h hx).comp (f:=Prod.fst) (x,v) contDiffAt_fst)
  refine contDiffAt_prod ?_
  intro j _; exact ((LinearMap.toContinuousLinearMap (((B j).coord (a j)).restrictScalars ℝ)).contDiff.contDiffAt).comp (f:=fun p : (_× (∀ i, S.Field (n i)))=>p.2 j) (x,v)
    ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun i=>S.Field (n i)) j).contDiff.contDiffAt.comp (x,v) contDiffAt_snd)
end YM.OPE.Frame

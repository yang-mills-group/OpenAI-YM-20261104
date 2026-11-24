import YM.Comparison.Density.Convert.Sources

/-!
# Rooted prices and closure

Inactive long-alternative slots are padded by zeros while preserving
root list. Need no fake proximity of two far-apart potential markers
whose preimage combinations are not among the short inputs. For each
short closure the halo is PAID via the input capacity. The hit test
counts incidences of all masks; to supply it from rooted budgets use
Curb later, including support reserve.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Convert
open Fusing Mirrors Transport RG Lattice Wilson Markers Registers Testing MeasureTheory
open Function Finset Push.AbsoluteSums Marker Multi AnalyticBridge.SectorAffine.Offset
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side}
variable {V : Type} [DecidableEq V] {R : Census V} {X : V → Type} [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)]

-- addresses include Hot's full roots list already, not choosing an I
-- merely by taking the best root.
abbrev Menu (R : Census V) (X : V → Type) (G : Gauge) (n : Side) := Address R → Option (Crown G X n)
variable (B : BudgetPoint) (K : LinkTube G) (O : Readers V X n)
variable (T : Menu R X G n)

def ward (p : Hot R) := p.sites.biUnion O.source.uses

def ann (i : Address R) := match T i with
    | none => ward O i.1
    | some a => a.plot

def bonded : Registers R X G n where
  static i := ward O i.1
  constant _ _ := 0
  sites := ann O T
  body i x := match T i with
    | none => (fun _=>0)
    | some a=> a.backs x

def issueT (i : Address R) := match T i with
    | none => (0:ℝ)
    | some a=> a.tab B K

def expense (i : Address R) := match T i with
    | none => (0:ℝ)
    | some a=> a.tally

def preMarks (x : Cross X) (i : Address R) (U : Config G n) := match T i with
    | none => (0:ℂ)
    | some a => a.grows x U

def leaked (i : Address R) (x : Cross X) : Config G n→ℂ:= match T i with
    | none => (fun _=>0)
    | some a=> a.drift B x

omit [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)] in
lemma taken (x i) (U) : preMarks T x i U=(bonded O T).supports B x i U+leaked B T i x U := by
  unfold preMarks bonded leaked; simp only [supports,ann]; cases T i
  · by_cases he: Healthy B.threshold (ward O i.1) U <;> simp [he]
  simp only [Crown.drift,Pi.sub_apply]; ring

structure Hatch (c a eF eR : ℝ) (w : V→ℝ) : Prop where -- add arguments explicitly
  issued i a : T i=some a → a.Allocated O B K i.1
  extraE : 0≤eR
  extraH : 0≤eF
  priced : Freight (later B eR extraE) w (ann O T) (issueT B K T) c
  taxed : Ac.Hit (ann O T) B.B (fun i=> Poly.toll w i.1.val * expense T i) (B.supportExponent+eF) a

namespace Hatch
variable [Fintype V] {c a eF eR : ℝ} {w : V→ℝ}
variable {B K T O}
variable (h : Hatch B K O T c a eF eR w)
include h
lemma shell : (bonded O T).Layout B O:= by
  have ht i v (hv:v∈i.1.sites): O.source.uses v ⊆ (bonded O T).sites i:= by
    dsimp only [ann,bonded]; split
    · exact fun _ hi=> mem_biUnion.mpr ⟨_,hv,hi⟩
    next hq=> exact (h.issued _ _ hq).pays _ hv
  refine ⟨fun i v hv x hx=> mem_biUnion.mpr ⟨_,hv,hx⟩,ht,fun _=> Slotted.vacant,fun _ _ _ _=>rfl,fun i U=>?_,fun i U=>?_,fun i x=>?_⟩
  · dsimp only [bonded]; cases hX:T i
    · exact Slotted.vacant
    exact Crown.backs_occ (h.issued i _ hX) _
  · dsimp only [bonded,ann]; cases hX:T i with
    | none=> exact fun _ _ _=>rfl
    | some j=> exact fun x y hd=> congrArg (j.factor • ·) ((h.issued i _ hX).reads U _ _ hd)
  dsimp only [bonded,ann]; cases hX:T i
  · exact (Crown.zeroRegular _ 0).1
  exact Crown.purchased (h.issued _ _ hX) x
omit [Fintype V] in
lemma costs : (bonded O T).Budget (later B eR h.extraE) O w 0 c := by
  refine ⟨⟨fun _=>0,⟨le_rfl,fun i=>le_rfl,fun v=> ?_⟩,fun x hx i=> by simp [bonded]⟩, issueT B K T,h.priced,fun x hx i v hv=>?_⟩
  · apply budget_of_sum (fun i=> by simp [BudgetPoint.mass]); simp [BudgetPoint.mass]
  dsimp only [bonded,ann,issueT]; cases hX:T i
  · exact (Crown.zeroRegular _ _).2
  exact (Crown.buys (h.issued _ _ hX) x hx v hv).2
lemma stain (i : Address R) (x : Cross X) : UsesFinal B.threshold (ann O T i) (leaked B T i x) ∧
    (∀ U, Healthy B.threshold (ann O T i) U → leaked B T i x U=0) ∧ GaugeInvariant (leaked B T i x) ∧ Measurable (leaked B T i x) := by
  unfold ann leaked; cases hX:T i
  · exact ⟨fun _ _ _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,measurable_const⟩
  exact ⟨(Crown.drift_support (h.issued _ _ hX) x).1,(Crown.drift_support (h.issued _ _ hX) x).2,
    Crown.drift_gauge (h.issued _ _ hX) x,Crown.drift_meas (h.issued _ _ hX) x⟩
lemma address (i : Address R) (U) : Slotted i.1.sites (fun x=> leaked B T i x U) ∧ Reads O.locus (ann O T i) i.1.sites (fun x=> leaked B T i x U):= by
  unfold ann leaked; cases hX:T i
  · exact ⟨Slotted.vacant,fun _ _ _=>rfl⟩
  exact Crown.drift_tracks (h.issued _ _ hX) U
omit [Fintype V] in
lemma taxes (i : Address R) (x : Cross X) (he : UnitPage x) (U) : ‖leaked B T i x U‖ ≤ expense T i := by
  unfold leaked expense; cases hX:T i; simp
  exact Crown.drift_bound (h.issued _ _ hX) x he U

lemma subsides (hw : ∀ i,0<w i) (x : Cross X) (i : Hot R) (U) : Summable fun j=> leaked B T (i,j) x U := by
  obtain ⟨v,hv⟩:= i.property; obtain ⟨p,y,hy,rfl⟩:= Testing.normalize x
  have ht j := ((h.address (i,j) U).1).stretch p y
  have hv' j : O.source.root v ∈ ann O T (i,j) := h.shell.contiguous (i,j) v hv (O.source.listed _)
  let W j:= Poly.toll w i.val * expense T (i,j)
  have he: Summable fun j=> W j*(Real.exp ((B.supportExponent+eF)*coverNumber B.B (ann O T (i,j)))) := by
    have H := budget_pull (fun j : ℕ=> (i,j)) (Prod.mk_right_injective _) (h.taxed (O.source.root v))
    simpa only [hv',↓reduceIte] using H.2.1
  have hh' := Poly.worth hw i.val; have hn j := (norm_nonneg _).trans (h.taxes (i,j) y hy U)
  simp_rw [ht]; refine Summable.const_smul _ (Summable.of_norm (Summable.of_nonneg_of_le (f:=fun j=>expense T (i,j)) (fun _=> norm_nonneg _) (fun i=> h.taxes _ y hy U) ?_))
  have hq : Summable W := by
    refine he.of_nonneg_of_le (fun j=> mul_nonneg hh'.le (hn j)) fun j=> ?_
    exact le_mul_of_one_le_right (mul_nonneg hh'.le (hn j)) (Real.one_le_exp (mul_nonneg (add_nonneg B.exponent_pos.le h.extraH) (by positivity)))
  exact (summable_mul_left_iff hh'.ne').1 hq
end Hatch
end YM.Comparison.Density.Convert

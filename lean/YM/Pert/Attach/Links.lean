import YM.RG.ActivityBounds
import YM.Work.H03
import YM.Ac.Tree
import YM.Push.ABSOLUTE_SUMS.Basic

/-! Unmarked mask-change attachments in the actual RG.Activities convention (not multiplying an integrated law by a perturbative error). We render a factor for each nonzero mask-difference term on a true unhealthy support, reindex product by overlap components which each need an old forced label. Countably many factors, quantitative tree budget when given exponents one stronger and a common small hit bound; can lower the support exponent after the conversion. Inspired by the marked `Extra/Together.../Gather` method (`YM.Extra.MULTISOURCE_TRAJECTORIES.Gather`). Here even unmarked hits survive in products which need not be nilpotent. -/

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Attach
open Function Lattice Wilson MeasureTheory RG
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge}

abbrev Old := ℕ ⊕ ℕ

structure Corrections (G : Gauge) (n : Lattice.Side) where
   region : ℕ → Support n
   value : ℕ → Config G n → ℝ

structure March (X:Corrections G n) (s:Signed) (b:Site n) where
   perm : Equiv.Perm ℕ
   region i : X.region (perm i) = (X.region i).image (affine s b)
   value i U : X.value (perm i) U = X.value i (pull s b U)

structure Prepared (t:ℝ) (X : Corrections G n) : Prop where
   flag i U : Healthy t (X.region i) U → X.value i U=0
   sym i : GaugeInvariant (X.value i)
   meas i : Measurable (X.value i)
   deps i : UsesFinal t (X.region i) (X.value i)
   move s b : Nonempty (March X s b)

variable (A:Activities G n) (X:Corrections G n)
namespace Corrections

def area : Old → Support n := Sum.elim (fun i=> (A.forced i).support) X.region
def inventory (X:Corrections G n) : Old → Support n := Sum.elim (fun i=> (A.forced i).inventory) (fun _=> ∅)
lemma area_le (l:Old) : X.inventory A l ⊆ X.area A l := by
   cases l with
    | inl i => exact (A.forced i).inventory_sup
    | inr j => exact Finset.empty_subset _
end Corrections

def weight (U:Config G n) (l:Old) := l.elim (fun i=>A.K i U) (fun j=>X.value j U)

def Cluster : Type := {s:Finset Old // Ac.Spark (X.area A) s ∧ s.toLeft.Nonempty ∧
       ((s.toLeft : Finset ℕ) : Set ℕ).PairwiseDisjoint fun i => (A.forced i).support}

def singleton (i:ℕ) : Cluster A X := ⟨{Sum.inl i},⟨⟨_,Finset.mem_singleton_self _⟩, by
     intro j hj k hk; rw [Finset.mem_singleton.mp hj,Finset.mem_singleton.mp hk]; exact .refl⟩,
    ⟨i,by simp⟩,by
      intro j hj k hk; simp at hj hk; subst j; subst k; simp⟩
lemma singleton_injective : Injective (singleton A X) := by
    intro i j he; have := Finset.singleton_inj.mp (congr_arg Subtype.val he); exact Sum.inl.inj this

def decoding : ℕ ≃ Cluster A X :=
   letI : Infinite (Cluster A X) := Infinite.of_injective (singleton A X) (singleton_injective A X)
   letI : Countable (Cluster A X) := by unfold Cluster; infer_instance
   letI : Encodable (Cluster A X) := Encodable.ofCountable _
   @Denumerable.eqv (Cluster A X) (Denumerable.ofEncodableOfInfinite _) |>.symm

def parts (i:ℕ) := Subtype.val (decoding A X i)
lemma parts_inj : Injective (parts A X) := Subtype.val_injective.comp (decoding A X |>.injective)

def full (s : Finset Old) := s.biUnion (X.area A)

def bill (s : Finset Old) := s.toLeft.biUnion (fun i=> (A.forced i).inventory)
lemma bill_union (s : Finset Old) : bill A s = s.biUnion (X.inventory A) := by
   ext x; constructor
   · intro hx; obtain ⟨i,hi,hx⟩:=Finset.mem_biUnion.mp hx
     exact Finset.mem_biUnion.mpr ⟨.inl i,Finset.mem_toLeft.mp hi,hx⟩
   intro hx; obtain ⟨i, hi, hb⟩:=Finset.mem_biUnion.mp hx
   cases i with
    | inr i => simpa [Corrections.inventory] using hb
    | inl i => exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_toLeft.mpr hi,hb⟩
lemma bill_sub (s : Finset Old) : bill A s ⊆ full A X s := by
   intro x hx; rw [bill_union (X:=X)] at hx; obtain ⟨i,hi,h⟩:=Finset.mem_biUnion.mp hx; exact Finset.mem_biUnion.mpr ⟨_,hi,X.area_le A _ h⟩

def page (i:ℕ) : ForcedAddress G n where
   support := full A X (parts A X i)
   inventory := bill A (parts A X i)
   inventory_ne := by
     obtain ⟨k,hk⟩:= (decoding A X i).2.2.1
     obtain ⟨x,hx⟩ := (A.forced k).inventory_ne
     exact ⟨x, Finset.mem_biUnion.mpr ⟨k,hk,hx⟩⟩
   inventory_sup := bill_sub A X _
   extraTest U := ∀ j∈(parts A X i).toLeft, (A.forced j).extraTest U

open Classical in
def entry (t:ℝ) (i:ℕ) (U:Config G n) : ℝ := if (page A X i).eligible t U then
       ∏ l∈parts A X i, weight A X U l else 0

def attach (t:ℝ) (R:Activities G n) : Activities G n := ⟨R.reg,page A X, R.E, entry A X t⟩
lemma sub_cover_old {i:ℕ} {j:ℕ} (hj:j∈ (parts A X i).toLeft) : (A.forced j).support ⊆ (page A X i).support :=
    fun x hx=>Finset.mem_biUnion.mpr ⟨.inl _,Finset.mem_toLeft.mp hj,hx⟩
end YM.Pert.Attach

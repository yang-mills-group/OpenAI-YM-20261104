import YM.Integration.ActualWilsonTaylorSlot
import YM.Integration.ActualWilsonJoinedCofactor

/-! The two original addresses of each supported Taylor/vacuum packet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonTaylorPackets
open Function Set Finset Lattice Wilson RG Extra.Histories Planned.GuardedAtom
open ActualWilsonPacketSplit ActualWilsonJoinedCofactor ActualWilsonTaylorSlot
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {W : Rep G n} {Y : ℕ → Support n}

def parts (W : Rep G n) (Y : ℕ → Support n) (p : ℕ × Finset ℕ) :=
  partition W (Y p.1) p.2

def Roots (W : Rep G n) (Y : ℕ → Support n) :=
  {p : ℕ × Finset ℕ // ((parts W Y p).1.1).Nonempty}

def stem (p : Roots W Y) : Key W Y :=
  ⟨(p.1.1,(parts W Y p.1).1.1), p.2, (parts W Y p.1).2.1⟩

def tail (p : Roots W Y) : Finset ℕ := (parts W Y p.1).1.2

theorem recover (p : Roots W Y) : (stem p).1.2 ∪ tail p = p.1.2 :=
  (partition W (Y p.1.1)).left_inv p.1.2

theorem collect (z : Key W Y) (J : Finset ℕ) (hJ : ∀ j ∈ J, Disjoint (scopes W j) (Y z.1.1)) :
    ∃ p : Roots W Y, stem p=z ∧ tail p=J := by
  let b : Packets W (Y z.1.1) := ⟨(z.1.2,J),z.2.2,hJ⟩
  let p := (z.1.1,z.1.2 ∪ J)
  have hb : parts W Y p = b := (partition W (Y z.1.1)).right_inv b
  have hn : ((parts W Y p).1.1).Nonempty := by rw [hb]; exact z.2.1
  refine ⟨⟨p,hn⟩,Subtype.ext (Prod.ext rfl ?_),?_⟩
  · exact congrArg (fun v : Packets W (Y z.1.1) => v.1.1) hb
  exact congrArg (fun v : Packets W (Y z.1.1) => v.1.2) hb

def place (K : Guard.Keeper W.p W.activities) : Roots W Y ↪ ℕ × Finset ℕ where
  toFun p := (address K (stem p), flip (address K (stem p)) (tail p))
  inj' := by
    intro p q h
    have hk : address K (stem p)=address K (stem q) := congrArg Prod.fst h
    have he : stem p=stem q := (address K).injective hk
    have ht : flip (address K (stem p)) (tail p)=flip (address K (stem q)) (tail q) :=
      congrArg Prod.snd h
    rw [hk] at ht
    have hj : tail p=tail q := (switch (address K (stem q))).injective ht
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · exact congrArg (fun z : Key W Y => z.1.1) he
    rw [←recover p,←recover q,he,hj]

theorem source_support (f : ℕ → Config G n → ℂ)
    (hf : ∀ r U, f r U≠0 → ¬ Healthy W.p.threshold (Y r) U) (p : ℕ × Finset ℕ)
    (U : Config G n) (h : f p.1 U * (W.activities.gasOccurrence W.p p.2 U : ℂ) ≠ 0) :
    ((parts W Y p).1.1).Nonempty := by
  have hv : W.activities.gasOccurrence W.p p.2 U ≠ 0 := by
    intro hv
    simp [hv] at h
  have hm : W.activities.admissible W.p U p.2 := by
    by_contra ha
    exact hv (if_neg (by exact ha))
  apply nonempty W (Y p.1) (parts W Y p) U _ (hf p.1 U (left_ne_zero_of_mul h))
  apply (admitted_iff W _ _ _).2
  have he : (parts W Y p).1.1 ∪ (parts W Y p).1.2=p.2 := (partition W _).left_inv p.2
  rwa [he]

theorem receipt (K : Guard.Keeper W.p W.activities) (f : ℕ → Config G n → ℂ)
    (p : Roots W Y) (U : Config G n) :
    f p.1.1 U * (W.activities.gasOccurrence W.p p.1.2 U : ℂ) =
      rows (Y := Y) K f (place K p).1 U * coat W (place K p).1 (place K p).2 U := by
  let z := stem p
  let b := parts W Y p.1
  change _ = rows (Y := Y) K f (address K z) U * coat W (address K z) (flip _ (tail p)) U
  rw [on_slot]
  have he : (W.activities.gasOccurrence W.p p.1.2 U : ℂ) = (occurrence W (Y p.1.1) b U : ℂ) := by
    rw [occurrence_eq, show b.1.1 ∪ b.1.2=p.1.2 from recover p]
  obtain ⟨hs,hz⟩ := geometry K z
  rw [he,split W (Y p.1.1) b U (address K z) hs hz]
  have hg : ((b.1.1 : Set ℕ).Pairwise (fun i j => Disjoint (scopes W i) (scopes W j)) ∧
      joined W (Y p.1.1) b.1.1 ∩ flags W.p.threshold U = b.1.1.biUnion (inventory W)) ↔
      gate z U := Iff.rfl
  by_cases h : gate z U
  · rw [if_pos (hg.mpr h),deposit,if_pos h]
    exact (mul_assoc _ _ _).symm
  rw [if_neg (mt hg.mp h),deposit,if_neg h]
  simp

theorem target_support (K : Guard.Keeper W.p W.activities) (f : ℕ → Config G n → ℂ)
    (b : ℕ × Finset ℕ) (U : Config G n)
    (h : rows (Y := Y) K f b.1 U * coat W b.1 b.2 U ≠ 0) :
    b ∈ Set.range (place (Y := Y) K) := by
  have hi : b.1 ∈ Set.range (address (Y := Y) K) := by
    by_contra hi
    rw [off_slot K f hi] at h
    simp at h
  obtain ⟨z,hz⟩ := hi
  let J := flip b.1 b.2
  have hJ : flip b.1 J=b.2 := involution ..
  have hper : permits W (scopes W b.1) (inventory W b.1) J U := by
    by_contra hd
    have hcoat : coat W b.1 b.2 U = 0 := by rw [←hJ,coat_eq,waiting,if_neg hd]
    exact h (by rw [hcoat,mul_zero])
  have hsub : Y z.1.1 ⊆ scopes W b.1 := by
    rw [←hz,(geometry K z).1]
    exact Finset.subset_union_left
  obtain ⟨p,hp,hj⟩ := collect z J (fun j h => (hper.2.1 j h).symm.mono_right hsub)
  use p
  change (address K (stem p),flip (address K (stem p)) (tail p))=b
  exact Prod.ext (hp ▸ hz) (by rw [hp,hz,hj,hJ])

end YM.Integration.ActualWilsonTaylorPackets

import YM.Integration.ActualWilsonJoinedCofactor

/-! Exchange complete remote components of a pair of original Wilson packets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonPacketSwitch
open Finset Function Lattice Wilson RG
open scoped BigOperators Classical
variable {n : Side} {ι : Type*}

def region (K : ι → Support n) (T : Support n) (s : Finset ι) : Support n :=
  univ.filter fun x => ∀ B : Support n, T ⊆ B →
    (∀ i ∈ s, ¬Disjoint (K i) B → K i ⊆ B) → x ∈ B

theorem root_subset (K : ι → Support n) (T : Support n) (s : Finset ι) :
    T ⊆ region K T s := fun _ h => mem_filter.mpr ⟨mem_univ _,fun _ H _ => H h⟩

theorem closed (K : ι → Support n) (T : Support n) (s : Finset ι) {i : ι} (hi : i ∈ s)
    (h : ¬Disjoint (K i) (region K T s)) : K i ⊆ region K T s := by
  obtain ⟨x,hx,hr⟩ := not_disjoint_iff.mp h
  intro y hy
  refine mem_filter.mpr ⟨mem_univ _,fun B hT hB => hB i hi ?_ hy⟩
  exact not_disjoint_iff.mpr ⟨x,hx,(mem_filter.mp hr).2 B hT hB⟩

theorem least (K : ι → Support n) (T : Support n) (s : Finset ι) (B : Support n)
    (hT : T ⊆ B) (hB : ∀ i ∈ s, ¬Disjoint (K i) B → K i ⊆ B) : region K T s ⊆ B :=
  fun _ h => (mem_filter.mp h).2 B hT hB

def inner (K : ι → Support n) (B : Support n) (s : Finset ι) : Finset ι :=
  s.filter fun i => ¬Disjoint (K i) B

def outer (K : ι → Support n) (B : Support n) (s : Finset ι) : Finset ι :=
  s.filter fun i => Disjoint (K i) B

def mix (K : ι → Support n) (B : Support n) (s t : Finset ι) := inner K B s ∪ outer K B t

def exchange (K : ι → Support n) (T : Support n) (z : Finset ι × Finset ι) : Finset ι × Finset ι :=
  let B := region K T (z.1 ∪ z.2)
  (mix K B z.1 z.2,mix K B z.2 z.1)

theorem contents (K : ι → Support n) (B : Support n) (s t : Finset ι) :
    mix K B s t ∪ mix K B t s=s ∪ t := by
  ext i
  by_cases h : Disjoint (K i) B <;> simp [mix,inner,outer,h,or_comm]

theorem restore (K : ι → Support n) (B : Support n) (s t : Finset ι) :
    mix K B (mix K B s t) (mix K B t s)=s := by
  ext i
  by_cases h : Disjoint (K i) B <;> simp [mix,inner,outer,h]

theorem involutive (K : ι → Support n) (T : Support n) : Involutive (exchange K T) := by
  rintro ⟨s,t⟩
  simp only [exchange,contents,restore]

def price (a b : ι → ℂ) (z : Finset ι × Finset ι) : ℂ := (∏ i ∈ z.1,a i)*(∏ i ∈ z.2,b i)

theorem split (K : ι → Support n) (B : Support n) (s t : Finset ι) (a : ι → ℂ) :
    (∏ i ∈ mix K B s t,a i)=(∏ i ∈ inner K B s,a i)*(∏ i ∈ outer K B t,a i) := by
  apply prod_union
  exact Finset.disjoint_left.mpr fun _ h j => (mem_filter.mp h).2 (mem_filter.mp j).2

theorem same (K : ι → Support n) (B : Support n) (s : Finset ι) :
    mix K B s s=s := by
  ext i
  by_cases h : Disjoint (K i) B <;> simp [mix,inner,outer,h]

/-- Every remote signed factor is literally shared on both sides of the exchange. -/
theorem signed (K : ι → Support n) (T : Support n) (s t : Finset ι) (a b : ι → ℂ) :
    let B := region K T (s ∪ t)
    let near := (inner K B s,inner K B t)
    let far := (outer K B s,outer K B t)
    price a b (s,t)-price b a (exchange K T (s,t))=
      (price a b near-price b a near)*price a b far := by
  intro B near far
  have hs := split K B s s a
  have ht := split K B t t b
  rw [same] at hs ht
  dsimp only [price,exchange,near,far]
  rw [hs,ht,split,split]
  ring

end YM.Integration.ActualWilsonPacketSwitch

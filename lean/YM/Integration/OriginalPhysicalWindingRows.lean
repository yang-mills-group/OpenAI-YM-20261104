import YM.Integration.RootedVacuumWinding
import YM.Integration.PhysicalWilsonPricedOutput
import YM.Integration.SignedRootedWindingReadout

/-! Descend the native joint winding measure to the true finite torus,
and read it in the physical held-root tables. Every independent marked
placement and every field coordinate has its own representative. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalPhysicalWindingRows
open Function Finset Filter Bloch Lattice Wilson RG Precision Gauge Marker
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Blue
open PhysicalWilsonRootedHessian PhysicalWilsonPricedOutput Next.Foundations
open scoped Classical BigOperators

variable {ι α : Type} [DecidableEq ι] [Fintype ι] [Fintype α] [DecidableEq α]
variable {G : Gauge} {n : Side} {j d : ℕ} {J : Finset ι} {o : ι} {D : ι → ℕ}

def diameter (S : Finset (Site n)) := S.sup fun x => S.sup fun y => separation x y

private theorem torus (x y : Site n) : separation x y ≤ (tor n).gap x y := by
  rw [separation_comm]
  change Finset.univ.sup (fun i => (lift (y-x) i).natAbs) ≤ Laurent.size (lift (y-x))
  exact Finset.sup_le fun i _ => FreeResolvent.own_size _ i

theorem wrapGap (x y : Cover) : separation (wrap n x) (wrap n y) ≤ terrain.gap x y := by
  have h := FreeResolvent.wrap_size n (y-x)
  rw [map_sub] at h
  exact (torus _ _).trans h

private theorem diameter_image {β : Type} [Fintype β] (p : β → Site n) :
    diameter (univ.image p) ≤ league (tor n) p := by
  apply Finset.sup_le; intro x hx
  obtain ⟨a,_,rfl⟩ := mem_image.mp hx
  apply Finset.sup_le; intro y hy
  obtain ⟨b,_,rfl⟩ := mem_image.mp hy
  exact (torus _ _).trans (leg_le (tor n) p a b)

omit [Fintype ι] in
/-- The finite positive-action reference minus the periodized positive
action is the negative of the signed log-ground row, on each field. -/
theorem quiet {S : Census ι} (T : Run G) (s : LocalFormal.Datum T.family S)
    (k j : ℕ) (h : Fin (j+1)) (o : Label G (T.family.side s.level s.period))
    {width σ : ℝ} (hw : 0 ≤ width) (hσ : width ≤ σ) :
    quietHeld T s width h o (fun z => quietReference T s k (j+1) z - quietCover T s k (j+1) z) ≤
      RootedVacuumWinding.held h o σ
        (RootedVacuumWinding.ground T.family.path.levels T.metals.O s.cutoff s.level
          (T.family.side s.level s.period) k j) := by
  apply sum_le_sum
  intro z _
  split_ifs with key
  · have pos : width * (diameter (univ.image fun i => (z i).1) : ℝ) ≤
        σ * (soar (tor (T.family.side s.level s.period)) z : ℝ) :=
      mul_le_mul (le_refl width) (by exact_mod_cast diameter_image (fun i => (z i).1))
        (Nat.cast_nonneg _) hw |>.trans (mul_le_mul_of_nonneg_right hσ (Nat.cast_nonneg _))
    have sign : quietReference T s k (j+1) z - quietCover T s k (j+1) z =
        -((RootedVacuumWinding.ground T.family.path.levels T.metals.O s.cutoff s.level
          (T.family.side s.level s.period) k j z : ℝ):ℂ) := by
      simp [quietCover,quietReference,RootedVacuumWinding.ground,Pi.sub_apply]
    dsimp only
    rw [sign,norm_neg,Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (Real.exp_monotone pos) (norm_nonneg _)
  · exact le_rfl

def clamp (J : Finset ι) (base z : ι → Site n) (i : ι) := if i∈J then z i else base i

def complete (J : Finset ι) (base : ι → Site n) (p : J → Site n) (i : ι) :=
  if h : i∈J then p ⟨i,h⟩ else base i

private abbrev Domain (J : Finset ι) (o : J) (u : Site n) (α : Type) (j : ℕ) :=
  {p : J → Site n // p o = u} × dock (Site n) α j

private def code (ho : o ∈ J) (u : Site n) (a : Domain J ⟨o,ho⟩ u α j) : Fence α J o j :=
  (fun i => lift u + lift (a.1.1 ⟨i.val,mem_of_mem_erase i.property⟩-u),unfoldAt (lift u) a.2)

omit [Fintype ι] [Fintype α] [DecidableEq α] in
private theorem active (ho : o ∈ J) (u : Site n) (a : Domain J ⟨o,ho⟩ u α j) (v : J) :
    wrap n (toe J o (lift u) (code ho u a).1 v.val) = a.1.1 v := by
  by_cases h : v.val=o
  · have h' : v=⟨o,ho⟩ := Subtype.ext h
    subst v; simp [toe,a.1.2]
  · have h' := mem_erase.mpr ⟨h,v.property⟩
    simp [toe,h,h',code]

omit [Fintype ι] [Fintype α] [DecidableEq α] in
private theorem sectioned (ho : o ∈ J) (u : Site n) (a : Domain J ⟨o,ho⟩ u α j) :
    RootedPeriodicMarkedWinding.Section n J o (toe J o (lift u) (code ho u a).1) := by
  intro v hv
  by_cases h : v=o
  · subst v; simp [toe]
  · rw [active ho u a ⟨v,hv⟩]
    simp [toe,code,h,mem_erase.mpr ⟨h,hv⟩]

omit [Fintype ι] [Fintype α] [DecidableEq α] in
private theorem injected (ho : o ∈ J) (u : Site n) : Injective (code (α:=α) (j:=j) ho u) := by
  intro x y eq
  apply Prod.ext
  · apply Subtype.ext; funext i
    rw [←active ho u x i,←active ho u y i,eq]
  · simpa only [code,slides_back] using congrArg (fun z : Fence α J o j => slideC n z.2) eq

omit [Fintype ι] [Fintype α] in
private theorem recovered {U : Type} [Zero U] (P : (ι → Site n) → Ten U (Co n α) j)
    (base : ι → Site n) (ho : o ∈ J) (u : Site n) (a : Domain J ⟨o,ho⟩ u α j) :
    towerV J o j (RootedPeriodicMarkedWinding.row n J o (fun z => P (clamp J base z)))
      (lift u) (code ho u a) = P (complete J base a.1.1) a.2 := by
  have support_ok := sectioned ho u a
  have positions : clamp J base (wrap n ∘ toe J o (lift u) (code ho u a).1) = complete J base a.1.1 := by
    funext v; by_cases h:v∈J
    · simpa [clamp,complete,h] using active ho u a ⟨v,h⟩
    · simp [clamp,complete,h]
  simp only [towerV,RootedPeriodicMarkedWinding.row,support_ok,true_and]
  have fields : slideC n (code ho u a).2=a.2 := slides_back (lift u) a.2
  have holds : unfoldAt (toe J o (lift u) (code ho u a).1 o) (slideC n (code ho u a).2)=
      (code ho u a).2 := by rw [fields]; simp [toe,code]
  rw [if_pos holds,positions,fields]

omit [Fintype ι] [Fintype α] [DecidableEq α] in
private theorem span_bound (ho : o ∈ J) (u : Site n) (a : Domain J ⟨o,ho⟩ u α j) :
    diameter (univ.image a.1.1 ∪ univ.image fun i => (a.2 i).1) ≤
      Syn terrain (toe J o (lift u) (code ho u a).1) J (code ho u a).2 := by
  let f := foyer (toe J o (lift u) (code ho u a).1) J (code ho u a).2
  have old (x) (hx : x ∈ univ.image a.1.1 ∪ univ.image fun i => (a.2 i).1) :
      ∃ t : J ⊕ Fin j, wrap n (f t) = x := by
    rcases mem_union.mp hx with h|h
    · obtain ⟨b,_,rfl⟩ := mem_image.mp h; exact ⟨.inl b,active ho u a b⟩
    · obtain ⟨b,_,rfl⟩ := mem_image.mp h; exact ⟨.inr b,congrArg Prod.fst
        (congr_fun (slides_back (lift u) a.2) b)⟩
  apply Finset.sup_le; intro x hx
  obtain ⟨s,hs⟩ := old x hx
  apply Finset.sup_le; intro y hy
  obtain ⟨t,ht⟩ := old y hy
  rw [←hs,←ht]
  exact (wrapGap _ _).trans (leg_le terrain f s t)

omit [Fintype ι] in
/-- Physical held-root absolute sum for the structured complex reader. The
original field and marked locations vary independently inside this sum. -/
theorem marked (P : (ι → Site n) → Ten (Pen D J) (Co n α) j)
    (base : ι → Site n) (ho : o ∈ J) (u : Site n) (v : SignedRootedWindingReadout.Tests D)
    {width σ U B : ℝ} (hw : 0 ≤ width) (hσ : width ≤ σ) (hU : 0 ≤ U)
    (hv : SignedRootedWindingReadout.amplitude J v ≤ U)
    (billed : PostMark J o j (RootedPeriodicMarkedWinding.row n J o (fun z => P (clamp J base z))) σ B d) :
    (∑ p : J → Site n, if p ⟨o,ho⟩=u then ∑ z : dock (Site n) α j,
      Real.exp (width*diameter (univ.image p ∪ univ.image fun a => (z a).1)) *
        ‖SignedRootedWindingReadout.read J v (P (complete J base p) z)‖ else 0) ≤ U*B := by
  let f (a : Domain J ⟨o,ho⟩ u α j) :=
    Real.exp (width*diameter (univ.image a.1.1 ∪ univ.image fun i => (a.2 i).1)) *
      ‖SignedRootedWindingReadout.read J v (P (complete J base a.1.1) a.2)‖
  let T := RootedPeriodicMarkedWinding.row n J o (fun z => P (clamp J base z))
  let g (i : Fence α J o j) := lineOut (toe J o (lift u) i.1) J o i.2 ^ d *
    Real.exp (σ*Syn terrain (toe J o (lift u) i.1) J i.2)*
      ‖SignedRootedWindingReadout.read J v (towerV J o j T (lift u) i)‖
  have sum : SumBudget g (U*B) := by
    simpa [g,T] using SignedRootedWindingReadout.rows J billed (lift u) (fun _ => v) U hU
      (fun _ => hv) (fun _ => 1) (fun _ => by simp)
  let E : Domain J ⟨o,ho⟩ u α j ↪ Fence α J o j := ⟨code ho u,injected ho u⟩
  have item a : f a ≤ g (E a) := by
    have meter : width*(diameter (univ.image a.1.1 ∪ univ.image fun i => (a.2 i).1):ℝ) ≤
        σ*(Syn terrain (toe J o (lift u) (E a).1) J (E a).2:ℝ) :=
      (mul_le_mul_of_nonneg_left (by exact_mod_cast span_bound ho u a) hw).trans
        (mul_le_mul_of_nonneg_right hσ (Nat.cast_nonneg _))
    have line := one_le_pow₀ (n:=d) (lineBound (p:=toe J o (lift u) (E a).1) ho (E a).2).1
    dsimp only [g,f]
    rw [show towerV J o j T (lift u) (E a) = P (complete J base a.1.1) a.2 from recovered P base ho u a]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (Real.exp_monotone meter).trans (le_mul_of_one_le_left (Real.exp_nonneg _) line)
  have reindex : (∑ p : J → Site n, if p ⟨o,ho⟩=u then ∑ z : dock (Site n) α j,
      Real.exp (width*diameter (univ.image p ∪ univ.image fun a => (z a).1)) *
        ‖SignedRootedWindingReadout.read J v (P (complete J base p) z)‖ else 0) =
      ∑ a : Domain J ⟨o,ho⟩ u α j, f a := by
    rw [Fintype.sum_prod_type]
    let L := univ.filter (fun p : J → Site n => p ⟨o,ho⟩=u)
    rw [←sum_filter,Finset.sum_subtype L (p:=fun p => p ⟨o,ho⟩=u) (by simp [L])]
  rw [reindex]
  refine (sum_le_sum fun a _ => item a).trans ?_
  have lower := sum.2.1.sum_le_tsum (univ.map E) (fun a _ => sum.1 a)
  simpa only [Finset.sum_map] using lower.trans sum.2.2

end YM.Integration.OriginalPhysicalWindingRows
end

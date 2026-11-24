import YM.Integration.WilsonThermometerCommonChambers
import YM.Integration.WilsonAddressedCollarEquations

/-! Uniformly on each actual occupied test cell, simultaneous translation
provides disjoint chambers and genuine Ward clearance for the three fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCompactChambers
open Function Filter Set Finset Lattice Wilson RG Source Extraction Cells
open WilsonOffsetReportingProducts WilsonSeparatedOriginalThermometerCells
open PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G : Gauge} (R : Run G)

theorem cleared {n : ℕ} (E : ∀ d, SectionData (R.family.labels.level d)) (radius : ℕ → ℕ)
    (d : Fin n → ℕ) : ∃ b : ℕ, ∀ᶠ N : ℕ in atTop, ∀ p (o : Fin n → Site (R.family.side N p)),
      (∀ i j, i≠j → b<separation (o j) (o i)) → Avoids (C:=R.family) E radius d o := by
  choose vsize vfixed using fun i => WilsonSeparatedOffsetSites.footprint (E (d i))
  choose asize afixed using fun i => WilsonSeparatedOffsetSites.footprint (R.family.localSection (d i))
  let b := univ.sup (fun i=>radius (d i)) + (univ.sup vsize ⊔ univ.sup asize)
  refine ⟨b,?_⟩
  filter_upwards [eventually_all.mpr vfixed,eventually_all.mpr afixed] with N vpaid apaid p o spaced
  intro i j ij
  have span := spaced i j ij
  have rh : radius (d i) ≤ univ.sup (fun k=>radius (d k)) := le_sup (f:=fun k=>radius (d k)) (mem_univ i)
  have vh : vsize j ≤ univ.sup vsize ⊔ univ.sup asize := (le_sup (f:=vsize) (mem_univ j)).trans le_sup_left
  have ah : asize j ≤ univ.sup vsize ⊔ univ.sup asize := (le_sup (f:=asize) (mem_univ j)).trans le_sup_right
  dsimp only [b] at span
  constructor
  · intro y hy
    have foot := apaid j p (o j) y hy
    have dist := separation_triangle (o j) y (o i)
    rw [separation_comm (o j) y] at dist
    change radius (d i) < separation y (o i)
    omega
  · intro y hy
    have foot := vpaid j p (o j) y hy
    have dist := separation_triangle (o j) y (o i)
    rw [separation_comm (o j) y] at dist
    change radius (d i) < separation y (o i)
    omega

theorem intersects (φ : Test 3) (legal : tsupport φ⊆conf 3)
    (E : ∀ d, SectionData (R.family.labels.level d)) (radius : ℕ → ℕ) (d : Fin 3 → ℕ) :
    ∃ p₀ : ℕ, ∀ r : ℝ, 0<r → r≤1 → ∀ᶠ m : ℕ in atTop, ∀ᶠ k : ℕ in atTop, ∃ early:m≤k,
      ∀ᶠ N : ℕ in atTop, ∃ h:k≤N, ∀ p≥p₀, ∀ o : Fin 3→ Site (R.family.side N p),
      (∃ x∈tsupport φ, positions (R:=R) r (N,p) x = o) →
      let S:=center R.family.S p (early.trans h) 0
      ∃ u : Site (R.family.side N p), ∃ v : Fin 3→ S.Cell, Injective v ∧
        Avoids (C:=R.family) E radius d (fun i=>o i+u) ∧
        ∀ i,o i+u∈S.margin (v i) (3*span R.family.S h p) := by
  obtain ⟨c,cp,periods⟩:=WilsonOriginalThermometerFineCells.separated R.family.S φ.hasCompactSupport legal
  obtain ⟨p₀,periods⟩:=eventually_atTop.1 periods
  obtain ⟨b,clear⟩:=cleared R E radius d
  refine ⟨p₀,fun r rp cap=>?_⟩
  filter_upwards [R.family.S.shrinks.eventually (gt_mem_nhds (show 0<r*c/4 by positivity))] with m small
  filter_upwards [eventually_ge_atTop m,R.family.S.shrinks.eventually
      (gt_mem_nhds (show 0<R.family.S.a m/32 by positivity [R.family.S.a_pos m]))] with k early narrow
  change R.family.S.a m<r*c/4 at small
  change R.family.S.a k<R.family.S.a m/32 at narrow
  refine ⟨early,?_⟩
  have room : 0<r*c/((b:ℝ)+4) := by positivity
  filter_upwards [eventually_ge_atTop k,clear,R.family.S.shrinks.eventually (gt_mem_nhds room)] with N hk ready tiny
  refine ⟨hk,fun p hp o live=>?_⟩
  let S:=center R.family.S p (early.trans hk) 0
  have base : R.family.S.a N*S.side.val = R.family.S.a m := R.family.S.embeds_scale (R.family.S.toDepth (early.trans hk) p)
  have top : R.family.S.a N*(span R.family.S hk p:ℝ) = R.family.S.a k := R.family.S.embeds_scale (R.family.S.toDepth hk p)
  obtain ⟨x,hx,atSite⟩:=live
  have distances (i j:Fin 3) (ij:i≠j) : r*c-2*R.family.S.a N ≤ R.family.S.a N*separation (o i) (o j) := by
    have raw:=periods p hp N r rp cap x hx i j ij
    change r*c-2*R.family.S.a N ≤ R.family.S.a N*separation (positions (R:=R) r (N,p) x i) (positions (R:=R) r (N,p) x j) at raw
    rwa [atSite] at raw
  have scaled : R.family.S.a N*((b:ℝ)+4)<r*c := (lt_div_iff₀ (by positivity : 0<(b:ℝ)+4)).mp tiny
  have smallN : 4*R.family.S.a N < r*c := by nlinarith only [scaled,mul_nonneg (R.family.S.a_pos N).le (Nat.cast_nonneg b)]
  have blocks : 3*(2*(3*span R.family.S hk p))<S.side.val := by
    apply Nat.cast_lt (α:=ℝ) |>.mp
    apply lt_of_mul_lt_mul_left (a:=R.family.S.a N) _ (R.family.S.a_pos N).le
    push_cast
    linarith only [base,top,narrow,R.family.S.a_pos k]
  have separate (i j:Fin 3) (ij:i≠j) : S.side.val < separation (o i) (o j) := by
    apply Nat.cast_lt (α:=ℝ) |>.mp
    apply lt_of_mul_lt_mul_left (a:=R.family.S.a N) _ (R.family.S.a_pos N).le
    linarith only [base,small,smallN,distances i j ij, mul_pos rp cp]
  obtain ⟨u,v,different,margin⟩:=WilsonThermometerCommonChambers.original S o (3*span R.family.S hk p)
    (Nat.mul_pos (by decide) (R.family.S.toDepth hk p).count.property) blocks separate
  refine ⟨u,v,different,ready p _ ?_,margin⟩
  intro i j ij
  rw [show separation (o j+u) (o i+u) = separation (o j) (o i) by simp only [separation,add_sub_add_right_eq_sub]]
  apply Nat.cast_lt (α:=ℝ) |>.mp
  apply lt_of_mul_lt_mul_left (a:=R.family.S.a N) _ (R.family.S.a_pos N).le
  nlinarith only [scaled,distances j i (Ne.symm ij),R.family.S.a_pos N]

theorem original (φ : Test 3) (legal : tsupport φ⊆conf 3)
    (E : ∀ d, SectionData (R.family.labels.level d)) (radius : ℕ → ℕ) (d : Fin 3 → ℕ) :
    ∃ p₀ : ℕ, ∀ r : ℝ, 0<r → r≤1 → ∀ᶠ m : ℕ in atTop, ∀ᶠ k : ℕ in atTop, ∃ early:m≤k,
      ∀ᶠ N : ℕ in atTop, ∃ h:k≤N, ∀ p≥p₀, ∀ o : Fin 3→ Site (R.family.side N p),
      weight φ (positions (R:=R) r (N,p)) o ≠ 0 →
      let S:=center R.family.S p (early.trans h) 0
      ∃ u : Site (R.family.side N p), ∃ v : Fin 3→ S.Cell, Injective v ∧
        Avoids (C:=R.family) E radius d (fun i=>o i+u) ∧
        ∀ i,o i+u∈S.margin (v i) (3*span R.family.S h p) := by
  obtain ⟨p₀,cells⟩:=intersects R φ legal E radius d
  refine ⟨p₀,fun r rp cap=>?_⟩
  filter_upwards [cells r rp cap] with m chosen
  filter_upwards [chosen] with k fit
  obtain ⟨early,fine⟩:=fit
  refine ⟨early,?_⟩
  filter_upwards [fine] with N law
  exact ⟨law.choose,fun p hp o live=>law.choose_spec p hp o (WilsonOriginalThermometerFineCells.occupied φ _ o live)⟩

end YM.Integration.WilsonThermometerCompactChambers

import YM.WilsonMS.ScalePath.AppliedLPT
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.Horizon
import YM.MS.Dial.Watch
import YM.XSpace.Regulated

/-!
# Choose the MS field reps, recover the *physical* filtered field structure

Common real bidegree lift from radial jets (`On.lifting`) for doing the
comparisons. A `Deck` is rather general (can even have negative grades in
principal, determined early); use no extra directions of the D continuation to
form the physical alphabet. Nor trace its open tensors before evaluating. The
whole Maxwell sector is the input/output here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Ensure
open Function Filter Set MeasureTheory XSpace
open Lattice RG Maxwell Source Labels Maxwell.Free
open MS MS.Local MS.Local.Physical MS.Plane MS.Koszul MS.Theater MS.Tone
open MS.Menus MS.Land MS.Local.BV MS.Landau.Detect
open Submodule
open scoped Classical Topology ContDiff BigOperators RealInnerProductSpace
variable {G : Gauge} {p : Labels.Pol G} {d r : ℕ}

lemma realForma (p : Labels.Pol G) :
    Free.realForm (Maxwell.reduceEq p) = reduceEq (Labels.conjPol p) := by
  apply Maxwell.equalPol
  intro A
  rw [Free.real_eval, jet_value, jet_value, conj_value]

lemma lit_sector (h : p ∈ Film0 G d r) : reduceEq p ∈ shellSector G d :=
  ⟨⟨p, limitH ((cinema _).mp h).1, ((cinema _).mp h).2.1⟩, rfl⟩

lemma observed_free (h : At p (d, r)) : MvPolynomial.IsWeightedHomogeneous bwt (reduceEq p) (d, r) := by
  have hh : MvPolynomial.IsWeightedHomogeneous bidegree p (d, r) := (nodeId _ _).mp h
  rw [← hh.weightedHomogeneousComponent_same, ←
    Free.commuting bidegree _ reduceEq (Free.reduce_grade (fun i => (i + 2, (1 : ℕ))))]
  exact MvPolynomial.weightedHomogeneousComponent_mem ..

lemma returns_to (h : p ∈ Film0 G d r) : On.lifting (reduceEq p) ∈ Film0 G d r := by
  let q : shellSector G d := ⟨reduceEq p, lit_sector h⟩
  obtain ⟨ht, hp, hv⟩ := (cinema p).mp h
  let x := On.sectionMap d q
  refine (cinema _).mpr ⟨?_, (show x.val ∈ invariantSpace G from x.property.2), ?_⟩
  · apply (nodeId _ _).mpr
    exact (pure_grade ..).mp (On.section_grade q (observed_free ht))
  rw [← On.lift_conj, realForma, hv]

variable (G)

/-- Real-linear idempotent on bidegree-pure Maxwell input. -/
def idempotent (h r : ℕ) : Film0 G h r →ₗ[ℝ] Film0 G h r :=
  (((On.lifting.toLinearMap).restrictScalars ℝ).comp (stageM G h r)).codRestrict (Film0 G h r)
    (fun i => returns_to i.property)

/-- keeps ANCILLARY real Section convention -/
def tangible (h r : ℕ) : Submodule ℝ (Law G) :=
  LinearMap.range ((Allowed G h r).subtype ∘ₗ (craftK G h r).toLinearMap ∘ₗ idempotent G h r)

lemma takes (h r : ℕ) (x : Film0 G h r) : orbit G (On.lifting (reduceEq x.val)) ∈ tangible G h r :=
  ⟨x, rfl⟩

lemma comprehension (h r : ℕ) : tangible G h r ⊔ Null G h r = Allowed G h r := by
  apply le_antisymm (sup_le ?_ (null_subset ..))
  swap
  · rintro f ⟨v, rfl⟩
    exact (craftK G h r (idempotent G h r v)).property
  intro f hf
  obtain ⟨x, hx, rfl⟩ := chooseX hf
  let p : Film0 G h r := ⟨x, hx⟩
  let y := idempotent G h r p
  let z := p - y
  apply Submodule.mem_sup.mpr
  refine ⟨orbit G y.val, takes G h r p, orbit G z.val, ?_, ?_⟩
  · apply (certN z.property.2 z.property.1).mpr
    change reduceEq (x - On.lifting (reduceEq x)) = _
    rw [map_sub, On.lift_recover, sub_self]
  rw [← map_add]
  apply congr_arg _
  change y.val + (x - y.val) = x
  ring
lemma distinctive (h r : ℕ) : Disjoint (tangible G h r) (Null G h r) := by
  apply Submodule.disjoint_def.mpr
  rintro v ⟨x, rfl⟩ hp
  let y := idempotent G h r x
  have he := (certN y.property.2 y.property.1).mp hp
  have hx : reduceEq x.val = 0 := Eq.trans (On.lift_recover _).symm he
  change orbit G (On.lifting (reduceEq x.val)) = 0
  rw [hx, map_zero, map_zero]

def deck : Deck G
    where
  carries
    | Int.ofNat n => tangible G n
    | Int.negSucc n => (Classical.choice (Deck.setting G)).carries (Int.negSucc n)
  sup h
    i := by
    cases h with
    | ofNat h => exact comprehension G h i
    | negSucc h => exact (Classical.choice (Deck.setting G)).sup ..
  disjoint h
    i := by
    cases h with
    | ofNat h => exact distinctive G h i
    | negSucc h => exact (Classical.choice (Deck.setting G)).disjoint ..
local notation "B" => deck G

lemma coincide (i : (B).BIndex d r) : On.lifting (reduceEq (film B i)) = film B i := by
  have ht := filmW (B) (h := d) i
  let A := film B (h := d) i
  have he : orbit G A ∈ tangible G d r := by
    rw [lamp_here]
    exact (B).form (d : ℕ) r i
  obtain ⟨x, hx⟩ := he
  let y := On.lifting (reduceEq x.val)
  have hp : y = A := opaqueL (returns_to x.property |>.2) ht.2 hx
  change On.lifting (reduceEq A) = A
  rw [← hp, On.lift_recover]

variable {G}

lemma byGrade {p : WickPol G} (h : MvPolynomial.IsWeightedHomogeneous bwt p (d, r)) :
    MvPolynomial.IsWeightedHomogeneous scaleW p d := by
  intro i hi
  have he := h hi
  rw [Finsupp.weight_apply] at he
  replace he := congr_arg Prod.fst he
  unfold Finsupp.sum at he
  simp only [Prod.fst_sum, Prod.smul_fst] at he
  exact he

lemma scope (a : Glyph B d) : Theater.Letters B a ∈ On.Grade G a.1.val :=
  ⟨letter_sector B a, byGrade (observed_free (G := G) (filmBasic B a |>.2))⟩

abbrev full (a : Plaid B d) : On.Grade G d :=
  ⟨Theater.Letters B (Land.read a), scope (Land.read a)⟩

lemma physical_dim (a : Plaid B d) : On.lifting (full a).val = Theater.ΕData B (Land.read a) :=
  coincide G (Land.read a).2.2

variable (G d)

lemma read_inj : Injective (Land.read : Plaid B d → Glyph B d) := by
  intro i j h
  simpa [Land.read] using h

lemma locations : LinearIndependent ℂ (full (G := G) (d := d)) := by
  refine LinearIndependent.of_comp (On.Grade G d).subtype ?_
  exact (illumined B d).comp _ (read_inj G d)

lemma spectral_range (c : On.Grade G d) : c ∈ Submodule.span ℂ (Set.range (full (G := G) (d := d))) := by
  let K := Daylight B d
  let Z : shellSector G d := ⟨c.val, c.property.1⟩
  have ht : c.val = ∑ i : Glyph B d, K.repr Z i • Theater.Letters B i := by
    have he := congr_arg Subtype.val (K.sum_repr Z)
    rw [AddSubmonoidClass.coe_finsetSum] at he
    simp_rw [K, readHeight] at he
    exact he.symm
  let bias := MvPolynomial.weightedHomogeneousComponent (R := ℂ) (scaleW (G := G)) d
  have hp (i : Glyph B d) :
    bias (Theater.Letters B i) = if h : i.1.val = d then Theater.Letters B i else 0 := by
    have he : MvPolynomial.IsWeightedHomogeneous scaleW (Theater.Letters B i) i.1.val := (scope i).2
    split_ifs with h
    exact
      (show MvPolynomial.IsWeightedHomogeneous scaleW (Theater.Letters B i) d from
          Eq.mp
            (congr_arg (fun n => MvPolynomial.IsWeightedHomogeneous scaleW (Theater.Letters B i) n) h)
            he).weightedHomogeneousComponent_same
    exact he.weightedHomogeneousComponent_ne d (Ne.symm h)
  have hc : c.val ∈ Submodule.map (On.Grade G d).subtype (Submodule.span ℂ (Set.range full)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rw [←
      (show MvPolynomial.IsWeightedHomogeneous scaleW c.val d from
          c.property.2).weightedHomogeneousComponent_same]
    rw [ht, map_sum]
    simp_rw [map_smul]
    apply sum_mem
    intro i _
    rw [show MvPolynomial.weightedHomogeneousComponent _ _ _ = _ from hp i]
    apply smul_mem
    split_ifs with h
    swap
    · exact zero_mem _
    apply Submodule.subset_span
    have he : ∃ a : Plaid B d, i = Land.read a := by
      rcases i with ⟨p, k⟩
      change p.val = d at h
      obtain hh : p = ⟨d, by omega⟩ := Fin.ext h
      revert k
      rw [hh]
      intro k _
      exact ⟨k, rfl⟩
    obtain ⟨a, rfl⟩ := he
    exact ⟨a, rfl⟩
  obtain ⟨x, hx, hX⟩ := hc
  exact (Subtype.ext hX : x = c) ▸ hx

noncomputable def stars : Module.Basis (Plaid B d) ℂ (On.Grade G d) :=
  Module.Basis.mk (locations G d) (fun c _ => spectral_range G d c)

lemma stars_eq (i : Plaid B d) : stars G d i = full i :=
  Module.Basis.mk_apply ..

end YM.WilsonMS.Ensure

import YM.Integration.WilsonFactoryGlyphEngineering
import YM.Integration.WilsonFactoryGlyphPairPrice
import YM.Integration.WilsonOrdinaryHomogeneousDetectors

/-! For the genuine homogeneous real mixed detectors, only the matching
two engineering heights contribute to the entire signed physical invoice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFactoryHomogeneousPairs
open Function Finset Lattice RG Spec OPE SharpGram RG12 RG17 MS MS.Menus MS.Local.Physical
open WilsonFactoryGlyphPairPrice WilsonFactoryPhysicalGlyphs
open scoped Classical BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
    (B : Deck G) (F : Final C f S) (d : ℕ)
set_option quotPrecheck false
local notation "handles" => WilsonOrdinaryHomogeneousDetectors.Handle F d
local notation "b₀" => WilsonOrdinaryHomogeneousDetectors.basis F d

theorem off (i : handles) (q : Glyph B d) (h : q.1.val ≠ i.1.val) :
    weight (C:=C) B d (b₀ i) q = 0 :=
  WilsonFactoryGlyphEngineering.off B C.labels d _ i.1.val
    (WilsonOrdinaryHomogeneousDetectors.eigenvalue F d i 2) q h

def chooseFee (j l : ℕ) (A H : Glyph B d → Glyph B d → ℂ) (q t : Glyph B d) :=
  if q.1.val=j ∧ t.1.val=l then A q t else H q t

variable (u v : WilsonOrdinaryHomogeneousDetectors.Handle F d)

theorem restrict_trial (A H : Glyph B d → Glyph B d → ℂ) :
    trial (C:=C) B d d (b₀ u) (b₀ v) (chooseFee B d u.1.val v.1.val A H) =
    trial (C:=C) B d d (b₀ u) (b₀ v) A := by
  unfold trial
  refine sum_congr rfl fun q _ => ?_
  by_cases hq : q.1.val=u.1.val
  · apply congrArg (weight (C:=C) B d (b₀ u) q • ·)
    refine sum_congr rfl fun t _ => ?_
    by_cases ht : t.1.val=v.1.val
    · rw [chooseFee,if_pos ⟨hq,ht⟩]
    · rw [off B F d v t ht,zero_smul,zero_smul]
  · rw [off B F d u q hq,zero_smul,zero_smul]

variable (J : ℝ → PhysMS.tower S) (r s : ℝ) (N p : ℕ) (x y : Site (C.side N p))
    (ζ : Wilson.Config G (C.side N p) → ℂ)
local notation "H" => joint B d J d r s N p x y ζ

theorem priced (good : Continuous ζ) (A : Glyph B d → Glyph B d → ℂ) :
    ‖C.omega N p (fun U => mark (C:=C) d J r (b₀ u) N p x U *
      (mark (C:=C) d J s (b₀ v) N p y U * ζ U)) - trial (C:=C) B d d (b₀ u) (b₀ v) A‖ ≤
      (fee B d C.labels * ‖b₀ u‖) * (fee B d C.labels * ‖b₀ v‖) *
        ∑ q : Glyph B d, ∑ t : Glyph B d,
          if q.1.val=u.1.val ∧ t.1.val=v.1.val then ‖H q t - A q t‖ else 0 := by
  let A' := chooseFee B d u.1.val v.1.val A H
  have h := WilsonFactoryGlyphPairPrice.priced B d J d r s (b₀ u) (b₀ v) N p x y ζ good A'
  rw [show trial (C:=C) B d d (b₀ u) (b₀ v) A' = _ from restrict_trial B F d u v A H] at h
  refine h.trans_eq ?_
  apply congrArg (fun m : ℝ => (fee B d C.labels * ‖b₀ u‖) * (fee B d C.labels * ‖b₀ v‖) * m)
  unfold bill
  refine sum_congr rfl fun q _ => sum_congr rfl fun t _ => ?_
  by_cases both : q.1.val=u.1.val ∧ t.1.val=v.1.val <;> simp [A',chooseFee,both]

end YM.Integration.WilsonFactoryHomogeneousPairs

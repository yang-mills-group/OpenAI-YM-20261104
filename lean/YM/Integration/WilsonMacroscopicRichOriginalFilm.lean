import YM.Integration.ActualOriginalDictionary

/-! Every issued physical MS glyph has an actual on-grade nonzero original Wilson
coefficient multiplying a nonzero curvature law on the same run. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichOriginalFilm
open Function Lattice Labels MS MS.Local.Physical MS.Landau MS.Lifting MS.Theater
open WilsonComparison.Finite PhysicalNext.Repeat.Legato ActualOriginalDictionary
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G)(B:Deck G)

theorem raw (d r:ℕ)(i:B.BIndex (d:ℤ) r):B.raw (d:ℤ) r i≠0:=by
  intro vanishes
  exact (Module.finBasis ℝ (B.carries (d:ℤ) r)).ne_zero i (Subtype.ext vanishes)

theorem original (d r:ℕ)(i:B.BIndex (d:ℤ) r):
    ∃j:(R.family.labels.level d).Index,coordinates R B d r i j≠0 ∧
      (R.family.labels.level d).grades j=(d,r) ∧
      ActualStencilClassicalLaw.law (R.family.labels.level d) j≠0:=by
  classical
  have active:∃j:(R.family.labels.level d).Index,coordinates R B d r i j •
      ActualStencilClassicalLaw.law (R.family.labels.level d) j≠0:=by
    by_contra! all
    apply raw B d r i
    rw [law_expansion R B d r i]
    apply Finset.sum_eq_zero
    intro j _
    rw [weight_cast R B d r i j]
    exact all j
  obtain ⟨j,live⟩:=active
  have coord:coordinates R B d r i j≠0:=by
    intro dead
    exact live (by rw [dead,zero_smul])
  refine ⟨j,coord,?_,?_⟩
  · by_contra other
    exact coord (off_grade R B d r i j other)
  · intro dead
    exact live (by rw [dead,smul_zero])

end YM.Integration.WilsonMacroscopicRichOriginalFilm

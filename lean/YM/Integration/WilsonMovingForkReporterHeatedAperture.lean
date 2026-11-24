import YM.Integration.WilsonPhysicalThermalWickHearing
import YM.Integration.WilsonReporterWeightedMarket

/-! A fixed finite panel of true homogeneous two-name directions is funded
before either cutoff at every aperture in the original closed window. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterHeatedAperture
open Lattice Wilson RG Labels Function Filter Set
open Next.Rank Next.Rank.Atlas Next.Rank.Station Next.Rank.Perch Next.Rank.Glimmer
open Next.Rank.Configuration Next.Rank.Tapes Next.Rank.Tapes.West Next.Rank.Ribbon
open Marker Glyph Exponential Cells
open WilsonPhysicalThermalWickSky (labels)
open WilsonPhysicalThermalWickRescale (pure)
open scoped BigOperators Classical Topology
variable {G:Gauge} {C:Family G}
local notation "A" => C.path.levels

structure Test (C:Family G) where
  deg : Fin 2 → ℕ
  height : ℕ
  elevated : ∀ i, deg i ≤ height
  raw : (i:Fin 2) → C.label (deg i)
  rank : Fin 2 → ℕ
  pure_rank : ∀ i, pure (rank i) (thawKey (labels raw elevated i))
  capped : ∀ i, rank i ≤ height
  increasing : rank 0 ≤ rank 1
  support : Set (Points 2)
  compact : IsCompact support
  clear : support ⊆ conf 2

def spread (E:Test C) := E.rank 1-E.rank 0

def Ready (E:Test C) (θ:ℕ) (lo hi:ℝ) (k:ℕ) : Prop :=
  (∀ b∈Icc lo hi,WallsSky b E.elevated E.raw E.support θ k) ∧
  ∀ {N p:ℕ} {ξ:Purse} {P:(i:ℕ)→Rep G (C.side i p)} {x:Points 2} {Ψ:AtlasData G C.S p},
    k≤N → ξ.taylor=θ → ξ.band∈Icc lo hi → tested A ξ.band k x∈E.support →
    ∀ (fit:FitSky A ξ.band k x)
      (F:(i:Fin 2)→StampDuty C k N p (E.deg i) ξ.taylor (P k) ξ.era.coast.Q Ψ),
      BellSky A Ψ E.height ξ.taylor fit → invariantAt (C:=C) k (wood A k) p Ψ →
      ∀ u:(i:Fin 2)→C.label (E.deg i),
        (∀i,Price.Solves C (mag A ξ.band k) (E.deg i) k N p (F i).T (E.raw i) (u i)) →
        let a := WilsonPhysicalThermalWickStretched.rates ((bill 1 (clim A k))^spread E)
        WilsonReporterWeightedReturn.Signed (WilsonReporterWeightedOrdinary.stretch C a E.raw)
          (WilsonReporterWeightedOrdinary.stretch C a u) fit F

private theorem uniform {ι:Type*} [Nonempty ι] (P:ℕ→ι→Prop)
    (priced:∀ f:ℕ→ι,∀ᶠ k in atTop,P k (f k)) : ∀ᶠ k in atTop,∀ s,P k s := by
  classical
  let f (k:ℕ) := if h:∃ s,¬ P k s then h.choose else Classical.arbitrary ι
  filter_upwards [priced f] with k good s
  by_contra no
  have bad : ∃ s,¬ P k s := ⟨s,no⟩
  exact bad.choose_spec (by simpa only [f,dif_pos bad] using good)

theorem original (simple:G.Simple) (made:C.Makes) (E:Test C) (θ:ℕ)
    (deep:100*(E.height+1)≤θ) (lo hi:ℝ) (six:6≤lo) (wide:lo≤hi)
    (poles:∀i,saves C (E.deg i)+(spread E:ℝ)+3≤lo) :
    ∀ᶠ k:ℕ in atTop,Ready E θ lo hi k := by
  classical
  let I := Icc lo hi
  letI : Nonempty I := ⟨⟨lo,le_rfl,wide⟩⟩
  have walls := uniform (ι:=I) (fun k s=>WallsSky s.1 E.elevated E.raw E.support θ k)
    (fun f=>mural_castSky E.elevated E.raw E.compact E.clear made simple lo six
      (fun i=>by linarith only [poles i,Nat.cast_nonneg (α:=ℝ) (spread E)]) θ
      (fun k=>(f k).1) (fun k=>(f k).2.1) hi (fun k=>(f k).2.2))
  obtain ⟨B,cost⟩ := WilsonReporterWeightedMarket.compact E.raw E.compact E.clear
  have heating := WilsonPhysicalThermalWickHearing.original simple E.raw E.elevated
    E.rank E.pure_rank E.capped E.increasing deep B
  filter_upwards [walls,heating] with k windows signed
  refine ⟨fun b hb=>windows ⟨b,hb⟩,?_⟩
  intro N p ξ P x Ψ live clock band member fit F bell inv u solved
  have member' := (windows ⟨ξ.band,band⟩).merry x member
  exact signed live clock fit F (clock.symm ▸ member') bell inv
    (fun i=>(poles i).trans band.1) (cost _ member).1 u solved

theorem finite {ι:Type*} [Finite ι] (simple:G.Simple) (made:C.Makes) (E:ι→Test C)
    (θ:ℕ) (deep:∀s,100*((E s).height+1)≤θ) (lo hi:ℝ) (six:6≤lo) (wide:lo≤hi)
    (poles:∀s i,saves C ((E s).deg i)+(spread (E s):ℝ)+3≤lo) :
    ∀ᶠ k:ℕ in atTop,∀s,Ready (E s) θ lo hi k :=
  eventually_all.mpr fun s=>original simple made (E s) θ (deep s) lo hi six wide (poles s)

end YM.Integration.WilsonMovingForkReporterHeatedAperture
end

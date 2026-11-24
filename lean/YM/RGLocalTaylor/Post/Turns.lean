import YM.RGLocalTaylor.Post.Reuse

/-! # All physical rotations for the fertility assumptions of EGeneration. Keep exact K. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Post
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open UVNext.CouplingReset Input PriceCompiler Rain Mallow Spring
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {X: Metals G} {D : Rolls X.p} {A: Alloy X D} {R:Factor A}
    {m N n : ℕ} {Q : UVNext.CouplingReset.In A.B.a m n} {l v:ℝ} (H:Spring R N m n l v Q) (x:ℝ)
local notation "I" => A.B.a.S.side m n
local notation "J" => A.B.a.clock.J (m+1)
local notation "Γ" => R.expense J (A.B.a.clock.J m)
local notation "y" => A.B.a.clock.hatBeta m
local notation "B" => (A.B.a.budget m)
local notation "b" => A.B.a.clock.hatBeta (m+1)
local notation "L₀" => D.L J
local notation "p₀" => H.H.latch x
local notation "Q₀" => H.H.houses (H.H.latch x)
local notation "k" => Rain.lint R.target A m
local notation "e" => Trio.base (Rain.lint R.target A m) (radiusB y)
local notation "Sq" => H.H.sister (H.H.latch x)
local notation "γ" => A.B.kin.alpha N m
local notation "OO" => Chi.canonical
local notation "α" => H.H.base
local notation "Ω" => H.H.doors
set_option quotPrecheck false
local notation "b₀" => (Rain.noteX H.H H.knows x)
local notation "φ" => H.W.offers H.ordinal (Rain.noteX H.H H.knows x)
local notation "Pu" => (Rain.screens R.target A m)

namespace Worker
open RG01.Survive Read Pane Slide
variable (M : ℕ)

open Refrain
local notation "u₀" => (lights H.H H.knows H.W H.ordinal x)
local notation "e'" => Read.Pane.locator k B
local notation "D₀" => Meadow.studio k (radiusB y)
local notation "t₀" => ((Mayer.arcRadius G L₀ y)^(M+1))⁻¹
variable {M} (he:Mallow.RG12.Earned (Mayer.decal G) R.shape A.delay)(hM:M≤A.B.a.clock.J (m+1))(hm:m<N)

open Ovens Ovens.Pipes
variable {p' u : ℝ}
variable (s : Signed)(b' : Site (A.B.a.S.side m n))

private lemma composer (Wv : Collection.Source G I) (f : Song.Magazine α → Config G I → ℝ) (hv : Wv.logRead=Song.choir f∘ Song.pennant α) (hk:Wv.hardRead=(H.H.fullSong x).hardRead):
    Nonempty (((Ω).read (uptake α H.ordinal Wv)).Moves s b'):= by
  let v k':= if k' ∈ Meadow.bouquet α H.ordinal then 0 else f k'
  have hh i: (uptake α H.ordinal Wv).logRead i=Song.choir v (Song.pennant α i):= by
    unfold uptake
    rw [hv]; dsimp only [Function.comp_apply]; let j:= Song.pennant α i
    change (if _ then (_:Config _ _→ℝ) else _)= Rim I • ((if _ then (_:Config G I→ℝ) else _) ∘ _)
    split
    next hh=> rw [if_pos ((Meadow.petaled _ _).1 hh)]; ext; simp
    next hh => rw [if_neg (fun ht=> hh ((Meadow.petaled _ _).2 ht))]; rfl
  unfold Listing.read; rw [show (uptake α H.ordinal Wv).logRead=_ from funext hh,show (uptake α H.ordinal Wv).hardRead=_ from hk]; exact Beam.moves α B OO Sq s b' v

include H x s b'
variable (ha:x∈Icc l v)
include ha hm

private lemma reused (Y V : Collection.Source G I) (T:Trio.Offer G I) (hf:V.logRead=(Marlin.bison Y T u₀).regular) (hk:V.hardRead=(H.V' x).hardRead)
    (he:Nonempty (((Ω).read Y).Moves s b')): Nonempty ((H.X'.read V).Moves s b'):= by
  have hv:= Marlin.reeds Ω e (2*e) Y T u₀ s b' he.some
  exact Anchor.impart ((H.V' x).hardRead) hv ((H.core hm x ha).transforms s b') rfl hf.symm rfl hk rfl

variable (M)
lemma transfixed : Nonempty ((H.X'.read (design H x M)).Moves s b') :=
  reused H x hm s b' ha _ _ _ rfl rfl (composer H x s b' _ _ (rfl : (offcut H x M).logRead=_) rfl)
lemma transfixed_tail : Nonempty ((H.X'.read (blanks H x M)).Moves s b') :=
  reused H x hm s b' ha _ _ _ rfl rfl (composer H x s b' _ _ (rfl : (ink H x M).logRead=_) rfl)
end Worker
end YM.RGLocalTaylor.Post

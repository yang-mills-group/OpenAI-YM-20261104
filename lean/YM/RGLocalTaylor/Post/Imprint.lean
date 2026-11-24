import YM.RGLocalTaylor.Read.Beacon
import YM.RG12.Burst.Cotton
/-!
# Physical Rain presentation and compatibility invoice

Not any equality between a Pair and a curve offered with independent β transport.
Only Spring: the same fixed input and `Faces` planning used all the way through
reset. Then all secondary `Meadow.barony` apertures can generate the log estimates
with exactly the `w` bought at this cutoff. Coefficients use the log-exponent
Taylor choice on the projected pre-logs, **including** the auxiliary purely Virgin
labels inserted by this representation. `ordinal` and all other look-ups retained
from actual representation; don't infer coefficient invariance if those are reselected.

Perturbation comparison along `x` always includes HDR horizon M (affecting only
the last tail and truncation of sums), before estimates. No fitting quantities out
of the output logs `opening`, `vents`, `delta`, `tau`. Exact scalar/field and actual
hard (unapproximated K often much smaller than any of these envelopes), no
claim that substituting approximant Art into finish + recompiling K will give
the same path or preserve the masks.
-/
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
abbrev offcut := modeled (χ:=OO) Sq γ (fun _ j=> M+1 ≤ j) (Mayer.issue Q₀ OO M)
abbrev ink := voted (χ:=OO) Sq γ (fun _ j=> M+1 ≤ j) (Mayer.issue Q₀ OO M)
-- use own assembly lookups before reading V.
def auth (i:Stars) : Match.Alliance (H.W.tiers i (Rain.noteX H.H H.knows x)) (H.W.tiers i (Rain.noteX H.H H.knows x)) 1 0:= Match.staple rfl rfl rfl
abbrev orderbook (i:Stars) := H.W.tiers i (Rain.noteX H.H H.knows x)
abbrev offAux (i:Stars) := modeled (χ:=OO) (auth H x i) γ (fun _ j=>M+1≤j) (Mayer.issue (orderbook H x i) OO M)
abbrev inkAux (i:Stars) := voted (χ:=OO) (auth H x i) γ (fun _ j=>M+1≤j) (Mayer.issue (orderbook H x i) OO M)
def offRay (i :Stars) : Trio.Offer G (Rain.moor R.target A m i):= Read.Pane.panelist (orderbook H x i) B H.ordinal (offAux H x M i)
def billRay (i :Stars) : Trio.Offer G (Rain.moor R.target A m i):= Read.Pane.panelist (orderbook H x i) B H.ordinal (inkAux H x M i)

variable {M}
private lemma licenses {c f': Side} {S:StepData c f'} {T:Tube G S} {R':RG.Rep G f'}
    (W: Cash (R.walls J (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m) (R.shape.μ J (A.B.a.clock.J m)) (D.L J) (R.target J (A.B.a.clock.J m)) (R.shape.o J (A.B.a.clock.J m)) (R.shape.c J (A.B.a.clock.J m)) T R')
    (h: Mallow.RG12.Earned (Mayer.decal G) R.shape A.delay) (hm:M≤J) (hp : Stamp T) : ∃ ωX,Mayer.Passport W (Γ).earn ωX (turnFee B) (Height.asset Γ) (B).order (B).power M:= by
  obtain ⟨w,hF⟩:= h J y (A.B.valid.pays m) (A.B.a.clock.J m) (step_paid A.B.a m) M hm
  have hV:= Rain.jersey (A:=A) (m:=m)
  refine ⟨w,?_⟩; rw [hV.1,hV.2.1,hV.2.2.2]; exact hF c f' S T hp R' _ W

local notation "t₀" => ((Mayer.arcRadius G L₀ y)^(M+1))⁻¹
variable (he:Mallow.RG12.Earned (Mayer.decal G) R.shape A.delay)(hM:M≤ A.B.a.clock.J (m+1))(hm:m<N)
include hM he hm
lemma physical : (H.H.fullSong x).logRead=(offcut H x M).logRead+(ink H x M).logRead ∧ orient B (Ω).reg ((ink H x M).logRead) t₀ := by
  have hi: preExponent B ≤ (Γ).earn:= by rw [preExponent,Rain.jersey (A:=A) (m:=m)|>.2.2.1]; exact R.pledging.agenda _ _ (step_paid A.B.a m)|>.1
  obtain ⟨c,hc⟩:= licenses (M:=M) (Q₀) he hM (Opera.protocol A.B hm R.pledging.conducts.full)
  obtain ⟨hg,h⟩:= Read.earning Sq γ (fun _ j=> M+1 ≤ j) (fun _ _ h=>h) (p:=B) rfl rfl hi (asset_pos ..) hc
  exact ⟨hg,h (Beam.contents (α) B) (Beam.patch _ _)⟩

lemma adjunct (i:Stars): φ i=offRay H x M i+billRay H x M i ∧ Read.Pane.PanelQuality B (billRay H x M i) ((Fintype.card (Site (Rain.moor R.target A m i)):ℝ)*t₀):= by
  obtain ⟨w,hw⟩:= licenses (M:=M) (orderbook H x i) he hM (Pane.ovation A N (Rain.panes R.target A m i) hm R.pledging.conducts.full)
  have hi: preExponent B ≤ (Γ).earn:= by rw [preExponent,Rain.jersey (A:=A) (m:=m)|>.2.2.1]; exact R.pledging.agenda _ _ (step_paid A.B.a m)|>.1
  obtain ⟨hg,hg'⟩:= Read.earning (auth H x i) γ (fun _ j=> M+1 ≤ j) (fun _ _ h=>h) (p:=B) rfl rfl hi (asset_pos ..) hw
  let X:= orderbook H x i
  let V:=Song.plusone X (auth H x i) OO γ
  exact ⟨(show φ i=Read.Pane.panelist X B H.ordinal V from funext fun yyy=> Meadow.aster OO B (auth H x i) rfl rfl rfl γ H.ordinal yyy).trans (Read.Pane.atPanel hg), Read.Pane.evaluated (H:=X) (p:=B) (hp:=hg' _ (Beam.patch _ _))⟩

variable (M)
-- reconstruct beacons + frame inputs always using original auth/H
local notation "D₀" => Meadow.studio k (radiusB y)

def design : Collection.Source G (A.B.a.S.side m n) where
  logRead := (Marlin.bison (uptake α H.ordinal (offcut H x M)) (Trio.ornament Pu (offRay H x M)) (lights H.H H.knows H.W H.ordinal x)).regular
  hardRead := (H.V' x).hardRead

def blanks : Collection.Source G (A.B.a.S.side m n) where
  logRead := (Marlin.bison (uptake α H.ordinal (ink H x M)) (Trio.ornament Pu (billRay H x M)) (lights H.H H.knows H.W H.ordinal x)).regular
  hardRead := (H.V' x).hardRead

-- no K model-side invariance through horizon if Rain book changes.
def stance := H.H.payment H.O x - Read.Pane.panelist α B H.ordinal (offcut H x M) 0 1
end Worker
end YM.RGLocalTaylor.Post

import YM.RGLocalTaylor.Post.Imprint

/-!
# Use of the semantic print in a true Spring. Ready for paying assembly next.
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

open Refrain
local notation "u₀" => (lights H.H H.knows H.W H.ordinal x)
local notation "e'" => Read.Pane.locator k B
local notation "D₀" => Meadow.studio k (radiusB y)
local notation "t₀" => ((Mayer.arcRadius G L₀ y)^(M+1))⁻¹
variable {M} (he:Mallow.RG12.Earned (Mayer.decal G) R.shape A.delay)(hM:M≤A.B.a.clock.J (m+1))(hm:m<N)
include he hM hm

lemma earrings : orient B H.X'.reg (blanks H x M|>.logRead) (t₀+turnFee B* (e' t₀)) := by
  have hY:= Read.Pane.upright (H:=α) (p:=B) (n:=H.ordinal) (v:=ink H x M) (hp:=(physical H x he hM hm).2)
  have hp:= Read.Pane.prayer (c:=I) B Pu (billRay H x M) (fun i=> adjunct H x he hM hm i|>.2)
  exact Marlin.reg_bison Ω e (2*e) _ (Trio.ornament Pu (billRay H x M)) u₀ hY hp

lemma letters : (H.V' x).logRead=(design H x M).logRead+(blanks H x M).logRead := by
  have hv : (uptick H.H H.ordinal x).logRead=(uptake α H.ordinal (offcut H x M)).logRead+(uptake α H.ordinal (ink H x M)).logRead := by
    rw [← Pane.restored (physical H x he hM hm).1]
    funext i; unfold uptake uptick; rw [Meadow.compass]
    change (if _ then (0:Config G I→ℝ) else _) = if i∈ Meadow.panel α H.ordinal then 0 else _
    split; next h=> exact (if_pos ((Meadow.petaled _ _).2 h)).symm
    next h=> exact (if_neg (fun q=> h ((Meadow.petaled _ _).1 q))).symm
  have hΞ := funext fun i=> (adjunct H x he hM hm i).1
  have hh: beacons H.H H.knows H.W H.ordinal x=Trio.ornament Pu (offRay H x M)+Trio.ornament Pu (billRay H x M):=by
    unfold beacons; rw [← Read.Pane.ornament_add]; exact congr_arg (Trio.ornament (c:=I) Pu) hΞ
  ext i U
  unfold V' paint Marlin.poursP design blanks graft Marlin.bison
  dsimp only [Function.comp_apply, Pi.add_apply]
  rw [hh,hv]; rcases Marlin.leanU I i with a|a
  · rfl
  exact mul_add ..

lemma rent : |H.τ x - stance H x M|≤ (Animals.ballCost D₀:ℝ)*t₀ := by
  have ha:= (H.knows _ H.H.he).1; obtain ⟨hL,hb⟩:= H.knows _ (p₀).2
  have hq : (Q l).path=(Q (p₀)).path:= ha.path.trans hL.path.symm
  have hΩ: H.H.base.supportP=(Q₀).supportP := Match.same_area hq (H.waves.reg _ H.H.he _ (p₀).2) (H.waves.forced _ H.H.he _ (p₀).2)
  let f x:= (Read.Pane.panelist (α) B H.ordinal (ink H x M))
  have hz : Meadow.barony Q₀ OO H.ordinal γ=Read.Pane.panelist α B H.ordinal (H.H.fullSong x) := funext fun k' => Meadow.aster OO B Sq hq hΩ (H.H.agrees _) γ H.ordinal k'
  have hu:= Read.Pane.atPanel (H:=α) (p:=B) (n:=H.ordinal) (physical H x he hM hm).1
  have hA : H.τ x=stance H x M - f x 0 1:= by
    unfold stance τ Rain.stanzaFee; rw [hz,hu]; unfold f; simp only [Pi.add_apply]; ring
  rw [hA]; rw [sub_sub_cancel_left,abs_neg]; exact (panelPoint (p:=B) (H:=α) (n:=H.ordinal) (v:=ink H x M) ((physical H x he hM hm).2) rfl (0:Site I))
end Worker
end YM.RGLocalTaylor.Post

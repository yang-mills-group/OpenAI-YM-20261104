import YM.WilsonMS.Calibration.News
/-!
# `PhysicalSum` program with canonical changes still present

`PortFull`: the Wick-compensated menu using `scoreW` (so `motto` term
included). This is the part that goes in the high calibration theory;
to use its estimates we have to price the effect of these additional terms
on the pinned `rentW` trajectory. Supply scaling relation here first.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BMenu
open MS MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit Cog
open scoped Topology ContDiff Interval
variable {G : Gauge} {I W : Type} [LinearOrder W] {L : I → Side} {S : Finset W} {e : ℤ}
  {X : Rake.Dance G I W} {Q : Seeds G I W} {F H : Glade G I} {n : ℕ} (c : Berth (W := W) (I := I))
  {A : Faces I}
local notation "Ψ" => (outside L)
local notation "ιW" => (Orbit.uniform G I)
open Native.Wilsonian Paint Rake.Geo Vane Land Program Logarithm Wind Menus
local notation "m0" => (fun (_ : I) => planeF)
local notation "ρk" => (constantP G I (LowP G))
local notation "Y" => (constantP G I (PlanetL G))
local notation "Qb" => Ensure.deck G
variable {T : Prescription (Ensure.deck G)} {R : Geo I} {v : W → Rake.Label (Ensure.deck G)}
  {V : BasisMenu G}
local notation "πA" => Scope G (Wind.skyline G T.team) R.η

abbrev PortFull (V : BasisMenu G) (T : Prescription (Ensure.deck G)) (u : Rake.Label Qb) :
    Actor G :=
  scoreW V T.team (T.fees u.h u.item)

lemma boardingA (hx : Crew Ψ ιW πA 0 A (goalsK c R.η (PortFull V T ∘ v)) X)
    (he : ∀ i t, Knits (X i t)) : AboveOrd V R T v (info c) (voyage c X) := by
  refine ⟨?_, fun p => ?_, fun s hs k => ?_⟩
  · unfold voyage
    rw [hx.1]
    funext i t p
    dsimp only [Fleet.vessel, Fleet.unload, Pi.zero_apply]
    rw [map_zero, map_zero]
  · let P := v p
    let Hw := rowFull V T.team (T.fees P.h P.item)
    let F : Rake.Site G I := fun n i t => lodging (c p i) (Scope G Hw R.η n i t)
    have hΨ : X { p } = F := by
      refine special p (fun n => ?_) hx
      rw [show goalsK c R.η (PortFull V T ∘ v) { p } n = _ from funext (fun i => goals_m c R.η p n i)]
      exact castP R.η (c p) (feeds V T.team (T.fees P.h P.item)) n L A
    unfold voyage
    rw [hΨ]
    funext n i t
    unfold Fleet.vessel
    rw [anchorC, dif_pos (Finset.singleton_nonempty _), Finset.min'_singleton]
    exact unpack_home (c p i)
  obtain H := hx.2 s (Finset.card_pos.mp (by omega)) k
  let f := X s k
  let E := Vista.fort Ψ A ιW πA 0 X s k
  have heL (i) : f i 0 = 0 := by
    rw [show f i 0 = goalsK c R.η (PortFull V T ∘ v) s k i from H.1 i, goals_t c R.η (by omega)]
    rfl
  have hE : Toned E :=
    (knit_plus (LiftE.knit (gen_zip0 Ψ (healthy G I) A) (he s k))
        (campusK (healthy G I) (fun k => feesBuy (skyPC G T.team |>.owes k) R.η) (fun _ _ => knit0 ..)
          (fun i _ => he i) k (fun i _ => he s i))).1
  obtain hz := curve (F := f) (H := E) H.2 (anchorC c s) hE heL
  have hu :
    (sailP m0 Y (voyage c X s k) +
        Rake.multi m0 (info c) ρk Y (initials R T) (voyage c X s) (voyage c X) k s) =
      (fun i t => (exp t : ℂ) • Fleet.vessel E (anchorC c s) i t) := by
    funext i t
    apply f_inj (anchorC c s i)
    rw [map_smul, show frameL _ (Fleet.vessel E _ i t) = E i (exp t) from accountable ..,
      show E i _ = _ from π_src (R := R) (X := X) c T A s L (fun i n => he i n |>.1) t k i,
      smul_inv_smul₀ (by exact_mod_cast (exp_pos t).ne')]
  unfold Trip
  rw [hu]
  exact hz

end YM.WilsonMS.BMenu

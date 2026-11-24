import YM.Integration.FVA1Physical.Wilson.MarkedBareMatch
import YM.FVA2.FundingOffer

/-! Direct bare-tier identification with the FVA2 solenoid, on its physical
stencil ticket and canonical bare coupling series. The engineering powers are
kept when extracting each coefficient. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open Filter Function YM.Lattice YM.RG YM.Wilson YM.Tree YM.Precision YM.Marker
open YM.Comparison.RG02 YM.FVA2.CityHistory YM.FVA2.RayScatter
open YM.FormalOPE.RG10.InversionTop YM.FormalOPE.RG10.MultiGauge
open YM.RGComparison.Core16 YM.RGComparison.Core16.Spool
open YM.RGComparison.Core16.Parcel YM.RGComparison.Core16.Parcel.Oven
open RGComparison.Core16.Lumen
open scoped Classical Topology ContDiff

variable {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio)
    {ι : Type} [Fintype ι] (J : ι → Lamp G) (y : ι → Site f)

/-- In the physical free-link coordinates, evaluate the actual lamp stencil
with all trunk slots set to zero and the named edges at their chart values. -/
def stencilSignal (b : Bool) (w : Future G S F × Pins G c) : ℝ :=
  look b (sight J (Fk.scene (earns S F J y) (0, w.1)))

private lemma signal_ray (u : Pins G c) (b : Bool) :
    ((look b ∘ sight J) ∘ Fk.scene (earns S F J y)) = stencilSignal S F J y b ∘ recover u := by
  funext v
  apply congrArg (fun x => look b (sight J x))
  funext j
  change Fk.scene (earns S F J y) v j = Fk.scene (earns S F J y) (0,v.2) j
  unfold Fk.scene earns
  split <;> simp

private lemma signal_hot (b : Bool) : ContDiffAt ℝ ω (stencilSignal S F J y b) 0 := by
  let e := earns S F J y
  have h₁ : ContDiffAt ℝ ω (Fk.scene e) 0 := by
    apply contDiffAt_pi.mpr
    intro j
    unfold Fk.scene
    rcases he : e j with i | i
    · exact turn_hot.contDiffAt.comp (f := fun x : Fk.Door G F.Free => x.2 i) _
        ((contDiff_apply ℝ _ _).contDiffAt.comp (f := Prod.snd) _ contDiffAt_snd)
    · exact contDiffAt_fst.smul contDiffAt_const
  have h₀ : Fk.scene e (0 : Fk.Door G F.Free) = 0 := by
    funext j
    unfold Fk.scene
    cases e j <;> simp [Fk.spread]
  have h₂ : ContDiffAt ℝ ω ((look b ∘ sight J) ∘ Fk.scene e) 0 :=
    (h₀.symm ▸ sphere J b : ContDiffAt ℝ ω (look b ∘ sight J) (Fk.scene e 0)).comp 0 h₁
  exact h₂.comp (f := fun w : Future G S F × Pins G c => ((0 : ℝ),w.1)) 0
    (contDiffAt_const.prodMk contDiffAt_fst)

local notation "D₀" => Descent.nil (top := f)
local notation "h₀" => (show (D₀).Room G from trivial)

/-- For the actual physical stencil, the full FVA2 conditional fit gives
the `Fk.read` coefficients of the lamp lens after its engineering shift. -/
theorem rank_solenoid (Z : ChartRatio G) (hZ : LocalRatio Z) (t : S.Choices)
    (h : Bid.Larger (G := G) S) (u : Pins G c) {P : Oven S.patch}
    (X : P.Form G) (H : P.Offers X S.kernel) (hu : ∀ i, ‖u i‖ ≤ X.Q)
    (v : (D₀).Tags) (b : Bool) :
    PowerSeries.mk (rankℝ J S F X Z u y b) =
      Stack.drop (power J) (Stack.read u (solenoid S F D₀ v t Z 1 h h₀
        (Stack.rise (stencilSignal S F J y b)))) := by
  let Q := gateQ S F t (retained D₀ v h₀)
  let hQ := useful S F D₀ v t h h₀
  unfold solenoid
  rw [Pi.one_apply, Spot.fusionL S F Z t h v]
  exact Fork.perch (lens (S := S) u X F) Z hZ (Spot.thermalHeat S F t h) Q
    (Spot.precisionHeat S F t h v) hQ u (earns S F J y) (Spot.prospect S F t u h P X H hu)
    (stencilSignal S F J y b) (Filter.EventuallyEq.of_eq (signal_ray S F J y u b)) (signal_hot S F J y b) (power J)

variable {C : Family G} [DecidableEq ι] {d m p : ℕ} (R : Census ι)
    (U : ι → Stamp.Reservation C (C.side (m+1) p) d)
    (hC : C.Makes) (hs : ∀ i, Bid.pop (C.localSection i))
local notation "St" => C.path.levels.clock.op m p

/-- Direct call from the independent normalized qlocal coefficient, including
each mixed marker set, to the corresponding coefficient of the FVA2 solenoid. -/
theorem normalized_solenoid (u : Pins G (C.side m p)) (L : Bulk.Chain C.path)
    (T : Forest (St).ratio) (t : (St).Choices) (s : R.Mode)
    {P : Oven (St).patch} {X : P.Form G} {Z : ChartRatio G}
    (H : P.Offers X (St).kernel) (h : Bid.Larger (G := G) St) (hu : ∀ i, ‖u i‖ ≤ X.Q)
    (hZ : LocalRatio Z) (v : (Descent.nil (top := C.side (m+1) p)).Tags)
    (b : Bool) {k r : ℕ} (hk : k ≤ r) :
    let J := modeLamp R U hC hs s
    let d₀ := Descent.nil (top := C.side (m+1) p)
    look b ((MSMatch.SourceTop.datum R m p U T t (axesP G _ u)).ordinaryCoefficient L r k s) =
      PowerSeries.coeff (power J + k) (Stack.read u (solenoid St T d₀ v t Z 1 h trivial
        (Stack.rise (stencilSignal St T J (modeSite R U s) b)))) := by
  dsimp only
  rw [normalized_coefficients R U hC hs u L T t s H h hu hZ hk]
  let J := modeLamp R U hC hs s
  let y := modeSite R U s
  have he := congrArg (PowerSeries.coeff k)
    (rank_solenoid St T J y Z hZ t h u X H hu v b)
  have hc : look b (Spool.rank J St T X Z u y k) = rankℝ J St T X Z u y b k := by
    cases b <;> rfl
  exact hc.trans (by simpa only [Stack.drop, PowerSeries.coeff_mk] using he)

end YM.Integration.FVA1Physical.Wilson


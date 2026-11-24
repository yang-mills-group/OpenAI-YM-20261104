import YM.WiderProfiles.Geometry
import YM.WiderProfiles.Fares
import YM.FVA2.Arrival.Runtime
/-!
# RawPrice (§F.2)
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.WiderProfiles
open Function Filter Set Finset Metric MeasureTheory Real Lattice
open MS MS.Local.Physical MS.Tide MS.Fleet MS.Orbit MS.Vista MS.Vane MS.Tone MS.Rake MS.Land MS.Dial
open PeakT (ordZ) -- fare commutes pointwise: PeakT.ν_norm
open XSpace.Cirrus Arrival
open scoped Topology ContDiff Classical

variable {G : Gauge} {n : ℕ} (μ : ℝ) (Y : XSpace.Initialize G)
    (u : Fin n → Label (Press.portDeck G))
    (A : Land.Prescription (Press.portDeck G))
    {O : Booked (Press.portDeck G)} (S : MS_Data G O)
local notation "g" => (Label.h ∘ u)

/-- Bond on the comap of the original `Front`; no filter or constants fixed sample-by-sample.
Includes both polynomial-in-θ bound assertions. Includes the empty mask and all orders. -/
theorem rawPrice (h : G.Simple) (hs : TaylorOKF S (Press.wickInput Y) A)
    (a : ℕ) (c D : ℝ) (hc : 0 < c) (hD : 1 ≤ D) (s : Finset (Fin n)) (k : ℕ) :
    Bond (along n a c D) (fun i : Domain n a c D => Schedule.theta (grab i.val)) mildG
      (fun i => Schedule.entries μ Y u A s k i.val)
      (fun i => MS.Dial.tour S u μ (Schedule.plot (familiar i.val)) s k) := by
  let T := trial n a c D μ; let l := along n a c D; let P := T.profile
  obtain ⟨V,hV,hp⟩ := finance μ n a c D hD
  have hm := trial_mesh μ n a c D hc hD
  obtain ⟨Z,X,hOrb,hPS,hX,hJ,hver⟩ := Tide.assemblyF_wide u T.off h
    (trial_clear μ n a c D) (trial_width μ n a c D) hV hm
    (trial_sparse μ n a c D hm) true hs
  -- Buy on the entire profile, for EVERY mask/order, before any singleton use
  have hpay (t : Finset (Fin n)) (j : ℕ) :
      Bond l P.θ mildG (fare g P Z t j) (fare g P (Fleet.toZ X) t j) :=
    fare_bond hp hJ (fun h => hver t h j)
  have hpay' := bond_ordZ hpay s k
  -- Identify *after* pricing
  refine hpay'.tee (Eventually.of_forall fun i => ?_) (Eventually.of_forall fun i => ?_)
  · rw [PeakT.ν_norm]
    -- §F's Top.identifies + Schedule.wholeAt (compare Arrival.Schedule.rate)
    let b := i.val; let K := μ-Schedule.theta b.F; let N := Schedule.psi b.F
    have hL := (Top.identifies Y u A (Schedule.bar b) (Schedule.σ b) (periodN N) K s
      ⟨N.val,two_mul (α:=ℕ) N.val⟩).1 (hPS i s)
    let d := Vane.charge (Label.h∘u) s
    change higher (Schedule.showR μ).profile d b * ordZ Z s k i = ((b.F.spacing:ℂ)^d)⁻¹*_
    rw [show ordZ Z s k i = _ from congr_fun hL k, Schedule.wholeAt Y u A s K
      (periodN N) _ _ b (Schedule.offset b), show periodN N = _ from Schedule.psi_back b.F,
      Schedule.meter μ u s i.property.sized]
  let y := Schedule.plot (familiar i.val)
  have hb : (fun t j => fare g P (Fleet.toZ X) t j i) = MS.Dial.book S u μ y := by
    have he := test_injective μ i hc
    have hx := Schedule.Dposition μ u S i.val i.property.sized he
    rw [show MS.Dial.book S u μ y = _ from hx.symm]
    exact funext fun t => funext fun j => fare_book u hX i rfl he
  unfold ordZ bury Dial.tour; rw [hb]
end YM.FVA2.WiderProfiles

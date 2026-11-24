import YM.Integration.WilsonCloseCaptureSignedPrice

/-! A single actual child of a Wilson block, with its own test pullback.
The same signed coordinate and full regular and forced transfer realize the
two grade-scaled bounds in both directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOffsetTransfer
open Function Filter Set Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof
open PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address RG05Readout.Native
open RG05Readout.Copper
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G)
local notation "C" => R.family

theorem original (simple : G.Simple) (paid : RG05Preconstruction.ReadoutPurchase R.b) (d : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ p N (live : m<N),
      let L := (C).S.block m
      let width := ld (C).path.levels m
      let α := Doors.rate L
      let M := (C).path.rep N p (m+1)
      ∃ K c β : ℝ, ∀ b : Bud (C) p m,
        let o := child (C) p m b
        let ρ := Native.pull (displacement (C) p m b) ((L.val:ℝ)⁻¹)
        ∃ (Y : Mark (C) d → Tape G ((C).side m p)) (z y : Mark (C) d → Palette (C) d),
          (∀ x : Palette (C) d,
            let a := size (amplify d (C) L x)
            let w := Slide x z
            size (amplify d (C) L x) ≤ width * size w ∧ size w ≤ width * a ∧
            Course (D:=R.doors N p m live) o ((Slide x (fun i => micro (C) i o M)).comp ρ)
              (Slide x Y) w (Slide x y) (margin d c K*a) (tollP d K c β*a)) ∧
          (∀ (F : Tape G ((C).side (m+1) p)) (x x' : Palette (C) d) (r : ℝ),
            Printed (C) d M o (kappa (C).path (m+1)) F x x' r →
            ∃ V l g, Course (D:=R.doors N p m live) o (F.comp ρ) V l g
              (margin d c K*size (amplify d (C) L x)+decay d L K c α*r)
              (tollP d K c β*size (amplify d (C) L x)+tollV d L K c α β*r) ∧
                size (l-Slide x z) ≤ decay d L K c α*r) := by
  obtain ⟨f,_,earned⟩ := (WilsonCloseCaptureSignedPrice.purchased R simple paid).currency
  filter_upwards [earned d] with m sale p N live
  let L := (C).S.block m
  let α := Doors.rate L
  obtain ⟨s,K,c,β,T,Q,plot,_,_,_,_,fee,hQ,clip,small,_⟩ := (sale p N live).author
  let t := beamCost d c K
  let γ := trim L + oldCost d K*α
  have hK := zero_le_one.trans plot.cursor.fits
  have hc := zero_le_one.trans plot.posp
  have hα : 0≤α := plot.a_pos
  have o0 : 0 ≤ oldCost d K := by unfold oldCost; positivity
  have m0 : 0 ≤ margin d c K := mul_nonneg (add_nonneg (sCpos hK) (aCpos hK)) hc
  have t0 : 0≤t := by change 0 ≤ margin d c K+1+c; linarith
  have g0 : 0≤γ := add_nonneg (lit L).le (mul_nonneg o0 hα)
  have a1 : α≤1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast L.property) (by norm_num)
  have g1 : γ≤1+oldCost d K := add_le_add (light L) (mul_le_of_le_one_right o0 a1)
  have invCost : 2*Q ≤ ld (C).path.levels m := by
    change 2*Q+t+(1+oldCost d K) ≤ ld _ _ at fee
    linarith
  have cost : t+γ ≤ ld (C).path.levels m := by
    change 2*Q+t+(1+oldCost d K) ≤ ld _ _ at fee
    linarith
  refine ⟨K,c,β,fun b => ?_⟩
  let o := child (C) p m b
  have parent := Bud.personal (C) p m b
  have pull := dist_box (C) p m b
  obtain ⟨Y,z,y,slot⟩ := slip R.makes live o parent plot pull
  let A := IsLinearMap.mk' (fun x => Slide x z) (slide_linear _)
  have bend : Contour (C) m d t c γ A := by
    apply sails_now (ξ:=margin d c K+1) plot
    · intro i
      exact (slot.age i).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (zero_le_one.trans (charge_one L i)))
    · intro i
      exact (slot.debits i).trans (le_add_of_nonneg_left (lit L).le)
  refine ⟨Y,z,y,?_,?_⟩
  · intro x a w
    obtain ⟨lo,hi⟩ := bend.earns t0 plot.posp g0 clip hQ small x
    exact ⟨lo.trans (mul_le_mul_of_nonneg_right invCost (size_ge _)),
      hi.trans (mul_le_mul_of_nonneg_right cost (size_ge _)),
      (all_sheet R.makes live o plot x slot).1⟩
  · intro F x x' r receipt
    exact stitch R.makes live o parent plot pull F x x' r receipt slot

end YM.Integration.WilsonThermometerOffsetTransfer
end

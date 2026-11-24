import YM.Integration.WilsonNeutralNativeFreeStep
import YM.Integration.WilsonWindowFormalAnnouncement
import YM.FormalBulk08.Elm.Forest
/-! Fixed-order fee for every coefficient of the actual nonbare primary
transition. The one original variable block house assigns the polynomial
before either the upper cutoff or the physical period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPrimaryWallet
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open scoped Topology BigOperators Matrix Classical

variable {G : Gauge} (R : Run G) {d D : ℕ} (wood : Primer.Families R.family)
variable (a : hue G) (depth : d < D) {U : ℕ → ℕ}
variable (grant : WilsonWindowFormalPurchase.Canonical U R.kit)

open Aster Dove Dove.Lab Primer

include grant in
theorem dated (simple:G.Simple)(o:Loc G 1)(E:ℕ):
    ∃ k : ℕ, ∀ x y : Letter (R.family.labels.level d), ∀ e ≤ E, ∃ c : ℝ, ∃ n : ℕ, 0 ≤ c ∧
      ∀ i : ℕ, k ≤ i → ∀ N : ℕ, i < N →
      |coeff e (Primer.fieldStep R.family a wood depth N i x y)| ≤
        c * Borough.ageZ (R.family.path.levels.clock.hatBeta i)^n:=by
  let J:=max (max (max 5 (d+3)) D) E
  have at5:5≤J:=by unfold J;omega
  have fit:d+3≤J:=by unfold J;omega
  have words:D≤J:=by unfold J;omega
  have order:E≤J:=by unfold J;omega
  let ann:=WilsonWindowFormalAnnouncement.on_run R grant
  obtain ⟨k,hk⟩:=Primer.always_opens (J:=J) R.family
  let H:=Primer.scripted R.family simple wood ann at5 hk
  let Z:=H.spare d D o J E fit depth words le_rfl order
  refine ⟨k,fun x y e he=>?_⟩
  obtain ⟨c,n,hc,hpay⟩:=(Elm.staccato Z (H.vac _ order) (chart_ok G) simple
    (ann.available.sections d) (ann.inputs d) a (by omega) x y e he).left
  refine ⟨c,n,hc,fun i hi N active=>?_⟩
  let site:=Primer.indexN R.family wood hi
  let u : Dove.Lab.transferPoint (Primer.ChamberU R.family wood k) := ⟨site,N,N,active,le_rfl⟩
  have cost: ((Dove.Lab.purseP (Primer.ChamberU R.family wood k)).day u) =
      Borough.ageZ (R.family.path.levels.clock.hatBeta i):=Borough.measure ann.power i
  exact (hpay u).trans_eq (by rw [cost])

end YM.Integration.WilsonNeutralPrimaryWallet
end

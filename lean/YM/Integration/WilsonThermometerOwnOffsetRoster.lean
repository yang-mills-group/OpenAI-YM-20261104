import YM.Integration.WilsonThermometerOwnOffsetGeometry
import YM.Integration.WilsonThermometerOwnOffsetInvoice

/-! The entire separated Wilson numerator for any finitely many normalized
own-offset coordinates on the original elected run, at a polynomial
reporting radius fixed independently of the UV cutoff and the period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOwnOffsetRoster
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetJoint
open WilsonThermometerOwnOffsetInvoice
open scoped Classical Topology
variable {G : Gauge} (R : Run G)
local notation "A" => R.alloy.B.a
local notation "β" => R.family.path.levels.clock.hatBeta

def filed {d p N k : ℕ} {I : Type} [Fintype I] [DecidableEq I] (hk:k≤N)
    (z : I → Site (R.family.side N p)) (V : I → Sight R.family d p)
    (r : I → Emblems R.family d) (t : ℕ) : Prop :=
  ∀ (names : Census I) (y : I → Palette R.family d), (∀ i,size (y i)≤1) →
    let f := fun j i=>(columns (k:=k) R z y V r j i).2.1
    let g := fun j i=>(columns (k:=k) R z y V r j i).2.2
    ∀ j (_:k≤j) (hn:j≤N), Integrable (density R z y r names hk hn) (prior G _) ∧
      (∀ i,(fun U=>(density R z y r names hk hn U).part (names.fire i))=
        Accent.manifest R.family.path p N f g j i) ∧
      Served (R.family.path.rep N p j) (f j) (Accent.tapes R.family.path p N g j)
        (density R z y r names hk hn) (origins R z j) (fun _=>radius R t k j) (topPitch R.family.path N j) 1

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (d : ℕ) :
    ∃ t ≥ d+3,∀ᶠ k : ℕ in atTop, ∀ p N (hk:k≤N) (I : Type) [Fintype I] [DecidableEq I]
      (z : I → Site (R.family.side N p)),
      (∀ i i':I,i≠i' → (R.family.path.levels.budget k).B^2 <
        separation (origins R z k i) (origins R z k i')) →
      ∃ (V : I → Sight R.family d p) (r : I → Emblems R.family d),
        (∀ i,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) k N p d
          (digits R N p (z i)) (V i) (r i)) ∧ filed R hk z V r t := by
  obtain ⟨u,up,test⟩ := Cap.cost (line (primaryLetter d)) (d+2)
  obtain ⟨t,dt,starts⟩ := Many.startPay (C:=R.family) simple d u up
  obtain ⟨k₀,starts⟩ := eventually_atTop.mp starts
  have grow := Many.beta_le' (C:=R.family) simple
  refine ⟨t,dt,?_⟩
  filter_upwards [eventually_ge_atTop k₀,WilsonThermometerOwnOffsetRadii.paid R simple (d+3) t,
    WilsonThermometerOffsetLedger.original R simple shop d,
    Many.theta_up (C:=R.family) (max 1 (2*u)) simple] with k late wallet lamp hot p N hk I _ _ z space
  choose V r H using fun i:I=>enroll R.makes lamp.1 hk (digits R N p (z i))
  refine ⟨V,r,H,?_⟩
  intro names y small
  have last := starts N (late.trans hk)
  have topRow (i:I) := top R (H i) (y i) (small i) up hk
    ⟨last.1,last.2 d le_rfl⟩ (wallet N hk)
  have prices (i:I) (j:ℕ) (hj:k≤j) (hn:j<N) :
      2*radius R t k (j+1)*charge R (r i) (y i) hj u ≤ 1 := by
    let X := span R k (j+1)
    let w := radius R t k (j+1)
    let b := β (j+1)
    have hkn := hj.trans j.le_succ
    have warm : max 1 (2*u) ≤ b := hot.trans (grow hkn)
    have b1 := (le_max_left 1 (2*u)).trans warm
    have fee : 2*u ≤ b^t := ((le_max_right 1 _).trans warm).trans
      (by simpa only [pow_one] using (pow_le_pow_right₀ b1 (show 1≤t by omega)))
    have smallcost := adjacent R (H i) (y i) (small i) up.le hj hn
    have wpos := (radius_pos R t k (j+1) hkn).le
    have axes := (span_pos R k (j+1)).le
    calc 2*w*charge R (r i) (y i) hj u ≤ 2*w*(X^(d+3)*u) :=
           mul_le_mul_of_nonneg_left smallcost (by positivity : 0 ≤ 2*w)
         _ = w*X^(d+3)*(2*u) := by ring
         _ ≤ w*X^(d+3)*b^t := mul_le_mul_of_nonneg_left fee (mul_nonneg wpos (pow_nonneg axes _))
         _ ≤ 1 := wallet (j+1) hkn
  exact issued R z y V r H lamp.1 simple hk (fun j _=>radius R t k j) test names
    (WilsonThermometerOwnOffsetGeometry.admitted R simple z t names space) topRow prices

end YM.Integration.WilsonThermometerOwnOffsetRoster
end

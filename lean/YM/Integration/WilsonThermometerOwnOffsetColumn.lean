import YM.Integration.WilsonThermometerOwnOffsetField
import YM.Integration.WilsonThermometerOffsetLedger

/-! The numerical source, its original once-divided forced wallet and the
same microscopic field at all dates of its own fine-site trajectory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOwnOffsetColumn
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.Local
open PhysicalNext.Repeat.Legato MergeProof Accent Trace.Physical
open WilsonThermometerOffsetTrajectory WilsonThermometerOwnOffsetField
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G)

theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b)
    (d : ℕ) (ε : ℝ) (hε : 0<ε) : ∀ᶠ m : ℕ in atTop,
    ∀ N p (live : m≤N) (z : Site (R.family.side N p)), ∃ r : Emblems R.family d,
    ∀ y : Palette R.family d,
      let t := primaryLetter d
      let x := (R.family.factory d N p).terminal (finer r live y t)
      ∀ j (away : m≤j) (reached : j≤N),
        let height := Real.exp (ε*(R.family.S.scale j-R.family.S.scale m))*size y
        let P := R.family.path.rep N p j
        let o := (R.family.S.toDepth reached p).parent z
        size (finer r away y) ≤ height ∧
        ∃ X Q : Coefficient (R.family.labels.level d) (R.family.side j p),
          Germ.projection (R.family.labels.level d) R.family.params P.p.threshold 0 X=
            finer r away y t ∧
          Q.Format o R.family.params P ∧ Q.remBound o P (kappa R.family.path j)
            ((1+Real.log (2+Real.log (R.alloy.B.a.clock.hatBeta j)))*height) ∧
          Q.density o (R.family.localSection d) P=
            X.density 0 (R.family.localSection d) P ∘ Lattice.pull 1 o ∧
          Q.density o (R.family.localSection d) P=
            dyes R.family j N p reached ((R.family.S.a j:ℂ)^d • R.family.O N p x z) := by
  obtain ⟨b,paid⟩ := eventually_atTop.mp (WilsonThermometerOffsetLedger.original R simple shop d)
  filter_upwards [eventually_ge_atTop b,string_paid (C:=R.family) hε] with m active cost N p live z
  obtain ⟨V,r,H⟩ := enroll R.makes (paid m active).1 live (WilsonThermometerOffsetResidue.digits R N p z)
  refine ⟨r,?_⟩
  intro y t x j away reached height P o
  let v := finer r away y
  have hv : size v≤height := (H.inverse le_rfl away reached y).trans
    (mul_le_mul_of_nonneg_right (cost j away) (size_ge _))
  have starts (e : ℕ) (he : e≤d) := ((paid m active).1.post e he).trans live
  obtain ⟨X,Q,coordinate,_,_,legal,invoice,motion,hQ⟩ :=
    actual R N p j z H away reached starts v
  have cap := (paid j (active.trans away)).2
  have billed := mul_le_mul cap.2 hv (size_ge _) (zero_le_one.trans (cap.1.trans cap.2))
  have successive : finer r reached v=finer r live y := by
    rw [Many.sumwalk r away reached]; rfl
  have raw : (R.family.factory d N p).terminal (finer r reached v t)=x :=
    congrArg (fun w : Palette R.family d => (R.family.factory d N p).terminal (w t)) successive
  refine ⟨hv,X,Q,coordinate,legal,rem_mono invoice billed,motion,?_⟩
  exact hQ.trans (congrArg (fun w : R.family.label d => dyes R.family j N p reached
    ((R.family.S.a j:ℂ)^d • R.family.O N p w z)) raw)

end YM.Integration.WilsonThermometerOwnOffsetColumn
end

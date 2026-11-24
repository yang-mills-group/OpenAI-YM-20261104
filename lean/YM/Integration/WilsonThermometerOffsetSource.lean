import YM.Integration.WilsonThermometerOffsetCylinder

/-! A single stored physical coefficient for the actual displaced and
inverse-calibrated bare field, with its measured germ and charged old gas. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOffsetSource
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local
open PhysicalNext.Repeat.Legato MergeProof Accent Trace.Physical
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (N p : ℕ) {m base d : ℕ}
theorem original {D : Rail R.family} {B : ℕ → ℕ → ℝ}
    {V : Sight R.family d p} {r : Emblems R.family d} {sites : ∀i,Bud R.family p i}
    (H : Enrolled R.makes D B base N p d sites V r) (entered : base ≤ m) (live : m ≤ N)
    (starts : ∀e≤d, R.family.ref e ≤ N) (t i : Letter d) (x : R.family.label (kept t)) :
    let P := R.family.path.rep N p m
    let y := point r (chunk t ((R.family.factory (kept t) N p).terminal.symm x)) N m
    let here := address R N p m sites (N-m) (by omega)
    let c := units R m d (N-m) * (readJ t 0 (test R p m sites (N-m) (line i))*
      (R.family.S.a N:ℂ)^(kept t))
    ∃ X : Coefficient (R.family.labels.level (kept i)) (R.family.side m p),
      X.Format 0 R.family.params P ∧
      X.remBound 0 P (kappa R.family.path m) (B d m*size y) ∧
      Germ.projection (R.family.labels.level (kept i)) R.family.params P.p.threshold 0 X=y i ∧
      X.density 0 (R.family.localSection (kept i)) P =
        dyes R.family m N p live (c • R.family.O N p x here) ∧
      invoice X 0 (R.family.localSection (kept i)) P = V m y (line i) := by
  intro P y here c
  obtain ⟨z,hPrinted⟩ := (H.legal m entered live).capacity0 y
  rcases hPrinted with @⟨X,F,fee,b,tail,cert,wallet,assembled,hx,hy,financed⟩
  have bill : fee i ≤ B d m*size y := ((Finset.single_le_sum
    (fun j _ => rem_nonneg (wallet j)) (Finset.mem_univ i)).trans
    (le_add_of_nonneg_right tail.nonneg)).trans financed
  have filed : V m y (line i) = invoice (X i) 0 (R.family.localSection (kept i)) P := by
    exact (congrArg (fun S : Tape G (R.family.side m p) => S (line i)) assembled.symm).trans
      (together_line X F tail i)
  refine ⟨X i,cert i,rem_mono (wallet i) bill,(congrFun hy i).symm,?_,filed.symm⟩
  have physical := congrFun (WilsonThermometerOffsetPhysical.original R N p H entered live starts t x) (line i)
  change pulseOut (V m y) (line i) = _ at physical
  have single := WilsonThermometerOffsetCylinder.bare R N p m sites
    (show m+(N-m)≤N by omega) t x (line i)
  rw [single] at physical
  exact (congrArg Prod.fst filed.symm).trans physical

end YM.Integration.WilsonThermometerOffsetSource
end

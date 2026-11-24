import YM.Integration.WilsonGraphStandaloneCorrelation

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace YM.Integration.WilsonGraphPublicFiledCoefficient

open YangMills YangMills.Matching
open YM.Integration.WilsonGraphStandaloneCorrelation

variable {g : YangMills.GaugeGroup} {n k : ℕ}

theorem inputCap (S : Conversion (maxwellReference g)) (a : Fin n → Label g)
    (ν : Fin n → Fin (k + 1)) : cutoff (S.inputs a ν) = cutoff a := rfl

theorem rawInput (S : Conversion (maxwellReference g)) (a : Fin n → Label g)
    (ν : Fin n → Fin (k + 1)) (x : YangMills.Points n) (j : ℕ) :
    bare g n j (S.inputs a ν) x =
      YM.MS.Graphical.separatedGraphSum (YM.FVA2.Teller.logNu 1) g.core (cutoff a) x j
        (fun i => YM.XSpace.Normalize.up (within a i)
          ((S.Z (a i).1 (ν i).val) (a i).2)) := rfl

/-- The filed coupling and the filed frame are applied in each submitted grade. -/
def nativeRead (f : ℕ → ℝ)
    (columns : (d r : ℕ) → (maxwellReference g).sector d → (maxwellReference g).sector d)
    (k : ℕ) (a : Fin n → Label g) (x : YangMills.Points n) : ℂ :=
  ∑ ν : Fin n → Fin (k + 1), ∑ j : Fin (k + 1),
    if (∑ i, (ν i).val) ≤ k then
      (couplingPower f j.val (k - ∑ i, (ν i).val) : ℂ) *
        YM.MS.Graphical.separatedGraphSum (YM.FVA2.Teller.logNu 1) g.core (cutoff a) x j.val
          (fun i => YM.XSpace.Normalize.up (within a i)
            (columns (a i).1 (ν i).val (a i).2))
    else 0

theorem displayed (S : Conversion (maxwellReference g)) (k : ℕ) (a : Fin n → Label g)
    (x : YangMills.Points n) :
    converted S k a x = nativeRead S.f (fun d r u => S.Z d r u) k a x := by
  obtain ⟨M, read⟩ := represented g
  rw [← converted_read S M read k a x]
  simp only [Conversion.correlation, read, nativeRead, rawInput]

theorem filed (S : Conversion (maxwellReference g)) (f : ℕ → ℝ)
    (columns : (d r : ℕ) → (maxwellReference g).sector d → (maxwellReference g).sector d)
    (clock : ∀ r, S.f r = f r)
    (fields : ∀ d r u, S.Z d r u = columns d r u)
    (k : ℕ) (a : Fin n → Label g) (x : YangMills.Points n) :
    converted S k a x = nativeRead f columns k a x := by
  rw [displayed]
  have hf : S.f = f := funext clock
  have hZ : (fun d r u => S.Z d r u) = columns := by
    funext d r u
    exact fields d r u
  rw [hf, hZ]

end YM.Integration.WilsonGraphPublicFiledCoefficient
end


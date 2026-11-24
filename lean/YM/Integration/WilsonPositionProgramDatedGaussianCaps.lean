import YM.Integration.WilsonPositionProgramDatedDrivers

/-! The covariance, all finite powers of the measured affine shift and the true source radii. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramDatedGaussianCaps
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Order
open PhysicalNext.Repeat.Legato
open WilsonPositionProgramFiniteRootEnvelope WilsonPositionProgramDatedDrivers
open scoped BigOperators Classical
variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V]{R:Census V}{r:ℕ}

def variance (T:Run G)(j:ℕ):ℝ:= Classical.choose (Classical.choose_spec (WilsonPositionProgramUniformGaussianCalendar.original T j))

theorem paid (T:Run G)(N j per:ℕ)(live:j<N):
    let S:=T.family.path.levels.clock.op j per
    let K:=(RunFormalChain.fromRun T).step N j per live
    ∀tag:S.Choices,∀i,(K.covariance (RegulatorIR.Halo.bios S) tag) i i≤variance T j := by
  have booked:=Classical.choose_spec (Classical.choose_spec (WilsonPositionProgramUniformGaussianCalendar.original T j))
  intro S K tag i
  exact (le_abs_self _).trans (((booked.2.2 N per live).2.1 tag i i))

def steps (grades:V→ℕ)(v h:ℕ)(i:Hot (Board R r)):ℕ:=length grades i*max v h

def power (R:Census V)(grades:V→ℕ)(r v h:ℕ):ℕ:=degree (steps (R:=R) (r:=r) grades v h)

def amount {α:Type}[Fintype α](cash:α→ℝ)(H:ℝ)(J:ℕ):ℝ:=budget cash*(max 1 H)^J

theorem nonneg {α:Type}[Fintype α](cash:α→ℝ)(H:ℝ)(J:ℕ):0≤amount cash H J:=
  mul_nonneg (WilsonPositionProgramFiniteRootEnvelope.nonneg _) (by positivity)

theorem funded (grades:V→ℕ)(v h t:ℕ)(ht:t≤ max v h)(f:Hot (Board R r)→ℝ)(i:Hot (Board R r))(c:0≤f i)
    {a δ H y z:ℝ}(hd:0≤δ)(hy:1≤y)(hz:1≤z)(moved:y≤H*z)
    (afforded:a≤δ*f i*y^(length grades i*t)):
    a ≤ (δ*amount f H (power R grades r v h))*z^(power R grades r v h):=by
  apply entered f (steps grades v h) i hd (zero_le_one.trans hy) hz moved
  exact afforded.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy (Nat.mul_le_mul_left _ ht)) (mul_nonneg hd c))

end YM.Integration.WilsonPositionProgramDatedGaussianCaps
end

import YM.FullVolume.Stage.Crests

/-! The existing Campaign already retains the literal initial PathData.
This receipt reads that field on the same Run; it adds no construction,
price, or estimate and does not identify a different representative. -/
set_option autoImplicit false

namespace YM.Integration.ActualRunStartupIdentity

/-- Exact initial PathData of the Kin stored in this Campaign's Run. -/
theorem initial_path {G : Gauge}
    (R : PhysicalNext.Repeat.Legato.Run G)
    (T : PhysicalNext.Repeat.Legato.Campaign R) (N : ℕ) :
    R.alloy.B.kin.path N N =
      WilsonStartup.Design.top G (R.alloy.B.a.params N).clip :=
  T.gains.Lead N

end YM.Integration.ActualRunStartupIdentity

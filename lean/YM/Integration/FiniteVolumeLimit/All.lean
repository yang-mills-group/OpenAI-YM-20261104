import YM.FVA2.CommonCalendar
import YM.FVA2.TransportB
import YM.Integration.PhysicalControl.All
import YM.FVA2.Prescription
import YM.FVA2.Cone
import YM.FVA2.Substitute
import YM.Integration.FiniteVolumeLimit.GaussianTable

/-!
Independent verification entry point. Co-importing these packages checks Lean
compatibility; it does not identify the qlocal coefficients with the FVA2
prescription. The separate GaussianTable lemmas record only the proved RG02
finite-truncation interface. See the accompanying semantic acceptance report.
-/
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true
set_option pp.funBinderTypes true
set_option pp.maxSteps 1000000

#check @YM.FVA2.Atoll.Main.joint_M
#check @YM.FVA2.Atoll.Main.install
#check @YM.FVA2.Both.Passage.CapReady.every
#check @YM.FVA2.RadScale.Era.proves
#check @YM.FVA2.RadScale.Era.chosen
#check @YM.FVA2.Plot.clock_eq
#check @YM.FVA2.Sail.finite_to_X_space_supplier
#check @YM.MS.RadL.exact_optics
#check @YM.MS.RadL.unique
#check @YM.RegulatorIR.FVAAlt2.PhysicalControlEstimates.sameRunEveryPhase
#check @YM.RegulatorIR.FVAAlt2.PhysicalControlEstimates.originalExistence
#check @YM.EveryPhase.all_characters
#check @YM.MS.Tide.remove
#check @YM.MS.Dial.LPT_to_MS
#check @YM.FiniteVolumeGaussianTables.numerator_table
#check @YM.FiniteVolumeGaussianTables.normalized_table
#check @YM.FiniteVolumeGaussianTables.connected_table

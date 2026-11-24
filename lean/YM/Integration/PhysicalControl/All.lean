import YM.FVAAlt2.Moving.Supplier
import YM.FVAAlt2.Sound.From
import YM.FVAAlt2.Pipeline.Urban
import YM.FVAAlt2.Moving.Born
import YM.Integration.PhysicalControl.SameRun

set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true
set_option pp.funBinderTypes true
set_option pp.maxSteps 1000000

#check @YM.RegulatorIR.FVAAlt2.Moving.Supplier.procurement
#check @YM.RegulatorIR.FVAAlt2.Moving.Supplier.supply_H
#check @YM.RegulatorIR.FVAAlt2.Moving.Supplier.Funding
#check @YM.RegulatorIR.FVAAlt2.Moving.Supplier.CorrelationMatch
#check @YM.RegulatorIR.FVAAlt2.Sound.From.fromPeriod
#check @YM.RegulatorIR.FVAAlt2.Pipeline.See.Urban.actualRun
#check @YM.RegulatorIR.FVAAlt2.Moving.ProgramT.established
#check @YM.RegulatorIR.FVAAlt2.PhysicalControlEstimates.sameRunEveryPhase
#check @YM.RegulatorIR.FVAAlt2.PhysicalControlEstimates.originalExistence
#check @YM.Integration.LocalFormal.runCoefficients
#check @YM.MS.Tide.remove
#check @YM.MS.Dial.LPT_to_MS
#check @YM.EveryPhase.all_characters

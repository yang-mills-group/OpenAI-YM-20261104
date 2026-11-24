import YM.MSbar.Pulse.Keg

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.RawBank
open PowerSeries
open scoped BigOperators

def cash (p:ℕ) (g:ℝ) (A:PowerSeries ℂ):ℂ:=∑e∈Finset.range (p+1),(g:ℂ)^e*coeff e A

end YM.Integration.WilsonPhysicalMarkedDefect.RawBank

import MSFormalSeries
import MSScalarInverse
import FormalConversion
import MSReference
import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields
import YangMills.WilsonProof.NativeSupport.MSGradeProjection

/-! # Formal field series on the free polynomial sectors

Composition is ordered from right to left on input fields. Each coefficient
uses only the coefficients through the specified order. A normalized constant
term gives the two-sided inverse. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.MSbar.Series

open scoped BigOperators
open PowerSeries

variable {g : GaugeGroup} (B : Maxwell.Reference g)










attribute [local irreducible] cauchy inverseFrame gradeFrame PowerSeries.invOfUnit





end YangMills.MSbar.Series

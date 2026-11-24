import YM.Integration.ActualStartupPacketInput
import YM.Integration.QLocalGradedVacuumLayers
import YM.Integration.QLocalVacuumRowRegularity

/-!
The actual original startup album inhabits the separate graded vacuum class.
Its original row functions are regular on their original supports, including
all zero padding. This is data and regularity only: no old VacuumPackets
receipt, canonical supBounds price, Invoice, admission purchase or new
qlocal grant is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualStartupGradedInput

open Lattice Wilson RG
open WilsonStartup WilsonStartup.Start WilsonStartup.IterationFour
open ActualStartupVacuumPackets ActualStartupPacketInput

/-- The exact original album, atoms, powers, roots and budgets supply the
graded class without a separate representation or rank hypothesis. -/
def gradedAlbum (G : Gauge) (n : Side) (p : BudgetPoint) (S : Stage)
    (r : ℕ) (width : ℝ) (hw : 0 ≤ width) :
    FullQLocal.GradedVacuumLayers (album G n p S r) p r (r + 2) width
      (albumCost G p S r width) where
  packets := albumPackets G n p S r width hw
  orders := grades G n p S r
  leading_rank a ha := (album_rank_power p S r a ha).le

/-- The same constructed packet supplies regularity of every complete
original row function, without a numerical derivative-bound premise. -/
theorem original_regular (G : Gauge) (n : Side) (p : BudgetPoint) (S : Stage)
    (r : ℕ) (width : ℝ) (hw : 0 ≤ width)
    (a : YM.IterationFour.Vacuum.Piece G n) (ha : a ∈ album G n p S r)
    (i : ℕ) :
    p.Regular (a.packet.labels i).support (a.packet.action i) :=
  (gradedAlbum G n p S r width hw).packets.regular a ha i

end YM.Integration.ActualStartupGradedInput
end

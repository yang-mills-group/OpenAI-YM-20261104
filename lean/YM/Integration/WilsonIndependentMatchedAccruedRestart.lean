import YM.Integration.WilsonIndependentMatchedBufferedVacuum
import YM.Integration.WilsonIndependentMatchedCoverProfile
import YM.Integration.WilsonPositionProgramTrialAccrued

/-! Two original vacuum tops with the same born marks and the complete reporting
coordinates measured from the first top. The first marked input is the literal
paid K stencil with its separately issued stable residual subtracted. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedAccruedRestart
open Function Finset Matrix Lattice Wilson RG Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonIndependentMatchedBufferedVacuum (Receipt)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonPositionProgramTrialAccrued (home)
open WilsonMarkedIndependentNormalizedElection (normalized)
open WilsonPositionProgramNormalizedMaster (fee)
open scoped BigOperators Classical
variable {G:Gauge}{a k t e u:ℕ}{H:Hol G}{Q:Fin (a+1)→SealR G}
    {w:∀s,Rails (Q s).h k t e}{P V A W:Credit}

abbrev Courts:=(s:Fin (a+1))→CutsP H (Q s).ans (Q s).path (w s) P V A W

def vector (X:Courts (H:=H) (w:=w) (P:=P) (V:=V) (A:=A) (W:=W)):Herit Q:=
  fun s=>home (Q s) (X s)

/-- Actual non-null part of each upper K word, on its own older N vacuum,
buffer the joint product and both original cuts. -/
def fitted (L:Levels G)(O:ChartRatio G)(X:Courts (H:=H) (w:=w) (P:=P) (V:=V) (A:=A) (W:=W))
    (F:Wilt Q)(m K N stop:ℕ)(y:ℝ)(o:CellR):Era G ℝ:=
  cruises L O N (capP Q) m stop (cruises L O N (capP Q) K m
    (MassP G ℝ a (fun s=>word ((X s).pt-(X s).springP (X s).i) (F s) (paceT L.S m K) y o (Q s).h)))

theorem first (L:Levels G)(O:ChartRatio G)(X:Courts (H:=H) (w:=w) (P:=P) (V:=V) (A:=A) (W:=W))
    (F:Wilt Q)(m K N stop:ℕ)(y:ℝ)(o:CellR)
    (levels:∀s,(X s).ax=L)(charts:∀s,(X s).tx=O)(bottom:∀s,(X s).m=m)
    (birth:∀s,(X s).ceilC=K)(prior:∀s,(X s).N=N):
    fitted L O X F m K N stop y o=WilsonIndependentMatchedBufferedVacuum.stopped L O Q F (vector X) m K N stop y o:=by
  unfold fitted WilsonIndependentMatchedBufferedVacuum.stopped WilsonIndependentMatchedRestartVacuum.reading
  apply congrArg (cruises L O N (capP Q) m stop)
  apply congrArg (cruises L O N (capP Q) K m)
  apply congrArg (MassP G ℝ a)
  funext s
  have paid:=WilsonPositionProgramTrialAccrued.source (Q s) (X s)
  rw [levels s,charts s,prior s,bottom s,birth s] at paid
  change word _ _ _ _ _ _=word (centralL L O N m K (Q s)
    (PermuteLens L O (Q s) N m (home (Q s) (X s)))) _ _ _ _ _
  rw [sub_eq_of_eq_add paid]

theorem original {L:Levels G}{O:ChartRatio G}{clock:ℕ→ℝ}{j:ℕ}{C wallet:Credit}
    (paid:Receipt Q L O clock j e u C wallet)
    (X:Courts (H:=H) (w:=w) (P:=P) (V:=V) (A:=A) (W:=W))
    (F:Wilt Q)(m K upper N N' stop:ℕ)(B:Fin (a+1)→ℝ)(Z y:ℝ)(o:CellR)
    (levels:∀s,(X s).ax=L)(charts:∀s,(X s).tx=O)(bottom:∀s,(X s).m=m)
    (birth:∀s,(X s).ceilC=K)(prior:∀s,(X s).N=N)
    (awake:j ≤ stop)(older:stop ≤ m)(base:m ≤ K)(buffer:K ≤ upper)(fine:upper ≤ N)(other:upper ≤ N')
    (room:Compar L.S clock stop m ≤ Z)(shape:Bough Q F y Z B):
    Fringed (capP Q) e u 1 (C.buy Z*∏s,B s*(wallet.buy (clock m)*fee (vector X) e s))
      (trailC L.S m upper) (fitted L O X F m K N stop y o)
      (WilsonIndependentMatchedBufferedVacuum.stopped L O Q F (vector X) m K N' stop y o):=by
  rw [first L O X F m K N stop y o levels charts bottom birth prior]
  exact paid _ _ _ _ _ _ _ _ _ _ _ _ awake older base buffer fine other room shape

end YM.Integration.WilsonIndependentMatchedAccruedRestart

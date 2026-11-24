import YM.XSpace.Regulated
import YangMills.WilsonProof.NativeSupport.YM.FVA2.Press.Deck
/-!
# Instantiate the dictionary of top stencils, genuine projections to the chosen covariance labels

Raw un-compensated columns (all real). Single choice of nonlinear orientation-compatible lifts
for the whole dictionary and `Y : Initialize`. No repair frame/hypotheses about its cost. `LitBook`
is what lets us apply `YM.MS.Tide.remove` / `Dial.LPT_to_MS` to THIS prescription.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Press
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Source.Drops Bid Work XSpace
open MS MS.Koszul MS.Cylinder Lab MS.Native MS.Native.Sew MS.Book MS.Local.Physical MS.Rake MS.Lifting MS.Theater MS.Menus
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge} (A:XSpace.Initialize G)
local notation "B" => portDeck G
-- raw (works with literal endpoints); for exact scheme conversion, add W self terms explicitly later

def program (A:XSpace.Initialize G) : LitBook (portDeck G) where
   stamp v u i:= dot (A.surveys v) (Theater.film (portDeck G) (h:=v) i)
   levels v u i:= (awake (A.surveys v) (r:=u) (Theater.filmW (portDeck G) i) (le_refl v)).1
   fit v u i:= by rw [← lamp_here]; exact (awake (A.surveys v) (r:=u) (Theater.filmW (portDeck G) i) (le_refl v)).2

def dictionary : Change.Dictionary (program A) where
 stamp v u i:= page (A.surveys v) _ ((Theater.cinema _).mp (Theater.filmW (portDeck G) (h:=v) (r:=u) i)).2.1
lemma place_eq (n:Side){w r:ℕ}(i:(B).BIndex w r)(p:Cover)(x:Wilson.Config G n): ((dictionary A).stamp w r i).placed n p x=( (wheel (A.surveys w) (On.lifting ( Maxwell.reduceEq (Theater.film B i (h:=w))))) (expandAt (wrap n p) x)).re:= by
    rw [← film_eq]; unfold Change.Stencil.placed; rw [← wrapped]; rfl
end YM.FVA2.Press

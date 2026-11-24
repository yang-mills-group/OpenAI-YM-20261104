import YM.FVAAlt2.First.Rental
import YM.FVAAlt2.First.Wet
import YM.FVAAlt2.Home.PoseVariant
/-!
# The bridge.Dual.Untilied now.PP ℝ. Explicit single-stage period comparison.
 Quantum Wick-regularized columns enters.End graph payment, then translate
 while keeping extra-budget team. S-definition corresponds to Full marks.
 Location-independent W_D.Wrong coefficients under other PP schemes not used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Pairing
open Function Finset Filter Topology Lattice Labels Source
open MS MS.Koszul MS.Native MS.Landau MS.Menus MS.Book MS.Cylinder MS.Cylinder.Taylor MS.Tone MS.Landau.Detect MS.Plane MS.Theater
open MS.Lifting MS.Local.Physical MS.Book.Convolve MS.Native.Studio MS.Native.Paint MS.Native.Wilsonian
open MS.Puff MS.Puff.Mom MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog MS.Dial MS.Tide MS.Swirl MS.Swirl.Near MS.Fleet
open PowerSeries (C coeff)
open Pert PertExtension PertExtension.Orb PertExtension.Orb.SlotEvaluation PertExtension.LatticePT Precision Billing SchemeRG11.Sway SchemeRG11.Sway.Lam SchemeRG11.Atoll SchemeRG11.Pile Lobby
open scoped Topology BigOperators ContDiff PowerSeries Classical
variable {W:Type}[LinearOrder W][Fintype W]{G:Gauge}{n:Side}{B:Deck G}
abbrev Tickets (v:W→Rake.Label B)(i:W):= Σ j: Glyph B (v i).h, Ban (owner j)
variable (a: Cover)(t:W→ Cover)(x:W→ Site n) {D:ChartRatio G}(h:LocalRatio D)(HN:Pert.Orb.Admissible n)(V:MS.Land.Prescription B)(y:ℝ) (v:W→ Rake.Label B)
local notation "ι'"=> Tickets v
local notation "Z"=> ExtraBook B
local notation "aP"=> ApplyMPl Z (Stripped V.team) V v
local notation "TX"=> fun i:W=> wrap n (a+t i)
local notation "CZ"=>PowerSeries ℂ
abbrev tilt (i:W)(k:Tickets v i):= bore v V y i k.1
abbrev testT (i:W)(k:Tickets v i):= Pairing.owes (o:=x i) (owner k.1) k.2.val
def IV (i:W)(k:Tickets v i) := k.2.val
def WN (i:W)(k:Tickets v i) := Pairing.light (owner k.1) k.2.val
def df (i:W) : Tickets v i:= ⟨MS.Land.read (v i).item,0⟩
-- proof after Lobby.permit
open Book.Program Ends
lemma permit (i:W) : aP i y= ∑ j:Tickets v i, scalS (tilt V y v i j) (substitute (Program.shift V.team y) (levels (IV v i j) (WN v i j))):=by
 let pf : ℝ→_:= Program.shift V.team; let f(j:Glyph B (v i).h):= substitute (pf y) ((Z).menu j.size j.grade j.2.2)
 rw [show aP i y= ∑ j:χ v i,scalS (bore v V y i j) (f j) from ?hall ]; swap
 · funext k; change Menus.rentPl _ (Stripped V.team) _ _ _= _; unfold Menus.rentPl; rw [Finset.sum_apply]; refine Finset.sum_congr rfl fun w _=>?_ ; unfold f pf scalS; rw [paired]; simp_rw [ Glyph.preamblePl,bore,unpack,strip_wobble,PowerSeries.coeff_mk]; rfl
 conv_rhs=> rw [Fintype.sum_sigma];
 refine sum_congr rfl fun j _=>?_ ; unfold f; rw [show (Z).menu j.size j.grade j.2.2=∑ k:Ban (owner j), levels (IV v i ⟨j,k⟩) (WN v i ⟨j,k⟩) from (?_ : total j.grade (price j.2.2)=_), map_sum ]; unfold scalS; rw [map_sum]
 unfold total; exact (Fin.sum_univ_eq_sum_range (fun k:ℕ=>cereal k (price j.2.2)) _).symm

def rawL (x:W→Site n)(v:W→Rake.Label B):= Lentry (∏ i:W, Lsup (x i) 1 (dream 1 (realCast (enterL (v i)))))
def postP (x:W→Site n):CZ:= ∑ j:(i:W)→ Glyph B (v i).h,(∏ i:W, bore v V y i (j i)) * redo V.team y (rawL x (fun i=> owner (j i)))
def readyP (x:W→Site n)(V:MS.Land.Prescription B)(D:ChartRatio G)(y:ℝ)(v:W→Rake.Label B): CZ:= ∑ j:(i:W)→ Tickets v i,(∏ i:W, tilt V y v i (j i)) * redo V.team y (tile D x (fun i=>owner (j i).1) (fun i=> (j i).2))
-- shape regroup
variable {Q T:Type} [Fintype Q][DecidableEq Q] [Fintype T][DecidableEq T]
variable (A:Module.Basis Q ℝ (Land G n))(P:Module.Basis T ℝ (ScalarGhost G n))
include A P h HN in
lemma earnP : readyP x V D y v= postP V y v x:=by
 let e: (Σ g:(i:W)→ Glyph B (v i).h,(i:W)→ Ban (owner (g i))) ≃ ((i:W)→ Tickets v i):= {
   toFun p i:=⟨p.1 i,p.2 i⟩
   invFun q:=⟨fun i=>(q i).1,fun i=>(q i).2⟩
   left_inv _:=rfl
   right_inv _:=rfl }
 unfold readyP postP; simp_rw [rawL,rawTiles A P HN h, map_sum,Finset.mul_sum]; rw [← Equiv.sum_comp e, Fintype.sum_sigma]; rfl
include A P h HN
lemma ent_p: PhysicalSum G V.team y n true (univ:Finset W) t a aP ( Ends.unpack (postP V y v TX) ):= by
 let s:= univ (α:=W); rw [ ←earnP (h:=h) ( x:=TX ) HN V y v A P ]; -- include signature
 suffices he:readyP TX V D y v=treeReg s V.team y (IV v) (testT TX v) (tilt V y v) (df v) D by
    rw [he]; refine PayReg h A P aP s V.team y t a (WN v) (IV v) (testT TX v) _ (fun i j=>ownsAt (TX i) (owner j.1) j.2.val ) (df v) (permit V y v) (fun i k=> (billRentPl Z (Stripped V.team) (V.fees (v i).h (v i).item) |>.actual k y).symm ) (fun i k=> ⟨_, Menus.rentLimitPl Z (Stripped V.team) (V.fees _ _) y k⟩) HN
 let E: ((i: (s:Type _))→ ι' i.1)≃((i:W)→ ι' i):= {
   toFun:= Billing.pad s (df v)
   invFun:=fun f i=> f i.1
   left_inv:=fun i=>funext (fun j=> (dif_pos j.property : Billing.pad s (df v) i j.val=i j))
   right_inv:=fun u=>funext fun i=> dif_pos (by simp [s]) }
 unfold readyP treeReg; symm; apply Fintype.sum_equiv E; intro u; refine congr_arg₂ (·*·) rfl ?_; unfold κpoint redo; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; apply congr_arg PowerSeries.mk; exact congr_arg (substitute _) (funext (fun i=>by rw [unpack,Pairing.tile,Lobby.ΦbaseT,PowerSeries.coeff_mk]; rfl))
end YM.FVAAlt2.Pairing

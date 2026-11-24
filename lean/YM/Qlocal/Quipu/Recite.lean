import YM.Qlocal.Quipu.Riser
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Eluder
open AllOrder AllOrder.Ink Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Turbin Sonnet Marker Kinetic Primitives.GCC.Anchor
variable {ι α :Type}[Fintype α][DecidableEq α][Fintype ι] {G:Gauge} {n:Side} {k N :ℕ} {a b r :ℝ}{R:Marker.Census α}
local notation "J"=> ι⊕α
local notation "E"=> rule J n
local notation "A"=> rule ι n
local notation "B"=> rule α n
local notation "Λ"=> Leaf n J
-- extend wall across both legs. χ preserves quiet.𝒮
namespace Dais
open Tender Turbin Lasso
-- L gauge.C.State Γ. manifest.
open Exterior (axisEquiv TypeFace)
open Zora Zora.Noon
local notation "T"=> Coarse G ⊕α
section books
variable (p:Lattice.Order) (x:rule (Coarse G) n)(o:α→Site n){s:Senses R}{w:Slip (Point ((Coarse G)⊕α))}(Y: Noon G N) (W:Config G n)
local notation "κ"=> (List.length (coin w))
local notation "i0"=> Fin (List.length (coin w))
variable (h:good s.val (chain w))(hP:List.length (coin w)≤N)(a:ℝ)(b:Cover)(z:Site n)(c:ℕ)
set_option quotPrecheck false
local notation "C0"=> (position h (Sonnet.root s))
abbrev purse (w:Slip (Point ((Coarse G) ⊕α)))(b:Cover)(i:Fin (coin w).length):= ((coin w).get i).1 - b
abbrev papers (w:Slip (Point ((Coarse G)⊕α)))(i:Fin (coin w).length):= axisEquiv.symm (((coin w).get i).2.1)
abbrev tend (w:Slip (Point ((Coarse G)⊕α)))(i:Fin (coin w).length) := ((coin w).get i).2.2
noncomputable def crust (p:Lattice.Order) {s:Senses R}{w:Slip (Point ((Coarse G)⊕α))}(h:good s.val (chain w))(Y: Zora.Noon G N)(hk:(coin w).length≤N) (a:ℝ) : Vase s G (coin w).length:= {
   stage:= hold h
   tan:= fun _=> true
   maps:= fun i=> Wand.curvy p (purse w (position h (Sonnet.root s)) i) (papers w i)
   ink:= fun i=> a*forecast Y (tend w) i
   legal:= (Stationary.paints G _).smul_mem a (funded Y (tend w) hk) }
-- Rain.R stance
local notation "H0"=> crust p h Y hP a
local notation "d"=> Zora.Noon.bill G Y (List.length (coin w))
lemma face_v (u:i0): size (purse w C0 u) ≤ meter w:= by let L₀:= (coin w).get u; let v:=memo (List.get_mem _ _) (i:=L₀); apply le_trans (subtract_size ..); rw [sum_meter]; rw [add_comm (meter (chain w))]; exact add_le_add v (cost_pos h _ (ownership s))
lemma voyage (u:i0): ((H0).maps u).range+((H0).maps u).tour.length ≤ 3*meter w+2:= by
 let t : ℕ:= size (purse w C0 u); have he:=face_v h u; change t ≤ meter w at he; let X: Wand G:= (H0).maps u; have hX:X.tour.length≤ 2*t+2:= trail_length; change t+X.tour.length≤ _; omega
lemma confidence (hw:List.length w≤ k) : (H0).momentum ≤ 5*k*(meter w)+2*k := by
 let M:=meter w; let X:= H0; let r:= (List.length (coin w)); let t:=((essence s).card); have hr : r ≤ k:= by unfold r; exact (Dais.enough h hw).trans (Nat.sub_le ..)
 have ht : t ≤ k:= by unfold t essence; rw [← weight_h h]; exact (le_trans (b:=List.length w) (by rw [leaves_length]; exact Nat.le_add_right ..) hw)
 have hX: X.reach ≤ ∑ _ : i0, (3*meter w+2):= Finset.sum_le_sum fun i _=> voyage p Y h hP a i; have hx: X.reach ≤ k*(3*M+2):= hX.trans (le_trans (le_of_eq (by simpa [r, M]
       )) (Nat.mul_le_mul_right _ hr)); have hY: X.stage.tariff≤ t*(2 * M):= (after_toll h).trans (by rw [show M= _ from sum_meter w]; change _ * _ ≤ (essence s).card * _; gcongr; exact Nat.le_add_right ..); change X.reach + X.stage.tariff ≤ 5*k*M+_; refine ((add_le_add hx (hY.trans (Nat.mul_le_mul_right _ ht))).trans_eq ?_); ring
lemma crystalH : (H0).sizeC ≤ |a| *Zora.Noon.bill G Y (List.length (coin w)):= by unfold Vase.sizeC crust; dsimp only; simp_rw [abs_mul,← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (Noon.bill_ge Y) (abs_nonneg _)
local notation "m"=> ((essence s).card:ℝ)
variable {u b0:ℝ}
lemma bill_pos (Y: Zora.Noon G N)(r:ℕ): 0≤Noon.bill G Y r:=by unfold Noon.bill; positivity
lemma buys (hw:List.length w≤k)(ht:0<u)(hx:u * (5*k:ℝ)≤ b0):
   (H0).fare u ≤ Noon.bill G Y (List.length (coin w)) *Real.exp (u*(2*k:ℝ))*Real.exp (b0*meter w) * |a|:= by
 let M:= meter w; let X:= Real.exp (u*(2*k:ℝ))
 rw [mul_assoc (Noon.bill ..),← Real.exp_add]; refine le_trans (b:= |a| * d *Real.exp (u*(2*k:ℝ)+b0*meter w)) (mul_le_mul (crystalH ..) (Real.exp_monotone ?_) (Real.exp_pos _).le (mul_nonneg (abs_nonneg _) (bill_pos ..))) ?_ ; swap -- simplify
 · apply le_of_eq; ring
 have he' : ((H0).momentum:ℝ)≤ 5*k*meter w+2*k:= by exact_mod_cast (confidence p Y h hP a hw) -- arity
 refine (mul_le_mul_of_nonneg_left he' ht.le).trans ?_; nlinarith only [mul_le_mul_of_nonneg_right hx (show 0 ≤ (meter w:ℝ) from Nat.cast_nonneg _)]
-- signal relation.Value at full group
variable (B':Config G n)
abbrev knot (p:Lattice.Order){s:Senses R}{w:Slip (Point ((Coarse G) ⊕α))}(h:good s.val (chain w)) (U:Config G n)(z:Site n)(i:Fin (coin w).length) := travel U z (trail p (purse w (position h (Sonnet.root s)) i) (papers w i))
lemma realized : (H0).read z k B'= a * ∑ i∈ Y.samples.support,Y.samples i* core i (tend w) (fun j=> theta G k (G.curvature (knot p h B' z j))) := by
 rw [←Noon.focused,Vase.globe]; let f(i: Fin (coin w).length):= theta G k (G.curvature (knot p h B' z i)); rw [mul_sum]; refine Finset.sum_congr rfl fun x _ =>?_ ; exact mul_assoc ..
local notation "F0"=> o (Sonnet.root s)
lemma born_co (u:i0): stood (there o h) ((coin w).get u)=(bent (o (Sonnet.root s)) (purse w (position h (Sonnet.root s)) u),axisEquiv (papers w u),tend w u):= by
 unfold stood there bent purse papers; rw [Equiv.apply_symm_apply,map_sub]; refine Prod.ext ?_ rfl; dsimp only; abel
lemma paid_terms : invoice (there o h) (coin w) x= ∏ i:i0,x (bent (o (Sonnet.root s)) (purse w C0 i),axisEquiv (papers w i),tend w i):= by
 let z:=there o h; let f(i:Point (Coarse G)):= x (stood z i); unfold Ink.invoice Ink.paid; rw [List.map_map]; change List.prod (List.map f (coin w))=_; have ht: List.map f (coin w)=List.ofFn (f ∘ (List.get (coin w))):= by rw [← List.map_ofFn, List.ofFn_get]
 rw [ht, List.prod_ofFn]; exact Finset.prod_congr rfl fun i _=> congr_arg _ (born_co o h i)
end books
end Dais
end YM.Qlocal.Quipu.Eluder

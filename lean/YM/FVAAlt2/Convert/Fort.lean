import YM.FVAAlt2.Convert.Telescope
import YM.FVAAlt2.First.Crib
/-!
# Calibration resolution for Wilson's position X scheme
Concrete application to EVERY controller Data, one compatible finite-to-all-order frame,
 all finite insertion lists supplied as `Datum`. Uses W_N^-1 on EXACT Section(C)
 from the same `Plan`. H&E orientation for boot supplied. `P.liftOff= LoftPP` standard
 off-shell *free* Taylor extension via same radial convention; no restriction on choice
 of position tests here except the full `Official` checks (alone sometimes expensive!).
 `arrive := Drivers.Pay` yields coefficientwise convergence horizon exact.
 No identification assumed between Pose.WB and prescription positions and phase. Proof.
 This is **before** final mass-independent stricter-grade frame adjustment.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Convert
open Finset Filter MeasureTheory Function Topology
open Labels Precision Extra.FD Maxwell Extraction FormalOPE FormalOPE.RG10
open PertExtension PertExtension.LatticePT PertExtension.Position
open FormalOPE.RG10.Position (Plan Official Stock Patience Drivers)
open FormalOPE.RG10.Gazebo FormalOPE.RG10.Carryon MS MS.Koszul MS.Local.Physical MS.Menus MS.Book MS.Land
open PowerSeries (C coeff constantCoeff)
open Home Report Matrix Profiles First
open scoped BigOperators Topology PowerSeries ContDiff Classical Matrix
variable {G:Gauge} {F:Frames G}{B:MS.Local.Physical.Deck G}
variable {U:MS.Land.Booked B}{d k n m:ℕ}
local notation "V"=> RG10.Position.Deck F d
local notation "N"=> Datum V
variable {Q:ChartRatio G}(P:Plan F)(hP:P.liftOff=LoftPP F)(hQ:LocalRatio Q)
set_option quotPrecheck false
local notation "Y"=> seats P.liftOff P.certified
variable {M: MS.Land.Booked (Home.seats P.liftOff P.certified)}
variable (X:Prescription (seats P.liftOff P.certified))(μ:ℝ)(S:MS_Data G M)
local notation "G'"=> science μ S F
local notation "κP"=> χ P S μ
local notation "L1" => Lobby.Table (nativeR P) Y
variable (hg:G.Simple)(hO:Official P.stock)(hp: Spect F M)
local notation "L'"=> (P.stock d).position (G' d)
set_option quotPrecheck false
-- Initialization.Regular portrait.
def river := ( Init (G') P.stock )
include hQ hP hO hp hg in
lemma peal_hot : Peaked P S μ:= by
 -- inspect ordering params
 have h : coeff 1 (Position.Peal.together F ((P.stock 6).positioned (G' 6)))= _:= First.Portray.canonical_first (X:=P.stock) hg hO P hP μ S hQ hp
 let u:= (κP).x; let s:= Position.Peal.slope G; have he:= Carryon.owed (F:=F) (Init (G') P.stock); change coeff 1 u*s = coeff 1 ( RG10.Position.Peal.together F _ ) * _ at he; rw [show coeff 1 ( Position.Peal.together F (Init (G') P.stock 6)) = s from h, if_pos (Position.Peal.pulse hg).ne', mul_one] at he; exact mul_right_cancel₀ (Position.Peal.pulse hg).ne' (he.trans (one_mul s).symm)
include hQ hP hg hO
variable (T: Launch (Lobby.Table (nativeR P) (seats P.liftOff P.certified)) S (F:=F) X)
include T
include μ
lemma horizon_paid (Yd:Drivers): Patience P Yd:= parks P S X Yd Q μ hg hO hQ T.high (tired μ P Q hg hQ T) (peal_hot P hP hQ μ S hg hO T.money) -- order?
variable {Ψ:Drivers}(C:Patience P Ψ)
theorem eqX : (κP).charge ∘ C.Yield (d:=d)= mix (science μ S F d) (of (L')) := congr_fun ( EqX P S X Ψ Q μ hg hO hQ T.high (tired μ P Q hg hQ T) ( peal_hot P hP hQ μ S hg hO T.money ) C ) d
-- actual mixed moment at (same μ) *position* coupling.T
abbrev f : Warp:= ( χ P S μ ).refund
-- not include Ψ implicit B? lean. argument order
lemma funding_one : coeff 1 ( f P μ S ).x=1:= by
 have hp:(κP).Hot:= (peal_hot P hP hQ μ S hg hO T.money).trans_ne one_ne_zero
 have he:= congr_arg (fun x:Warp=> coeff 1 x.x) (( κP ).cash hp); rw [Warp.step, Warp.heats] at he; rw [ show coeff 1 (κP).x=1 from peal_hot P hP hQ μ S hg hO T.money,one_mul] at he; exact he.trans (PowerSeries.coeff_one_X)
local notation "u"=> f P μ S
abbrev Zpre (d:ℕ): Matrix (RG10.Position.Deck F d) (RG10.Position.Deck F d) (PowerSeries ℝ):= (of ((P.stock d).position (science μ S F d))).map ((f P μ S).charge)
theorem price_Gx : C.Yield (d:=d) = mix ((f P μ S).charge ∘ G' d) (Zpre P μ S d) := by
 rw [ show C.Yield (d:=d)= _ from congr_fun (Y_eq P S X Ψ Q μ hg hO hQ T.high (tired μ P Q hg hQ T) ( peal_hot P hP hQ μ S hg hO T.money ) C) d ]; -- gives arrival C
 symm; exact Warp.untie _ ( f P μ S) (G' d)
end YM.FVAAlt2.Convert

import YM.FVAAlt2.Home.Erect
/-!
# $W to MS: finite-regulator frame conversion equations (concrete)
After this we can apply numerical leading and implicit position-frame
 solve in R.Old's exact coordinates. `_Spec.Visible`. θ and ε throughout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home
open Function Set Finset Filter Topology Lattice
open Precision Extra.FD Maxwell Labels Extraction
open FormalOPE PertExtension PertExtension.LatticePT PertExtension.Position FormalOPE.RG10.InversionTop
open MS MS.Local.Physical MS.Koszul MS.Menus MS.Book MS.Plane MS.Theater MS.Land
open MeasureTheory
open RG10.Position (Plan Spur Loft)
open PowerSeries (C coeff constantCoeff)
open Profiles
open scoped Topology BigOperators ContDiff PowerSeries Classical
variable {G:Gauge}{L:Frames G}{B:Deck G}
variable {W:Type*} {H:Source.Hol G} {d r:ℕ}
variable (R:Lobby.Registry L H)(D: ChartRatio G)(q:ℕ+)(m:ℕ) (μ:ℝ)
set_option linter.unusedSectionVars false
local notation "F"=> Glyph B d
local notation "Y"=> RG10.Position.Deck L d
local notation "V"=> LatticePT.Native q m
local notation "PSc"=> PowerSeries ℂ
local notation "PS"=> PowerSeries ℝ
variable (K: MS.Land.Prescription B)
local notation "ρ"=> K.team
local notation "ε"=> epsilon q m
local notation "t"=> μ- Profiles.Θ q m
-- extend rows by zero under hike
abbrev high(p:F): (Lobby.owner p).h≤d:= by change p.size≤d; exact Nat.le_of_lt_succ p.1.isLt
abbrev rel (K:Prescription B) (x:ℝ)(p:Rake.Label B)(a:ℝ)(j:Glyph B p.h):= Lobby.changePrice K x (fun _ :Unit=> p) a () j
def oilPoint (x:ℝ)(p:F)(a:ℝ)(j: F): PSc:= ∑ i: Glyph B (Lobby.owner p).h, if up (high p) i=j then rel K x (Lobby.owner p) a i else 0
abbrev aboard (a x:ℝ)(d:ℕ): Matrix (Glyph B d) (Glyph B d) PSc := Matrix.of (fun p=> oilPoint K x p a)
lemma onOil (x a:ℝ)(p:F)(j:Glyph B (Lobby.owner p).h): aboard K a x d p (up (high p) j)= rel K x (Lobby.owner p) a j:= by change oilPoint _ _ _ _ _=_; unfold oilPoint; rw [Finset.sum_eq_single j,if_pos rfl]; exact fun i _ hi=> if_neg (fun h=> hi (up_inj _ h)); simp
lemma realOil(p j:F) : RSpec (aboard K ε t d p j):= RSpec.finSum _ fun i _=>by split; apply specPrice (W:=Unit); simpa using RSpec.place 0 -- f annotation

lemma summ_mul {α:Type}(Gx: (Fin r→ Native q m) → α→PSc)(a : α→PSc)(s:Finset α)(x:(Fin r→E4) →ℝ) : Profiles.visit q m x (fun j=>∑ i∈s, a i * Gx j i )=∑ i∈s,a i*Profiles.visit q m x (fun j=>Gx j i) := by
 unfold Profiles.visit; simp_rw [Finset.mul_sum]; conv_rhs=> rw [Finset.sum_comm];
 apply sum_congr rfl; intro i _; rw [Finset.sum_comm]; apply sum_congr rfl; intro j _; exact sum_congr rfl fun i _=> by ring
lemma redoC (f:ℂ)(w:PSc): Lobby.redo ρ t (C f*w)= C f*Lobby.redo ρ t w:= by simp only [← PowerSeries.smul_eq_C_mul,map_smul]
lemma scale_pay (h:(Fin r→E4)→ℝ)(U:(Fin r→V)→PSc) : Profiles.visit q m h ((Lobby.redo ρ t) ∘ U)= Lobby.redo ρ t (Profiles.visit q m h U):=by unfold Profiles.visit; simp_rw [map_sum]; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=> Eq.symm (redoC ..)

abbrev dim_report {I:Type*}(v:Datum I):Points v.1.n→ℝ:= Complex.re ∘ (fun x=>v.1.test x)
local notation "nB"=> readC L B d
local notation "oB"=> overΩ L B d

def genus (w:Datum F): PSc:= YReport D R K (Lobby.owner ∘ w.snd) μ (dim_report w) q m
lemma mixEra : genus R D q m μ (d:=d) K=mix ( (Lobby.redo K.team t) ∘ mintC R D q m ) (aboard K ε t d):=by
 funext p; rcases p with ⟨p₀,p⟩; let U (i:Fin (p₀.n)) := Lobby.owner (p i); let J (i:Fin (p₀.n)):=Glyph B (U i).h; let tx(i:Fin p₀.n)(j:J i): F:=up (high (p i)) j; symm; rw [monoread (p:=p₀) p _ _ tx (fun i=> up_inj _) ?hp]; swap
 · intro i k hk; unfold aboard; rw [Matrix.of_apply,oilPoint]; exact sum_eq_zero fun j _=> if_neg (fun h=> hk ⟨j,h⟩)
 unfold genus YReport Lobby.newEra; rw [ summ_mul ]; refine sum_congr rfl fun u _=>?_ ; unfold comp mintC; simp_rw [Lobby.owner]; -- maybe splash
 let z:=fun i:Fin p₀.n=> Lobby.owner (u i); let c:= Lobby.redo ρ t; let h:=canon (J:=Glyph B d) ⟨p₀,p⟩; set p1:= Profiles.visit q m h (fun x=> Lobby.Paid D R x ε z);
 change c p1 * _= (∏ i,Lobby.changePrice K t U ε i (u i))* _; rw [mul_comm (c p1),← scale_pay]; refine congr_arg₂ (· * ·) (Finset.prod_congr rfl fun i _=>?_ ) rfl; exact onOil ..

-- however don't put t ring-change matrix on given `Plan.begins` twice. handle pieces with .C constant
set_option quotPrecheck false
local notation "dR"=> (din L B d).map C
local notation "dO"=> (dout L B d).map C
local notation "σ"=> Lobby.redo K.team t
lemma θin (L:Frames G)(B:Deck G): readC L B d=( (din L B d).map C ).map into:= Matrix.ext fun i j=> by simp only [Matrix.map_apply,din,RG10.Position.into_C]; exact congr_arg PowerSeries.C (starc L B i j).symm
lemma θout (L:Frames G)(B:Deck G): overΩ L B d=((dout L B d).map C).map into:= Matrix.ext fun i j=>by simp only [dout,Matrix.map_apply,RG10.Position.into_C]; exact congr_arg PowerSeries.C (starb L B i j).symm
lemma redoes (f: Datum Y→ PSc): σ ∘ mix f nB=mix (σ ∘ f) nB:=by funext v; unfold mix; simp_rw [Function.comp_apply,map_sum,readC,Matrix.map_apply, ← map_prod, mul_comm (f _)]; refine sum_congr rfl fun j _=>?_ ; rw [redoC,mul_comm] -- args adjust

variable (L B)
def frameO (k:MS.Land.Prescription B)(d:ℕ): Matrix (RG10.Position.Deck L d) (RG10.Position.Deck L d) PS:= (dout L B d).map C * ((aboard k ε t d).map takeReal * (din L B d).map C)
variable {L B}
lemma frame_board : (frameO L B q m μ K d).map into=oB*(aboard K ε t d*nB):= by
 rw [frameO,Matrix.map_mul,Matrix.map_mul,θin L,θout L B]
 rw [show ((aboard K ε t d).map takeReal).map into= _ from (show ((aboard K ε t d).map takeReal).map into= aboard K ε t d from Matrix.ext (fun i j=> realOil q m μ K i j))]

variable {P:Plan L} {K: Prescription (seats P.liftOff P.certified)}
local notation "β"=> seats P.liftOff P.certified
lemma authentic (hD: LocalRatio D) :
   PertExtension.Position.insert _ _ (into ∘ PowerSeries.subst (revise K.team t) ∘ P.begins q m d) ((frameO L β q m μ K d).map into)= mix (genus (nativeR P) D q m μ (d:=d) K) (overΩ L β d):= by
 rw [mixSame,frame_board,mixEra,initialMS D q m P hD,redoes, mix2,mix2,Matrix.mul_assoc]; congr! 1; funext w; exact Eq.symm (tidy ..)
end YM.FVAAlt2.Home

import YM.AlbaMS.Barr.Tears
/-!
# Canonical waves don't change physical values

Transition includes ghost normalization and A normalization and corresponding
L and K, at fixed bare coupling. Doesn't use any convergence criterion on frame
except later for CT and measure testing. Works throughout truncated Pert diagrams
via algebra rather than assuming nonlinear chart at Landau slice. Uses oscillator
from based root, solves cohom-with-marks at finite geometry.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Barr
open Set Function Filter IsNilpotent Matrix
open scoped BigOperators Classical Topology Matrix InnerProductSpace ENNReal
open Nexus Bric Coil Loft Inlay Inlay.Net Tune Odom Cutis Cutis.Winter Lattice
variable {R S:Type*}[CommRing R][CommRing S]{E B:Type*}
section weft
variable {ρ:E→Bool}(a b c:E→R)
lemma run_weft (h:∀ i, a i*b i=c i)(F:Coil ρ R): weft a (weft b F)=weft c F:=by
  ext l; rw [wefts, wefts,wefts,← mul_assoc]; congr 1; induction l with|nil=>simp|cons i l ih=> simp_rw [List.map_cons,List.prod_cons,← h i, ← ih,mul_mul_mul_comm (a i)]
lemma one_on : weft (ρ:=ρ) a 1=1 := by ext l; rw [wefts]; cases l<;>simp
end weft
-- focusing on a and measure constant; can talk about this across phases but not implementing high ν.
structure Still (P T:Tune R): Prop where
  value : T.a=P.a
  point : T.z=P.z
  eta : T.D=P.D
-- direction P-chart → T-chart
variable (P T:Tune R) {G:Gauge}
def lane (v : Leaf G E B) : R:= match v with
| .inl (.inl _)=> ↑(T.A*P.A⁻¹)
| .inl (.inr _)=> ↑(P.A*T.A⁻¹)
| .inr (.inl _)=> ↑(T.Gc*P.Gc⁻¹)
| .inr (.inr _)=> ↑(P.Gc*T.Gc⁻¹)
namespace Still
variable {P T} (h:Still P T)
include h
lemma laneS (x : Leaf G E B): lane P T x * P.loomT x=T.loomT x:=by
  have hx (a:R)(U V:Rˣ): ↑(V*U⁻¹)* (a * ↑U)=a*(V:R):= by rw [mul_left_comm, Units.val_mul,mul_assoc, Units.inv_mul,mul_one]
  rcases x with (i|i)|(i|i)<;> simp only [lane,loomT,h.value,h.eta,Sum.elim_inl, Sum.elim_inr];
  · exact hx ..
  · convert! hx _ (P.A⁻¹) (T.A⁻¹) using 1; rw [inv_inv,mul_comm (P.A)]
  · exact hx ..
  convert! hx _ (P.Gc⁻¹) (T.Gc⁻¹) using 1; rw [inv_inv,mul_comm (P.Gc)]
lemma levels (k:ℕ)(Ω:Heave G E B ℝ): T.up k Ω=weft (lane P T) (P.up k Ω):=by
  rw [Tune.up,h.point,h.eta]; exact (run_weft _ _ _ h.laneS _).symm

-- θ-compatible and Measure-term equivalence.
lemma commute (x y:Leaf G E B): T.bracket x y*lane P T x * lane P T y=P.bracket x y:=by
  have he (A:R)(U V:Rˣ): A*↑(V*U⁻¹)*↑(U*V⁻¹)=A:=by rw [mul_assoc,← Units.val_mul, show (V*U⁻¹)*(U*V⁻¹)=1 from by group,Units.val_one,mul_one]
  simp only [bracket,h.value,h.eta]; rcases x with (i|i)|(i|i)<;> simp only [Loft.oriented];
  · split_ifs with heq; subst y; exact he _ P.A T.A; simp
  · simp
  · split_ifs with heq; subst y; exact he _ P.Gc T.Gc; simp
  simp
variable [Fintype E][Fintype B] {Ω:Net E B}(F:Odom.Book Ω G)
lemma charter : F.charter T= weft (lane P T) (F.charter P) := by unfold Odom.Book.charter Tune.fuelT; simp only [map_sub,h.levels]
lemma guide (U:Heave G E B R): weft (lane P T) (quantum P.bracket Finset.univ (F.charter P) U)= quantum T.bracket Finset.univ (F.charter T) (weft (lane P T) U):= by
  rw [h.charter]; have hv i j : T.bracket i j * lane P T (G:=G) (E:=E) (B:=B) i* lane P T j=1* P.bracket i j:= by rw [h.commute i j, MulOneClass.one_mul]
  rw [quantum_apply,quantum_apply,map_sub,weft_touch (lane _ _) hv,weft_cross _ hv,one_smul,one_smul]
end Still

namespace Salute
variable {n:Side}{u: Precision.ChartRatio G}(hu:Precision.LocalRatio u)
variable [Algebra ℚ R][DecidableEq E][DecidableEq B] [Fintype E][Fintype B] {Ω:Net E B}
noncomputable def bouquet (W: Odom.Book Ω G) (A: Fritz (Flit G E) (Flit G B) R) (T:Tune R) (F:Heave G E B R) : R:= Fritz.levy A.hop (W.stim T) F
protected abbrev standard (b:Heave G (Foil n) (Nail n true) R) : R:= bouquet (Root G u n true hu) (drive P) P b

-- package Lot remembers P
variable (X:Odom.Book Ω G)
def planeBook := (phys X P.a).beam P.D
abbrev total := (P.D (P.a⁻¹))^4
omit [Algebra ℚ R] in
lemma isRoot : IsUnit (total P):= by unfold total; exact ((isUnit_iff_ne_zero.mpr (show P.a⁻¹≠0 from inv_ne_zero P.ha.ne')).map _).pow _
omit [DecidableEq E][DecidableEq B] in
lemma legal (h:IsNilpotent (X.stim P))(he:IsNilpotent P.z): Fritz.Align (planeBook P X) (X.stim P) (total P):=⟨X.stim_tone _,h,X.stim_rank P he,by unfold planeBook Lot.q; rw [← plaza X P]; exact X.engine_master P⟩
omit [DecidableEq E][DecidableEq B] in
lemma bridge : Fritz.Part (planeBook P X) (total P) (X.stim P)= quantum P.bracket Finset.univ (X.charter P):=by rw [Fritz.Part, show (planeBook P X).combo= X.fair P from (plaza X P).symm,Odom.Book.stim, show X.fair P + (X.charter P - X.fair P)=X.charter P from add_sub_cancel ..]; rfl
end Salute
end YM.MSBar.Barr

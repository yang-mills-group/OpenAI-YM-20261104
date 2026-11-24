import YM.FVAAlt2.Home.Vista
/-! Actual `Position.Plan.begins` across SAME stencil, read analytically at
 prescribed inversion points (and their invariant top extrapolation). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home.Profiles
open Function Finset Filter Topology Lattice Labels Source FormalOPE RG10
open PertExtension PertExtension.LatticePT PertExtension.LatticePT.Mixed PertExtension.Orb PertExtension.Orb.SlotEvaluation PertExtension.Series PertExtension.Series.Tested Precision Pert.Orb
open Extra.FD Maxwell Extraction InversionTop
open RG10.Position (Plan Loft Library prelude inkAt owner)
open PowerSeries (C coeff)
open MeasureTheory MS MS.Koszul MS.Menus MS.Book MS.Theater
-- `Classical` localized: many simp over finite subtypes of cfg.
open scoped BigOperators Topology ContDiff PowerSeries Classical
variable {G:Gauge}{L:Frames G}{H:Hol G}{B:MS.Local.Physical.Deck G}{d:ℕ}
variable (R:Lobby.Registry L H) (D:ChartRatio G)
variable (q:ℕ+) (m:ℕ)
lemma goodReg : Admissible (side q m):= by
 refine ⟨?_, even_iff_two_dvd.mp (side_even ..) ⟩; change 4≤8*q.val^(m+1)*q.val^(m^2); have he:1 ≤ q.val:= q.pos; nlinarith [one_le_pow₀ (n:=m+1) he,one_le_pow₀ (n:=m^2) he] -- ambiguous n variables

variable {W:Type}[Fintype W][LinearOrder W](Ψ:(W→E4)→ℝ)(h:W→ℕ)
local notation "V"=> Native q m
local notation "ε"=> epsilon q m
local notation "u"=> origins q m
local notation "A"=> (W→ Native q m)
local notation "Pr" => PowerSeries ℂ
local notation "eT"=> 4*Fintype.card W
-- approximate profile measurement using ANY polynomial-ready weighted Φ. a label-list distribution certificate, reads exact profile-by-assembly geometry. Current Ψ is real (uses RG10.Position).

def address (x:A) (o:V)(i:W) := x i + o
def visit (F:(W→Native q m)→ Pr): Pr:=∑ x:A,∑ o∈u, C ((epsilon q m ^ (4* Fintype.card W)* Mixed.price q m Ψ x:ℝ):ℂ)* F (address q m x o)
def curve (v:(i:W)→Label G (h i)): Pr:= visit q m Ψ (fun x:A=>C ((↑ε:ℂ)⁻¹ ^ ∑ i,h i) * FullT D R h x v) -- arg order FullT D first
lemma tariff : (↑ε:ℂ)^(4*Fintype.card W) * ((↑ε:ℂ)⁻¹ ^(∑ i:W,h i))=∏ i:W, (↑(ε^4/ε^(h i)):ℂ):= by push_cast; rw [Finset.prod_div_distrib, Finset.prod_const,Finset.card_univ, Finset.prod_pow_eq_pow_sum, ← pow_mul]; rw [div_eq_mul_inv,inv_pow]

lemma distributes {J: W→Type} [∀ i,Fintype (J i)](f: (i:W)→ J i→ ℂ)(P: (i:W)→ J i→Label G (h i)) : curve R D q m Ψ h (fun i=>∑ j:J i,f i j • P i j)=∑ r:(i:W)→ J i, C (∏ i,f i (r i))* curve R D q m Ψ h (fun i=> P i (r i)):=by
 unfold curve visit; simp_rw [distribute, Finset.mul_sum]; conv_rhs=> rw [Finset.sum_comm]
 -- wait wrong twice
 apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; apply sum_congr rfl; intro y _; apply sum_congr rfl; intro z hz; ring

lemma curve_basis (hD:LocalRatio D)(p:Sbox (L:=L) h)(hp: ∀ i,((L.level (h i)).grades (p i)).1=h i) :
    let w : W→ LatticePT.Word G := fun i=> ⟨h i,L.level (h i),R.use _, H,R.owns _,R.bid _, p i,hp i⟩
    curve R D q m Ψ h (fun i=>(L.level (h i)).basis (p i))= into (PowerSeries.mk (Mixed.polynomialTop w q m Ψ)):= by
 intro w; ext1 k; rw [into_coeff,PowerSeries.coeff_mk]; unfold curve visit Mixed.polynomialTop; simp_rw [map_sum,Complex.ofReal_sum]; refine sum_congr ?_ fun i _=>sum_congr rfl fun o _=>?_;
 · congr 1; apply Subsingleton.elim -- choose instance
 let x:= address q m i o; set t:=Mixed.price q m Ψ i; let s : Pr:= C ((t:ℝ):ℂ);
 rw [Complex.ofReal_mul,Complex.ofReal_pow,mul_comm (_^_:ℂ), map_mul PowerSeries.C (x:=(↑t:ℂ)), mul_assoc,← mul_assoc ((PowerSeries.C _):Pr) (PowerSeries.C _) (FullT D R _ x _), ← map_mul,tariff, bunker D hD R h x p hp _ (goodReg q m),PowerSeries.coeff_C_mul,map_sum,Finset.mul_sum ]; refine sum_congr (by change (univ:Finset (Mixed.Task w)) = _; congr 1; apply Subsingleton.elim) fun j _=>?_ ; rw [PowerSeries.coeff_mk,Complex.ofReal_mul]; rfl

lemma pose_not (P:Loft L)(hP:Loft.Level L P)(p:W→RG10.Position.Token L) (hD:LocalRatio D): curve R D q m Ψ (fun i=>(p i).1) (fun i=>P.lift _ (owner (p i)))=into (RG10.Position.prelude H R.use R.owns R.bid P p q m Ψ) :=by
 -- unit orbit.Test per h with only local Φ
 rw [funext (fun i=> ( RG10.Position.tinted P hP (p i) ).symm), distributes ]; unfold RG10.Position.prelude; rw [map_sum]; refine sum_congr ?_ fun k _=>?_;
 · congr 1; apply Subsingleton.elim
 rw [map_mul,RG10.Position.into_C, Complex.ofReal_prod]; exact congr_arg _ (curve_basis R D q m Ψ _ hD (fun i=> (k i).val) (fun i=> congr_arg Prod.fst (k i).property))
-- Canonical plan fixes H and S.
def nativeR (P:Plan L): Lobby.Registry L P.H:= ⟨P.source,P.sound,P.chosen⟩
def beginC (P:Plan L)(v:PertExtension.Position.Mark (RG10.Position.Deck L d) PertExtension.Physical.Profile.n):= curve (nativeR P) D q m (fun x=>Complex.re (v.1.test (YM.points x))) (fun i=>(RG10.Position.Deck.token L d (v.2 i)).1) (fun i=>P.liftOff.lift _ (RG10.Position.owner (RG10.Position.Deck.token L d (v.2 i)))) -- fill
lemma agreement (P:Plan L)(v:PertExtension.Position.Mark (RG10.Position.Deck L d) PertExtension.Physical.Profile.n)(hD:LocalRatio D): beginC D q m P v=into (P.begins q m d v):= pose_not (W:=Fin v.fst.n) (nativeR P) _ q m _ _ P.certified _ hD
end YM.FVAAlt2.Home.Profiles

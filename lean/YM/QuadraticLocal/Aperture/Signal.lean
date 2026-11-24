import YM.QuadraticLocal.Aperture.Bunch
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Aperture
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder PertExtension PertExtension.Series AllOrder.Laplace AllOrder.Laplace.SigmaP Response Laurent Stationary
open PositionX.Jet Extra.Iteration AllOrder.Floe AllOrder.Floe.Pace AllOrder.Floe.Aero AllOrder.Floe.StateE
open AllOrder.Catch AllOrder.Catch.Clock Sienna
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Ink Marker Sunrise Toggle Radial
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {L n f: Side}{ι V: Type} [Fintype V][DecidableEq V] {W b D α a B C Ω κ V₀:ℝ}{k p M:ℕ}
variable {P:Patch}{K:KernelChoices}{S : StepData n f} {s:Teller G}{η : Stage}
open Metric ConnectedActivityE6.Coat
open Till Tilt Lantern Aux Aux.Name
namespace Bunch
variable (I:V→Loan)(u:∀ i, Atom G (I i).r)(α:V→Site n→ Site f)(x:V→Site n)
local notation "φ"=> V→ℝ
local notation "loc" i=> α i (x i)
local notation "Vc"=>mapC x
variable (v: V→ℝ)
-- Fix the forest and its associated configuration spaces.
variable (F:Forest S.ratio)
local notation "Y"=> Body (Precision.Key F G)
local notation "X"=> Apex n G × Body (Precision.Key F G)
local notation "E"=> ℝ×(Apex n G × Body (Precision.Key F G))
local notation "u₀" i=> Loan.leafMatter (I i) (u i) (α i (x i)) F
local notation "Φ" i:max=> Aperture.scene F (beamF I u α x i)
local notation "Σ₁"=> Aperture.scene F (beam I u α x v)
local notation "T0" i:max=> -(v i)
open Fire AllOrder.Kinetic AllOrder.Kinetic.Port PertExtension Series GaussianScore PositionX.Gauss Drawer
abbrev Pen (i:V)(d:ℕ):= Loan.alloy (I i) (u i) (loc i) F d
local notation "P₀" => Bunch.Pen I u α x F
local notation "ϰ" => Bough.train I u α
lemma scene_eq : Aperture.scene F (beam I u α x v)=∑ i:V, (-(v i)) • (Φ i):=by ext1 x; unfold Aperture.scene beam; simp only [Finset.sum_apply]; rfl
lemma chip (i:V)(z:Apex n G × Body (Precision.Key F G))(d:ℕ): Radial.jet (Φ i) (d+2) (1,z)= (P₀ i d) z:=by
 let U':= u₀ i; have h:= Loan.healthy (I i) (u i) (loc i) F; have hp:= (I i).crest; let k':=(I i).e+(I i).toll; have he: (I i).stamp+1+(I i).r=k'+2:=by unfold k'; have h':=(I i).recovery; omega
 change Radial.jet (fun x:E=> x.1^((I i).stamp+1)*U' x.2) (d+2) (1,z)= _
 by_cases hz:k' ≤ d; · rw [favor_exp U' h.smooth, if_pos (show (I i).stamp+1≤d+2 from (by omega)),one_pow,one_mul,Pen,Loan.alloy,if_pos hz]; apply congr_arg (fun i=> (jet U' i) z); omega
 unfold Pen Loan.alloy; rw [if_neg hz]; exact favor_pocket _ h.smooth (k'+2) _ _ _ h.vanish 1 z he.symm (by omega)
variable (R:Layout G)(J:Finset Age)(hZ:Legal J R){B:ℝ→ Config G f→ℝ}{t:S.Choices}{O:ChartRatio G}
variable (W:Desk F O B t)
local notation "L'" => Bough.train I u α R J F W
local notation "L₁" => add_Sign F (spend R J B) (beam I u α x v) (augment F R J W hZ) (esteem I u α x v F)
set_option quotPrecheck false
local notation "F₁"=> (fderiv ℝ (W).quiet 0)
local notation "S'"=> (castle W.hard W.quiet W.pay.steer)
local notation "T'"=> Bough.survey (mapC x)
variable (z:Apex n G)
omit hZ in
lemma orb (Z:Body (Precision.Key F G))(j:ℕ): (L' j) ((z,T' v), Z)=(Floe.books F R J W) j (z,Z)+∑ i:V,v i*(Pen I u α x F i j (goldL F (F₁) (z,Z))):=by
 unfold Bough.train; rw [Pi.add_apply]; simp only [Finset.sum_apply]; apply congr_arg ((books F R J W j (z,Z))+ ·); apply Finset.sum_congr rfl; intro i _; unfold Bough.soldier Bough.survey mapC; change ∑ s:Site n, ((if s=x i then 1 else 0)*v i)* _ = _; simp
include hZ
lemma momentJ (Z:Body (Precision.Key F G))(d:ℕ) : (L' d) ((z,T' v), Z)= (Impulse (F₁) (L₁).high (W.paid)) d (z,Z):=by
 by_cases hd:d=0; · subst d; rw [Bough.bye, Response.Impulse, win0]; rfl
 rw [orb]; let p:= Response.colorful (F₁) (z,Z); let A:=(W.high+venue F R J); let a' : Config G n→ℝ:=0; let b:= spine (F₁) (Real.log∘W.paid) 0 d (z,Z)
 rw [Response.Impulse,win_atn _ hd,Floe.books,Impulse,win_atn _ hd]; unfold token; change (b-Radial.jet A (d+2) p)+_= b-Radial.jet (A+Σ₁) (d+2) p
 rw [jet_add (show ContDiffAt ℝ ω A 0 from (augment F R J W hZ).pay.activity) (esteem I u α x v F).nice,scene_eq, goth (fun i _=> (show ContDiffAt ℝ ω (-(v i) • (Φ i)) 0 from (adept I u α x F i).nice.const_smul (-v i)))]; let P:= goldL F (F₁) (z,Z); simp_rw [jet_scale _ _ (adept I u α x F _).nice (d+2) p, show p=(1,P) from rfl,chip,smul_eq_mul,neg_mul,Finset.sum_neg_distrib]; abel_nf; rfl
lemma finance (j:ℕ) : distilled (L₁) j z= Response.connected (S') volume L' j (z,T' v):=by
 let U:= (F₁); let V':= Impulse (F₁) (L₁).high W.paid; let s:= (z,T' v); let A:=(S'); let E':= EXP L'; let T:= LOG (climate (S') volume V'); have ht(y:Y): swap (L') (s,y)= Function.swap V' (z,y):= funext fun j=>momentJ I u α x v F R J hZ W z y j -- typo shadow
 have hh : swap (climate (S') volume L') s= swap (climate (S') volume V') z:= by ext1 i; apply congr_arg (A.average volume); funext y; unfold EXP; change _= expS ((swap V') (z,y)) i; rw [← ht]; rfl
 change logS (swap (climate A volume V') z) j = _; rw [← hh]; rfl
end Bunch
end YM.QuadraticLocal.Aperture

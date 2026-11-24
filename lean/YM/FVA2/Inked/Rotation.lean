import YM.FVA2.Inked.Hero
import YM.FVA2.Press.Lead
/-!
 # Real-test and complex Momentum probes agree (with I factors reinstated) on all torchs
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Inked.Music
open Function Filter Set Finset MeasureTheory Topology
open scoped ContDiff BigOperators Classical
open Lattice RG Maxwell Gen
open MS MS.Koszul MS.Plane MS.Native MS.Native.Draft MS.Cylinder MS.Cylinder.Taylor MS.Momentum MS.Theater
open MS.Color MS.Arts MS.Motif MS.Landau MS.Landau.Detect MS.Halo MS.Book MS.Heat MS.Tone MS.Plane.Wire
open Position.OpenAxis
variable {E F J Y : Type}[NormedAddCommGroup E][NormedSpace ℝ E]{G:Gauge}
local notation "P"=> E4
local notation "L"=> Lane4 G
local notation "I"=> Complex.I
local notation "W"=> G.Color
local notation "K"=> Cfield G 0
local notation "Q"=> ℝ→ℂ
variable {v:Axis}{i:G.ColorIndex}{f g h k:ℝ→ℂ}
structure Lamp (f g:ℝ→ℂ): Prop where
    real : ContDiff ℝ ∞ f
    complex : ContDiff ℝ ∞ g
    phase (j:ℕ) : reading j g= I^j * reading j f
namespace Lamp
private lemma at0 (j:ℕ)(c:ℂ): reading j (fun _=>c)=if j=0 then c else 0:= by cases j <;> simp [reading, iteratedDeriv_const ] -- inspect
lemma simple (c:ℂ): Lamp (fun _:ℝ=>c) (fun _=>c):= ⟨contDiff_const,contDiff_const,fun j=>by rw [at0]; by_cases h:j=0<;> simp [h]⟩
lemma times (u:Lamp f g)(v:Lamp h k): Lamp (fun t=>f t*h t) (fun t=>g t*k t):= by
    refine ⟨ u.real.mul v.real,u.complex.mul v.complex,fun j=>?_⟩; rw [ read_mul u.real v.real, read_mul u.complex v.complex, Finset.mul_sum ]; apply Finset.sum_congr rfl; intro i hi; rw [ u.phase i,v.phase, mul_mul_mul_comm, ← pow_add, show i+(j-i)=j from (by have h:= Finset.mem_range.mp hi; omega) ]
lemma sum {f g:F→ℝ→ℂ} (S:Finset F)(h:∀ i∈S,Lamp (f i) (g i)): Lamp (fun t=> ∑ i∈S,f i t ) (fun t=> ∑ i∈S,g i t ):= by refine ⟨ ContDiff.sum (fun i hi=> (h i hi).real), ContDiff.sum (fun i hi=> (h i hi).complex), fun j=>?_⟩; rw [ read_sum (fun i hi=> (h i hi).real), read_sum (fun i hi=> (h i hi).complex), Finset.mul_sum ]; exact Finset.sum_congr rfl (fun i hi=>(h i hi).phase j)
abbrev circ (x:ℂ)(t:ℝ): ℂ:= Complex.exp (x*t)
private lemma nCirc (x:ℂ)(t:ℝ)(n:ℕ): iteratedDeriv n (circ x) t=x^n*circ x t:= by
    induction n generalizing t with
    | zero=> simp
    | succ n ih=> 
        rw [iteratedDeriv_succ,funext ih,deriv_const_mul_field]; have he:HasDerivAt (circ x) (circ x t*x) t:=by convert! ((Complex.ofRealCLM.hasDerivAt (x:=t)).const_mul x).cexp using 1; simp [circ];
        rw [he.deriv,pow_succ];ring
private lemma rCirc (x:ℂ): ContDiff ℝ ∞ (circ x):= by unfold circ; exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
lemma exponent (x:ℝ): Lamp (fun t:ℝ=> ↑( Real.exp (t*x) )) (circ (I*(x:ℂ)) ):= by
    rw [ show (fun t:ℝ=> (↑( Real.exp (t*x) ):ℂ))=circ (x:ℂ) from funext fun t=> by unfold circ; rw [Complex.ofReal_exp]; push_cast; rw [mul_comm (t:ℂ)] ]; refine ⟨ rCirc _,rCirc _, fun i=>?_⟩; simp [reading,nCirc, mul_pow, circ,Complex.real_smul,mul_left_comm _ (I^i)] -- overly simplified
end Lamp
-- initial LHS: `trim` paywave but ℝ.
def trim (x:Lane4 G) (i:LightMode G Cover)(t:ℝ) : ℝ:= (way id x.1 i.1:ℝ)* Real.exp (t*MS.Momentum.pairing x.2 (Tone.bornv i))
abbrev kite (x:L)(t:ℝ): Lane4 G:= (x.1,t • x.2)
lemma flight (x:L)(i:LightMode G Cover) : Lamp (fun t=> (( trim x i t ):ℂ) ) (fun t=> paywave ( kite x t ) i ):= by
    have ht (t:ℝ): MS.Momentum.pairing (t • x.2) ( bornv i )=t*MS.Momentum.pairing x.2 (bornv i):=by unfold MS.Momentum.pairing; rw [ Finset.mul_sum ]; exact Finset.sum_congr rfl (fun _ _=> mul_assoc ..)
    by_cases h:x.1=i.1
    · have he : ∀ R:Type, ∀ [CommRing R], way (R:=R) id x.1 i.1=1:= fun _ _=> by unfold way; simp [h];
      unfold trim paywave; change Lamp _ (fun t:ℝ=> ( way id x.1 i.1 )*Tone.bill (t • x.2) (bornv i)); simp_rw [he,one_mul]; obtain hr:=(Lamp.exponent (MS.Momentum.pairing x.2 (bornv i))); convert! hr using 1; funext t; unfold Tone.bill Lamp.circ; rw [ht,Complex.ofReal_mul]; congr 1; ring
    change x.1≠id i.1 at h; unfold trim paywave; change Lamp _ (fun t:ℝ=> (way id x.1 i.1)* _ ); simp only [need id h, zero_mul,Complex.ofReal_zero]; exact Lamp.simple _
-- pocket formula. Avoidance of non-gauge.Direction positivity.
lemma focuses (i:F→LightMode G Cover)(g:Cyl F ℂ)(w:Legs (Lane4 G)) : Lamp ( fun t=> shade (fun y j=> (( trim y (i j) t ):ℂ)) g w ) (fun t=> shade (fun y j=> paywave y (i j)) g ( Wire.sail (ray w) t )) := by
    induction w generalizing g with
    | nil=> exact Lamp.simple _
    | cons l w ih=> obtain ⟨s,hs⟩:= fromCyl g; simp_rw [ show ∀ t:ℝ,Wire.sail (ray (l::w)) t = kite l t :: Wire.sail (ray w) t from fun _=>rfl,deriv_lum _ _ g hs ]; exact Lamp.sum _ (fun j _=> ( flight l (i j) ).times ( ih (enter j g) ))
-- Useful when `real side` amplitude factored as t^length. Need remove t^length.
lemma factorQ (n m:ℕ)(u:ContDiff ℝ ∞ f): reading (m+n) (fun t:ℝ=> t^n • f t)= reading m f:= by
    induction n with| zero=> simp | succ n ih=>
       rw [show m+(n+1)=m+n+1 by omega,show (fun t:ℝ=> t^(n+1) • f t) = (fun t:ℝ=> t • (t^n • f t)) from funext fun t=> by rw [pow_succ', mul_smul] ]; let A(t:ℝ):= t^n • f t; let k:=m+n; obtain he: ContDiff ℝ ∞ A:= ((contDiff_id.pow n).smul u)
       rw [← ih]; unfold reading; rw [iter_weight he.contDiffAt, Nat.factorial_succ,Nat.cast_mul]; change ( (((k+1:ℕ):ℝ))*(k.factorial:ℝ))⁻¹ • ( ((k+1:ℕ):ℝ) • _ ) = _; rw [ smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (by exact_mod_cast k.succ_ne_zero),mul_one]
end YM.FVA2.Inked.Music

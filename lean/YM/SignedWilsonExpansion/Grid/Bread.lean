import YM.SignedWilsonExpansion.Grid.Simple
import YM.SignedWilsonExpansion.Grid.Dual
namespace YM.SignedWilsonExpansion.Overlap
/-! A kernel-checkable dual-type derivative at zero transfer. `Worth`
is on the **functions** of xy. Includes derivatives of radial amplitudes.
All four teeth cited when pricing. Two indices over pair in plane 02; sign in the probe
`x • side i` uses curl F02 both indices transverse to time = three. Keep ux dependence on each, and
vx weight routed. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Koszul MS.Plane MS.Plane.Flux MS.Landau MS.High MS.Landau.Detect MS.Landau.Detect.Mark
open FVA2 FVA2.Lambda Area Walk Bubble Heter TreeLine AxisChoice JetD
open scoped Classical Topology ContDiff BigOperators RealInnerProductSpace
local notation "e" => port
local notation "T" => side
local notation "σ" => (ℝ×ℝ)
local notation "P" => FourP
local notation "Ω" => Momentum.sq
def assay (F:Panel) (i j:Bool) :σ→ℝ:= fun w=>F (port i) (port j) ( w.1 • side i ) ( w.2 • side j )
def survey (F:Panel):ℝ:= ∑ i:Bool, ∑ j:Bool,tooth (assay F i j)
abbrev Ready (F:Panel): Prop:=∀ i j:Bool,ContDiff ℝ ∞ (assay F i j)
lemma Ready.add {U V:Panel}(u:Ready U)(v:Ready V): Ready (fun i j p q=> U i j p q+V i j p q):=fun i j=>(u i j).add (v i j)
lemma Ready.switch {U:Panel} (u:Ready U): Ready (fun i j p q=> U j i q p):= fun i j=> ( u j i ).comp (contDiff_snd.prodMk contDiff_fst)
lemma aug {U V:Panel}(u:Ready U)(v:Ready V): survey (U+V)= survey U+survey V:= by unfold survey; rw [← Finset.sum_add_distrib ]; refine Finset.sum_congr rfl (fun i _=>?_) ; rw [ ← Finset.sum_add_distrib ]; exact Finset.sum_congr rfl fun j _=>tooth_add (u i j) (v i j)
lemma sw_f {U:Panel}(u:Ready U): survey (fun i j p q=> U j i q p)=survey U:= by unfold survey; rw [ Finset.sum_comm ]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>Heter.swap (u i j)
attribute [local fun_prop] AxisChoice.poly_g AxisChoice.poly_p
variable {h:ℝ→ℝ}(hp:ContDiff ℝ ∞ h)(k:P)
local notation "TXK" => fun i j p q=>TX h i j p q k
include hp
lemma tReady : Ready TXK:= by intro i j; unfold assay TX feather yMark Slice.rib bond Momentum.sq; fun_prop
omit hp
lemma tS : survey TXK=0:= by
    have he(i j:Bool): Heter.dY (assay TXK i j)=(fun _=>0):= by ext x; unfold assay Heter.dY; simp_rw [ tQuiet h i j k ]; simp
    unfold survey tooth; simp_rw [ he ]; simp
-- shifted rail even when both external momenta are independent
local notation "a" => k 0
local notation "b" => k 1
local notation "c" => k 2
local notation "Λ" => Ω k
-- Present shifts via additive linear powers and δ. Want simp for neg exposed only.
abbrev θ (k:P)(i:Bool):ℝ:= if i then k 0 else -k 2
lemma shifted (i:Bool)(x:ℝ): Ω (k+x • T i)= Λ+ 2*θ k i *x+x^2:= by rw [heel]; cases i <;> simp only [θ,Bool.false_eq_true,↓reduceIte]; ring
lemma backward (i:Bool)(x:ℝ): Ω (-k+x • T i)= Λ-2*θ k i*x+x^2:= by rw [shifted]; simp_rw [sq_neg]; cases i <;> simp only [θ,Bool.false_eq_true,↓reduceIte, Pi.neg_apply] <;> ring
lemma offset (i j:Bool)(x y:ℝ): Ω (k+(x • T i+y • T j)) =
    Λ + 2*θ k i*x+x^2+ 2*θ k j*y+y^2 + 2*(if i=j then 1 else 0)*x*y:= by
        rw [← add_assoc,shifted,shifted]; cases i <;> cases j <;> simp [θ,side,unitV,spike] <;> ring
open JetD.Slip
private abbrev num := Slip.constant
private abbrev xv := Slip.fst
private abbrev yv := Slip.snd
local infixl:65 " +ₑ " => Slip.tied
local infixl:65 " -ₑ " => fun s t=> Slip.tied s (Slip.negS t)
local infixl:70 " *ₑ " => Slip.both
abbrev startW (i:Bool): Slip:= num Λ +ₑ num (2*θ k i) *ₑ xv +ₑ (xv *ₑ xv)
abbrev endW (i:Bool) : Slip:= num Λ -ₑ num (2*θ k i) *ₑ yv +ₑ (yv *ₑ yv)
abbrev centerW (i j:Bool): Slip:= startW k i +ₑ num (2*θ k j) *ₑ yv +ₑ (yv *ₑ yv) +ₑ num (2*if i=j then 1 else 0) *ₑ xv *ₑ yv
lemma paidStart (i:Bool): Worth (fun x=>Ω (k+x.1 • T i)) (startW k i) := by simp_rw [shifted]; exact ((( Worth.c _ ).add (( Worth.c _ ).mul Worth.x)).add Worth.x.square)
lemma paidEnd (i:Bool): Worth (fun x=>Ω (-k+x.2 • T i)) (endW k i) := by simp_rw [backward]; exact ((( Worth.c _ ).sub (( Worth.c _ ).mul Worth.y)).add Worth.y.square)
lemma paidCenter (i j:Bool): Worth (fun x=>Ω (k+(x.1 • T i+x.2 • T j))) (centerW k i j) := by
    obtain A:=paidStart k i; simp_rw [ shifted ] at A
    simp_rw [offset]; exact ((A.add ((Worth.c _).mul Worth.y)).add Worth.y.square).add (((Worth.c _).mul Worth.x).mul Worth.y)
include hp
local notation "Pᵥ" => fun i j p q=>VX h i j p q k
local notation "Pᵣ" => fun i j p q=>RX h i j p q k
local notation "Pᵤ" => fun i j p q=>UX h i j p q k
def wage (h:ℝ→ℝ)(s:Slip): Slip:= s.roof h *ₑ s
lemma Worth_w (i:σ→ℝ)(s:Slip)(u:Worth i s): Worth (fun x=> weight h (i x)) (wage h s):= ( u.layer hp ).mul u
def vStub : Bool→Bool→Slip
  | false,false=>((num (-16 * Λ)) *ₑ (((((num (-a ^ 2 * b ^ 2 - a ^ 2 * c ^ 2)) +ₑ ((num (a ^ 2 * c)) *ₑ xv)) -ₑ ((num (a ^ 2 * c)) *ₑ yv)) +ₑ (((num (a ^ 2)) *ₑ xv) *ₑ yv)) +ₑ (((num (b ^ 2)) *ₑ xv) *ₑ yv)))
  | false,true=>((num (-16 * Λ)) *ₑ (((num (-a * b ^ 2 * c - a * c ^ 3)) +ₑ ((num (a * c ^ 2)) *ₑ xv)) +ₑ (((num (b ^ 2)) *ₑ xv) *ₑ yv)))
  | true,false=>((num (-16 * Λ)) *ₑ (((num (-a * b ^ 2 * c - a * c ^ 3)) -ₑ ((num (a * c ^ 2)) *ₑ yv)) +ₑ (((num (b ^ 2)) *ₑ xv) *ₑ yv)))
  | true,true=>((num (16)) *ₑ ((((num (Λ * b ^ 2 * c ^ 2)) -ₑ (((num (Λ * b ^ 2)) *ₑ xv) *ₑ yv)) +ₑ (num (Λ * c ^ 4))) +ₑ (((num (a ^ 2 * b ^ 2)) *ₑ xv) *ₑ yv)))
omit hp
lemma rated_v (i j:Bool): Worth (fun x:σ=>vCard k x.1 x.2 i j) ( vStub k i j ) := by
   cases i <;> cases j
   · exact (( Worth.c (-16 * Λ)).mul ((((( Worth.c (-a ^ 2 * b ^ 2 - a ^ 2 * c ^ 2)).add (( Worth.c (a ^ 2 * c)).mul Worth.x)).sub (( Worth.c (a ^ 2 * c)).mul Worth.y)).add ((( Worth.c (a ^ 2)).mul Worth.x).mul Worth.y)).add ((( Worth.c (b ^ 2)).mul Worth.x).mul Worth.y)))
   · exact (( Worth.c (-16 * Λ)).mul ((( Worth.c (-a * b ^ 2 * c - a * c ^ 3)).add (( Worth.c (a * c ^ 2)).mul Worth.x)).add ((( Worth.c (b ^ 2)).mul Worth.x).mul Worth.y)))
   · exact (( Worth.c (-16 * Λ)).mul ((( Worth.c (-a * b ^ 2 * c - a * c ^ 3)).sub (( Worth.c (a * c ^ 2)).mul Worth.y)).add ((( Worth.c (b ^ 2)).mul Worth.x).mul Worth.y)))
   · exact (( Worth.c (16)).mul (((( Worth.c (Λ * b ^ 2 * c ^ 2)).sub ((( Worth.c (Λ * b ^ 2)).mul Worth.x).mul Worth.y)).add ( Worth.c (Λ * c ^ 4))).add ((( Worth.c (a ^ 2 * b ^ 2)).mul Worth.x).mul Worth.y)))
include hp
lemma vnote (i j:Bool): Worth (assay Pᵥ i j) ( vStub k i j *ₑ ((wage h (startW k i)) *ₑ (wage h (endW k j))) ) := by
    unfold assay; simp_rw [folded_v];
    obtain A:=paidStart k i
    obtain B:=paidEnd k j
    exact ( rated_v k i j ).mul (( Worth_w hp _ _ A ).mul ( Worth_w hp _ _ B ))
lemma vReady : Ready Pᵥ:= fun i j=>( vnote hp k i j ).clean
set_option maxRecDepth 6000 in
set_option maxHeartbeats 800000 in
lemma vS : survey Pᵥ=16*Λ^2*(h Λ)^2*(-Λ*a^2 - 4*Λ*b^2 + a^2*b^2):= by
    unfold survey; simp_rw [ ( vnote hp k _ _ ).taxes ]; simp only [ Fintype.sum_bool,
       vStub,wage,startW,endW, θ, Bool.false_eq_true,
       ↓reduceIte,  num,tied,both,roof,constant,xv,yv,Slip.fst,Slip.snd,negS,
       zero_mul,mul_zero,add_zero,zero_add,mul_one,neg_zero ]; ring
def uStub : Bool→Bool→Slip
  | false,false=>((num (8 * Λ)) *ₑ (((num (-b ^ 2 - c ^ 2)) +ₑ ((num (c)) *ₑ xv)) +ₑ ((num (c)) *ₑ yv)))
  | true,true=>(num (-8 * Λ * c ^ 2))
  | false,true=>(num (0))
  | true,false=>(num (0))
omit hp
lemma rated_u (i j:Bool): Worth (fun x:σ=>uCard k x.1 x.2 i j) ( uStub k i j ) := by
   cases i <;> cases j
   · exact (( Worth.c (8 * Λ)).mul ((( Worth.c (-b ^ 2 - c ^ 2)).add (( Worth.c (c)).mul Worth.x)).add (( Worth.c (c)).mul Worth.y)))
   · exact ( Worth.c (0))
   · exact ( Worth.c (0))
   · exact ( Worth.c (-8 * Λ * c ^ 2))
include hp
lemma unote (i j:Bool): Worth (assay Pᵤ i j) ( uStub k i j *ₑ (wage h (centerW k i j)) ) := by
    unfold assay; simp_rw [folded_u];
    obtain C:=paidCenter k i j
    exact ( rated_u k i j ).mul ( Worth_w hp _ _ C )
lemma uReady : Ready Pᵤ:= fun i j=>( unote hp k i j ).clean
set_option maxRecDepth 6000 in
set_option maxHeartbeats 800000 in
lemma uS : survey Pᵤ=-16*Λ*( 2*Λ*a^2*c^2*deriv (deriv h) Λ + 2*Λ*b^2*c^2*deriv (deriv h) Λ + Λ*b^2*deriv h Λ + 2*Λ*c^4*deriv (deriv h) Λ + 4*Λ*c^2*deriv h Λ + 4*a^2*c^2*deriv h Λ + 4*b^2*c^2*deriv h Λ + b^2*h Λ + 4*c^4*deriv h Λ + 4*c^2*h Λ ):= by
    unfold survey; simp_rw [ ( unote hp k _ _ ).taxes ]; simp only [ Fintype.sum_bool,
       uStub,wage,startW,centerW, θ, Bool.true_eq,Bool.false_eq_true,
       ↓reduceIte, num,tied,both,roof,constant,xv,yv,Slip.fst,Slip.snd,
       zero_mul,mul_zero,add_zero,zero_add,mul_one ]; ring
def rStub : Bool→Bool→Slip
  | false,false=>(((num (-32 * Λ)) *ₑ (((num (Λ)) -ₑ ((num (2 * c)) *ₑ xv)) +ₑ (xv *ₑ xv))) *ₑ ((((num (-a ^ 2 * b ^ 2 - a ^ 2 * c ^ 2)) +ₑ ((num (a ^ 2 * c)) *ₑ xv)) +ₑ ((num (a ^ 2 * c)) *ₑ yv)) +ₑ (((num (b ^ 2)) *ₑ xv) *ₑ yv)))
  | false,true=>(((num (32 * Λ)) *ₑ (((num (Λ)) -ₑ ((num (2 * c)) *ₑ xv)) +ₑ (xv *ₑ xv))) *ₑ ((((((num (a * b ^ 2 * c)) -ₑ ((num (a * b ^ 2)) *ₑ xv)) +ₑ (num (a * c ^ 3))) -ₑ ((num (2 * a * c ^ 2)) *ₑ xv)) +ₑ ((num (a * c)) *ₑ (xv *ₑ xv))) -ₑ (((num (b ^ 2)) *ₑ xv) *ₑ yv)))
  | true,false=>(((num (-32 * Λ)) *ₑ (((num (Λ)) +ₑ ((num (2 * a)) *ₑ xv)) +ₑ (xv *ₑ xv))) *ₑ ((((((num (-a * b ^ 2 * c - a * c ^ 3)) +ₑ ((num (a * c ^ 2)) *ₑ yv)) -ₑ ((num (b ^ 2 * c)) *ₑ xv)) +ₑ (((num (b ^ 2)) *ₑ xv) *ₑ yv)) -ₑ ((num (c ^ 3)) *ₑ xv)) +ₑ (((num (c ^ 2)) *ₑ xv) *ₑ yv)))
  | true,true=>((num (32 * Λ)) *ₑ ((((((((num (Λ * b ^ 2 * c ^ 2)) -ₑ (((num (Λ * b ^ 2)) *ₑ xv) *ₑ yv)) +ₑ (num (Λ * c ^ 4))) +ₑ (((num (a ^ 2 * b ^ 2)) *ₑ xv) *ₑ yv)) +ₑ ((num (2 * a * b ^ 2 * c ^ 2)) *ₑ xv)) +ₑ ((num (2 * a * c ^ 4)) *ₑ xv)) +ₑ ((num (b ^ 2 * c ^ 2)) *ₑ (xv *ₑ xv))) +ₑ ((num (c ^ 4)) *ₑ (xv *ₑ xv))))
omit hp
lemma rated_r (i j:Bool): Worth (fun x:σ=>rCard k x.1 x.2 i j) ( rStub k i j ) := by
   cases i <;> cases j
   · exact ((( Worth.c (-32 * Λ)).mul ((( Worth.c (Λ)).sub (( Worth.c (2 * c)).mul Worth.x)).add Worth.x.square)).mul (((( Worth.c (-a ^ 2 * b ^ 2 - a ^ 2 * c ^ 2)).add (( Worth.c (a ^ 2 * c)).mul Worth.x)).add (( Worth.c (a ^ 2 * c)).mul Worth.y)).add ((( Worth.c (b ^ 2)).mul Worth.x).mul Worth.y)))
   · exact ((( Worth.c (32 * Λ)).mul ((( Worth.c (Λ)).sub (( Worth.c (2 * c)).mul Worth.x)).add Worth.x.square)).mul (((((( Worth.c (a * b ^ 2 * c)).sub (( Worth.c (a * b ^ 2)).mul Worth.x)).add ( Worth.c (a * c ^ 3))).sub (( Worth.c (2 * a * c ^ 2)).mul Worth.x)).add (( Worth.c (a * c)).mul Worth.x.square)).sub ((( Worth.c (b ^ 2)).mul Worth.x).mul Worth.y)))
   · exact ((( Worth.c (-32 * Λ)).mul ((( Worth.c (Λ)).add (( Worth.c (2 * a)).mul Worth.x)).add Worth.x.square)).mul (((((( Worth.c (-a * b ^ 2 * c - a * c ^ 3)).add (( Worth.c (a * c ^ 2)).mul Worth.y)).sub (( Worth.c (b ^ 2 * c)).mul Worth.x)).add ((( Worth.c (b ^ 2)).mul Worth.x).mul Worth.y)).sub (( Worth.c (c ^ 3)).mul Worth.x)).add ((( Worth.c (c ^ 2)).mul Worth.x).mul Worth.y)))
   · exact (( Worth.c (32 * Λ)).mul (((((((( Worth.c (Λ * b ^ 2 * c ^ 2)).sub ((( Worth.c (Λ * b ^ 2)).mul Worth.x).mul Worth.y)).add ( Worth.c (Λ * c ^ 4))).add ((( Worth.c (a ^ 2 * b ^ 2)).mul Worth.x).mul Worth.y)).add (( Worth.c (2 * a * b ^ 2 * c ^ 2)).mul Worth.x)).add (( Worth.c (2 * a * c ^ 4)).mul Worth.x)).add (( Worth.c (b ^ 2 * c ^ 2)).mul Worth.x.square)).add (( Worth.c (c ^ 4)).mul Worth.x.square)))
include hp
lemma rnote (i j:Bool): Worth (assay Pᵣ i j) ( rStub k i j *ₑ ((startW k i).roof h *ₑ wage h (centerW k i j)) ) := by
    unfold assay; simp_rw [folded_r];
    obtain A:=paidStart k i
    obtain C:=paidCenter k i j
    exact ( rated_r k i j ).mul (( A.layer hp ).mul ( Worth_w hp _ _ C ))
lemma rReady : Ready Pᵣ:= fun i j=>( rnote hp k i j ).clean
set_option maxRecDepth 6000 in
set_option maxHeartbeats 800000 in
lemma rS : survey Pᵣ=32*Λ^2*(h Λ)^2*(-4*Λ*b^2 - Λ*c^2 + a^2*b^2):= by
    unfold survey; simp_rw [ ( rnote hp k _ _ ).taxes ]; simp only [ Fintype.sum_bool,
       rStub,wage,startW,centerW, θ, Bool.true_eq,Bool.false_eq_true,
       ↓reduceIte, num,tied,both,roof,constant,xv,yv,Slip.fst,Slip.snd,negS,
       zero_mul,mul_zero,add_zero,zero_add,mul_one,neg_zero ]; ring

end
end YM.SignedWilsonExpansion.Overlap

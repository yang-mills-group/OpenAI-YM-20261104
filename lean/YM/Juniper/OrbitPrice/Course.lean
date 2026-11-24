import YM.Juniper.OrbitPrice.Eject
/-!
 # Cutoff-uniform pass consumer with actual nonlinear UV scale contraction

 Local defect only on exact Phi of MIXED input (perturbative NEW E only),
 same p, true inherited K (no update across defect). Avoid dependence on
 q (=period index) or hypotheses of a coupling/reset match beyond ONE step.
 preserve full EBound / Valid / affine etc for callers. Requires subsequent
 audit to supply Model choices in SAME orbit (see Note).
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Native
open UVExtension Function Filter Set Lattice Wilson RG Shoot Supply Pressure Precision
open Org PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset
open Shoot Org
open ThroughLaunch Roof Roost Input Progress.DirectedRecipe Time Camp Oriel
open Tabernacle Dales Guild Spire
open scoped Topology BigOperators InnerProductSpace Classical
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A) (hG:G.Simple)
    (S : Spire.Uses R hG) (N n : ℕ)
local notation "B" => A.B.a
local notation "Y#"=> S.fits N n
local notation "Fn"=> S.cart N n
variable (b : ℝ) (hb : (b:ℂ)∈ Camp.Broad A.B.a)

def genes (i:ℕ):= (Y#).Rest Fn S.grove.coins b i
local notation "x!"=> genes R hG S N n b -- check binder order
local notation "β!"=> (Y#).Third Fn S.grove.coins b
local notation "s!" => (Y#).Sail Fn S.grove.coins b
local notation "ε" => S.grove.witness
local notation "ζ" => S.grove.pledge
local notation "κ" => S.realBeat b N n
set_option quotPrecheck false
local notation "φ" => (S.fits N n).W

def model   {i:ℕ}(y:(S.fits N n).Home i):=
  merge y ((S.fits N n).Rest Fn S.grove.coins b i)
local notation "C!"=> model R hG S N n b
def analyticPass (i:ℕ)(hi:i<N) (y:(S.fits N n).Home (i+1)) :=
  ((Y#).charts i hi).choiceV R hG ζ _ ((Y#).shirts i hi) (C! y) (β! (i+1))
def pulsePass (i:ℕ)(hi:i<N) (y:(S.fits N n).Home (i+1)) :=
  A.B.kin.alpha N i + ((Y#).charts i hi).claim R _ (C! y) (β! (i+1))
def output (i:ℕ)(hi:i<N) (y:(S.fits N n).Home (i+1)):=
  let β:= β! (i+1)
  mount R N i n (analyticPass R hG S N n b i hi y|>.val) (β + pulsePass R hG S N n b i hi y)
    (flatRate B i n (mount R N (i+1) n (C! y|>.val) β (s! (i+1))))
def input (i:ℕ) (y:(S.fits N n).Home i):=
  mount R N i n (C! y|>.val) (β! i) (s! i)
local notation "Ψ"=> input R hG S N n

lemma actual (i:ℕ) : (S.realBeat b N n i)=mount R N i n ((x! i)|>.val) (β! i) (s! i) := rfl

variable (y: ∀ i:ℕ,(S.fits N n).Home i)
local notation "d"=> fun i=> ‖trueE (x! i) - trueE (y i)‖
local notation "L"=> analyticPass R hG S N n
local notation "P"=> pulsePass R hG S N n
local notation "Φ"=> output R hG S N n
include hb
private lemma expose :
    (Y#).Shot x! β! s! ∧ β! 0=A.B.a.clock.bar+b ∧ ∀ i≤N, ‖place B i n (φ i) (x! i)‖ ≤ soft := by
  let H:=Y#; obtain ⟨hT,hX⟩:= (Y#).acts Fn (S.token N n) S.grove.coins hb
  exact ⟨hT,hX,fun i hi=> (H.plates S.grove.enabled S.grove.climbed hT hb hX i hi).1⟩

-- single consumer even with varying output shell threshold. exports Actual K bounds.
lemma native (i:ℕ)(hi : i<N)(he:‖trueE (y (i+1))‖<rim):
    let U:= x! i; let Y:= L b i hi (y (i+1)); let K:= Φ b i hi (y (i+1)); let X':= Ψ b (i+1) (y (i+1))
    ‖place B i n (φ i) U - place B i n (φ i) Y‖≤ soft * (d (i+1)) ∧
      |(κ i|>.beta)-(κ (i+1)|>.beta)-P b i hi (y (i+1))| ≤ worth B (i+1)*(d (i+1)) ∧
      (∀ x : Config G ((B).S.side (i+1) n), (κ (i+1)|>.eval) x=X'.eval x * Real.exp (- (Tabernacle.floor (A.B.a.budget (i+1)) (x! (i+1)-y (i+1)).val).additive (A.B.a.budget (i+1)) x)) ∧
      K.eval=(A.B.a.clock.op i n).push (κ (i+1)|>.beta) X'.eval ∧ 0 < K.eval 1 ∧
      ‖place B i n (φ i) Y‖≤ soft ∧ K.activities.KBound (A.B.a.budget i) (Return.forcing A.B i) ∧
      (κ i|>.activities).KBound (A.B.a.budget i) (Return.forcing A.B i) ∧
      (κ i|>.eval)=(A.B.a.clock.op i n).push (κ (i+1)|>.beta) (κ (i+1)|>.eval) := by
  obtain ⟨h,h',hS⟩:= expose R hG S N n b hb
  let f:=x!; let Y:=L b i hi (y (i+1)); let E:= Y#; let a:=s! (i+1)
  intro U Y₀ K X'
  have hz := h.alive (i+1) hi; have hx:= (Y#).doors h i hi; let hΔ:= hx.2.1
  let hE : ‖place B (i+1) n (φ (i+1)) (f (i+1))‖<rim:= (hS (i+1) hi).trans_lt (by norm_num [soft,rim])
  obtain ⟨hf,hU,hq,hK,H,hh⟩ := actual_defect R hG ζ ((Y#).charts i hi) S.grove.enabled (φ (i+1)) ((Y#).shirts i hi) a ((Y#).rootc h hb h' _ hi) hz.1 hE he -- wait argument order
  let t':= β! (i+1); let W:=(Y#).charts i hi
  let u:= (W.choiceV R hG ζ _ ((Y#).shirts i hi) (x! (i+1)) t'); let v:= W.claim R _ (x! (i+1)) t'
  let q:= t'+A.B.kin.alpha N i; let q':=q+ W.claim R _ (C! (y (i+1))) t'
  have he:u=U:= by unfold u;rw [Tour.choiceV, dif_pos hz]; exact hx.2.1.symm
  have hk: (κ i).beta = q+v:= by unfold v; rw [Tour.claim,dif_pos hz]; exact hx.1
  have hy' : |(κ i).beta-t'-P b i hi (y (i+1))|≤ worth B (i+1)*(d (i+1)) := by
     rw [hk, show q+v-t'-P b i hi (y (i+1)) = (q+v)-q' by unfold q' q pulsePass; ring]; exact hU  -- β⁺
  -- syntactic rewriting associativity inside K cumbersome; give macro
  refine ⟨he ▸ hf, hy', fun x=>separated R _ a x, ?_,?_,H,?_,?_,?_⟩
  · dsimp only [K,output,pulsePass]; rw [← add_assoc]; exact hq
  · dsimp only [K,output,pulsePass]; rw [← add_assoc]; exact hK.trans_eq (congr_fun hq.symm 1)
  · exact hh -- K.activities defeq
  · rw [show κ i= _ from h.passes i hi]; exact (synthetic R hG ζ W _ hz _).2.2.2
  rw [show κ i= _ from h.passes i hi]; exact (synthetic R hG ζ W _ hz _).1
end YM.Juniper.Native

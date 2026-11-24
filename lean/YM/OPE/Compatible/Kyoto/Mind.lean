import YM.OPE.Compatible.Kyoto.Brawn
import YM.OPE.Compatible.Kyoto.Ploy
import YM.OPE.Compatible.Kyoto.Team
import YM.OPE.Compatible.Kyoto.Cloud
import YM.OPE.Compatible.Kyoto.Gazer
import YM.OPE.Compatible.Kyoto.Opal
import YM.OPE.Compatible.Kyoto.TreeQ
import YM.OPE.Compatible.Ice.Ares
import YM.OPE.Compatible.Nut.Hero
import YM.OPE.Compatible.Silva.Bride
import YM.OPE.Compatible.Kyoto.Room
/-!
# Transport of a single coefficient observation

`RequestZ` gives a coarse-period threshold for a pair of exponents.
For `-11/10 < v < t'`, when the coarse period eventually exceeds or
equals this threshold and the matching and rate hypotheses hold,
`LeapYear` bounds the difference between the coarse observation
and the scaled, transported fine observation at upper rate `t'`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I :Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}

variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full GlowPack Yolk Pipes Dial Raucous Zeph Zeph.Dew Borealis Flume.Script 
open Next.Free
section
variable {L:PriceBook H T}{a:Axis}
namespace MatchZ

section
open Lass.Zest Lass PhysicalNext.Repeat.Aroma Pressure ConnectedActivityE6 Shell Channel
variable {Ξ:Medal P' G K.K P'.J} {P₀:Teller G}
variable {E:ConnectedActivityE6.Target G P₀} {Q:Side}{W C κ:ℝ}{o:ConnectedActivityE6.Target.Order G W}
variable (F:I→Mug P' p p' T j R Ξ)
variable (L₁:∀ i,Wall P' E Q o κ C k (F i).hostS){l₀:Filter I} (hq:Chase (Eve L₁) l₀)
local notation "ζ"=>Eve L₁
local notation "X*!"=> fate (Eve L₁)
variable {β ε:I→ℝ}
set_option quotPrecheck false
variable (R1:ℝ)(hV:∀ i,|MatchZ.fare ((F i).row)|≤R1)(hv:Mag P'.J j) (hp:Wage (Eve L₁) l₀ (fun i=> (F i).row.fine.fees) 0)
set_option quotPrecheck false
open Limn
open Spells Labels Source Cameo Yolk Pill Lass.Zest.Torch Ibis
variable (V:Foyer L hs a l (d+6)){he:highStage L hs a V ≤ P'.J} {he':highStage L hs a V ≤ j}
variable (X:BankW L hs a V he p)
variable (Y:BankW L hs a V he' p')
variable (hz: Shear L₁ (fun i=>(F i).pV) l₀ β)
variable {c r' t:ℝ}(H₀:StackP R c r' t)
variable {A:Labels.Frame G l}{U₀:Hol G}{S:SectionData A}
variable {M:∀i,A.Coeff → Coefficient A (F i).f}{N:∀i,A.Coeff → Coefficient A (F i).c} {η γ:I→ℝ}
variable (P₁:∀ i,Torch S U₀ 0 (F i|>.pW) (M i) d (η i))
variable (P₂:∀ i,Torch S U₀ 0 (F i|>.pV) (N i) d (γ i))
variable (hf:Torch.BondS P₁ (βM (Eve L₁)) l₀ (Chase.σW (Eve L₁)))(hc:Torch.BondS P₂ β l₀ ε)
variable (hΔ: Cameo.Quench (fate (Eve L₁)) l₀ (fun i=> (F i).pW.beta) (fun i=> (F i).pV.beta) (fun i=> (F i).row.fare) (Chase.σW (Eve L₁)) ε)
variable (H0: ∀ᶠ i in l₀,(F i).pV.eval=(F i).hostS.Z.push (F i).pW.beta (F i).pW.eval)
local notation "κS"=> Chase.σW ζ
local notation "δh"=> (P'.L.val:ℝ)^l
variable (z:I→A.Coeff)(z':I→A.Coeff)
variable (hM: Receipt (βM (Eve L₁)) l₀ z)(hN:Receipt β l₀ z')
variable (hF:∀ᶠ i in l₀,(N i (z' i)).density 0 S (F i|>.pV)= ((P'.L.val:ℝ)^l) • ((F i|>.hostS.Z).push (F i|>.pW.beta) ((M i (z i)).density 0 S (F i|>.pW))))
variable (R'':Spells.Pad G)(e':ℂ→L[ℝ]ℝ) (hK:  Wage (Eve L₁) l₀ (fun i=> ((↑(F i).c.val:ℝ))⁻¹) v)(hq':-(11/10:ℝ)< v)
local notation "T1*"=>fun i=> tintX V (he:=he) (P₁ i) (F i).row.fine R'' ((Chase.σW (Eve L₁)) i) e' (z i)
local notation "T2*"=>fun i=> tintX V (he:=he') (P₂ i) (F i).row.coarse R'' (ε i) e' (z' i)
local notation "W˘"=>fun i=> Ibis.vintage G V.pay.st.hτ ((F i).row.fare) ((T2*) i)-((P'.L.val:ℝ)^l) • Flail (F i) V ((T1*) i)
local notation "ΖQ"=> V.pay.st
abbrev RequestZ (hx:4 ≤ j)(hb:l+6≤ m)(ξ υ:ℝ)(h:ξ<υ)(ht:-(11/10:ℝ)< ξ)(UU_:Type):ℝ→ℕ:=Classical.choose (Ibis.Hear (I:=UU_) G K.K hx V.pay.st.τ (d+6) V.pay.st.hτ h (show l+1+6≤ m+1 from by omega) (show -(1/2:ℝ)≤0 by norm_num) (show 3*(-(1/2:ℝ))≤ ξ by linarith))
variable {t':ℝ} 
local notation "ZT"=> fun i=> Stint V (F i|>.row) Ξ
local notation "N*"=> fun i=> (F i).row.coarse
local notation "C*"=> fun i=> (F i).row.fine
local notation "Á"=> FaithV
variable (heL:l+6≤d)(hT:v<t')(hW:∀ᶠ i in l₀, RequestZ (P':=P') (j:=j) V (hazard V he') heL v t' hT hq' I (fate (Eve L₁) i) ≤ (F i).c.val)(hC:Wage (Eve L₁) l₀ (fun i=> (F i).row.coarse.fees) 0)(hB:P'.L= V.pay.st.S.L^m)
include hf hM in
private lemma submittedFine : Alive l₀ (fate (Eve L₁)) (T1*) :=
  hf.FineB z hM (fun i => (F i).row.fine.ℳ.gear) P'.order_cut R'' e' V.pay.st.hτ

include hc hN in
private lemma submittedCoarse : Alive l₀ (Counters β) (T2*) :=
  hc.FineB z' hN (fun i => (F i).row.coarse.ℳ.gear) (hazard V he') R'' e' V.pay.st.hτ

include hq hz in
private lemma shareClock (source : I → solar G (d+6) V.pay.st.τ)
    (cost : Alive l₀ (Counters β) source) : Alive l₀ (fate (Eve L₁)) source := by
  intro m
  obtain ⟨bound, rate, paid⟩ := cost m
  exact ⟨bound, foTest hq.high hz.Currency rate, paid⟩

private abbrev hearingReceipt :=
  Γsprig F L₁ hq hp V hz H₀ P₁ P₂ hf hc hΔ H0 z z' hM hN hF R'' e' hK hq'
    (he := he) (he' := he')

private abbrev operatorPrice :=
  StintCost V Ξ (fun i => (F i).row) R1 hV hq.tense hp hv

private abbrev actorReceipt :=
  Eventually.of_forall (f := l₀) (fun i => Alc (F i) V ((T1*) i) he he')

private abbrev transferFront :=
  Fickle (r := m) (e := d) (u := -(1/2:ℝ)) (L := l₀) (Xη := fate (Eve L₁))
    (W' := Chase.σW (Eve L₁)) (α := fun _ => (P'.L.val:ℝ)^l)
    X.cart (C*) (N*) Y.cart (T1*) (ZT)
    (Eventually.of_forall fun i => StampP (he' := he) V (F i).row Ξ hB) hq.tense hp hC
    (operatorPrice (F := F) (L₁ := L₁) (hq := hq) (V := V) (R1 := R1)
      (hV := hV) (hp := hp) (hv := hv)) (hΔ.fine.pays hq.tense) (by norm_num)

include hq hf hc hΔ hF hM hN hW hT hC hB hK hq' hz heL H0 hv H₀ hp hV X Y P₁ P₂ F K R1 z z' ε e'
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
private abbrev rebookedTransfer :=
  let fine := T1*
  let coarse := T2*
  let moved := fun i => Flail (F i) V (fine i)
  let a : Alive l₀ (fate (Eve L₁)) fine := submittedFine (F := F) (L₁ := L₁) (V := V)
    (he := he) (P₁ := P₁) (hf := hf) (z := z) (hM := hM) (R'' := R'') (e' := e')
  let b : Alive l₀ (Counters β) coarse := submittedCoarse (F := F) (V := V)
    (he' := he') (P₂ := P₂) (hc := hc) (z' := z') (hN := hN) (R'' := R'') (e' := e')
  let paid := shareClock (F := F) (L₁ := L₁) (hq := hq) (V := V) (hz := hz) coarse b
  let movedPaid : Alive l₀ (fate (Eve L₁)) moved := Flail_pay V F hq.tense hp a
  transferFront (F := F) (L₁ := L₁) (hq := hq) (hp := hp) (R1 := R1)
    (hV := hV) (hv := hv) (hC := hC) (V := V) (X := X) (Y := Y) (P₁ := P₁)
    (z := z) (R'' := R'') (e' := e') (hΔ := hΔ) (hB := hB)
    coarse moved (N := fun i => (F i).c) (fun i => (0:Site (F i).c))
    (β := fun i => (F i).row.fare) movedPaid paid (RateLE.const (δh) hq.tense) hΔ.toll v t' hT heL (by linarith only [hq'])
    Y.ear hW

private abbrev physicalTransfer :=
  let movedExactly := actorReceipt (F := F) (L₁ := L₁) (V := V) (he := he)
    (he' := he') (l₀ := l₀) (P₁ := P₁) (R'' := R'') (e' := e') (z := z)
  let heard := hearingReceipt (F := F) (L₁ := L₁) (hq := hq) (hp := hp) (V := V)
    (hz := hz) (H₀ := H₀) (P₁ := P₁) (P₂ := P₂) (hf := hf) (hc := hc)
    (hΔ := hΔ) (H0 := H0) (z := z) (z' := z') (hM := hM) (hN := hN)
    (hF := hF) (R'' := R'') (e' := e') (hK := hK) (hq' := hq') (he := he) (he' := he')
  let drift := hΔ.driftB.mono (show -(3/2:ℝ) ≤ t' by linarith only [hT, hq'])
  let a := submittedFine (F := F) (L₁ := L₁) (V := V) (he := he) (P₁ := P₁)
    (hf := hf) (z := z) (hM := hM) (R'' := R'') (e' := e')
  rebookedTransfer (F := F) (L₁ := L₁) (hq := hq) (R1 := R1) (hV := hV)
    (hv := hv) (hp := hp) (V := V) (X := X) (Y := Y) (hz := hz)
    (P₁ := P₁) (P₂ := P₂) (hf := hf) (hc := hc) (hΔ := hΔ)
    (z := z) (z' := z') (hM := hM) (hN := hN)
    (R'' := R'') (e' := e') (hq' := hq') (heL := heL) (hT := hT)
    (hW := hW) (hC := hC) (hB := hB) (by
      with_reducible exact movedExactly) heard (Ω := ε)
    ((hΔ.wide.pays hq.tense).mono (by norm_num)) drift (a.score hq.tense)

lemma LeapYear : Wage (Eve L₁) l₀ (fun i=> FaithV V Y (P₂ i) ((N*) i) R'' (ε i) (z' i) e' - (δh) • (τΡ X.cart ((C*) i) Y.cart ((N*) i) ((ZT) i) ((Chase.σW ζ) i) (FaithV V X (P₁ i) ((C*) i) R'' ((Chase.σW ζ) i) (z i) e'))) t':=by
  with_reducible
    exact physicalTransfer (F := F) (L₁ := L₁) (hq := hq) (R1 := R1) (hV := hV)
      (hv := hv) (hp := hp) (V := V) (X := X) (Y := Y) (hz := hz) (H₀ := H₀)
      (P₁ := P₁) (P₂ := P₂) (hf := hf) (hc := hc) (hΔ := hΔ) (H0 := H0)
      (z := z) (z' := z') (hM := hM) (hN := hN) (hF := hF)
      (R'' := R'') (e' := e') (hK := hK) (hq' := hq') (heL := heL)
      (hT := hT) (hW := hW) (hC := hC) (hB := hB)
end
end MatchZ
end
end YM.OPE.Stroke

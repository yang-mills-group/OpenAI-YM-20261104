import YM.OPE.Compatible.Cant.Orion
import YM.OPE.Compatible.Cant.Wiz
import YM.OPE.Compatible.Cant.View
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# The graded transport action on phase forms

`YM.OPE.Stroke.stamped` combines flow commutation, preservation of truncation, and the grade-wise pairing and scaling identities into a `Pipes.Stamp` for the induced action `Race`.
For pinned sites on sufficiently large even lattices at each grade, it also identifies the target port of a transported vector with the action on its source port.
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
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}{V:(i':M)→ Alps K T i (Y i')}{A':(i:ℕ)→ Submodule ℝ (Bead G l i)}{hq:1 ≤ Y}{hp:4 ≤ i}{U:Z.Ω M Y}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) -- use
open Pipes
local notation "Sγ"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
variable {uα:I→ℝ}{A:(v:I)→Alps K T j (uα v)}
local notation "μ"=>lapPrice (Patch.L P)
section
variable (hX: Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)
variable {ht:4 ≤ j}{hz:1≤uα}{U':Z.Ω I uα}
variable (he: Z.Floss A U' ht (le_trans zero_le_one hz) k Hp a)(f':Tracts G d τ→L[ℝ] Tracts G d τ) (i':M)(j':I)
local notation "AC"=> Ace D₀ H hs a (V i') (A j') (zero_le_one.trans (hq i')) (zero_le_one.trans (hz j')) hp ht r f'
local notation "CΓ"=>Sapling (V:=A) (H:=H) (hs:=hs) (hq:=hz) (hp:=ht) (a:=a) (D₀:=D₀) j'
variable (h':∀ i,(A i).clip=p')(hv:l*l≤ τ 0)(L:Lance X)(T₀: Ace D₀ H hs a (V i') (A j') (zero_le_one.trans (hq i')) (zero_le_one.trans (hz j')) hp ht r f')
local notation "Vγ" e:max v:max => InVivid (U:=U) (U':=U') (hz:=hz) (A:=A) (ht:=ht) Z a f' i' j' e v
local notation "Cρ"=> Carries (hp:=hp) (ht:=ht) (hq:=hq) (V:=V) (A:=A) (hz:=hz) Z a f' U U' i' j'
local notation "A₁"=> Dux G l A'
-- Use the graded readouts associated with the reduction maps κ.
local notation "K*!"=> SternK (V:=V) (hq:=hq) (hp:=hp) Z a U
local notation "T*!"=> SternK (V:=A) (hp:=ht) (hq:=hz) Z a U'
private lemma stampFromForms {depth : ℕ} {W : Fin depth → Type}
    [∀ e, NormedAddCommGroup (W e)] [∀ e, NormedSpace ℝ (W e)]
    (price : ℕ → ℝ) (form : (e : Fin depth) → ℕ → ΦB (W e))
    (action : Mel W →ₗ[ℝ] Mel W) (order : ℕ)
    (flow : ∀ z, FlowP W (action z) = action (FlowP W z))
    (tested : ∀ e (p q : Jewel (W e)) j,
      form e 0 j (PDiag action e p) (PDiag action e q) = form e order j p q ∧
        (PDiag action e p) 0 = (price e.val)^order • p 0)
    (truncated : ∀ e, e ≤ depth → ∀ z, trims e z → trims e (action z)) :
    Pipes.Stamp (V := W) price form action order :=
  ⟨fun z => (flow z).symm, fun e p => (tested e p p 0).2,
    fun e p q j => (tested e p q j).1.symm, truncated⟩

include hX he hv h' L T₀
private abbrev selectedStamp {κ:(e:J!)→Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} (C:Bals Hp Z a A' κ) {M':(e:J!)→(m:M)→ Jewel (A' e.val)→ₗ[ℝ] U.flag e.val m} {P':(e:J!)→(m:I)→ Jewel (A' e.val)→ₗ[ℝ] U'.flag e.val m} (F:K*! κ M') (P'':T*! κ P') {m:J!→Side}{t:∀ i,Even (m i).val}(x y:∀ i,Site (m i))(hz':∀ i,barrier P ≤ (m i).val)(hw:∀ i,Pins K P (x i) (y i)) :=
  let action := Race (V := A₁) (R := M') P'' i' j' f'.toLinearMap
  let carried := poet (hq := hq) (hz := hz) Hp Z a hX he f' i' j' h' hv L T₀ C
  let tested (e : J!) := gramSigma (hq := hq) (hz := hz) Hp Z a hX he f' i' j'
    h' hv L T₀ e C F P'' (t e) (x e) (y e) (hz' e) (hw e)
  let flow := RaceDr F P'' i' j' f'.toLinearMap T₀.comm
  let stamp := stampFromForms (W := A₁) (lapPrice P.L)
    (fun e => TokZ Hp Z a e (A' e.val) (t e) (x e) (y e)) action r flow tested
    (fun e he w => RaceTrim F P'' i' j' f'.toLinearMap w e he (carried e he))
  And.intro stamp (fun x : F! => over F P'' i' j' f'.toLinearMap x (carried (l+1) le_rfl))

set_option maxHeartbeats 200000 in
lemma stamped {κ:(e:J!)→Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} (C:Bals Hp Z a A' κ) {M':(e:J!)→(m:M)→ Jewel (A' e.val)→ₗ[ℝ] U.flag e.val m} {P':(e:J!)→(m:I)→ Jewel (A' e.val)→ₗ[ℝ] U'.flag e.val m} (F:K*! κ M') (P'':T*! κ P') {m:J!→Side}{t:∀ i,Even (m i).val}(x y:∀ i,Site (m i))(hz':∀ i,barrier P ≤ (m i).val)(hw:∀ i,Pins K P (x i) (y i)) :
    let g:= Race (V:=Dux G l A') (R:=M') P'' i' j' f'.toLinearMap
    Pipes.Stamp (V:=Dux G l A') (lapPrice P.L) (fun e=>TokZ Hp Z a e (A' e.val) (t e) (x e) (y e)) g r ∧
      ∀ x:F!, port P'' j' (f' x)= g (port F i' x):=by
  exact selectedStamp (hq := hq) (hz := hz) Hp Z a hX he f' i' j' h' hv L T₀ C F P''
    x y hz' hw
end
end YM.OPE.Stroke

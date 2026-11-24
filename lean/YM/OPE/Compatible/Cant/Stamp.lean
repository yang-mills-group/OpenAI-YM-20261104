import YM.OPE.Compatible.Cant.Rose
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# Reading the diagonal action from a target representative

`YM.OPE.Stroke.SternK` specializes `Pipes` to the graded flag readouts.
`RoadsGate` computes the diagonal of the induced action `Race` from any target flag representative whose difference from the transported source lift lies in the target `Sapling` submodule.
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
noncomputable abbrev SternK (U:Z.Ω M Y)(κ:(e:J!)→Mint Z e.val →ₗ[ℝ] Jewel (A' e.val))(R:(e:J!)→(m:M)→Jewel (A' e.val)→ₗ[ℝ] U.flag e.val m):Prop:= Pipes (V:=Dux G l A') (E:=Tracts G d τ) U.flag Sγ (ReadK Z κ U) (Gift G D₀.aware).toLinearMap R
local notation "K*!"=> SternK (V:=V) (hq:=hq) (hp:=hp) Z a U
local notation "T*!"=> SternK (V:=A) (hp:=ht) (hq:=hz) Z a U'
-- The induced action on each grade is its diagonal.

-- Specialize the existing graded diagonal rule before choosing a flag representative.
private abbrev physicalDiagonal
    {κ : (e : J!) → Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}
    {M' : (e : J!) → (m : M) → Jewel (A' e.val) →ₗ[ℝ] U.flag e.val m}
    {P' : (e : J!) → (m : I) → Jewel (A' e.val) →ₗ[ℝ] U'.flag e.val m}
    (P'' : T*! κ P') :=
  PDiagD (d := l+1) (V := A₁) (E := F!) (F := F!) (M := M) (Q := I)
    (A := U.flag) (R := M') (B := U'.flag)
    (Y' := fun j => Sapling (V:=A) (H:=H) (hs:=hs) (hq:=hz) (hp:=ht) (a:=a) (D₀:=D₀) j)
    (W := ReadK Z κ U') (g' := (Gift G D₀.aware).toLinearMap) (S := P')
    (P := P'') i' j' f'.toLinearMap

set_option maxHeartbeats 200000 in
lemma RoadsGate (e:J!){κ:(e:J!)→Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} {M':(e:J!)→(m:M)→Jewel (A' e.val)→ₗ[ℝ] U.flag e.val m} {P':(e:J!)→(m:I)→Jewel (A' e.val)→ₗ[ℝ] U'.flag e.val m}(P'':T*! κ P')(v:Jewel (A' e.val))(q:U'.flag e.val j')(h:f' (M' e i' v|>.val)-q.val∈ CΓ): PDiag (Race (V:=Dux G l A') (R:=M') P'' i' j' f'.toLinearMap) e v= κ e (U'.read e.val e.isLt j' q):=by
  have coordinate := physicalDiagonal (hz := hz) (M' := M') (P' := P')
    (Z := Z) (a := a) (f' := f') (i' := i') (j' := j') P'' e v q h
  exact coordinate.trans (LinearMap.comp_apply (κ e) (U'.read e.val e.isLt j') q)
end
end YM.OPE.Stroke

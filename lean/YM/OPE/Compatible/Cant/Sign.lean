import YM.OPE.Compatible.Cant.Stamp
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# Target flag representatives for the graded diagonal

`YM.OPE.Stroke.laysQ` chooses a target flag representative for the transported source lift modulo the target residual submodule.
Its readout gives the grade-`e` diagonal of `Race` on the original vector, and its first readout component equals the original first component scaled by `(lapPrice P.L e.val)^r`.
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
include he h' hv L T₀ in
private lemma carriedFlag {κ : (e : J!) → Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}
    (C : Bals Hp Z a A' κ) (e : J!) (hx : Cρ e.val) (w : U.flag e.val i') :
    ∃ q : U'.flag e.val j', f' w.val - q.val ∈ CΓ ∧ q.val 0 = f' w.val 0 := by
  have hQ := hx w.val (le_sup_left (a := U.flag e.val i') w.property)
  have flag := (T₀.flag e.val e.isLt.le w.val 0 (trims.be _)).2
    ((U.quake e.val e.isLt i' w 0 (trims.be _)).1)
  exact Earth (hq := hz) Hp Z a U' h' he C hv L e.val e.isLt.le j' (f' w.val) hQ flag


private lemma carriedHead {κ : (e : J!) → Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}
    (C : Bals Hp Z a A' κ) (L' : AC) (e : J!) (p : U.flag e.val i')
    (q : U'.flag e.val j') (v : Jewel (A' e.val)) (head : q.val 0 = f' p.val 0)
    (read : κ e (U.read e.val e.isLt i' p) = v) :
    ReadK Z κ U' e j' q 0 = (μ e.val)^r • v 0 := by
  have phase := pupil (hp := hp) (ht := ht) (hq := hq) (hz := hz)
    Z a f' i' j' L' e p q head
  have heads := Bals.headLift Hp Z a C e (U'.read e.val e.isLt j' q)
    (U.read e.val e.isLt i' p) ((μ e.val)^r) phase
  exact heads.trans (congrArg (fun z : Jewel (A' e.val) => (μ e.val)^r • z 0) read)

include hX he hv h' L T₀ in
private lemma transportGrade {κ : (e : J!) → Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}
    (C : Bals Hp Z a A' κ) (e : J!) (p : U.flag e.val i') :
    ∃ q : U'.flag e.val j', f' p.val - q.val ∈ CΓ ∧ q.val 0 = f' p.val 0 := by
  have carried := poet (hq := hq) (hz := hz) Hp Z a hX he f' i' j' h' hv L T₀ C e.val e.isLt.le
  exact carriedFlag (Hp := Hp) (Z := Z) (a := a) (i' := i') (j' := j') (f' := f')
    (hq := hq) (hz := hz) (L := L) (he := he) (h' := h') (hv := hv) (T₀ := T₀) C e carried p

private lemma extendFlagRead {B : Type*} {residual first diagonal scaled : B → Prop}
    (representative : ∃ q, residual q ∧ first q)
    (read : ∀ q, residual q → diagonal q) (scale : ∀ q, first q → scaled q) :
    ∃ q, residual q ∧ diagonal q ∧ scaled q := by
  obtain ⟨q, rest, head⟩ := representative
  exact ⟨q, rest, read q rest, scale q head⟩

include hX he hv h' L T₀
set_option maxHeartbeats 200000 in
lemma laysQ (e:J!) {κ:(e:J!)→ Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} (C:Bals Hp Z a A' κ) {M':(e:J!)→(m:M)→ Jewel (A' e.val)→ₗ[ℝ] U.flag e.val m} {P':(e:J!)→(m:I)→ Jewel (A' e.val)→ₗ[ℝ] U'.flag e.val m} (F:K*! κ M') (P'':T*! κ P')(v:Jewel (A' e.val)): ∃ q:U'.flag e.val j',f' (M' e i' v|>.val)-q.val∈ CΓ ∧ PDiag (Race (V:=Dux G l A') (R:=M') P'' i' j' f'.toLinearMap) e v= κ e (U'.read e.val e.isLt j' q) ∧ ReadK Z κ U' e j' q 0= (μ e.val)^r • (v 0) :=by
  let p := M' e i' v
  have representative := transportGrade (hq := hq) (hz := hz) Hp Z a hX he f' i' j' h' hv L T₀ C e p
  have read : κ e (U.read e.val e.isLt i' p) = v := Pipes.toll F e i' v
  have diagonal := RoadsGate (ht := ht) (A := A) (hz := hz) (M' := M') Z a f' i' j' e P'' v
  exact extendFlagRead representative diagonal (fun q head =>
    carriedHead (hq := hq) (hz := hz) Hp Z a f' i' j' C T₀ e p q v head read)
end
end YM.OPE.Stroke

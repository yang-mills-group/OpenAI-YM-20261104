import YM.OPE.Compatible.Cant.Xy
import YM.OPE.Compatible.Cant.Wiz
import YM.OPE.Compatible.Cant.View
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# Pairings and the first component of a graded diagonal

For pinned sites on an even lattice satisfying the barrier bound, `YM.OPE.Stroke.gramSigma` identifies the order-zero pairing of two images under the grade-`e` diagonal of `Race` with their order-`r` pairing.
The same diagonal multiplies the first component by `(lapPrice P.L e.val)^r`.
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
lemma hermZ (X:E→ Q)(g:Q→ E)(M:Q→ Q)(P:E→F→Prop)(T:F→Q)(h:∀ z,∃ w:F,P (g z) w∧ M z=T w)(hf:∀ x,X (g x)=x)(A B:Q→Q→ℝ)(hA:∀ x y p q,P x p→ P y q→ A (T p) (T q)=B (X x) (X y))(v w:Q) : A (M v) (M w)=B v w:=by
       obtain ⟨p,hp,hx⟩:=h v; obtain ⟨q,hq,hy⟩:=h w; rw [hx,hy,hA _ _ p q hp hq,hf,hf]
private lemma pairAndHead {W : Type*} (source : E → Q) (lift : Q → E) (matrix : Q → Q)
    (related : E → F → Prop) (target : F → Q) (first scaled : Q → W)
    (rows : ∀ z, ∃ p, related (lift z) p ∧ matrix z = target p ∧ first (target p) = scaled z)
    (recover : ∀ z, source (lift z) = z) (left right : Q → Q → ℝ)
    (forms : ∀ x y p q, related x p → related y q → left (target p) (target q) = right (source x) (source y))
    (u v : Q) : left (matrix u) (matrix v) = right u v ∧ first (matrix u) = scaled u := by
  have gram := hermZ source lift matrix related target (fun z => by
    obtain ⟨p, hp, hm, _⟩ := rows z
    exact ⟨p, hp, hm⟩) recover left right forms u v
  obtain ⟨p, _, eq, head⟩ := rows u
  exact ⟨gram, (congrArg first eq).trans head⟩

include hX he hv h' L T₀
private abbrev comparePhysicalForms (e:J!) {κ:(e:J!)→ Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} (C:Bals Hp Z a A' κ) {M':(e:J!)→(m:M)→ Jewel (A' e.val)→ₗ[ℝ] U.flag e.val m} {P':(e:J!)→(m:I)→ Jewel (A' e.val)→ₗ[ℝ] U'.flag e.val m} (F:K*! κ M') (P'':T*! κ P') (t:Even n.val)(x y: Site n)(hz':barrier P≤ n.val)(hx:Pins K P x y)(j : Phase) :=
  let f := PDiag (Race (V := Dux G l A') (R := M') P'' i' j' f'.toLinearMap) e
  let L' (order : ℕ) := TokZ Hp Z a e (A' e.val) t x y order j
  let rows := laysQ (hq := hq) (hz := hz) Hp Z a hX he f' i' j' h' hv L T₀ e C F P''
  let recover := Pipes.toll F e i'
  let forms := dualHerm (hq := hq) (hz := hz) Hp Z a hX he f' i' j' T₀ C e t x y hz' hx
  pairAndHead (E := ↥(U.flag e.val i')) (F := ↥(U'.flag e.val j'))
    (Q := Jewel (A' e.val)) (ReadK Z κ U e i') (M' e i') f
    (fun p q => f' p.val - q.val ∈ CΓ) (ReadK Z κ U' e j') (fun z => z 0)
    (fun z => (μ e.val)^r • z 0) rows recover (fun x y => L' 0 x y) (fun x y => L' r x y)
    (fun p q a b hp hq => forms p q a b hp hq j)

set_option maxHeartbeats 200000 in
lemma gramSigma (e:J!) {κ:(e:J!)→ Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} (C:Bals Hp Z a A' κ) {M':(e:J!)→(m:M)→ Jewel (A' e.val)→ₗ[ℝ] U.flag e.val m} {P':(e:J!)→(m:I)→ Jewel (A' e.val)→ₗ[ℝ] U'.flag e.val m} (F:K*! κ M') (P'':T*! κ P') (t:Even n.val)(x y: Site n)(hz':barrier P≤ n.val)(hx:Pins K P x y)(u v:Jewel (A' e.val))(j:Phase):
     let f:= PDiag (Race (V:=Dux G l A') (R:=M') P'' i' j' f'.toLinearMap) e; let L(t'):=(TokZ Hp Z a e (A' e.val) t x y t') j; L 0 (f u) (f v)=L r u v ∧ f u 0= (μ e.val)^r • (u 0) :=by
  exact comparePhysicalForms (hq := hq) (hz := hz) Hp Z a hX he f' i' j' h' hv L T₀
    e C F P'' t x y hz' hx j u v
end
end YM.OPE.Stroke

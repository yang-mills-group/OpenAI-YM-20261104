import YM.OPE.Compatible.Cant.Sign
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# Equality of phase coefficients across the two readouts

`YM.OPE.Stroke.dualHerm` compares two source flag representatives with two target representatives whose differences from the transported inputs lie in the target residual submodule.
At pinned sites on an even lattice satisfying the barrier bound, the target order-zero `TokZ` coefficient equals the source order-`r` coefficient at each phase.
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
private lemma readPairCoefficient {κ : (e : J!) → Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}
    (C : Bals Hp Z a A' κ) (e : J!) (t : Even n.val) (x y : Site n)
    (large : barrier P ≤ n.val) (pins : Pins K P x y) (p q : Mint Z e.val)
    (order : ℕ) (phase : Phase) :
    Por Hp Z e.val phase t x y a order p q =
      TokZ Hp Z a e (A' e.val) t x y order phase (κ e p) (κ e q) :=
  (ParD Hp Z a C e t x y large pins p q order phase).trans
    (laEQ Hp Z a e order t phase x y (A' e.val) (κ e p) (κ e q)).symm

include hX he T₀ in
private lemma transportPairCoefficient (e : J!) (t : Even n.val) (x y : Site n)
    (large : barrier P ≤ n.val) (pins : Pins K P x y) (p q : U.flag e.val i')
    (u v : U'.flag e.val j') (hy : f' p.val - u.val ∈ CΓ) (hh : f' q.val - v.val ∈ CΓ)
    (phase : Phase) :
    Por Hp Z e.val phase t x y a r (U.read e.val e.isLt i' p) (U.read e.val e.isLt i' q) =
      Por Hp Z e.val phase t x y a 0 (U'.read e.val e.isLt j' u) (U'.read e.val e.isLt j' v) := by
  have self (w : U.flag e.val i') : w.val - w.val ∈ Sγ i' := by
    rw [sub_self]
    exact (Sγ i').zero_mem
  have transported := commuting (hz := hz) (hq := hq) Hp Z a hX t x y pins he f' i' j'
    e large phase T₀ p.val q.val p q u v (self p) (self q) hy hh 0
  simpa only [Nat.zero_add] using transported

include hX he T₀
set_option maxHeartbeats 200000 in
lemma dualHerm {κ:(e:J!)→Mint Z e.val→ₗ[ℝ] Jewel (A' e.val)}(C:Bals Hp Z a A' κ)(e:J!) (t:Even n.val)(x y:Site n)(hW:barrier P≤ n.val)(hz':Pins K P x y) (p q:U.flag e.val i')(u v:U'.flag e.val j')(hy:f' p.val-u.val∈ CΓ)(hh:f' q.val-v.val∈CΓ)(j:Phase):
     let s:= ReadK Z κ U e i'; let g:= ReadK Z κ U' e j'; TokZ Hp Z a e (A' e.val) t x y 0 j (g u) (g v)=TokZ Hp Z a e (A' e.val) t x y r j (s p) (s q):=by
  intro s g
  have source := readPairCoefficient Hp Z a C e t x y hW hz'
    (U.read e.val e.isLt i' p) (U.read e.val e.isLt i' q) r j
  have target := readPairCoefficient Hp Z a C e t x y hW hz'
    (U'.read e.val e.isLt j' u) (U'.read e.val e.isLt j' v) 0 j
  have transported := transportPairCoefficient (hz := hz) (hq := hq) Hp Z a hX he f' i' j'
    T₀ e t x y hW hz' p q u v hy hh j
  exact target.symm.trans (transported.symm.trans source)
end
end YM.OPE.Stroke

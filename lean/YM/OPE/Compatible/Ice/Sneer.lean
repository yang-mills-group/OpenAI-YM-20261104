import YM.OPE.Compatible.Ice.Guru
/-!
# Rate bounds for a translated quadratic reading

Under the field, period, and `Audible` hypotheses of `ΓLight`, a fixed translation
by `vintage` preserves the rate estimate for `τPledge`. `Paying` extends this
estimate to a varying translation parameter with rate exponent zero by expressing
the reading in terms of its values at translations zero and one.
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
variable {Y:M→ℝ}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) 
open Pipes
local notation "μ"=>lapPrice (Patch.L P)
section
open GlowPack
variable (W:GlowPack Hp Z a (k:=k)) (U:Z.Ω M Y)(hq:1 ≤ Y)(hp:4 ≤ i)(V:(i':M)→Alps K T i (Y i'))
local notation "W!"=>Dux G l W.W
local notation "E!"=>Eagle Hp Z a W
variable {W Hp Z a U V} {hq hp}
variable (D:Cart Hp Z a W U hq hp V) (j':M)
open GlowPack
open Silt.Phere
open Ibis
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000
variable (h:Stone Z Y U) (s t:ℝ)(hs':s<t)(he:l+6 ≤ e)(hb:u ≤ 0)(ht: 3*u ≤ s)
private lemma evaluateStage {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : Filter I) (c : I → ℝ) (v : I → M) (op : M → E →L[ℝ] B) (inputs : I → E)
    (hc : Tendsto c L atTop) (hU : RateLE L c (Y ∘ v) 0)
    (price : Wealth op Y 1) (measured : RateLE L c inputs t) :
    RateLE L c (fun i => op (v i) (inputs i)) t :=
  RateLE.of_norm_le (((height_W L c op v price hc hU).norm.mul measured.norm).mono (by norm_num))
    (Eventually.of_forall fun i => (op (v i)).le_opNorm _)

private lemma dockedRate {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (aware : Aware d τ) (gear : M → Train i) (rank : 4 ≤ i) (level : ℕ)
    (op : M → solar G d τ →L[ℝ] B) (floor : 1 ≤ Y) (cost : Wealth op Y 1)
    (docked : Docked gear rank op level 3 K) (L : Filter I) (c : I → ℝ)
    (v : I → M) (inputs : I → solar G d τ) (hc : Tendsto c L atTop)
    (hU : RateLE L c (Y ∘ v) 0)
    (measured : ∀ z : Phase, RateLE L c (fun i =>
      StageM (e := level) (K := K) gear rank z (v i) (inputs i)) t) :
    RateLE L c (fun i => op (v i) (inputs i)) t := by
  let samples (z : Phase) (j : I) := StageM (e := level) (K := K) gear rank z (v j) (inputs j)
  obtain ⟨A, B₁, C, hA, hB, hC, split⟩ := Trinity aware gear rank op floor cost docked
  have r₂ := evaluateStage (t := t) L c v A (samples 2) hc hU hA (measured 2)
  have r₁ := evaluateStage (t := t) L c v B₁ (samples 1) hc hU hB (measured 1)
  have r₀ := evaluateStage (t := t) L c v C (samples 0) hc hU hC (measured 0)
  apply ((r₂.add r₁ hc).add r₀ hc).congr
  exact Eventually.of_forall fun i => (DFunLike.congr_fun (congr_fun split (v i)) (inputs i)).symm

include h
abbrev Bξ (d:ℝ) := Eψ D j' 2 ∘L vintage G D₀.aware d
omit h in
lemma Ξprice (c:ℝ): Wealth (fun i=> Bξ D i c) Y 1:=PledgeW (Ecost D 2) (wealthC (vintage G D₀.aware c)) 
lemma ΘDawn (c:ℝ):Docked (fun i=> (V i).gear) hp (fun i=> Bξ D i c) (l+1) 3 K:=by
       constructor
       · intro i p hv; apply (ΦBud D 2 h).hush i; apply rugged (L:=K.K) (V i).gear hp D₀.aware _ c hv
       intro v p hv; rw [show p=0 from Subtype.ext (funext fun i=> hv i i.isLt),map_zero]
private lemma shiftedReadout (shift : ℝ) (L : Filter I) (c w : I → ℝ)
    (B : I → solar G d τ) (v : I → M) (hc : Tendsto c L atTop)
    (hU : RateLE L c (Y ∘ v) 0)
    (stages : ∀ phase : Phase, RateLE L c (fun i =>
      StageM (e := l+1) (K := K) (fun m => (V m).gear) hp phase (v i)
        (Ripple G D₀.aware (w i) (B i))) t) :
    RateLE L c (fun i => τPledge D (v i) (w i) (vintage G D₀.aware shift (B i))) t := by
  let inputs (i : I) := Ripple G D₀.aware (w i) (B i)
  have measured := dockedRate (t := t) D₀.aware (fun m => (V m).gear) hp (l+1)
    (fun m => Bξ D m shift) hq (Ξprice D shift) (ΘDawn D h shift) L c v inputs hc hU stages
  apply measured.congr
  exact Eventually.of_forall fun i =>
    (congr_arg (Eψ D (v i) 2) (via G D₀.aware shift (w i) (B i))).trans
      (reformat D (v i) (w i) _).symm

variable (F:ℝ→ℕ)(hF:F=(Hear (I:=I) G K.K hp τ d D₀.aware hs' (show l+1+6 ≤ e+1 from by omega) hb ht).choose)(L: Filter I)(c w:I→ℝ)(B0:I→solar G d τ)(N:I→Side)(x:∀ i,Site (N i))(v:I→M) (hc:Tendsto c L atTop)(hw:∀ᶠ i in L,F (c i) ≤ (N i).val) (ha:Alive L c B0)(hV:RateLE L c w u)(hU:RateLE L c (Y ∘ v) 0)(hW:Audible G K.K N L c i e (fun i=> (V (v i)).gear) hp (fun i=> Aview (B0 i) (x i) (w i)) s)
include hF hc hw ha hV hU hW
lemma ΓLight (t':ℝ) : RateLE L c (fun i=> τPledge D (v i) (w i) (vintage G D₀.aware t' (B0 i))) t:=by
  apply shiftedReadout D h (t := t) t' L c w B0 v hc hU
  intro z
  simp_rw [waysL]
  exact (Hear G K.K hp τ d D₀.aware hs' (show l+1+6 ≤ e+1 by omega) hb ht (I := I)).choose_spec
    L c w B0 _ N x hc (hF ▸ hw) ha hV hW z
lemma Paying (q:I→ℝ)(hz:RateLE L c q 0) : RateLE L c (fun i=> τPledge D (v i) (w i) (vintage G D₀.aware (q i) (B0 i))) t:=by
       let Y(i):= τPledge D (v i) (w i); let f(i:I):= Y i (B0 i); let p(i:I):= Y i (vintage G D₀.aware 1 (B0 i)); have hf:= AuroraWitness D h s t hs' he hb ht F hF L c w B0 N x v hc hw ha hV hU hW; have hp:= ΓLight D h s t hs' he hb ht F hF L c w B0 N x v hc hw ha hV hU hW 1
       refine (hf.add ((hz.smul (hp.sub hf hc)).mono (by norm_num)) hc).congr (Eventually.of_forall fun i=>?_); apply Eq.symm; change Y i _= f i+q i • (p i-f i); exact Eq.trans (congr_arg _ (toneR ..)) (wheelW ..) 
where wheelW {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y] (f:X→L[ℝ] Y)(x v:X)(q:ℝ): f (x+q • (v-x))= f x+q • (f v-f x):=by rw[map_add,map_smul,map_sub]
end
end YM.OPE.Stroke

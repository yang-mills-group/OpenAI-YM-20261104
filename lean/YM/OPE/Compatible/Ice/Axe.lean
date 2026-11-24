import YM.OPE.Compatible.Ice.Room
import YM.OPE.Compatible.Chest.Booth
/-!
# A quadratic reading from three phase estimates

`τPledge` evaluates the three phase readings with weights `1`, `t`, and `t^2`.
`reformat` expresses the result as a single phase-two reading of `Ripple`.
`AuroraWitness` uses the three `Hear` estimates and their period cutoff to pass
from an `Audible` input at exponent `s` to a `RateLE` bound at exponent `t > s`,
under the stated field, frame, and parameter bounds.
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
noncomputable abbrev τPledge (t:ℝ):solar G d τ→L[ℝ] OrthoC W:= Eψ D j' 0+t • Eψ D j' 1+t^2 • Eψ D j' 2
lemma reformat (t:ℝ) (x:solar G d τ): τPledge D j' t x= Eψ D j' 2 (Ripple G D₀.aware t x):=by
        exact Β_w (trellisA G D₀.aware) t (fun i:Phase=> Eψ D j' i) (fun i j h x=>shifts D j' i j h x) x
where Β_w {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] (S:E→L[ℝ] E)(t:ℝ)(f:Phase→E→L[ℝ] F)(hp:∀ i j:Phase,i.val+1=j.val→∀ x,f j (S x)=f i x)(x:E): (f 0 +t • f 1+t^2 • f 2) x=f 2 (S (S x)+t • S x+t^2 • x):=by simp only[_root_.add_apply,_root_.smul_apply,map_add,map_smul]; rw [show f 2 (S x)=_ from hp 1 2 rfl _, show f 2 (S (S x))= _ from hp 1 2 rfl _, hp 0 1 rfl]
lemma height_W {X:Type}[NormedAddCommGroup X](φ:Filter I)(c:I→ℝ)(A:M→X)(v:I→M)(h:Wealth A Y 1)(ht:Tendsto c φ atTop)(hs:RateLE φ c (Y ∘ v) 0): RateLE φ c (A∘v) 0:=by obtain ⟨b,hb,k,H⟩:=h; apply RateLE.of_norm_le (((RateLE.const b ht).mul (hs.pow k ht)).mono (by norm_num)); exact Eventually.of_forall fun i=> by simpa using H (v i)
section
variable {t : ℝ}

private lemma pricedEvaluation {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : Filter I) (c : I → ℝ) (v : I → M) (A : M → E →L[ℝ] B)
    (g : I → E) (hc : Tendsto c L atTop) (hU : RateLE L c (Y ∘ v) 0)
    (hA : Wealth A Y 1) (hg : RateLE L c g t) :
    RateLE L c (fun i => A (v i) (g i)) t :=
  RateLE.of_norm_le (((height_W L c A v hA hc hU).norm.mul hg.norm).mono (by norm_num))
    (Eventually.of_forall fun i => (A (v i)).le_opNorm _)

private lemma threeRates {B : Type} [NormedAddCommGroup B] (L : Filter I)
    (c : I → ℝ) (total f g h : I → B) (eqn : ∀ i, total i = f i + g i + h i)
    (hc : Tendsto c L atTop) (hf : RateLE L c f t) (hg : RateLE L c g t)
    (hh : RateLE L c h t) : RateLE L c total t := by
  have he : total = f + g + h := funext eqn
  rw [he]
  exact (hf.add hg hc).add hh hc

private abbrev stageSample (G : Gauge) (K : Sponsor G) (aware : Aware d τ)
    (V : M → Train i) (hp : 4 ≤ i) (level : ℕ) (v : I → M)
    (w : I → ℝ) (inputs : I → solar G d τ) (z : Phase) (j : I) :=
  StageM (K := K) (e := level) V hp z (v j) (Ripple G aware (w j) (inputs j))

private lemma priceThreeStages (S : Light D) (L : Filter I) (c w : I → ℝ)
    (inputs : I → solar G d τ) (v : I → M) (hc : Tendsto c L atTop)
    (hU : RateLE L c (Y ∘ v) 0)
    (stages : ∀ z : Phase,
      RateLE L c (stageSample G K D₀.aware (fun m => (V m).gear) hp (l+1) v w inputs z) t) :
    RateLE L c (fun j => τPledge D (v j) (w j) (inputs j)) t := by
  let g := stageSample G K D₀.aware (fun m => (V m).gear) hp (l+1) v w inputs
  apply threeRates L c _ (fun j => S.S (v j) (g 2 j)) (fun j => S.T (v j) (g 1 j))
      (fun j => S.F (v j) (g 0 j)) _ hc
  · exact pricedEvaluation L c v S.S (g 2) hc hU S.sCost (stages 2)
  · exact pricedEvaluation L c v S.T (g 1) hc hU S.tCost (stages 1)
  · exact pricedEvaluation L c v S.F (g 0) hc hU S.fCost (stages 0)
  · intro j
    exact (reformat D (v j) (w j) (inputs j)).trans
      (S.Lup (v j) (Ripple G D₀.aware (w j) (inputs j)))

end

variable (h:Stone Z Y U) (s t:ℝ)(hs':s<t)(he:l+6 ≤ e)(hb:u ≤ 0)(ht: 3*u ≤ s)
include h
lemma AuroraWitness (F:ℝ→ℕ)(hF:F=(Hear (I:=I) G K.K hp τ d D₀.aware hs' (show l+1+6 ≤ e+1 from by omega) hb ht).choose)(L: Filter I)(c w:I→ℝ)(B0:I→solar G d τ)(N:I→Side)(x:∀ i,Site (N i))(v:I→M) (hc:Tendsto c L atTop)(hw:∀ᶠ i in L,F (c i) ≤ (N i).val) (ha:Alive L c B0)(hV:RateLE L c w u)(hU:RateLE L c (Y ∘ v) 0)(hW:Audible G K.K N L c i e (fun i=> (V (v i)).gear) hp (fun i=> Aview (B0 i) (x i) (w i)) s) : RateLE L c (fun i=> τPledge D (v i) (w i) (B0 i)) t:=by
  apply priceThreeStages D (light D h).some L c w B0 v hc hU
  intro z
  change RateLE L c (fun j => StageM (K := K) (e := l+1) (fun m => (V m).gear) hp z (v j)
    (Ripple G D₀.aware (w j) (B0 j))) t
  simp_rw [waysL]
  exact (Hear G K.K hp τ d D₀.aware hs' (show l+1+6 ≤ e+1 by omega) hb ht (I := I)).choose_spec
    L c w B0 _ N x hc (hF ▸ hw) ha hV hW z
end
end YM.OPE.Stroke

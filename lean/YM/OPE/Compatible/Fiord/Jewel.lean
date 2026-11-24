import YM.OPE.Compatible.Fiord.Link
import YM.OPE.Compatible.Camo.Hilt
import YM.OPE.Compatible.Fiord.Rein
/-!
# Marginal plans. True relative density jets, *before* normalization
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.OPE.Owl.HillZ
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset
open Silt Libra Coin Rill Silt.Float Votive PertExtension Series GaussianScore Radial Next.Foundations
open Merchant Merchant.Aloof Merchant.Sleeve Merchant.SiteL
open Next.Free Next.Scheduling Stroke Spells Lass Lass.Zest Pill CardinalQ
variable {I:Type}{φ:Filter I}{G:Gauge} {K:Sponsor G}{T:Seasons K}
variable {β:I→ℝ}{n:I→Side}{S:Stage}{i j d r k:ℕ}{τ s a B:ℝ}
variable (A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x))(U: Scaffold φ (Counters β) n (Mnd i S A) r)
variable (D:I→ Law (Merchant.Chamber G r))(hs:G.Simple)
open Merchant.SiteL
variable (h:Tendsto β φ atTop)(hD: GaugeD A U D)
open Cinders Metric Set Zeph Jargon Crown PertExtension Flock Stranded
variable {N:ChartRatio G} {s c R:ℝ} (H:StackP N s c R)(hN:LocalRatio N)
variable (x:∀ i,Bid.Dir G (n i)) (g:ℂ→L[ℝ]ℝ) (P:Pad G)
open Ibis Jargon Crown Exterior Silt.Phere Paver
variable (hz:4 ≤ i)
set_option quotPrecheck false
open Silt.Phere Jargon Crown Paver Cloud
open Stranded Merchant.SiteL Libra.Shift ScriptJ
local notation "TC"=> Merchant.Chamber G r
noncomputable abbrev visor (j:I) := SweepR (Mater A j) (Punched A U j) (D j)
abbrev Ytape (j:I) := Bid.Dir G (n j)× Merchant.Chamber G r
noncomputable abbrev CoverΩ (N:ChartRatio G)(j:I)(p: Bid.Dir G (n j) × Merchant.Chamber G r):= Fob A U D N j p.1 p.2
private lemma fstΛ {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] (x:E)(y:F): ContinuousLinearMap.fst ℝ E F (x,y)=x∧ ContinuousLinearMap.snd ℝ E F (x,y)=y:=⟨rfl,rfl⟩
private lemma split_pair {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] E) (B : E →L[ℝ] F) (x : E) (y : F) :
    let T := A.comp (ContinuousLinearMap.fst ℝ E F)
    T (x,y) = A x ∧ (ContinuousLinearMap.snd ℝ E F + B.comp T) (x,y) = y + B (A x) := by
  simp only [ContinuousLinearMap.comp_apply, _root_.add_apply, (fstΛ x y).1, (fstΛ x y).2, and_self]
lemma torn (j:I)(x:Bid.Dir G (n j))(y: TC): visor A U D j (x,y)= Kho A U D j x y:=by
       rw [WFul]; unfold visor SweepR; rw [_root_.add_apply,ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]; rw [(fstΛ (E:=Bid.Dir G (n j)) (F:=TC) x y).1,(fstΛ x y).2]
variable {A U D}
private lemma tickHt {E F J:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F][NormedAddCommGroup J][NormedSpace ℝ J][FiniteDimensional ℝ J](p q:F→ℝ)(Z T:E→L[ℝ] F)(P:J→ℝ)(W:E→L[ℝ]J) :
       let h(k l:ℕ)(x:F):=-jet p k x-jet q l x
       let a(k l:ℕ)(x:E):= h k l (Z x)-h k l (T x)
       Carat (fun x:E=> flareTok (a 3 1 x) (a 4 2 x+jet P 2 (W x))):=by
        intro h a; let Q(x:E):= flareTok (a 3 1 x) (a 4 2 x+jet P 2 (W x)); have hp (k l:ℕ)(hv:l ≤ k) :anthem k (a k l):=by
             let f:= h k l; have hz:f= (-1:ℝ) • (jet p k + jet q l):=funext fun x=>by simp only[Pi.smul_apply,Pi.add_apply,f,h,smul_eq_mul]; ring
             have hf:anthem k f:=hz.symm ▸ (((jetLyr _ k).add ((jetLyr _ l).bloat hv)).scale _); rw [show a k l=f ∘ Z + (-1:ℝ) • (f ∘ T) from funext fun i=> (by change f (Z i)-f (T i)= f (Z i)+(-1:ℝ)*f (T i); ring)]; exact (hf.compLinear Z.toLinearMap).add ((hf.compLinear T.toLinearMap).scale _)
        let hc:=hp 3 1 (by omega); intro i; fin_cases i
        · exact anthem.bank ..
        · exact hc
        let y:=jet P 2 ∘ W; change anthem 6 (skry Q 2); rw [show skry Q 2=(a 4 2+y)+ (1/2:ℝ) • (a 3 1)^2 from funext fun x=> (by change _+ (a 3 1 x)^2/2=(a 4 2 x+y x)+(1/2:ℝ)*(a 3 1 x)^2; unfold y; simp only [Function.comp_apply]; ring)]; exact ((((hp 4 2 (by decide)).bloat (by decide)).add (((jetLyr _ _).compLinear W.toLinearMap).bloat (show 2 ≤ 6 by decide))).add ((hc.powers 2).scale _)) -- parenthesis inspect
private def jet_gap {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q : E → ℝ) (k l : ℕ) (x y : E) :=
  (-jet p k x - jet q l x) - (-jet p k y - jet q l y)

private def pair_chart {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (p q : E → ℝ) (Z : E × F →L[ℝ] E)
    (A : E →L[ℝ] E) (B : E →L[ℝ] F) (P : F → ℝ) (x : E × F) :=
  flareTok (jet_gap p q 3 1 (Z x) (A x.1))
    (jet_gap p q 4 2 (Z x) (A x.1) + jet P 2 (x.2 + B (A x.1)))

private lemma pair_poly {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (p q : E → ℝ)
    (Z : E × F →L[ℝ] E) (A : E →L[ℝ] E) (B : E →L[ℝ] F) (P : F → ℝ) :
    Carat (pair_chart p q Z A B P) := by
  let T := A.comp (ContinuousLinearMap.fst ℝ E F)
  let W := ContinuousLinearMap.snd ℝ E F + B.comp T
  have he : pair_chart p q Z A B P = (fun x =>
    flareTok (jet_gap p q 3 1 (Z x) (T x)) (jet_gap p q 4 2 (Z x) (T x) + jet P 2 (W x))) := by
    funext ⟨x,y⟩
    have hh := split_pair A B x y
    change T (x,y) = A x ∧ W (x,y) = y + B (A x) at hh
    simp only [pair_chart, hh.1, hh.2]
  rw [he]
  exact tickHt p q Z T P W

private lemma chart_matches (j : I) : CoverΩ A U D N j =
    pair_chart (KPole A j) (LPole A j) (visor A U D j) (mixT A U D j)
      (PinT G) (feeX N) := by
  funext ⟨x,y⟩
  simp only [pair_chart, jet_gap, torn, CoverΩ, Fob, FelT, ExT,
    show ∀ a b : Token, (a - b).l = a.l - b.l from fun _ _ => rfl,
    show ∀ a b : Token, (a - b).h = a.h - b.h from fun _ _ => rfl, PolV]

lemma κHeft (j:I): Carat (CoverΩ A U D N j):=by
  rw [chart_matches]
  exact pair_poly _ _ _ _ _ _
lemma δHeft (j:I) : Carat (Eday A U D N j):= casket (ν:=Chart.tangent G (fieldP r)) (L:=D j) (κHeft (A:=A) (U:=U) (D:=D) (N:=N) j) -- Eday defeq can match.un
lemma Mammon (j:I): Carat (ΩReal A U D (Plato n) N j):=by
       let P:= LinearMap.fst ℝ (Bid.Dir G (n j)) TC; let q:=Eday A U D N j; let U'(x:Bid.Dir G (n j)):= (q x)⁻¹; have he:Carat U':=tipC (δHeft j) (fun _=> fullHt ..); have ht: Carat (U' ∘ P):=by intro i; exact (he i).compLinear P
       exact skS ht (κHeft (U:=U) (D:=D) (N:=N) j) -- syntax Gfont
end YM.OPE.Owl.HillZ

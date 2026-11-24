import YM.OPE.Compatible.Fiord.Note
import YM.OPE.Compatible.Mason.Zeal
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
open Silt.Phere Jargon Crown Paver Cloud Stranded Merchant.SiteL Libra.Shift ScriptJ Drift
local notation "TC"=> Merchant.Chamber G r
open Borealis Borealis.Lav Cameo Claw Libra.Char Variance
local notation "Tc"=> Merchant.Chamber G r
variable {τ':Phase→ℕ}{C V W:Forge G n}{H:Aware (d+6+6) τ'}
variable (hX:AcctΩ A U g P hz H C V W)
noncomputable abbrev SpecA (N:ChartRatio G)(j:I) := SnapL A U D g P (Plato n) N j
local notation "M!"=>Mouth A U D
noncomputable def MRest (N:ChartRatio G)(j:I) := ΩReal A U D (Plato n) N j*Gsky A U D g P hz j
include hX
lemma scTape: ∀ᶠ j in φ, SpecA A U D g P N j=MRest A U D g P hz N j +(Mouth A U D W N j+Mouth A U D C N j-Mouth A U D (C-V) N j):=by
       filter_upwards [hX.turnS] with j hi; ext1 x
       let m:=visor A U D j x; let P0:=ego G n (Ctag A g P hz H) j; let y:= ArtY A P g j m; let R:= Gsky A U D g P hz j x; have hp:y=P0 m+ R:=φMatch A U D g P hz H j x
       have hx:P0 m= W j m+ V j m:=sub_eq_iff_eq_add.mp (show P0 m-V j m=_ from congr_fun hi m); let L:= MonoΩ A U D N j x.1 x.2; have hz: Kho A U D j x.1 x.2=m:=by with_reducible_and_instances exact (torn A U D j x.1 x.2).symm
       unfold SpecA SnapL StoryF MRest; simp only[ΩReal,Mouth,wMirror,Plato,Bx,By,hz,Pi.add_apply,Pi.sub_apply,Pi.mul_apply]; with_reducible_and_instances change L*y=L*R+( L*W j m+L*C j m-L*(C j m-V j m)); rw [hp,hx]; ring
local notation "μT"=> Chart.tangent G (fieldP r)
local notation "Kr"=>marX A U D
local notation "Φ0"=> SpecA A U D g P N
include hD
omit hX in lemma χBase (j:I) : Status (MRest A U D g P hz N j):= fun i=> ((KinΔ A U D hD g P hz j).color i).hW
omit hD in lemma δHeads:∀ᶠ i in φ, Status ((C-V) i):= StatusE (C-V) (δRoll A U g P hz hX)
omit hD in lemma δLau: ∀ᶠ i in φ, Status (C i) ∧ Status (W i):= (StatusE C hX.cr).and (StatusE W (fun s=> (hX.lr.roll s).tariff))
lemma Scroll :∀ᶠ j in φ, Status (SpecA A U D g P N j):=by
        let ν:= YTape (G:=G) (r:=r); filter_upwards[scTape (N:=N) A U D g P hz hX,δLau A U g P hz hX,δHeads A U g P hz hX] with i hi ⟨hv,ht⟩ hp; rw[hi]; exact puffP_add _ _ (χBase (N:=N) A U D hD g P hz i) (puffP_sub _ _ (puffP_add _ _ (handy A U D i _ ht) (handy A U D i _ hv)) (handy A U D i _ hp)) -- signature
omit hX hD in
private lemma TransBank {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][MeasurableSpace F][BorelSpace F][FiniteDimensional ℝ F](A:Law F)(ν:Measure F)[ν.IsAddHaarMeasure](p q r s:E×F→Token)(hq:Status q)(hp:Status p)(hr:Status r)(hs:Status s)(a b c:E→Token)(h:crossT ν A q=a)(he:crossT ν A p=b)(hv:crossT ν A r=0)(hL:crossT ν A s=c):crossT ν A (q+(p+r-s))=a+b-c:=by
       rw[Salt_add _ _ hq (puffP_sub _ _ (puffP_add _ _ hp hr) hs),SaltShift _ _ _ _ (puffP_add _ _ hp hr) hs,Salt_add _ _ hp hr,h,he,hv,hL]; abel
include hN
lemma DSpin: ∀ᶠ i in φ, crossT (μT) (D i) (SpecA A U D g P N i)= ΞMark A U D g P hz N i+ W i- marX A U D (C-V) N i:=by
        filter_upwards[δLau A U g P hz hX,δHeads A U g P hz hX,scTape (N:=N) A U D g P hz hX,Lodger A U D hN g P hz hX, LoadE A U D hD hN g P hz hX] with i ⟨hv,hh⟩ he hx ht hr; let Q:=MRest A U D g P hz N i; let S0:= D i; rw [hx]; let p:=Mouth A U D W N i; let q:= Mouth A U D C N i; let X:= Mouth A U D (C-V) N i; let μ:=Chart.tangent G (fieldP r)
        have hu:= TransBank S0 μ p Q q X (χBase (N:=N) A U D hD g P hz i) (handy A U D i _ hh) (handy A U D i _ hv) (handy A U D i _ he) (crossT μ S0 Q) (W i) (crossT μ S0 X) rfl ht hr rfl
        unfold ΞMark MRest; unfold Q MRest at hu; with_reducible_and_instances exact hu

noncomputable abbrev RentZ (N:ChartRatio G) := ΦMean A U D g P (Plato n) N
lemma trueΦ : ∀ᶠ i in φ,RentZ A U D g P N i= tariff (et A i) (ΞMark A U D g P hz N i+W i-marX A U D (C-V) N i):=by
        filter_upwards [Scroll (N:=N) A U D hD g P hz hX,DSpin A U D hD hN g P hz hX] with i hi hx; rw[←hx]; ext1 a; let P:= SpecA A U D g P N i; exact (Boν (D i) μT P hi a (et A i)).symm
end YM.OPE.Owl.HillZ

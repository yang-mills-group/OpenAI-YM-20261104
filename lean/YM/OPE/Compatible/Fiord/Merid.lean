import YM.OPE.Compatible.Fiord.Velas
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
open Borealis Cameo Claw Libra.Char Variance
local notation "Tc"=> Merchant.Chamber G r
-- dynamic account. exact epochs *truth/replay* with same OR.B
variable {τ': Phase→ℕ}
structure AcctΩ (H:Aware (d+6+6) τ') (C V W:Forge G n) : Prop where
       -- C true, V trunc, W exterior model
       wage : WageK U.top (VesselP i S A) (ShadowP i S A U) (ShadowL i S A U) C V
       rise (c:ℝ) : Silks φ (Counters β) c (C-V)
       cr (s:Phase):∀ᶠ i in φ,Tall (eyeR C s i) (d+6+6+s.val)
       pr :PlaneQ (fun j=> bark (WorkB A j)) φ (Counters β) V (d+6+6)
       lr :PlaneQ (fun j=>leash r (WorkB A j)) φ (Counters β) W (d+6+6)
       turnS:∀ᶠ j in φ, ego G n (Ctag A g P hz H) j-V j= W j
section
lemma BodyStill (j:I)(v:Bid.Dir G (n j))(y:Merchant.Chamber G r) : let L:=leash r (WorkB A j); BlurD G L (n j) (v+Stair A U j y)=BlurD G L (n j) v:=by
        intro L; funext i; let p:= Moor i.val (n j); have ht:p∉ fringe r (n j):=by
              rintro h; obtain ⟨x,hX⟩:= from_port (Punched A U j) p h; have hy:= (fieldH x.val).1 x.property; have hh:= (tons i.val).1 i.property; have H:i.val=x.val:= berth_dir (eraSeal A U j) hh.1 (surf (show r<WorkB A j from broader A U j) hy.1) hX.symm; exact hh.2 (H.symm ▸ hy.1)
        rw [echoP,echoP,Pi.add_apply,show Stair A U j y (arkE p)=0 from silly _ _ y p ht,add_zero]
lemma FieldSord (j:I)(x:Bid.Dir G (n j))(y:Tc) : let L:=leash r (WorkB A j); BlurD G L (n j) (visor A U D j (x,y))=BlurD G L (n j) x:=by
        let P:= BlurD G (leash r (WorkB A j)) (n j); let z:= pour (Stair A U j) (chrom (KPole A j)) (D j) x; let R:=mixT A U D j; let F:= Stair A U j; intro Z; have hx:R x+F z=x:=by unfold R mixT; with_reducible_and_instances exact (SiteL.alongQ F (chrom (KPole A j)) (D j) x).symm
        have hp:=BodyStill A U j (R x) z; have hz:P (R x +F z)=P (R x):= by with_reducible_and_instances exact hp
        rw[hx] at hz; rw[torn,WFul]; calc
            _ = P (R x):=by with_reducible_and_instances exact BodyStill A U j (R x) y
            _ = _:=by with_reducible_and_instances exact hz.symm
lemma anyLy {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {f:E→ℝ}(h:Tall f k): anthem k f:=by obtain ⟨P,H⟩:=h.stock; rw[H]; exact anthem.total _ _ (fun i hi=> (lyricCost _).bloat (by have h:= mem_range.mp hi;omega))
lemma StatusE (f:Forge G n) (hf:∀ p:Phase,∀ᶠ i in φ,Tall (eyeR f p i) (k+p.val)):∀ᶠ i in φ, Status (f i):=by filter_upwards [eventually_all.mpr hf] with i h p; exact Stature.poly (anyLy (h p)).cost _
end
variable {C V W:Forge G n}{H:Aware (d+6+6) τ'}(hz':AcctΩ A U g P hz H C V W)
include hz'
lemma δRoll (s:Phase): ∀ᶠ j in φ,Tall (eyeR (C-V) s j) (d+6+6+s.val):=by filter_upwards [hz'.cr s,(hz'.pr.roll s).tariff] with j hj hi; let hT:=Tall.bite hj hi; fin_cases s<;>exact hT
lemma ExtE : ∀ᶠ i in φ,∀ v:Bid.Dir G (n i) × Merchant.Chamber G r, wMirror A U D W i v=W i v.1:=by
        filter_upwards [(hz'.lr.roll 0).here,(hz'.lr.roll 1).here,(hz'.lr.roll 2).here] with i h hη hS a; obtain ⟨x,y⟩:=a; have he:= FieldSord A U D i x y; exact JetS.eta _ _ (h.jury _ _ he) (hη.jury _ _ he) (hS.jury _ _ he)
include hD hN
lemma LoadE :∀ᶠ i in φ,crossT (Chart.tangent G (fieldP r)) (D i) (ΩReal A U D (Plato n) N i*wMirror A U D C i)=0:=by
        filter_upwards[Honest A U D hN (HillZ.load A U D hD hN hz'.wage)] with i hi; funext v; specialize hi v; let L:=D i; let W:=wMirror A U D C i; let P:=visor A U D i; let G0:= ΩReal A U D (Plato n) N i; change draw _ L _=0; rw [← hi]; apply congr_arg (fun s=>draw s (D i) _); funext x; simp only[Pi.mul_apply,wMirror]; rw[torn]; rfl -- orientation L def
end YM.OPE.Owl.HillZ

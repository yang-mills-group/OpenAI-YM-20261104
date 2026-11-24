import YM.OPE.Compatible.Lintel.Ump
/-! # Full Sail. Thermal receipts along deck probes. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Y Z:Type}{G:Gauge}{n m c f:Side}{S:StepData c f}{p q:Clip}{R T:PathData G} {P:Patch}{K:KernelChoices}{V:ChartRatio G} {i j t r:ℕ} {s s' u α T₁ T₂ b b' d U ℓ:ℝ}
namespace Script
open Page Virgin
section cart
variable (P)
def collarY (R:PathData G):= payVolume (drip G P.L) (leafV R 2)
def collarH (V:ChartRatio G):= payVolume (drip G P.L) (crownY V)
variable (D:Boxes G P K)
end cart
namespace Boxes
variable (D:Boxes G P K)
def lip (R:PathData G)(p:Clip):= tuneV D.dot (voteV P K R p 3) (voteV P K R p 4)
def crownZ (R:PathData G)(p:Clip)(V:ChartRatio G):= collarY P R+ D.lip R p +(-1:ℝ) • collarH P V
def talo (R:PathData G)(p:Clip)(V:ChartRatio G):=raft D.main (D.crownZ R p V)
def tuneP (R:PathData G)(p:Clip)(V:ChartRatio G)(n:Side)(x: Fin 2→ deck (Tile G P.L) n):= library n (collarY P R) x + tuneH D.dot (voteV P K R p 3) (voteV P K R p 4) n x+(-1:ℝ)*library n (collarH P V) x
def silo (R:PathData G)(p:Clip)(V:ChartRatio G)(n:Side)(x: Fin 2→deck (Shade G) n):= D.tuneP R p V n fun i=> D.main.acts n *ᵥ x i
lemma folk_lip (h:R.Bounds p s u b):folk (D.lip R p):= folksT D.rocket1 (folkS (penne_unit R p P K h 3) _) (folkS (penne_unit R p P K h 4) _)
lemma folk_collar (P:Patch)(h:R.Bounds p s u b): folk (collarY P R):= fun i=> volume_bill _ (drip_cash ..) _ _ (leafSongs R p 1 2 i h).2.1.choose_spec
lemma folk_cap (P:Patch)(V:ChartRatio G):folk (collarH P V):= fun i=>volume_bill _ (drip_cash ..) _ _ ((crowns V i).choose_spec)
lemma folk_crown (h:R.Bounds p s u b):folk (D.crownZ R p V):=folkF (folkF (folk_collar P h) (D.folk_lip h)) (folkS (folk_cap P V) _)
lemma rapid (h:R.Bounds p s u b)(d:ℕ): treasury (D.talo R p V) (D.silo R p V) d:=by
    have hp:=D.folk_crown (V:=V) h; have he(i):= tunes_advance _ D.rocket1 _ _ (folkS (penne_unit R p P K h 3) ((3:ℕ).factorial:ℝ)) (folkS (penne_unit R p P K h 4) ((4:ℕ).factorial:ℝ)) i
    exact treasuryT D.main D.rocket2 hp (fun i=> treasuryA (treasuryA (treasuryR (collarY P R) i) (folk_whole (folk_collar P h)) (he i) (folk_whole (D.folk_lip h))) (folk_whole (folkF (folk_collar P h) (D.folk_lip h))) (treasuryS (treasuryR (collarH P V) i) (-1:ℝ)) (folk_whole (folkS (folk_cap P V) _)))
end Boxes
-- exact docket T, reads directly from x-rays. polynomial.
variable (S) (hr: Odd S.ratio.count.val) (X:Boxes G S.patch S.kernel)
local notation "F"=> forest S.ratio hr
lemma marchY (h: LocalRatio V)(hp: R.Bounds p s u b)(x:vertP S.ratio hr G):
    let a:=dance S hr G x
    library c (collarY S.patch R) ![a,a]= iteratedFDeriv ℝ 2 (springF F R) 0 ![x.2,x.2] ∧ library c (collarH S.patch V) ![a,a]=iteratedFDeriv ℝ 2 (taxY F V) 0 ![x.2,x.2] :=by
     intro a; let L:= ribz S hr (G:=G); let B:=spool G f (L x); let Y:AxisChart G F→L[ℝ] Bid.Dir G f:= (arm G f 1).toContinuousLinearMap ∘L (Stationary.pad F); let T:= drip G S.patch.L; have ht:Whole T:= drip_cash ..; have he:installed S.ratio T *ᵥ a= B:= paintDrip S hr x
     let D:= swornY R (n:=f); let N:= festival (n:=f) V
     have hv (A:Script (Shade G) 2)(W:Bid.Dir G f→ℝ)(hv:Voice A (spool G f).toContinuousLinearMap W)(h:Summable A)(hk:ContDiffAt ℝ ω W 0): library c (payVolume T A) ![a,a]=iteratedFDeriv ℝ 2 (W ∘ Y) 0 ![x.2,x.2]:=by
         erw [volume_torque (g:=S.ratio) ht A h ![a,a],jets_linear Y (hk.of_le le_top)]; have hf(i: Fin 2) : installed S.ratio T *ᵥ (![a,a] i)=B:=by fin_cases i <;> exact he
         let p:= ![Y x.2,Y x.2]; erw [show (fun i:Fin 2=> installed S.ratio T *ᵥ (![a,a] i))= _ from funext (fun i=> (hf i).trans (show B=spool G f (p i) from by fin_cases i <;> rfl))]; apply Eq.trans (hv p); rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]; apply congr_arg (iteratedFDeriv ℝ 2 W 0); ext1 i; fin_cases i <;> rfl
     rw [show springF F R= D ∘ Y from funext fun i=>by unfold springF; rw [spoolP]; rfl,show taxY F V=N ∘ Y from funext fun i=>fete S F i h]
     have hh:=leafSongs R p f 2 0 hp; exact ⟨hv _ _ hh.2.2 (sootS hh.2.1.choose_spec) (tubesY R p f hp).1, hv _ _ (crownsS f h) (folk_whole (crowns _)) (festivalS f h)⟩
end Script
end YM.OPE.Flume

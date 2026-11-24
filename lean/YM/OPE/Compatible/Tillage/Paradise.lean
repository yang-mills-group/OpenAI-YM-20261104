import YM.OPE.Compatible.Tillage.Plink
/-!
# Recurrence control stake of tagged packs
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Flume Flume.Script Frequency
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n c f L:Side}{P:Patch}{K:KernelChoices}{I J M:Type}{m k r d:ℕ}{σ C s u z:ℝ}{B:Sponsor G} {H:Seasons B}
namespace Alps
open Page Virgin Planned.PrimaryIntegral295.Carrier Boxes
variable {v w Z X:M→ℝ}{T: Medal P G B.K P.J}{U:∀ i:M,Alps B H P.J (v i)}{V:∀ i:M,Alps B H P.J (w i)}
-- Act
abbrev display (P:Patch)(B:Sponsor G)(g:Train P.J)(q:Script (Shade G) r):= Script.mat G.ColorIndex (ship P g) B.K.penalty q
lemma displayP {g:Train P.J}{p:Script (Shade G) r}(h:folk p):folk (display P B g p):= folk_volP (chrome_sum (stored _ _ B.K.penalty_pos P.order_cut)) h
lemma forkSub (T:Boxes G P K){P Q:Script (Shade G) r} (h:folk P)(hp:folk Q):stitch (player T (P-Q))=stitch (player T P)-stitch (player T Q):=by
     have hh:= player_bill T P h; have he:= player_bill T Q hp; rw [← stitchSub hh he]; apply congr_arg; unfold player; rw [volVSub (drip_cash ..) h hp, raftSub _ T.rocket2 (folk_volP (drip_cash ..) h) (folk_volP (drip_cash ..) hp)]
namespace Roles
variable (B0: Roles T U V s Z X)
abbrev orderB (T:Medal P G B.K P.J) (U:∀ i:M, Alps B H P.J (v i))(q:M→ Script (Shade G) r) (i:M):= stitch (player (Qmark T U i) (q i))
include B0
lemma flees {q:M→Script (Shade G) r}(hp:Loan m q 1 X):Loan m (orderB T U q-orderB T V q) Z X:=by
    let A:= fun i=> payVolume (drip G P.L) (q i); have hx:Loan m A 1 X:=Loan.plat (drip G P.L) (drip_cash G P.L) hp; have hS:=pay_tt B0.ext₁ B0.price B0.fuel zero_le_one hx; have hS':=pay_tt B0.ext₂ B0.price B0.fuel zero_le_one hx; apply Loan.stilt hS hS'; refine pay_ttδ B0.ext₁ B0.ext₂ B0.dist₁ hx hx (show Loan m (A-A) Z X from ?_) B0.price B0.fuel B0.tune; rw [sub_self]; exact Loan.zero _ _
lemma pager {p q:M→(r:ℕ)→Script (Shade G) r}(h:∀ i,folk (p i (r+1)))(hq:∀ i,folk (q i (r+1)))(hz:Loan m (fun i=>q i (r+1)) 1 X)(hy:∀ i,∃ Y, stint ((p-q) i) (r+1) Y)(ht:∀ a,a<r+1 → 0 < a → Loan m (fun i=> (p-q) i a) Z X):
    Loan m ((orderB T U (fun i=>p i (r+1))-orderB T V (fun i=>q i (r+1)))-(fun i=> display P B (U i).gear ((p-q) i (r+1)))) Z X:=by
       have hX:=B0.flees hz; have hp := drone P B T; obtain ⟨e,D,he,HH⟩:=pitchUp B P; have hv:0 ≤ Z:=fun i=> (B0.tune i).le
       have hg:= fam_slides B0.fuel hv (H:=fun i=> Qmark T U i) (fun i=>hp _) he (fun i=> HH _) hy ht; rw [show ((orderB T U _-orderB T V _)-_)=_ from ?_]; exact hg.seize hX B0.fuel hv
       ext1 i; simp only [Pi.sub_apply,Pi.add_apply, display, adjV,orderB]; rw [forkSub (h:=h i) (hp:=hq i)];abel
end Roles
end Alps
end YM.OPE.Votive

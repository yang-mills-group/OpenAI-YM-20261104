import YM.OPE.Compatible.Kash.Logs
/-!
# Sap.EOM radical membership at launch.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}{R:Patch}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Alps Roles Planned.PrimaryIntegral295.Carrier Hark Quit.Jac
variable {u d s r l k m:ℕ}{W I E:Type}{τ:Phase→ℕ}
variable {K:Sponsor G}{S:Seasons K}{t:ℝ}(A: Alps K S s t)(hr:LocalRatio P)(hp:4  ≤  s)(hs:G.Simple)(hv:0  ≤  t)(R:Patch){n:Side}(x y:Site n)(H:Even n.val)
local notation "M!"=> CountL n R.L
local notation "Y!"=> solar G d τ
local notation "μ"=> lapPrice (Patch.L R) l
section
open Quit.Jac
variable (p:solar G (d+1) τ) (k:Antitone τ)
lemma Rflip (a:Axis): spose a G d τ (slipK k p)= slipK k (spose a G (d+1) τ p):=by
        apply Subtype.ext; apply faithful _ _ (spose a G d τ (slipK k p)).property.1 (slipK k _).property.1; intro n i; change Vtap (Quit.Mirror a G _ _ (slipK k p).val) _ i= Vtap (slump _ k) _ i
        rw [show Vtap (Quit.Mirror a G _ _ (slipK k p).val) _ i= _ from (show inkM (spread G d τ _) d _ i=Vtap (slump p.val k) (dart a 0) (streak a G n i) from toner a _ (0:Site n) i), DelayK,DelayK]; exact congr_arg (Ū*·) (toner a p.val _ i).symm
-- Sap on same contour powers.Ph.BodyBudget.PhShape.Car cross.Stations.Gamma.Support.Resize clock basis
include H hr
lemma Sought (q:solar G d τ): PriceZ.Warp A H hp hs x y (slipK k p) q P=Ū*PriceZ.Warp A H hp hs x y p (see q) P:=by
        rw [linkZ A x y H hs hp hr,linkZ A x y H hs hp hr]; dsimp only; let Q':= isolate H (bramble H) p.val (see q).val x y; have he : isolate H (bramble H) (slipK k p).val q.val x y= (fun i=>Ū*Q' i):=by
             funext i; change Vtap (slump p.val k) x _ * Vtap q.val y _= Ū*(Vtap p.val x _ * Vtap (soar q.val) y _); rw [DelayK,Low]; exact mul_assoc ..
        rw [he]; exact coin_F _ _ _ _ Q' (isolateB _ _ _ _ _ _) (Lid.hat_toll _ hr)
omit H
local notation "Z₀"=> MainSap A hr hp hs hv R l
lemma thaw (he:p ∈ MainSap A hr hp hs hv R l) : slipK k p∈ MainSap A hr hp hs hv R l:=by
        rintro n x y H hR i q; let K(i:Phase):=fun j:ℕ=>BitA A hr hp hs hv R x y H i j (slipK k p) q; let S(i:Phase):= fun j:ℕ=>BitA A hr hp hs hv R x y H i j p (see q); have ht(i:Phase)(j:ℕ): K i j=(Ū*(WQ (P:=P) (R:=R) A hp hs x y H p (see q) j)).seq i.val:= by
             unfold K; rw[BitSeq]; exact congr_arg (fun v:Token=> v.seq i.val) (Sought A hr hp hs _ _ _ p k q)
        have hv(i j):S i j=(WQ (P:=P) (R:=R) A hp hs x y H p (see q) j).seq i.val:=BitSeq ..; have hh(i):Thick (μ*(μ)) (S i):= he n _ _ H hR i (see q); change Thick (μ*μ) (K i); fin_cases i
        · change Thick _ (K 0); rw [show K 0=0 from funext fun i=> (ht 0 i).trans (boneS _)]; exact Thick.hex ⟨0,Hex.zero _ 0⟩ le_rfl (mul_pos (EndFare ..) (EndFare ..))
        · change Thick _ (K 1); rw[show K 1=S 0 from funext fun i=>(ht 1 i).trans ((boneL _).trans (hv 0 i).symm)];exact hh _
        change Thick _ (K 2); rw [show K 2=S 1 from funext fun i=>(ht 2 i).trans ((boneH _).trans (hv 1 i).symm)]; exact hh _
lemma thaws (a:Axis)(he:p∈SailSap A hr hp hs hv R a l): slipK k p∈SailSap A hr hp hs hv R a l:=by
        obtain ⟨hx,hV⟩:= he; refine ⟨thaw A hr hp hs hv R p k hx,?_⟩; change spose a G d τ (slipK k p) ∈ MainSap A hr hp hs hv R l; rw [Rflip]; exact thaw A hr hp hs hv R _ k hV
omit hr
lemma SlipLive (x:I→solar G (d+1) τ){V:I→ℝ}{g:Filter I}(h:Ibis.Alive g V x): Ibis.Alive g V (fun i=>slipK k (x i)):=by
        intro m; obtain ⟨b,hb,hY⟩:=h m; refine ⟨b,hb,?_⟩; filter_upwards [hY] with i hi; have hc:= Sack.coins ((hi 0).2 0)
        unfold Tide;intro j; unfold Ibis.Goan; change Volume (spread G d τ (slump (x i).val k) j) _ _ _; rw[spreadYs]; fin_cases j
        · rw[Drift.glide_nil _ (by decide)]; exact ⟨fun _ _=>rfl,fun i=> Sack.zero hc _⟩
        · apply (hi 0).raise _ _ le_rfl; change d+1+0 ≤ d+1; omega
        exact (hi 1).raise _ (le_of_eq (show d+1+1=d+2 from Nat.add_assoc ..)) le_rfl
end
end YM.OPE.Variance

import YM.FormalOPE.RG10.StationaryMarks.Bide
import YM.FormalOPE.RG10.InversionTop
/-!
 # compatibility with `InversionTop` formal readout (bare real WilsonX top)
 at the common bare coupling. Arbitrary other positive formal weights may be scheduled;
 no assumption that block iterations are approximating the top readout. Only for formal diagrams.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.StationaryMarks
open Function Filter Topology Set Metric MeasureTheory PertExtension Precision
open BlockGauge Inherit Push.Loops Chart Lattice RG Filter Finset
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial PowerSeries
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
open Orb
variable {G:Gauge} {n:Side} (L: Fabric G n)
 def attending (O:Wilson.Config G n→ℝ): L.LinksOn→ℝ:= O ∘ Orb.liftLinks ∘ L.principal
lemma eligible {O:Wilson.Config G n→ℝ} (hO: Orb.PreTest O): Multipurpose L (attending L O) where
 reading:={
   meas := (hO.continuous.comp ((Orb.lift_cont G).comp (L.principal_cont))).measurable
   bounded:= let ⟨m,H⟩:= isCompact_univ.exists_bound_of_continuousOn hO.continuous.continuousOn; ⟨m,fun i=> H _ (Set.mem_univ _)⟩
   leg g _ V:= by
     unfold attending; simp only [Function.comp_apply,Fabric.spin_main]
     rw [show Orb.liftLinks (even_spin (g ∘ track) (L.principal V))= Lattice.gauge (g∘track) (Orb.liftLinks (L.principal V)) from funext fun i=> (Orb.path_law _ _ (track_even g) i).symm]
     exact hO.gauge _ (track_even g) _ }
 required:= by
   refine ⟨L.atop,?_⟩
   let i:= entrance L
   have he: ((attending L O) ∘ L.atop.board) ∘ expLinks G L.atop.Bulk = (Orb.restrictedO O ∘ expLinks G (Cotree n)) ∘ Strong.wave i := by
    ext1 x; simp only [Function.comp_apply,attending]; rw [←key_agrees]; rfl
   rw [he]; exact (show ContDiffAt ℝ ∞ _ (Strong.wave (G:=G) i 0) from by rw [map_zero]; exact hO.curved.germ).comp _ ((Strong.wave (G:=G) i).contDiff.contDiffAt)

-- without entering top chart, directly use real integral in `before_tree_formula`
lemma top_integral {q: L.Accounts→ℝ}{t:ℝ}(H:q none=1/t^2)(O: Wilson.Config G n→ℝ) :
 (∫ u:LinkFrame G n, L.splitFee q u * O (Orb.liftLinks u) ∂Fabric.now G n)=Orb.preNum O t:= by
 apply integral_congr_ae (Filter.Eventually.of_forall fun i=>?_)
 unfold Fabric.splitFee Fabric.wilson Orb.preDensity; rw [H]; ring_nf -- math real?
lemma topRatio {q: L.Accounts→ℝ}{t:ℝ}(hp:∀ i,0<q i)(H:q none=1/t^2){O:Wilson.Config G n→ℝ}(hO:PreTest O): L.balanced q (attending L O)=Orb.preExpectation O t:= by
 have ha:= L.top_kept (O ∘ Orb.liftLinks) q (eligible L hO).reading hp
 unfold attending; rw [show O ∘ Orb.liftLinks ∘ L.principal= (O ∘ Orb.liftLinks) ∘ L.principal from rfl,ha]
 have hc:= top_integral L H (1: Wilson.Config G n→ℝ)
 simp only [Pi.one_apply,mul_one] at hc; unfold preExpectation; rw [hc, ← top_integral L H O]; rfl

variable {P:ChartRatio G}(w: L.Accounts→ PowerSeries ℝ)(T:L.loom.Truss)
theorem staple_root (H: LocalRatio P)(hw:∀ i,0<term (w i) 0)(hT:w none=1){O:Wilson.Config G n→ℝ}(ho:PreTest O):
 scene L T w P (attending L O)= PowerSeries.mk (Orb.diag (Orb.restrictedO O)):= by
 apply PowerSeries.ext; intro i
 let e j:= shrink (w j) i
 have hv j:Through i (w j) (e j):= Through.symm (shrink_width _ _)
 let z j t:= sheet w i t j
 have hp j:0<term (e j) 0:= lt_of_lt_of_eq (hw j) (hv j 0 (Nat.zero_le _))
 have hP i: Tracks (z i) ((model L T e).w i):=photo w _ i
 have hh:= drawn L T e z H (eligible L ho) hp hP
 have hZ: Tracks (preExpectation O) (PowerSeries.mk (diag (restrictedO O))):= by rw [Tracks,Tracks.asTerm]; exact Orb.before_tree_formula L.even (Orb.traySpec G) ho
 apply Eq.trans (horizon_pres L T w e hw H (eligible L ho) hv (waits_no ((eligible L ho).passes L T)) i (by omega))
 apply congr_arg (fun x=> coeff (R:=ℝ) i x) (hh.seam hZ ?_)
 filter_upwards [Tested.eventually_pos, (enough L T e hp).event hP] with t ht he
 apply topRatio L (fun i=> div_pos (he i) (pow_pos ht 2)) _ ho
 unfold z sheet; rw [hT]; simp [Tested.peval,Tested.term,Zone.eval, coeff_one, Finset.sum_ite_eq']; -- syntax .L.Screen
-- agrees with Real marked part at common λ
lemma prior (H:LocalRatio P)(hw:∀ i,0<term (w i) 0)(hT:w none=1){O: Wilson.Config G n→ℝ}(ho:PreTest O): InversionTop.into (scene L T w P (attending L O))=
 (InversionTop.feed L.even).step (InversionTop.vertices G n) (InversionTop.raw (Orb.restrictedO O)):= by rw [staple_root L w T H hw hT ho]; exact (InversionTop.tree_agreement L.even ho.curved).symm
end YM.FormalOPE.RG10.StationaryMarks

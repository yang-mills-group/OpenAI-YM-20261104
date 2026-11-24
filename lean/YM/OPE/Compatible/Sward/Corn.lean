import YM.OPE.Compatible.Sward.Kite
import YM.OPE.Compatible.Lob.Top
import YM.OPE.Compatible.Frog.Eye
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
-- budget C estimate.O. Use masks of bad axes
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
open Votive
variable {N:Side}{L:KernelChoices} (x:Site N)
open Drift Shell Char
variable {τ :Char.Phase→ℕ}{d:ℕ}
open PertExtension Series GaussianScore
open Matrix
open Flock Shift
section harm
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
-- scale linear λ source
abbrev CardM (f:E→Token)(k:ℕ): Prop:=∀ i:Phase, anthem (k+3*i.val) (skry f i)
lemma shinesL (f:E→Token)(q:F→ₗ[ℝ] E)(h: CardM f k): CardM (f ∘ q) k:= fun j=> (h j).compLinear q
lemma Meets (f g:E→Token)(hp: CardM f k)(hx:Carat g):CardM (f*g) k:=by
       let q(i:Phase):=k+3*i.val; have h(i j h:Phase)(ht:q i+3*j.val=q h): anthem (q h) ((skry f i)*(skry g j)):= ht ▸ (hp i).times (hx j)
       intro i; fin_cases i
       · exact h 0 0 0 rfl
       · exact (h 0 1 1 (by norm_num[q])).add (h 1 0 1 rfl)
       exact ((h 0 2 2 (by norm_num[q])).add (h 1 1 2 (by unfold q; norm_num))).add (h 2 0 2 rfl)
variable [FiniteDimensional ℝ F][MeasurableSpace F][BorelSpace F](μ:Measure F)[μ.IsAddHaarMeasure](A:Law F)
lemma nectar (p: E×F→Token)(hp:CardM p k):CardM (Libra.Shift.crossT μ A p) k:=by
       intro i; have hv:= hp i; fin_cases i <;> exact gains _ _ _ hv
end harm
lemma InkG (p:Tower (Shade H) d τ): CardM (inkM (spread H d τ p) d x) d:=by
       intro i;rw [levelT]; exact (polW x (m:=τ i) (p i)).bloat (by omega)
open Libra.Adhesion
section
variable [MeasurableSpace E][NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][BorelSpace E][Fintype I]
variable (F:Fiber E H I)(P:ChartRatio H)
omit [BorelSpace E] in lemma pict (f: E×Keys H I→Token)(hp:CardM f k)(h:LocalRatio P):CardM (F.predicts P f) k:=by
       let μ:= Chart.tangent H I; let T:=F.cloth P; let X:=Libra.Shift.crossT μ F.Q T; let Y:=f ∘ (Fiber.drape E (Keys H I) F.M); have ht:= atlasH F P; have he:CardM Y k:= shinesL _ _ hp
       apply Meets (Libra.Shift.crossT μ F.Q (Y*T)) (fun i=>(X i)⁻¹) (nectar _ _ _ (Meets _ _ he ht))
       apply tipC (p:=X) (casket ht); intro i; exact headD μ F.Q (fun j:Keys H I=> T (i,j)) fun _=>curT (F.signPay h) _
end
end YM.OPE.Silt.Phere

import YM.OPE.Compatible.Frog.Loom
/-!
# Euler normal. weighted seats at nonfixed capacity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l k:ℕ} {C:KernelChoices}
variable {τ:Phase→ℕ}
local notation "T!"=> Tower (Shade G) d τ
-- raw Euler D0
noncomputable def kindle (G:Gauge)(k j m:ℕ)(_h:k ≤ j): Seat k m (Shade G)→L[ℝ] Seat j m (Shade G):= ContinuousLinearMap.pi fun i=>moduleAt m k i.val (Shade G)
lemma kindle_eq (x:Seat k m (Shade G))(h:k ≤ j): lilies m j _ (kindle G k j m h x)=lilies m k _ x:=by
     funext i; by_cases ht:i ≤ j
     · rw [soup,moduleAt,dif_pos ht]; rfl
     rw [(sproutV ..|>.1 _ (by omega : j < i)),(sproutV ..|>.1 _ (by omega : k < i))]
noncomputable def Dower (G:Gauge)(k m:ℕ): Seat k m (Shade G)→L[ℝ] Seat k m (Shade G):= ContinuousLinearMap.pi fun i=> (i.val:ℝ) • (ContinuousLinearMap.proj i)
lemma dowerP (x:Seat k m (Shade G))(i:ℕ): lilies m k _ (Dower G k m x) i= (i:ℝ) • lilies m k _ x i :=by
     by_cases h:i≤ k
     · rw [soup,soup,moduleAt,dif_pos h]; exact map_smul (seed m i (Shade G)) (i:ℝ) _
     rw [(sproutV m k x).1 _ (not_le.mp h),(sproutV m k _).1 _ (not_le.mp h), smul_zero]
lemma nScore {v:ℝ}(A:Curtain (Shade G))(h:Volume A d m v)(x: deck (Shade G) n)(u:Site n)(k:ℕ)(hk:d≤k) : Flair (fun i=> (i:ℝ) • A i) k x u= deriv (fun i:ℝ=> Flair A d (i • x) u) 1:=by
     let Z(i:ℕ)(v:ℝ):= Script.value u (A i) (v • x); let f(i:ℕ):= Script.value u ((i:ℝ) • A i) x; have he(i):HasDerivAt (Z i) (f i) 1 :=by
          have ht(z:ℝ): Z i z=Script.value u (A i) x*z^i:=Grid.rollScale ..; have hv := ((hasDerivAt_id' (1:ℝ)).pow i).const_mul (Script.value u (A i) x); rw [funext ht]; convert! hv using 1; simp only [one_pow,mul_one]; unfold f Script.value; rw [score_scaled,mul_comm]
     have hp:= HasDerivAt.fun_sum (A:=Z) (u:=range (d+1)) (fun i _=> he i); change (∑ i∈range (k+1),f i)=deriv (fun i:ℝ=> ∑ j∈range (d+1), Z j i) 1; rw [hp.deriv]; symm; refine sum_subset (range_mono (Nat.add_le_add_right hk _)) ?_ ; intro i _ hz; unfold f; rw [h.1 _ (Nat.not_lt.mp (fun he=>hz (mem_range.mpr he))),smul_zero]; simp [Script.value,scribe]
-- D. Stepping
lemma ascLower (h:Aware d τ): τ 2≤ τ 0:=h.mono (by decide)
noncomputable def peakV (G:Gauge)(h:Aware d τ): Seat (d+(0:Phase).val) (τ (0:Phase)) (Shade G)→L[ℝ] Seat (d+(2:Phase).val) (τ (2:Phase)) (Shade G):= glasses (Shade G) _ _ _ (ascLower h) ∘L kindle G d (d+2) _ (by omega) ∘L Dower ..
-- orders unaffected if i<2
noncomputable def traceOf (G:Gauge)(b:ℝ)(h: Aware d τ):Tower (Shade G) d τ→L[ℝ] Tower (Shade G) d τ:= ContinuousLinearMap.single (R:=ℝ) (fun i:Phase=>Seat (d+i.val) (τ i) (Shade G)) 2 ∘L ((b/2) • peakV G h) ∘L ContinuousLinearMap.proj 0
noncomputable def rebase (G:Gauge)(h:Aware d τ)(b:ℝ):Tower (Shade G) d τ→L[ℝ] Tower (Shade G) d τ :=1+traceOf G b h
lemma peak_eq (A: Seat d (τ 0) (Shade G))(h:Aware d τ)(k:ℕ): lilies (τ 2) _ _ (peakV G h A) k= (k:ℝ) • (lilies (τ 0) d (Shade G) A) k:=by unfold peakV; rw [ContinuousLinearMap.comp_apply, putG,forgets,ContinuousLinearMap.comp_apply]; erw [kindle_eq (Dower G d (τ 0) A), dowerP]
lemma sail (b:ℝ)(i:Phase)(h:Aware d τ)(x:T!)(hz:i≠2): rebase G h b x i=x i:=by
     simp [rebase, traceOf,hz, Pi.single_eq_of_ne]
lemma sip (b:ℝ)(h:Aware d τ)(x:T!):rebase G h b x (2:Phase)= x 2+(b/2) • peakV G h (x 0):=by simp [rebase,traceOf]
end YM.OPE.Drift

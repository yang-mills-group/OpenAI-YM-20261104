import YM.GradedFar.Pallet
/-!
# BY-embedding in the actual m_N experiment

Convenience lemmas for moving positions in f-grid to N when applying the Auth sales.
The sales apply directly on the resulting more general reports. Quiet with global
translation `s` on (N,period), even a shift as large as whole run. Requires distance bound
checked before this transmission at same calendar p. No extension here to history
conditional estimates on non-constant labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Auth
open Function Filter Set PowerSeries Metric MeasureTheory
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits Lattice FullVolume
open XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor Tariff Tariff.Playbill Tariff.Crosser Tariff.Billboard Tariff.Sunshine Batch
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(P:ℝ→tower S)
variable {n m N N' p h :ℕ} (H:Ratio (C.S.side N p) (C.S.side N' p))
def shot (u:Positions n) : Positions n:= fun i=> H.count.val • u i
lemma preserves (u:Positions n): Order.grid C N' (shot H u)= Order.grid C N u:= by
 ext i a; change C.S.a N'* ((↑(_ :ℤ)):ℝ)= C.S.a N * (u i a :ℤ); -- simp
 unfold shot
 simp only [nsmul_eq_mul, Pi.smul_apply, Int.cast_mul, Int.cast_natCast]
 rw [← mul_assoc,C.S.embeds_scale] -- inspect
lemma rolls (u:Positions n) (i) : wrap _ (shot H u i)= H.embed (wrap _ (u i)) := (H.embed_wrap _).symm
lemma read_at (u:Positions n){d:Fin n→ℕ}(v:AppointedH140Inputs G d)(L:Fin n→ℝ)(s:Lattice.Site (C.side N' p)): assemble F P L d N' p s (shot H u) v =
    (Wilson.partition G (C.side N' p) (C.beta N' p):ℂ)⁻¹ * ∫ U, (Wilson.bare (C.beta N' p) U:ℂ) * ∏ i, C.O N' p (d:=d i) (call F P (d i) (L i) (v i)) (H.embed (wrap _ (u i))+s) U ∂Wilson.prior G (C.side N' p) := by rw [really]; simp_rw [rolls]
lemma transferred (x:Points n)(y:Points m)(r T:ℝ)(u:Positions n)(v:Positions m)(L:ℝ)
    (ht: RoundedWell C N x y r T u v L): RoundedWell C N' x y r T (shot H u) (shot H v) L:= by
 have hu{n':ℕ}(u:Positions n'):Fin.append (shot H u) (shot H v)=shot H (Fin.append u v):= funext fun i=> Fin.addCases (fun i=> by simp [shot]) (fun j=>by simp [shot]) i
 have hv: (0:Positions 1)=shot H (0:Positions 1):=by ext; simp [shot]
 constructor; · rw [hu,rounded,preserves]; exact ht.1
 rw [hv,hu,rounded,preserves]; exact ht.2
end YM.Integration.GradedFar.Auth

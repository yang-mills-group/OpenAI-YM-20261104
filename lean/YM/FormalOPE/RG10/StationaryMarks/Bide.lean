import YM.FormalOPE.RG10.StationaryMarks.Figures
import YM.PertExtension.Normalized
/-!
 # Scheduled general coefficients at each inversion-regulated truss for any finite StepData
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.StationaryMarks
open Function Filter Topology Set Metric MeasureTheory PertExtension Precision
open BlockGauge Inherit Push.Loops Chart Lattice RG
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial PowerSeries
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {f:Side} (L: Fabric G f) (T R:L.loom.Truss) (w:L.Accounts→ PowerSeries ℝ)

 def model : Survey G T.Bulk L.Accounts where
 w:=w
 field i u:= L.price (T.board u) i
lemma enough (hw:∀ i,0<term (w i) 0): (model L T w).Ready where
 sincere _:= punctual L T _
 localAll _:= componentProbe L T _
 lead_pos:=hw
 entire:= prepared L T (fun i=> term (w i) 0) hw
 def scene (P: ChartRatio G)(O:L.LinksOn→ℝ): PowerSeries ℝ:= (model L T w).ratecard P (O ∘ T.board)
lemma horizon_pres (w') (hw:∀ i,0<term (w i) 0){P:ChartRatio G}(HP:LocalRatio P){O:L.LinksOn→ℝ}(H:Multipurpose L O){l n:ℕ}
 (h:∀ i, Through n (w i) (w' i)) (hh:Waits l (O ∘ T.board)): Through (l+n) (scene L T w P O) (scene L T w' P O):= (enough L T w hw).belongs HP (H.passes _ T) (show Survey.Continued n (model L T w) (model L T w') from ⟨rfl,h⟩) hh

-- expose fully quantified port to real diagram show `advanced` uses w-ratio scaled schedule.
variable (z:L.Accounts→ℝ→ℝ)
lemma rescale_spend {t:ℝ}(u:L.LinksOn):
 L.spend (fun i=> z i t/t^2) u = L.spend (fun i=> z i t) u /t^2:= by unfold Fabric.spend; rw [Finset.sum_div]; refine Finset.sum_congr rfl fun _ _=> ?_; ring
lemma advanced (O:L.LinksOn→ℝ)(hf:L.Reading O){t:ℝ}(ht:0<t)(h:∀ i, 0< z i t):
 (model L T w).advanced z (O ∘ T.board) t= scale G T.Bulk t * L.provision (fun i=>z i t/t^2) O:= by
 rw [L.control T hf (fun i=> div_pos (h i) (pow_pos ht 2)), Survey.advanced,journal]; congr 1; unfold Fabric.review; apply integral_congr_ae (Filter.Eventually.of_forall ?_)
 intro u; change _ * _=(O (T.board u))*_; rw [rescale_spend L,← neg_div]; rfl
lemma notation_real (O:L.LinksOn→ℝ)(hf:L.Reading O){t:ℝ}(ht:0<t)(h:∀ i, 0< z i t): ((model L T w).advanced z (O ∘ T.board)/(model L T w).advanced z 1) t = L.balanced (fun i=> z i t / t^2) O := by
 rw [Pi.div_apply,advanced L T w z O hf ht h, show 1 = ((1:L.LinksOn→ℝ) ∘ T.board) from rfl,advanced L T w z 1 L.house ht h, mul_div_mul_left ..]; rfl
 unfold scale; positivity
lemma drawn {P:ChartRatio G}(HP:LocalRatio P){O:L.LinksOn→ℝ}(H:Multipurpose L O)(hw:∀ i,0<term (w i) 0)(hs:∀ i,Tracks (z i) (w i)): Tracks (fun t=> L.balanced (fun i=> z i t / t^2) O) (scene L T w P O):= by
 let M:= enough L T w hw
 have he : ∀ i, Tracks (z i) ((model L T w).w i):=hs
 apply Tracks.patch (M.unitized HP (H.passes _ T) he);
 exact ((M.event he).and Tested.eventually_pos).mono (fun t ⟨h,h'⟩ => notation_real L T w z O H.reading h' h)
-- therefore polynomial schedules suffice for gauge independ on all regulators
variable {T R}
theorem anyTruss {P Q:ChartRatio G}(HP:LocalRatio P)(HQ:LocalRatio Q){O:L.LinksOn→ℝ}(H: Multipurpose L O)(hw:∀ i,0<term (w i) 0): scene L T w P O = scene L R w Q O:= by
 apply PowerSeries.ext; intro i
 let q:= fun j=> shrink (w j) i; let z:=fun j t=> sheet w i t j
 have hi j:Through i (w j) (q j):=Through.symm (shrink_width _ _)
 have ha j:0<term (q j) 0:= by rw [show term (q j) 0=term (w j) 0 from (shrink_width _ i 0 (Nat.zero_le i))]; exact hw j
 rw [horizon_pres L T w q hw HP H hi (waits_no (H.passes L T)) i (by omega), horizon_pres L R w q hw HQ H hi (waits_no (H.passes L R)) i (by omega)]
 rw [Tracks.seam (u:=(fun t=> L.balanced (fun i=> z i t/t^2) O)) (f:= scene L T q P O) (drawn L T q z HP H ha (photo w i)) (drawn L R q z HQ H ha (photo w i)) (Filter.EventuallyEq.refl _ _)]

-- canonical tree may now be used; `atop` deterministic.
end YM.FormalOPE.RG10.StationaryMarks

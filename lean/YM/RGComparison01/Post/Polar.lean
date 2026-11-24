import YM.AnalyticBridge.VERIFIED_RESET_STEP.Comparison
import YM.Pert.Kinetic.Densities
/-!
# Read two genuinely different energy bills in one projection

 Need branch before α change and after α change at these SAME books.
 And model is SIGNED part only. K not subtracted (represented cost
 of K uses the actual force reserve later). Cover wiring at this
 projection, not reading canonical curvature Fk into models without
 an actual certificate. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Post.Polar
open Function Filter Set Lattice Wilson RG RG.Shoot Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup Averaging AnalyticBridge.VerifiedReset.Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport Push.AbsoluteSums
open UVNext.CouplingReset
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ} {X : Listing G n} {v V z: Collection.Source G n}
lemma born (hG:G.Simple) (hV: Projects (X.read V) p H) (hv: Projects (X.read v) p w) (h:z.logRead=v.logRead-V.logRead): delta (X.read v)= delta (X.read V)+delta (X.read z):= by
   have he : delta (X.read v)-delta (X.read V)=delta (X.read z):= by
      unfold Averaging.delta Averaging.total; rw [←(hv.seriesAt hG ..).tsum_sub (hV.seriesAt hG ..)]
      apply tsum_congr; intro i; unfold censusAt; dsimp only [Listing.read]; split; rw [h]; exact (projection_sub _ (hv.regular i) (hV.regular i) ..).symm; ring
   linarith
lemma terrain (hG:G.Simple) (hV: Projects (X.read V) p H) (hv: Projects (X.read v) p w) (h:z.logRead=v.logRead-V.logRead) (R: PathData G) (c:Clip) (α β:ℝ):
   (branch X R c p V α).regular + (branch X R c p z (β-α)).regular=(branch X R c p v β).regular:= by
   have hD:delta (X.read z)=delta (X.read v)-delta (X.read V):= by linarith only [born hG hV hv h]
   have he (i : EKey n) (Δ Δ' : ℝ): archive X R c v β Δ i - archive X R c V α Δ' i=archive X R c z (β-α) (Δ-Δ') i:= by
      have hz := Collection.archive_sub hv.regular hV.regular R α Δ Δ' i (c:=c)
      rcases i with i|⟨a,d⟩|⟨a,d⟩
      · change _-_ = rebate (X.reg i) (z.logRead i); rw [h]; exact hz
      · exact hz
      funext U; change d.fresh R 0 (factor*β) _ _ - d.fresh R 0 (factor*α) _ _ = d.fresh R 0 (factor*(β-α)) (factor*(Δ-Δ')) _
      rw [mul_sub,mul_sub]; exact congr_fun (High.fresh_sub R d 0 _ _ _ _) (a.view U)
   funext i
   change _+archive _ _ _ _ _ _ _= (archive X R c v β (delta (X.read v)) (numbering _ i)); rw [hD,←he]; exact add_sub_cancel .. -- check orient
lemma collection (hv: Projects (X.read v) p w): |(∑' i,v.logRead i 1) / (Fintype.card (Site n):ℝ)| ≤ w:= by
   obtain ⟨b,h,hz,hB⟩:= Pert.Kinetic.payment_sum hv.bound
   have h₁ i : ‖v.logRead i 1‖ ≤ p.mass (X.reg i).support (b i):= ((h i).2 1 (flat_ok p _) [] (by simp) (by simp)).trans (p.loMass _ _ (h i).1)
   change |_/sites n| ≤ _
   rw [abs_div, abs_of_pos (sites_pos n),div_le_iff₀ (sites_pos n),mul_comm]; exact (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (by intros; positivity) h₁ hz)).trans (((Summable.of_nonneg_of_le (by intros; positivity) h₁ hz).tsum_le_tsum h₁ hz).trans hB) -- specify f
lemma stamp (hG:G.Simple) (hV: Collection.Local X p V H w) (e b:ℝ) (hv:Collection.Local X p v e b) (h:z.logRead=v.logRead-V.logRead) (τ:ℝ): Collection.vac v τ =Collection.vac V τ - (∑' i,z.logRead i 1) /(Fintype.card (Site n):ℝ):= by
   unfold Collection.vac; rw [h]; simp only [Pi.sub_apply]; rw [Summable.tsum_sub (hv.raw_sum hG 1).1 (hV.raw_sum hG 1).1]; unfold sites; ring
end YM.RGComparison01.Post.Polar

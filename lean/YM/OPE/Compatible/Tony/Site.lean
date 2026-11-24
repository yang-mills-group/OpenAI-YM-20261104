import YM.OPE.Compatible.Tony.Britt
/-!
# Echo from exterior field; derivatives at origin with Roster.K governs
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
local notation "D!"=> Bid.Dir G n
-- if an edge has at least one outside endpoint, at most one boundary link.Generative derivative support.S
section
open Next.Rank.Spindle
noncomputable abbrev CoatH (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (U:ℝ)(W:ℝ→ E)(k:ℕ):=∀ j:ℕ,j ≤ k→ ‖iteratedDeriv j W 0‖ ≤ U^j*‖iteratedDeriv 0 W 0‖ -- optional
lemma nthM (G:Gauge)(j:ℕ): ∃ C:ℝ,0 ≤ C∧ ∀ b n,∀ h:Board n b,∀ (x: Bid.Dir G n)(e:Edge (Site n)), ¬ Trim b e→ Roster x ≤1→ ‖iteratedDeriv j (fun t:ℝ=> G.mat (hermM h (represent (t • x)) e)) 0‖ ≤ C*(1+(b:ℝ))^(2*j):=by
       obtain ⟨c,hc,H⟩:=tipHeight G j; let f:ℝ→ G.Mat:=fun _=>1; let C:=max c ‖iteratedDeriv j f 0‖; refine ⟨C,hc.trans (le_max_left ..),fun b n h x e hE hx=>?_⟩; let U(t:ℝ):= represent (t • x); let y:=(1+(b:ℝ))^(2*j); have hy:1 ≤ y:= one_le_pow₀ (by linarith only [Nat.cast_nonneg (α:=ℝ) b]); have hs(i): ‖iteratedDeriv j (fun t:ℝ=> G.mat (stemL h (U t) i)) 0‖ ≤ C*y:=by
             unfold stemL; split
             next h' => let p:↥(StepsL.RingP b):=⟨_,grand h i h'⟩; have he : ‖iteratedDeriv j (fun t:ℝ=> G.mat (travel (expandAt 0 (U t)) (anchorX b) ((quay b).voyage p))) 0‖≤ _:=H b n h x hx p; rw [add_comm (b:ℝ)] at he; exact he.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (zero_le_one.trans hy))
             exact (le_max_right c (‖iteratedDeriv j f 0‖)).trans (le_mul_of_one_le_right (hc.trans (le_max_left ..)) hy)
       unfold hermM; simp_rw [if_neg hE]; by_cases hp:e.1∈berth b; swap
       · have hz:b<pdist e.1:= by_contra fun hz=> hp ((berthH e.1).2 (not_lt.mp hz)); simp_rw [stem_off h _ e.1 hz, inv_one,one_mul]; exact hs (dotUp e)
       have hz:b<pdist (dotUp e):=lt_of_not_ge fun hz=>hE ⟨(berthH _).1 hp,hz⟩; simp_rw [stem_off h _ _ hz,mul_one, G.mat_inv]; let p:ℝ→ G.Mat:= fun t=> G.mat (stemL h (U t) e.1); let S:= (starL' ℝ:G.Mat≃L[ℝ] G.Mat).toContinuousLinearMap; have hc:ContDiff ℝ ω p:= (hubT h e.1 G).comp (contDiff_id.smul contDiff_const); rw [show (fun t:ℝ=>star (G.mat (stemL h (represent (t • x)) e.1)))=S ∘ p from rfl]; change ‖iteratedDeriv j (S∘p) 0‖ ≤ _; rw [show iteratedDeriv j (S∘p) 0=star (iteratedDeriv j p 0) from Prom.adv_root S hc j]; rw [norm_star]; exact hs e.1
lemma HearSize (G:Gauge)(j:ℕ): ∃ C:ℝ,0 ≤ C∧ ∀ b n,∀ h:Board n b,∀ (x:Bid.Dir G n)(e:Edge (Site n)), ¬Trim b e→ Roster x ≤1→ ‖iteratedFDeriv ℝ j (fun t:ℝ=> G.plog (G.mat (hermM h (represent (t • x)) e))) 0‖ ≤ C*(1+(b:ℝ))^(2*j):=by
       choose C hc H using fun i=>nthM G i; let K:=1+∑ i∈range (j+1), C i; let D:=(∑ i∈range (j+1), ‖iteratedFDeriv ℝ i G.plog 1‖); have hd:0≤D:=sum_nonneg (fun i _=>norm_nonneg _); have hk:1≤ K:= le_add_of_nonneg_right (sum_nonneg fun i _=>hc i)
       refine ⟨(j.factorial:ℝ)*D*K^j,mul_nonneg (mul_nonneg (by positivity) hd) (pow_nonneg (zero_le_one.trans hk) _),fun b n h x e hT hx=>?_⟩
       let t:=1+(b:ℝ); let f(v:ℝ):=G.mat (hermM h (represent (v • x)) e); have hF:f 0=1:=by unfold f; rw [zero_smul,link_one,herm_eye]; simp
       have ht(i:ℕ)(he:1≤ i)(hp:i ≤ j): ‖iteratedFDeriv ℝ i f 0‖ ≤ (K*t^2)^i:=by
            rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; apply (H i b n h x e hT hx).trans; rw [mul_pow, ← pow_mul]; refine mul_le_mul_of_nonneg_right ?_ (by positivity); exact (single_le_sum (s:=range (j+1)) (f:=C) (fun i _=> hc i) (mem_range.mpr (by omega))).trans ((le_add_of_nonneg_left zero_le_one).trans ((pow_one K).symm.trans_le (pow_le_pow_right₀ hk he)))
       have hp:= strap f G.plog 0 j (((Wheat h e G).comp (contDiff_id.smul contDiff_const)).of_le le_top|>.contDiffAt) (show ContDiffAt ℝ (j: WithTop ℕ∞) G.plog (f 0) from hF.symm ▸ G.plog_diff.of_le le_top) D (K*t^2) (by intro i hi;rw [hF]; exact single_le_sum (f:=fun i=>‖iteratedFDeriv ℝ i G.plog 1‖) (fun _ _=>norm_nonneg _) (s:=range (j+1)) (mem_range.mpr (by omega))) ht
       rw[mul_pow,←pow_mul,←mul_assoc] at hp; exact hp
end
end YM.OPE.Merchant

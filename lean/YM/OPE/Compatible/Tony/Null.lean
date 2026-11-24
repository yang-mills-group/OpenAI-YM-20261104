import YM.OPE.Compatible.Tony.Loan
/-!
# Guide supports, holder.D Physical through every period freeze
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
namespace Sleeve
local notation "Q"=> Bid.Dir G n
lemma Her {p:ℕ}(hp:Board n p)(H:Board n (p+1))(P:Q→ℝ): Crisp (bark p) (P∘Λace G hp):=⟨fun _ _ hj=>congr_arg P (railK hp H _ _ hj)⟩
-- author substitution.Yient.Wealth
variable {I:Type}{A:I→ Side}{a c:ℝ}{φ:Filter I}{Z:I→ℝ}{e:RootEdge}{W:I→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v:I→ℝ}
variable (V:(j:I)→ Alps K T i (v j))
variable (hc:G.Simple)
section indiv
variable (Y:Alps K T i a)(h:Board n b)
include hc
lemma easy : Once (VoxM Y h) (VenM Y h):=by
       let p:=Dune Y (n:=n); let q:=Rh Y (n:=n); let L:=Λace G h; have hz:L 0=0:=eΛ ..; have hY := DuneAt (n:=n) Y hc; have he:= Advice Y h; have ht:= Zags Y h; have hL:=haloStage h G; refine ⟨(((hz.symm ▸ hY.sm: ContDiffAt ℝ ω p _).comp (f:=L) _ hL)).congr_of_eventuallyEq he,fun x k hv=>?_ ,((hz.symm ▸ hY.sg: ContDiffAt ℝ ω q _).comp (f:=L) _ hL).congr_of_eventuallyEq ht⟩
       interval_cases k; · rw[jet_zero,he.eq_of_nhds,Function.comp_apply, eΛ]; exact (jet_zero p 0).symm.trans (hY.zero _ _ (by omega))
       have hg:fderiv ℝ p 0=0:=by
            apply ContinuousLinearMap.ext; intro y; have hx:=hY.zero y 1 (by omega); unfold jet at hx; rw[iteratedFDeriv_one_apply] at hx; norm_num at hx; exact hx
       unfold jet; rw [iteratedFDeriv_one_apply,he.fderiv_eq, show fderiv ℝ (Dune Y∘ Λace G h) 0=0 from ?_]; simp; change fderiv ℝ (p ∘ L) 0= _; rw [fderiv_comp,hz,hg]; simp; · rw [hz]; exact hY.sm.differentiableAt (by simp)
       exact hL.differentiableAt (by simp)
omit hc in
private lemma EraTax {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](K V:E→ℝ)(A:E→E)(L:F→L[ℝ] E)(hc:K=ᶠ[𝓝 0] (V∘A))(h:∀ i,A (L i)= L i)(hP:ContDiffAt ℝ ω K 0)(hv:ContDiffAt ℝ ω V 0)(x y:F):chrom K (L x) (L y)=chrom V (L x) (L y):=by
       have ht:Tendsto L (𝓝 0) (𝓝 0):=L.map_zero ▸ L.continuous.continuousAt.tendsto; have he:K ∘ L=ᶠ[𝓝 0] V ∘ L:=by
            filter_upwards [ht.eventually hc] with i hi; exact hi.trans (congr_arg V (h _))
       have hh(g:E→ℝ)(hk:ContDiffAt ℝ ω g 0): chrom g (L x) (L y)=chrom (g ∘ L) x y:=by rw [Merchant.podium,Merchant.podium,linearX L 2 g hk _]; congr 1; ext1 i; fin_cases i <;>rfl
       rw [hh _ hP, hh _ hv,Merchant.podium,Merchant.podium,(he.iteratedFDeriv ℝ 2).eq_of_nhds]
set_option maxHeartbeats 200000
lemma Zully (hp:Board n (r+1))(he:r<b)(u:Chamber G r) (x:Chamber G r):chrom (VoxM Y h) (sailT G hp u) (sailT G hp x)= chrom (Dune Y (n:=n)) (sailT G hp u) (sailT G hp x):=by
        apply EraTax (VoxM Y h) (Dune Y) (Λace G h) (sailT G hp) (Advice Y h) _ ((easy hc Y h).sm) ((DuneAt Y hc).sm)
        intro i; have ht:=Tride hp h he (0:Bid.Dir G n) i; rwa[zero_add,eΛ,zero_add] at ht
lemma Eraρ (hp:Board n (r+1))(he:r<b)(Z:Law (Chamber G r))(hZ: SiteL (sailT G hp) (chrom (Dune Y)) Z):SiteL (sailT G hp) (chrom (VoxM Y h)) Z:= by
       refine ⟨turnsT _ ((easy hc Y h).sm.of_le le_top),?_⟩; rw [hZ.earns]; exact LinearMap.ext fun u=> LinearMap.ext fun x=> (Zully hc Y h hp he u x).symm
end indiv
noncomputable def rawP (b:I→ℕ)(h:∀ i,Board (A i) (b i)) : GlyphQ G A:=fun i=> VoxM (V i) (h i)
noncomputable def rawL (b:I→ℕ)(h:∀ i,Board (A i) (b i)): GlyphQ G A:=fun i=> VenM (V i) (h i)
section Calls
-- ∆ represent.Chamber derivatives
variable (W:I→ℕ)
variable (h:∀ i,Board (A i) (W i))
variable (M:Audience φ Z A W r)
include M
lemma Inform {P R:GlyphQ G A}(hp:∀ i,ContDiffAt ℝ ω (P i) 0)(hv:∀ i,R i=ᶠ[𝓝 0] P i ∘ Λace G (h i))(e:↥(fieldP r))(u:G.ColorIndex)(i:I): bat (functorE 0 e.val u) (R i)=ᶠ[𝓝 0] bat (functorE 0 e.val u) (P i)∘ Λace G (h i):=by
       have ht : bat (functorE 0 e.val u) (R i)=ᶠ[𝓝 0] bat (functorE 0 e.val u) (P i ∘ Λace G (h i)):= ((hv i).fderiv (𝕜:=ℝ)).mono fun j hj=> DFunLike.congr_fun hj _; exact ht.trans (target (M.room i).money _ (M.room i).wide _ _ _ (hp i))
end Calls
end Sleeve
end YM.OPE.Merchant

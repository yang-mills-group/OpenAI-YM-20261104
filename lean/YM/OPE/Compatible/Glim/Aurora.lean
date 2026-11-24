import YM.OPE.Compatible.Glim.Course
/-! # Local budgets of marker.Serial seam. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume.Script Glass
variable {n:Side}(H:Even n.val)(T:Plot H)(p:T.Free)(b:Bool){F:Type}{i k:ℕ}
local notation "L!"=> offZ H T (G:=G)
local notation "E!"=> Keys G T.Free
variable {K:Sponsor G}{S:Seasons K}{v:ℝ}(A:Alps K S i v)
local notation "Fo"=> Bid.Dir G n
abbrev Rh := swornY A.live (n:=n)
def Dune := frameD A (n:=n)-(fun _ =>frameD A (0:Fo))
lemma DuneAt (h:G.Simple) : Once (Dune A (n:=n)) (Rh A) :=by
    let V:= frameD A (n:=n); have ht:ContDiffAt ℝ ω V 0:= (A.fullK 1).plot n; refine ⟨ht.sub contDiffAt_const,fun x s hs=>?_,(A.fullL 1).plot n⟩
    interval_cases s; · rw [jet_zero]; unfold Dune;simp
    unfold jet Dune; erw [iteratedFDeriv_one_apply,fderiv_sub (ht.differentiableAt (by simp)) (differentiableAt_const _), fderiv_const_apply,show fderiv ℝ V 0=0 from dawnV A h,sub_zero]; simp
lemma Dunear : steady_r (Dune A (n:=n)):=by intro s u; funext x; unfold Dune frameD swornV; simp only[Function.comp_apply,Pi.sub_apply]; rw [rep_shifts,main_pull]
lemma Rhythm : steady_r (Rh A (n:=n)):=by intro s u; funext x; unfold Rh swornY; simp only [Function.comp_apply,rep_shifts,loopChannel]
lemma DuneKind : insured (tor n) (Dune A):=by
     constructor; intro x y u hp; have he:= ((Mar_ord ..).1 hp); let F:= A.fullK 2; have hv:frameD A x= frameD A y:= by
         unfold frameD swornV; simp only [Function.comp_apply]; rw [←he]; exact (F.stand n u (represent x)).symm
     unfold Dune;simp only [Pi.sub_apply,hv]
lemma RhythmKind : insured (tor n) (Rh A):=by
    constructor; intro x y u hp; have he:= ((Mar_ord ..).1 hp); unfold Rh swornY; simp only [Function.comp_apply];rw [← he]; exact ((A.fullL 2).stand n u _).symm
variable (U: Bor H A 0)
set_option maxHeartbeats 200000 in
lemma FullHarvest : (U.L T).f=ᶠ[𝓝 0] CostsH H T (Dune A):=by
     let V:= T.rollX (G:=G); have he:Tendsto V (𝓝 0) (𝓝 0):= V.map_zero ▸ V.continuous_of_finiteDimensional.tendsto _; rw [U.acts]; filter_upwards [he.eventually U.u] with x h; rw [Function.comp_apply,show U.f _= _ from h]; change frameD A (offZ H T x)/4- frameD A (cloak H (0:Keys G (Limb H))) /4= (4:ℝ)⁻¹*(frameD A (L! x)- frameD A 0); rw [(cloak H).map_zero]; ring
lemma FullSigns : (U.L T).w=ᶠ[𝓝 0] Real.exp ∘ fun x=>-(CostsH H T (Rh A) x):=by
     let V:= T.rollX (G:=G); have he:Tendsto V (𝓝 0) (𝓝 0):= V.map_zero ▸ V.continuous_of_finiteDimensional.tendsto _; rw [U.serves]; filter_upwards [he.eventually U.t] with x h; rw [Function.comp_apply,show U.w _= _ from h]; change Real.exp (-0*mural H A _-Rh A _ /4)= Real.exp (-((4:ℝ)⁻¹*Rh A (L! x))); unfold offZ; ring_nf;rfl
open Shell
lemma SolDisplay (V:Lid G T.Free)(hr:LocalRatio P)(a:Finset F)(u:F→ScriptJ E!)(h:∀ i∈a,(u i).B): V.pay P (∑ i∈a,u i)=∑ i∈a,V.pay P (u i) :=by
     let μ:= Chart.tangent G T.Free; have he(q:ScriptJ E!):V.pay P q=fair μ (penon V) (V.hat P) q := V.cutOut hr _ _ (penon_shape V); simp_rw [he]; exact fairSum μ (penon V) (V.hat P) (V.hat_toll hr) a u h
local notation "B"=>Phone G
abbrev WindV(Y:Fo→G.Color)(i:G.ColorIndex):= ((Phone G).coord i)∘ Y ∘ offZ H T (G:=G)
variable {U}
lemma Reflector (U:Bor H A 0)(h:G.Simple)(hr:LocalRatio P)(k:Kv)(r:ℕ)(Y:Fo→G.Color)(hv:AwayZ H T p k Y)(hp:Variance.Cand r Y)(x:ScriptJ E!)(hx:x.B):
    let S:= Cake (whiz (Plate H T p k)) (b.xor (dir H (Plate H T p k))) (Dune A) (Rh A) Y r
    (U.L T).pay P ((S ∘ offZ H T)*x)=∑ i:G.ColorIndex,(U.L T).pay P (Pawn.mold (WindV H T Y i) r * Topper p ((Phone G) i) b x):=by
       let f:=Dune A (n:=n); let g:=Rh A (n:=n); let Z:=CostsH H T g; let Q:=DuneAt (n:=n) A h; intro R; change (U.L T).pay P (((Cake _ _ _ _ _ r)∘ L!)*x)= _ ; rw[← crisp H T p b k Y hv hp (DuneAt A h) (Dunear (n:=n) A) (Rhythm A)]; unfold Cake;rw [sum_mul, SolDisplay _ _ _ hr _ _ ?_]; rotate_left
       · intro i _; exact height (stampL _ _ _ (fun _ _=> tallJ _ _) _ _ (ScriptJ.key (tallJ _ _) (tallJ _ _)) (tallJ _ _)) hx
       apply sum_congr rfl; intro i _; rw [← meltSame _ _ (FullHarvest H T A U)]; exact marrow p ((Phone G) i) b (U.L T) Z hr (FullSigns H T A U) (windH H T (DuneAt A h)).sg _ _ (tallJ _ _) hx
end YM.OPE.Variance

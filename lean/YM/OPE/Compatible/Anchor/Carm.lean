import YM.OPE.Compatible.Anchor.Tex
/-! # contour forge. Leading at origin.Affine ∞ support -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Labels
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r l:ℕ}{Z I J M E F:Type}{n:Side}
local notation "Q!"=>CoverConfig G
abbrev SpiceD (G:Gauge)(α:Fin r→ℕ):= ContinuousMultilinearMap ℝ (fun i=>Taylor G (α i)) G.Color
variable {α:Fin r→ℕ}(A:SpiceD G α)(e:RootEdge)
def Abalo (A: SpiceD G α):Prop:=∀ u x,A (fun i=> Taylor.paint u (x i)) = G.adjoint u (A x)
abbrev placeW (V: Q!):= travel V 0 (carryP e.1)
def Cloudy (V:Q!):G.Color:= G.adjoint (placeW e V)⁻¹ (A (fun i=>Motif (α i) V)) -- root moved
lemma clocksAw (h:Abalo A)(s:Cover→ G.El)(V:Q!) : Cloudy A e (Lattice.gauge s V)=G.adjoint (s e.1) (Cloudy A e V):=by
     simp only [Cloudy, MotifCast,h _ (fun i=> Motif (α i) V),placeW,travel_gauge,carryP, route_end]; rw [← G.adjoint_mul,← G.adjoint_mul]; refine DFunLike.congr_fun ?_ _; apply congr_arg; group
lemma Coat : Sensed (Cloudy A e):=by
     let f(i:Q!):= A (fun j=> Motif (α j) i); let V(x:Q!):=G.mat (placeW e x); have he:Sensed V:= candleTravel ..; let v(i:Fin r)(x:Q!):= Motif (α i) x; have hp:Sensed f:= (candles v (fun i=> MotifLit ..)).chain A A.contDiff
     let B(x: G.Color)(p:G.Mat):= G.projectColor (star p* G.colorMat x* p); have hv(x:Q!):Cloudy A e x=B (f x) (V x):=by unfold B V f Cloudy Gauge.adjoint; simp [Gauge.mat_inv,Gauge.conjugate]
     refine ⟨?_,fun E _ _ X h=>?_⟩
     · obtain ⟨s,hs⟩:=hp.see; obtain ⟨p,hP⟩:=he.see; exact ⟨s∪p,fun v u h=> by rw[hv,hv,hs v u (h.mono fun _ hl=> Finset.mem_union_left _ hl),hP v u (h.mono fun _ hl=> Finset.mem_union_right _ hl)]⟩
     rw [funext hv]; let T:= he.sense E X h; let P:= hp.sense E X h; unfold B; exact (G.projectColor.toContinuousLinearMap.contDiff.comp (((starL ℝ (A:=G.Mat)).contDiff.comp T|>.mul (G.colorMat.toContinuousLinearMap.contDiff.comp P)).mul T))
lemma augV (Z:fieldX (Shade G))(i:RootEdge): ContDiff ℝ ω (fun t:ℝ=> G.mat ((lotU (t • Z)) i)):= G.exp_jet.comp (show ContDiff ℝ ω (fun t:ℝ=> indexS i (t • Z)) from by simp_rw [map_smul]; exact contDiff_id.smul contDiff_const)
lemma adContour (G:Gauge): Continuous (fun x:G.El×G.Color=> G.adjoint x.1 x.2):=by
     let U (x:G.El×G.Color):= G.mat x.1; have hp:Continuous U:= G.continuous_mat.comp continuous_fst; unfold Gauge.adjoint; change Continuous _;
     exact G.projectColor.continuous_of_finiteDimensional.comp ((hp.mul (G.colorMat.continuous_of_finiteDimensional.comp continuous_snd)).mul ((starL ℝ (A:=G.Mat)).continuous.comp hp))
local notation "θ"=> 𝓝[>] (0:ℝ)
abbrev ClearW (u:fieldX (Shade G)):= A (fun i=> templateX G (α i) u)
lemma senseLim [NormedAddCommGroup F][NormedSpace ℝ F](v:ℝ→F)(hp:v 0=0)(a:F)(h:HasDerivAt v a 0): Tendsto (fun t:ℝ=>t⁻¹ • v t) θ (𝓝 a):=by have ht:=h.tendsto_slope_zero; simp only[zero_add,hp,sub_zero] at ht;exact ht.mono_left (nhdsWithin_mono _ (by intro i hi; exact ne_of_gt (show 0 < i from hi)))
set_option maxHeartbeats 200000 in
lemma forTer (v:fieldX (Shade G)):Tendsto (fun t:ℝ=> (t^r)⁻¹ • Cloudy A e (lotU (t • v))) θ (𝓝 (ClearW A v)):=by
    let V(t:ℝ):= lotU (t • v); let X(j:Fin r)(t:ℝ):=Motif (α j) (V t); let U(j:Fin r):=templateX G (α j) v; have h(i): Tendsto (fun t:ℝ=> t⁻¹ • X i t) θ (𝓝 (U i)):=by
        have ht:X i 0=0:=by unfold X V; rw[vacant_t,MotifZero]
        -- hasderivative
        have hv : HasDerivAt (X i) (U i) 0:= MotifGo ..; apply senseLim (F:=Taylor G _) _ ht _ hv
    let y(t:ℝ):=(placeW e (V t))⁻¹; have hQ:Tendsto y θ (𝓝 1):=by
        have ha: G.mat (placeW e (V 0))=G.mat 1:=by unfold placeW V; rw [vacant_t,tripOne]
        have he:Continuous V:=by apply continuous_pi; intro i; unfold V lotU; simp_rw [map_smul]; exact G.lieExp_cont.comp (continuous_id.smul continuous_const)
        have ht:placeW e (V 0)=1:= G.mat_injective ha; have hv := ((continuous_travel (G:=G) (carryP e.1) (0:Cover)).comp he).tendsto (0:ℝ); change Tendsto (placeW e ∘ V) _ (𝓝 (placeW e (V 0))) at hv; rw [ht] at hv; have hV:Tendsto y (𝓝 (0:ℝ)) (𝓝 1):=(by simpa only[inv_one] using! hv.inv); exact hV.mono_left nhdsWithin_le_nhds
    have hg:Tendsto (fun t:ℝ=>A (fun i=>t⁻¹ • X i t)) θ (𝓝 (A U)):= A.cont.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)
    have hv:= ((adContour G).continuousAt (x:=(1,A U))).tendsto.comp (hQ.prodMk_nhds hg); change Tendsto (fun t=>G.adjoint (y t) (A (fun i=> t⁻¹ • X i t))) θ (𝓝 (G.adjoint 1 (A U))) at hv; rw [G.adjoint_one] at hv; refine hv.congr (fun t=>?_)
    erw [ContinuousMultilinearMap.map_smul_univ (c:=fun _=>(t:ℝ)⁻¹),prod_const,card_univ,Fintype.card_fin,inv_pow,map_smul];rfl
end YM.OPE.Variance

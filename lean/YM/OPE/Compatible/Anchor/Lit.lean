import YM.OPE.Compatible.Anchor.Costs
/-! # Top germ angular momentum -/
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
variable {i j d k m r n l:ℕ}{Z I J M E F:Type}
local notation "θ"=> 𝓝[>] (0:ℝ)
lemma FundS (A: Fin r→ℕ)(E:Fin r→Type)[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)][NormedAddCommGroup F][NormedSpace ℝ F](P:ContinuousMultilinearMap ℝ E F)(v:(i:Fin r)→ℝ→E i)(u:(i:Fin r)→E i)(h:∀ i,BillUp (E i) (A i) (v i) (u i)):
    BillUp F (∑ i,A i) (fun t=> P (fun i=>v i t)) (P u):=by
         have hv:Tendsto (fun t:ℝ=> P (fun i=>(t^A i)⁻¹ • v i t)) θ (𝓝 (P u)):= P.cont.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h); refine hv.congr (fun t=>?_); rw [ContinuousMultilinearMap.map_smul_univ (f:=P) (c:=fun i:Fin r=>((t:ℝ)^A i)⁻¹),prod_inv_distrib,prod_pow_eq_pow_sum];
lemma scoringUp (i:Fin d) (x:Alphabet G d): BillUp (Taylor G i.val) (i.val+1) (fun t=>templateX G i.val (showerW d t x)) (x i):=by
    let f(j:Fin d):=templateX G i.val (jetΦ G j.val (x j)); let K(j:Fin d)(t:ℝ):= t^(j.val+1) • f j; rw [show (fun t=>templateX G i.val (showerW d t x))=fun t:ℝ=>∑ j,K j t from ?_]; swap
    · funext t;rw [showerW,LinearMap.sum_apply,map_sum]; apply sum_congr rfl; intro j _; exact map_smul (templateX G i.val) _ _
    let v(j:Fin d):=if j=i then f i else 0; have he:(∑ j,v j)=x i:=by unfold v; rw [sum_ite_eq',if_pos (Finset.mem_univ i)]; exact decisions (x i)
    change Tendsto _ _ _; rw [← he]; apply UpLayer univ K v; intro j _
    by_cases hp:i=j
    · subst j; rw [show v i=f i from if_pos rfl]; exact UpPure _
    rw [show v j=0 from if_neg (Ne.symm hp)]; by_cases ht:i.val≤ j.val
    · have heq:=UpPrice (E:=Taylor G i.val) (p:=f j) (Nat.add_le_add_right ht 1); rw [if_neg (fun h=>hp (Fin.ext (by omega)))] at heq; exact heq
    have hx: f j=0:= retainedX _ (ledgeL (x j).val) (by omega); unfold K BillUp; simp [hx]
noncomputable abbrev SpiceK (G:Gauge)(α:Fin r → Fin d):= SpiceD G (fun i=>(α i).val)
lemma coupT (k:Fin r→Fin d)(Q: SpiceK G k)(x:Alphabet G d): BillUp G.Color (rankX k) (fun t=> ClearW Q (showerW d t x)) (Q (fun i=> x (k i))) := FundS _ _ _ _ _ fun i=> scoringUp (k i) x
lemma UpBrick {f g:ℝ→ℝ}{x y:ℝ}(h:BillUp ℝ i f x)(ht:BillUp ℝ j g y): BillUp ℝ (i+j) (f*g) (x*y):=by
     apply (h.mul ht).congr; intro t; simp only[pow_add, _root_.mul_inv_rev, smul_eq_mul, Pi.mul_apply]; ring
lemma UpColor {x:G.Color} {p:ℝ→G.Color} (h:BillUp G.Color i p x)(a:G.ColorIndex): BillUp ℝ i (fun t=>p t a) (x a):= Up_h h (chin a)
abbrev Dotty (x y:G.Color):ℝ:= ∑ i,x i * y i
lemma UpDot {x y:G.Color}{p q:ℝ→ G.Color}(h:BillUp G.Color i p x)(hp:BillUp G.Color j q y): BillUp ℝ (i+j) (fun v=> Dotty (p v) (q v)) (Dotty x y):= UpLayer univ _ (fun i:G.ColorIndex=>x i*y i) (fun i _=>UpBrick (UpColor h i) (UpColor hp i))
end YM.OPE.Variance

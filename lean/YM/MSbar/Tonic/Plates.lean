import YM.MSbar.Duel.Cycle
import YM.MSbar.Folia.Cinema
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tonic
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{c f:Side}{S:StepData c f}
local notation "J"=> Positions (Primary c G)
local notation "X"=> Primary c G
local notation "Q"=> Config G f
variable (β t:ℝ)(U:Config G f)(M:Config G c)(v:S.Choices)
noncomputable def rowS (G:Gauge) (b r:ℝ)(e:Bond c)(p:G.Mat)(x:Positions (Primary c G)):ℝ:=b*(1-(Matrix.trace (G.mat (postcard G c r x e)*p)).re / G.repDim)
noncomputable def plateV (S:StepData c f)(β r:ℝ)(A:Bond c→ G.Mat) (y:J) := -β*S.kernel.penalty*(∑ i:Bond c,rowS G 1 r i (A i) y)
noncomputable def tribe (S:StepData c f)(β r:ℝ)(U:Config G f)(v:S.Choices): Positions (Primary c G)→ℝ:=fun x=> -β*noiseTaylor S (postcard G c r x) U v
noncomputable def wing (S :StepData c f)(U:Config G f)(v:S.Choices): Bond c→ G.Mat:= fun i=>G.mat ((S.prediction U v i)⁻¹)
local notation "B₀"=> tribe S β t U v
local notation "Φ"=> wing S U v
variable (x:Positions (Primary c G))(L:List (Primary c G))(i j:Primary c G)(e:Bond c)
lemma lines : tribe S β t U v= plateV S β t (wing S U v):=by unfold tribe plateV rowS wing noiseTaylor Gauge.price; simp only [G.mat_mul,mul_assoc,one_mul]
lemma stage_Row (a:ℝ) (e:Bond c): ContDiff ℝ ω (fun x: J × G.Mat=>rowS G a t e x.2 x.1):=by
    let g(x:J):=tint G _ x; have he(x): G.mat (postcard G c t x e) = G.mat (G.lieExp (g (t • x) (e.1,Exterior.coord e.2))):=congr_arg _ (Work.F03.represent_link _ _)
    have hu : ContDiff ℝ ω (fun v:J × G.Mat=>G.mat (postcard G c t v.1 e)*v.2) :=by simp_rw [he]; let m(y:J× G.Mat):=y.1; have hp:ContDiff ℝ ω (fun z:J × G.Mat=> t • m z):=contDiff_fst.const_smul t; let L:=(tint G (Body 1 c)); exact (G.exp_jet.comp ((contDiff_apply ℝ G.Color (e.1,Exterior.coord e.2)).comp (L.contDiff.comp hp))).mul (contDiff_snd)
    let L':= Complex.reCLM.comp (Matrix.traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap; exact ContDiff.mul contDiff_const (contDiff_const.sub ((L'.contDiff.comp hu).div_const _))
lemma river (s:StepData c f): ContDiff ℝ ω (fun v:Positions (Primary c G)× (Bond c→G.Mat)=>plateV s β t v.2 v.1):=by unfold plateV; apply ContDiff.mul contDiff_const; apply ContDiff.sum; intro i _; refine (stage_Row t 1 i).comp (f:=fun v:J× (Bond c→ G.Mat)=>(v.1,v.2 i)) ?_; exact contDiff_fst.prodMk ((contDiff_apply ℝ G.Mat i).comp contDiff_snd)
lemma bean : ContDiff ℝ ω (tribe S β t U v) :=by rw [lines]; exact (river β t S).comp (f:=fun x:J=>(x,Φ)) (contDiff_id.prodMk contDiff_const)
noncomputable def crew (S:StepData c f)(β r:ℝ)(U:Config G f)(v:S.Choices):= fun x:Positions (Primary c G)=> Real.exp (tribe S β r U v x)
noncomputable def strap (S:StepData c f)(β r:ℝ)(v:S.Choices)(x: Positions (Primary c G))(L:List (Primary c G))(U:Config G f) := buoy (crew S β r U v) x L / crew S β r U v x
local notation "Uθ"=> crew S β t U v
lemma twig (i:Primary c G) : strap S β t v x (L++[i]) U= Yarn L.length (fun h:List Bool=> strap S β t v x (takeout true h L) U *buoy (tribe S β t U v) x (takeout false h L ++ [i])):=by
    let f:= Uθ; let g:= B₀; let n:=L.length; let h:=Duel.stallA g i; have hv:ContDiff ℝ (↑(n+1:ℕ)) g:=(bean ..).of_le le_top; have hh:ContDiff ℝ (↑(n+1:ℕ)) f:=hv.exp; have he: Duel.stallA f i=(f*h):=by funext z; unfold Duel.stallA f crew; rw [(hv.differentiable (by simp) z).hasFDerivAt.exp.fderiv];rfl
    have hx(l:List X)(hx:l.length≤ n)(f:J→ℝ)(h:ContDiff ℝ (↑(n+1:ℕ)) f): buoy f x (l++[i])= buoy (Duel.stallA f i) x l:= by unfold buoy; simp only [List.map_append,List.map_cons,List.map_nil]; rw [Lis.fore (n+1) h.contDiffAt, Lis.takeG (n+1) h.contDiffAt]; rfl; all_goals rw [List.length_map]; omega
    have ht:ContDiffAt ℝ n f x:= hh.contDiffAt.of_le (by exact_mod_cast Nat.le_succ n); unfold strap; rw [hx L le_rfl f hh,he,paisley n f h _ _ ht ((hv.contDiffAt.fderiv_right (m:= (n:ℕ∞ω)) (by simp)).clm_apply (g:=fun _=> (@bolt X i)) contDiffAt_const) le_rfl, div_eq_mul_inv,← poker]; refine stitch _ fun v ht=> ?_; rw [show buoy h _ _= _ from (hx (takeout false v L) ((sunset _ v L ht).trans_le ((part_le ..).trans_eq ht)) g hv).symm]; unfold f g; ring
end YM.MSbar.Tonic

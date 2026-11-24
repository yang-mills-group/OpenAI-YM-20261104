import YM.MSbar.Lease.Funds
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Cottage
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup Bulk
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {c f:Side} {S:StepData c f} {U:Config G f}{R: Rep G f}{R':Rep G c}{σ C T K B a b v r δ w β u:ℝ}{M k m:ℕ}
open ConnectedActivityE6 Finset RG.PathData Tree Push.Uniform Pressure SectorNext.Vacuum AnalyticBridge.VerifiedReset Next.Scheduling Precision Stock Metric Posture
variable (P:Patch)(D:KernelChoices)(p:Palisade)(J:Voice G) (L L' : Stage) (g : Clear G J)(x c₀:ℝ)
set_option quotPrecheck false
local notation "Ξ"=> tip G P.L
local notation "Kx"=> sizingW D
local notation "q!"=> voyageB (tip G P.L x)
local notation "b!"=> radiusB (tip G P.L x)
local notation "E!"=> skies (tip G P.L x)
local notation "r'"=> rot p (tip G P.L x)
local notation "H!"=> fear -- unused
variable (e d:ℝ)(f' l:ℝ→ℕ)(hf:Beam G P.L (fun x=>(f' x:ℝ)))(hg:Beam G P.L (fun x=>(l x:ℝ)))
include hf hg
lemma funding (G':Gauge) : Pole G P.L (fun x=> leaseX L P G p e x e (f' x) (l x)) :=by
   let v x:=f' x*4; let d x:= tip G P.L x; have hv:Beam G P.L (fun x=>(v x:ℝ)):=by unfold v; push_cast; exact hf.mul (Beam.coin _)
   let j x:=lastY P (f' x); have he:Beam G P.L (fun x=>(j x:ℝ)):=by unfold j lastY; push_cast; exact hf.mul (Beam.coin _)
   have hm:=leaseGlow G P v hv; let r x:=curtains L G (tip G P.L x) e p (v x) (f' x) (l x) (j x); have hr:Beam G P.L r:= ((Beam.coin _|>.mul hg).add ((heat_glow G P p L f' hf).add hm)).add he -- args
   exact (heatZero G P r hr).mul ((Rate.power (G:=G) (L:=P.L) (a:=e)).mul_right _)
omit hg in
lemma rateBed (e' :ℝ): Rate G P.L e' (fun x=> bedLease G P x (f' x) e'):=by
   let g x:= ((f' x:ℝ)*4); have hg: Rate G P.L 0 g:=(hf.tick).mul_right _; have hh:= valor G P.L e'; let H x:= (Lattice.box (macroR P)).card*courage G P.L x+courage G P.L x+(Fintype.card G.ColorIndex:ℝ)* (tip G P.L x)^e'; have hz : Rate G P.L e' H:=((hh.mul_left _).add hh).add (Rate.power.mul_left _); have he:=hg.mul hz; rw [zero_add] at he; exact he
include g
set_option pp.universes false in
lemma honored (m:ℕ): ∀ᶠ x in atTop, Credit P D G J p L L' m e x d (f' x) (l x) :=by
   let a:=min d (d-e)-1; let c:=tip G P.L
   have hx:a<d:=by unfold a; linarith only [min_le_left d (d-e)];
   have hz:e+a<d:=by unfold a; linarith only [min_le_right d (d-e)]
   let v x:= bedLease G P x (f' x) a; let H x:= payRoad L' G P x (f' x); let u x:= c x^e; let k x:= leaseX L' P G p e x e (f' x) (l x); let f x:= u x*v x+(H x-1)*u x+H x*k x
   have hl:Rate G P.L a v:=rateBed P f' hf _ -- order
   have hk:Pole G P.L k:=funding P p L' e f' l hf hg G
   have hp : Pole G P.L (fun x=> H x-1):=Pole.error G P (status G P L' f' hf)
   have hP:Rate G P.L 0 H:= ((hp 0).add (Rate.const (G:=G) (L:= P.L) (1:ℝ))).congr (Eventually.of_forall fun x=> (sub_add_cancel (H x) 1).symm) -- name
   have he:Rate G P.L e u:=Rate.power; have hF:=he.mul hl
   have hi :Rate G P.L (e+a) f:= ((he.mul hl).add (Pole.mul hp he _)).add ((hP.mul (hk _)).weaken (by rw [zero_add]))
   by_cases hy:0<p.gap∧0<p.a∧0< p.density
   swap
   · exact Eventually.of_forall fun x=>⟨fun X Y F i W R R' ha hc h hh _ _ _ _=> (hy ⟨hh.buys.pos_m,hh.buys.pos_a,hh.buys.pos_C⟩).elim⟩
   filter_upwards [ (Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G P.L)).eventually_ge_atTop 1, hi d hz, hl d hx, fees p P J g, solders P D J L L' p g hy.1 hy.2.1 hy.2.2, ever P D J L L' p g m a] with x hx hf0 hd Hc h H'
   constructor
   intro s T S X Y F i W R R' A A' hm t h₀ hY hL hw U A₀ B Q Y₀ G₀ -- shift naming Q=V; Y₀=μ etc
   have hC':=hm.case_; rw [A] at hC'; obtain ⟨h₁,hGo,hQc,hD,hβ,hno,hz₁,hz₂,hz₃,hz₄,hz₅,hz₆,hz₇,hz₈⟩:= Hc
   have hjS:=h R R' hC' hm.hull
   let I:=base J U; have hQ: Q ∈ calm G s I:=Tinted.litV P D J p L L' x W hjS g hw _ rfl hz₄
   have ha: R.p.B ≤ voyageB U:=by rw [hC'.size]; unfold voyageB; change radiusB U≤ _+radiusB U+_; omega -- check let
   have hp : Posture p J F A₀ B (base J U) (rot p U) (voyageB U) (radiusB U) X Y W Y₀ R.p :=by
       have ht:= terror F i p W t hw hβ; have hv : Posture p J F A₀ B (base J U) (rot p U) (voyageB U) (radiusB U) X Y W Y₀ R.p:= ⟨hGo,hQc, by linarith only [ht,hz₁],hw.trans hD,hQ,hz₄,hz₂,hz₃,hC'.threshold ▸ hz₅,ha,h₀,A.symm ▸ hz₆, ?_⟩; exact hv
       unfold deepCopy; rw [hC'.size]; unfold voyageB; have he: U=tip G P.L x:=rfl; rw [he]; dsimp only; omega
   have hh:0<S.push R.beta R.eval Q:=by rw [← hm.taskEval]; unfold Rep.eval; rw [Activities.gas_one _ _ (voids hQ hjS.holm),mul_one]; exact Real.exp_pos _
   have hS: Admitted Q R S L'.width L'.paths (ability U) (lbt U) 1:=⟨hC'.lawful,fun i=> (hm.shine i).le,hh,S.isKernel hm.bends.1 _⟩
   have hv':chance S R Q G₀ᶜ ≤ v x := by
       apply (glows P D p J L L' F i W x a X Y g A A' hm t H' hjS hw hp hS).trans; let d₀:= (Lattice.box (macroR P)).card*courage G P.L x+courage G P.L x+ (Fintype.card G.ColorIndex:ℝ)*c x^a; unfold v bedLease; apply mul_le_mul_of_nonneg_right _ (show 0≤ d₀ from ?_); exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hY) (by norm_num); have hz:0<c x:=zero_lt_one.trans h₁;unfold d₀ courage; positivity
   refine ⟨hp,hv'.trans ((le_abs_self _).trans hd),fun u' ht hB hu=>?_⟩; let Ω:=ability U; let σ:= L'.width; let C:=L'.paths; let Z:= lbt U; have hv := brought P D p J L L' g x hm A A' X Y F i W hp t f' _ hL hY e hx
   let r(t:ℝ):= t^(-(1:ℝ)); let w':= woolModel F X J R Y i Q Y₀ A₀ B; let d₁:=wSize G R.p σ C Ω Z R.beta (voyageB U) Y.card X.card p (rot p U) B; let ε:= Real.exp (silkRoad C σ Ω Z R.beta X.card (voyageB U) R.p (radiusB U)); let a₁:= Real.exp d₁/moss G (r U) (board F X).card
   have hj:0<U:=zero_lt_one.trans h₁
   have hR : Rota (S:=S) R Q (youth F Y) F (board F X) G₀ w' a₁ ε:= Posture.harvest t g hp hS.lawful hm.bends.1 hC'.decent ((half_pos hj).le.trans hC'.beta) hz₇ hz₈ -- args
   let q:=courage G P.L x; have he : 0 ≤ q := (Real.exp_pos _).le; let δ₀:= q*(R.p.mass (youth F Y) (a₁* u x* 2)* Real.exp ((youth F Y).card*1:ℝ)); obtain ⟨hz,hs,hK⟩:= hv; have hz':0≤u x:=Real.rpow_nonneg hj.le _
   refine (Rota.revenue hS hR u' ht (u x) hB hu hm.bends.1 hm.primal hm.storm hm.lights hm.shine (voids hQ hjS.holm) he (sub_nonneg.mp hz) hv').trans (le_trans (b:=f x) ?_ ((le_abs_self _).trans hf0)); change u x * v x+(ε-1)* u x + ε* δ₀ ≤ _
   apply add_le_add (add_le_add_right (mul_le_mul_of_nonneg_right (sub_le_sub_right hs _) hz') _)
   · apply mul_le_mul hs hK; change 0 ≤ δ₀; unfold δ₀ BudgetPoint.mass; have hu:0≤a₁ := hR.rate_pos; positivity
     exact (Real.exp_pos _).le
end YM.MSbar.Heath.Cottage

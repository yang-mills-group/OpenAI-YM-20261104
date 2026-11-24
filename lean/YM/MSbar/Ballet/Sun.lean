import YM.MSbar.Ballet.Radar
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Ballet
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Alto Mosaic Mosaic.Issue
variable {G:Gauge}
open Supply Input
variable {O:ChartRatio G}{K:MapPrices}{B:Sheet G}{D:Rolls B}{Θ:Protection D}{Y0:Delays Θ}{W:Bar Y0}{I:Wait W}{P:PostCost D}(A:Directed G I O K P)
open Heath
-- Grow Season. Deliberately use Nest spring at each op including beyond N for Decent.
variable (Y: History G)(h:Y.Selected)(hM:∀ i p,Bid.Larger (G:=G) (Y.levels.clock.op i p))(N p i:ℕ)(hi:i ≤ N)
local notation "R"=> Y.rep N p
include hi h
lemma betaP :0 < (Y.rep N p i).beta:= (half_pos (zero_lt_one.trans (Y.levels.fits.delayed i))).trans_le (h.represents N p i hi).band.1
include hM
open MeasureTheory
lemma validP : Touch (Y.rep N p i).eval∧ Continuous (Y.rep N p i).eval :=by
    induction hi using Nat.decreasingInduction with
    | self=>
       let b:= (Y.rep N p N).beta; have hb:= betaP Y h N p N le_rfl; let F: Config G (Y.S.side N p)→ℝ:= bare b
       have he:Continuous F:= bare_cont _; obtain ⟨C,hC⟩:= isCompact_univ.bddAbove_image (f:=fun x=>‖F x‖) he.norm.continuousOn; rw [(h.starts N p).2]; exact ⟨⟨fun t U=>bare_gauge b U t,fun U s t=> bare_pull b U s t,⟨he.measurable,C,fun i=>hC ⟨i,Set.mem_univ _,rfl⟩⟩,bare_pos b⟩, he⟩
    | of_succ i hi ih=> rw [(h.steps N p i hi).1]; have hp:=Y.levels.blocks i p; exact ⟨safePush _ ⟨hp.branches,hp.symmetric,hp.gauge,hM ..⟩ ih.1,Progress.DirectedRecipe.continuous_push _ _ hp.branches _ (ih.1.stage.integrable _)⟩
variable (he :∀ j, Y.levels.clock.hatBeta (j+1) ≤ 2*Y.levels.clock.hatBeta j)
include he
lemma slope : let S:= Y.levels.clock; let c:= S.hatBeta i; Quasi (R i).eval (c*Stock.sizingW S.kernel) :=by
    intro S c; let F:= (R i).eval; have ht (C:ℝ)(h:Quasi F C)(ht:C ≤ c*Stock.sizingW S.kernel): Quasi F (c*Stock.sizingW S.kernel) := ⟨h.cost.trans ht,h.positive,fun i U V=> (h.shift ..).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht (G.chord_nonneg _))) (h.positive ..))⟩
    let b:= (R i).beta; have hx:0<c:= zero_lt_one.trans (Y.levels.fits.delayed i); have hp:=h.represents N p i hi; have hb:S.kernel.penalty>0:= S.kernel.penalty_pos
    by_cases hh:i=N; · subst i; refine ht _ (?_:Quasi F (wrath b)) ?_
                       · unfold F; rw [(h.starts N p).2]; exact bare_quasi b (betaP _ h _ _ N le_rfl|>.le)
                       have he: Fintype.card PlaqAxes=6:= by decide
                       have hb0:b ≤ 2*c:= hp.band.2; unfold wrath Stock.sizingW; rw [he]; push_cast; nlinarith only [hb0,hx,mul_pos hx hb]
    have hℓ:i+1 ≤ N:=by omega
    let L:=S.op i p; let A:= (R (i+1)).eval; let B':=(R (i+1)).beta
    apply ht (B'*S.kernel.penalty*2)
    · unfold F; rw [(h.steps N p i hℓ).1]; have hx:= validP Y h hM N p _ hℓ; exact noisy_push _ (hM i p|>.1) (betaP _ h _ _ _ hℓ|>.le) (hx.1.stage.integrable _) (fun i=> (hx.1.pos i).le)
    have hw: B' ≤ 2*(2*c):= (h.represents N p _ hℓ|>.band.2).trans (mul_le_mul_of_nonneg_left (he i) zero_le_two); unfold Stock.sizingW; nlinarith only [mul_le_mul_of_nonneg_right hw hb.le,hx,mul_pos hx hb]
omit he hM
open Push.AbsoluteSums
lemma fact (ht:WilsonStartup.Decent (Y.levels.params i).clip (Y.levels.budget i)) : Stock.FaceValue (Y.levels.params i) (Y.levels.clock.hatBeta i) (Y.rep N p i):=by
   obtain ⟨hg,hp,hb,hW⟩:=h.represents N p i hi
   let S:=Y.levels.clock; let Q:= S.hatBeta i; let T:=R i; have hV : S.loopCap i ≤ Stock.lbt Q:=by
       have he:S.monitor i≥1:=Real.one_le_exp (sq_nonneg _)
       have hr:S.theta (S.J i)≤1:= le_trans (Y.levels.fits.thetaRange i|>.2) (inv_le_one_of_one_le₀ (by exact_mod_cast (le_trans (by omega : 1 ≤ 4) (S.adm i))))
       exact mul_le_mul_of_nonneg_left (le_trans (Real.rpow_le_rpow_of_exponent_le he hr) (le_of_eq (Real.rpow_one _))) zero_le_two
   have hh : S.forcedAllowance i ≤1:= Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by unfold Calendar.monitor; positivity))
   refine ⟨by rw [hg];rfl,hp,Y.levels.fits.delayed i,hW.1,hW.2,by rw [hg];rfl,by rw [hg]; rfl,?_,by rw [hg,hp]; exact ht⟩
   obtain ⟨hU,hd⟩:=hb; obtain ⟨ha,hf,hM,hQ,hw⟩:=hd; obtain ⟨w,h₃,hY⟩:=hw
   exact ⟨{hU with two:= budget_loosen hU.two hV},ha,hf,hM,hQ,w,h₃, fun x=>budget_loosen (hY x) hh⟩
end YM.MSbar.Ballet

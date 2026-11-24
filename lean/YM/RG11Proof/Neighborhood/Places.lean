import YM.RG11Proof.Grove.Generic
/-!
# OPE shrinkage geometry at a fixed subtraction length one

Inner coordinates x at scale r=e^-s (relative to chosen center c),
all distinct; exterior c & y at fixed separated positions. Full
separation for r sufficiently small (prove for any fixed or compact families
on all supports with y-geometry fixed or compact). Distinguish n, q arity
from ℝ s; allow n or q=0. Nothing about contact or growing-scale
approximations unless costs separately announced.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Neighborhood
open scoped Classical BigOperators ContDiff Topology
open Set Function Filter MeasureTheory WithLp
variable {G:Gauge}{F:Labels.Frames G}{n m:ℕ}

/-- A fixed environment of arbitrary exterior insertions, all separated from
center and each other. -/
structure Tail (m : ℕ) where
  c : E4
  y : Points m
  apart : Points.cons c y∈conf _

/-- join at chosen positive radius -- can be defined at arbitrary t. -/
def driven (t:ℝ)(x:Points n)(y:Tail m):Points (n+m) := points <| Fin.append (fun i:Fin n=> y.c+t • (x i)) (y.y.ofLp)

def shifted (t:ℝ)(x:Points n)(c:E4):Points n:=points fun i=>c+t • (x i)

def coupled (x:Points n)(y:Points m):Points (n+m):=points (Fin.append x.ofLp y.ofLp)

@[simp] theorem shifted_at (t:ℝ)(x:Points n)(c:E4)(i) : shifted t x c i=c+t • (x i):=rfl
@[simp] theorem coupled_pull (x:Points n)(y:Points m)(i:Fin n):coupled x y (Fin.castAdd m i)=x i:= Fin.append_left ..
@[simp] theorem coupled_push (x:Points n)(y:Points m)(i:Fin m):coupled x y (Fin.natAdd n i)=y i:= Fin.append_right ..

theorem rounded : Continuous (fun z:Points n × Points m=> coupled z.1 z.2):=by
   unfold coupled points
   apply (PiLp.continuous_toLp ..).comp
   have he:=Fin.continuous_append (X:=E4) n m
   exact he.comp (((PiLp.continuous_ofLp 2 _).comp continuous_fst).prodMk ((PiLp.continuous_ofLp 2 _).comp continuous_snd))
theorem shifted_ball (y:Tail m): Continuous (fun z:ℝ × Points n=>shifted z.1 z.2 y.c):=by
   unfold shifted points; fun_prop

 theorem smooth_driving (y:Tail m):Continuous (fun z:ℝ × Points n=>driven z.1 z.2 y):=
   rounded.comp ((shifted_ball y).prodMk (g:=fun _=> y.y) continuous_const)

theorem shifted_conf (t:ℝ)(h:0 < t)(c:E4){x:Points n}(hx:x∈conf n): shifted t x c∈ conf n:=by
   intro i j he; apply hx
   change x i=x j
   rw [←one_smul ℝ (x i),←one_smul ℝ (x j),← inv_mul_cancel₀ h.ne',mul_smul,mul_smul,show t • x i=t • x j from add_left_cancel (a:=c) he]
theorem coupled_conf {x:Points n}{y:Points m}(h:x∈conf n)(hf:y∈conf m)(he:∀ i j,x i≠y j):coupled x y∈conf _:=by
   intro i j; induction i using Fin.addCases with
   | left i =>
     induction j using Fin.addCases with
     | left j=> intro hp; exact congrArg (Fin.castAdd m) (h (by simpa only [coupled_pull] using hp))
     | right j=> intro hp; exact False.elim (he i j (by simpa only [coupled_pull,coupled_push] using hp))
   | right i=>
     induction j using Fin.addCases with
     | left j=> intro hp; exact False.elim (he j i (by simpa only [coupled_pull,coupled_push] using hp.symm))
     | right j=> intro hp; exact congrArg (Fin.natAdd n) (hf (by simpa only [coupled_push] using hp))

-- separation eventually along log, uniform over inner compact K and outer
-- compact Γ represented by c,y Joint separate at every σ. Requires fixed gaps
-- in exterior, e.g. if varying exhibit continuity & sep on compact. Later
-- growing geometry version in credit needs separate placement proof (trans
-- factorized through matched frames). Basic proof using isCompact.tendsto (?)
 theorem isolates {K:Set (Points n)} (hK:IsCompact K)(h:K ⊆conf n)(y:Tail m):
    ∀ᶠ u:ℝ in atTop,∀ x∈K,driven (Real.exp (-u)) x y∈conf _:=by
   obtain ⟨C,hC⟩:=hK.exists_bound_of_continuousOn (f:=fun x:Points n=> x) continuousOn_id
   have hm : y.y∈conf m:=Points.tail_in y.apart -- tail definition/propositions
   have hc (j:Fin m): y.c ≠ y.y j:=by
     intro he; apply Fin.succ_ne_zero j; exact y.apart (by change Points.cons _ _ j.succ=Points.cons _ _ 0; simpa [Points.cons] using he.symm)
   have hlim(j:Fin m):∀ᶠ u:ℝ in atTop,Real.exp (-u)*C < ‖y.y j-y.c‖:=(Filter.Tendsto.eventually_lt_const (norm_pos_iff.mpr (sub_ne_zero.mpr (hc j).symm)) (by
     have he: Filter.Tendsto (fun u:ℝ=>Real.exp (-u)) Filter.atTop (𝓝 0):=Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
     simpa using he.mul_const C))
   have ht:∀ᶠ u:ℝ in atTop,∀j:Fin m,Real.exp (-u)*C < ‖y.y j-y.c‖:=Filter.eventually_all.mpr fun j=> hlim j
   filter_upwards [ht] with u hu x hx
   apply coupled_conf (shifted_conf _ (Real.exp_pos _) _ (h hx)) hm
   intro i j hj
   have he:Real.exp (-u) • x i=y.y j-y.c:=eq_sub_of_add_eq' hj
   apply (hu j).not_ge
   rw [←he,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
   exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le x i).trans (hC _ hx)) (Real.exp_pos _).le
end YM.RG11.Neighborhood

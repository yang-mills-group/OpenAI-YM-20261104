import YM.FormalBulk08.Hay.Motor
import YM.FormalBulk08.Borough.Pine
import YM.Pert.Flow.ActionStep

/-!
 Physical witness translation for the LOW common germs. Logical force: this is an
 identification at positive perturbative orders with the *prescribed nonlinear* base
 and reset of the actual paths. Doesn't ask density, measure, support masks
 in hypotheses except exact matched sizes/provenance; doesn't supply actual
 error estimate from these. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.First
open Function Filter Set MeasureTheory Lattice RG Exterior Wilson Precision
open Stationary hiding shine Rays
open scoped Topology BigOperators ENNReal Matrix ContDiff Classical
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa Broc City Cork Lotus Shore Gorge Laurent Bloch Flat Next.Free Bank Wine Dove
open Next.Foundations PhysicalNext.Repeat.Legato
variable {G:Gauge}{K:KernelChoices}{ρ:ChartRatio G}{A:Levels G}{C:Family G}
-- avoid abusing pole `alpha`; this is formal per-installment.
def stride (A:Levels G)(R:∀ i, Lodge ((A.clock.op i 0).patch))(ρ:ChartRatio G)(a:hue G)(N m:ℕ): Pence:= scalar a (waken (destination A N m) (R m) (model A R (Hay.Wday A) ρ a N (m+1)) ρ (Hay.Wday A m))
lemma gains (R:∀ i,Lodge ((A.clock.op i 0).patch))(a:hue G)(hp:LocalRatio ρ)(hs:G.Simple) (N m:ℕ)(h:m<N):
    Fresh (stride A R ρ a N m) ∧ Still (stride A R ρ a N m):= by
   have H := (genu A R (Hay.Wday A) _ a hp hs (N:=N) (i:=m+1) h).toStory
   exact sig_mat _ _ (creed _ _ _ _ _ H (A.clock.adm _) hp) A.clock.kernel.penalty_pos (A.clock.adm m)
lemma two_by (p q:Pence) : coeff 2 (p*q)= coeff 0 p *coeff 2 q + coeff 1 p * coeff 1 q + coeff 2 p * coeff 0 q:= by
   rw [coeff_mul,show Finset.HasAntidiagonal.antidiagonal (2:ℕ)={(0,2),(1,1),(2,0)} from ?_]
   · simp [add_assoc]
   decide
lemma spin_price (p:Pence)(h:Fresh p)(hp:Still p) : Through 3 (wake p) (X+ PowerSeries.C (- coeff 2 p/2) * X^3) := by
   let t:=nextU p; have hv:= fresh_N p; have he := next_even p h hp 1 (by norm_num); have H:= congr_arg (coeff 2) (post_grid p h); rw [two_by,sq,two_by,h,hp 1 (by norm_num), hv,he] at H
   simp only [one_mul,zero_mul,add_zero,  show coeff 0 (nextU p*nextU p)=1 from Fresh.mul hv hv, mul_one] at H
   intro i hi; rw [wake,map_add,coeff_C_mul];interval_cases i
   · simp [coeff_zero_eq_constantCoeff_apply]
   · change coeff (0+1) _=_;rw [coeff_succ_X_mul,fresh_N p];norm_num [coeff_X_pow]
   · change coeff (1+1) _=_;rw [coeff_succ_X_mul,he]; norm_num [coeff_X_pow,coeff_X]
   · change coeff (2+1) _=_; rw [coeff_succ_X_mul]; norm_num [coeff_X_pow,coeff_X,coeff_one] at *; linarith only [H]
variable (C)
abbrev perc (m:ℕ):= C.path.levels.clock.J m
variable {C}
-- every tor size; not a regulator-limit claim for thermal discrepancy
lemma low_use (hG:G.Simple)(hp:Provenance G C ρ)(h:LocalRatio ρ) (N p m:ℕ)(hz:m≤N)
   (L:∀ i,Lodge ((C.path.levels.clock.op i 0).patch)) (a:hue G) :
    let A:= C.path.levels
    let V := A.params m
    let K:= (C.path.rep N p m).path
    ∀ n:Side, Through 2 (stone (Dove.model A L (Hay.Wday A) ρ a N m) n) (Hay.novel V.clip K n) := by
   obtain ⟨J,T,Q,Y,X,hT,E,H⟩:=hp.vacuum
   intro S V K; obtain ⟨δ,B,D,hd,hB,hD,W⟩:= Hay.manuscript G hG V.width V.paths V.clip.direct V.width_pos V.paths_pos.le V.clip.quadratic_pos.le 2
   have hb : K=T.path N m:= E N p m hz; rw [hb]; obtain ⟨P,hP,hk⟩:= W V.clip le_rfl _ _ (hT.cap N m hz)
   intro n; rw [← hP.buys]; exact Hay.diary (Hay.mature L h hG hT N a m hz P hP) n
-- formal payout even ζ=0 low growth. Stronger than raw calibration identities.
lemma beta_point (hG:G.Simple)(hp:Provenance G C ρ)(h:LocalRatio ρ) (N p m:ℕ)(hz:m<N)
    (L:∀ i,Lodge ((C.path.levels.clock.op i 0).patch))(a:hue G):
    let Z:= stride C.path.levels L ρ a N m
    |C.path.β N p m - C.path.β N p (m+1) - coeff 2 Z| ≤ 1 ∧
     |coeff 2 Z + G.slopeConstant*Real.log ((C.S.block m).val:ℝ)|+1 ≤ (C.path.levels.params (m+1)).drift
   := by
   obtain ⟨J,T,Q,Y,X,hT,E,H⟩:=hp.vacuum
   intro Z; have he : coeff 2 Z=T.alpha N m:= Hay.first_read L h hG hT N m hz a
   rw [he];exact ⟨H N p m hz,hT.kinetic N m hz⟩
end YM.FormalBulk08.First

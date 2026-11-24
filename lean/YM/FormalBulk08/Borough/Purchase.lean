import YM.FormalBulk08.Borough.Market
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Borough
open Lattice Laurent Bloch Precision Stationary RG Wilson Filter Function
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
open Next.Free Reef Flat Dove Dove.Lab North Elm Spigot Aster Source Drops Labels
open RG.Supply Push.PriceCompiler
variable {G:Gauge}{K:KernelChoices}{W:Borough.Window G K}{F:∀ d,Frame G d}{H:Hol G}{ρ:ChartRatio G}{Q:Herald}{Y:Sheet G}{P:Rolls Y}{T:Protection P}{V:Delays T}{M:Bar V}{B:Wait M}{A:Levels G}
-- Pure criteria at common data, no Readout premises.
structure Evergreens (K:KernelChoices)(Q:Herald)(F:∀ d,Frame G d)(H:Hol G)(ρ:ChartRatio G)(W:Borough.Window G K)(A:Levels G):Prop where
    beta : ∀ m,Real.exp 1 ≤ A.clock.hatBeta m
    payment: ∀ m, ∃ B:ℝ,0≤B∧ B ≤ ageZ (A.clock.hatBeta m) ∧ Counter K Q (A.S.block m) (A.clock.J (m+1)) F H ρ W B
    pre : Pre K W ρ F H (fun j=>(A.clock.factor j).val)
lemma pre_enlarge {f g:ℕ→ℕ}(p:Pre K W ρ F H f)(h:f≤g):Pre K W ρ F H g:= by
    have e (j:ℕ) : (f j:ℝ) ≤ (g j:ℝ):= by exact_mod_cast h j
    exact ⟨fun E j t a b c=> (p.vacuum E j t a b c).trans (e j),fun X E R d j t o a b c v k h=> (p.fields X E R d j t o a b c v k h).trans (e j)⟩ -- indent
lemma launch {f:ℕ→ℕ}(p:Pre K W ρ F H f)(hv:∀ i,f i≤(P.L i).val)(h:Prices K Q F H ρ W V)(ha:Paid B A): Evergreens K Q F H ρ W A:= by
    have hh (i):= h.allpay _ _ (ha.pays i); refine ⟨fun m=>(hh m).1,fun m=>?_,pre_enlarge p ?_⟩
    · conv at hh =>skip
      rw [← A.fits.sameFactor m,ha.lengths]; exact (hh m).2
    intro i; change f i≤(A.clock.factor _).val; rw [ha.lengths]; exact hv i
lemma launch_sheet (p:Pre K W ρ F H Y.floorL)(h:Prices K Q F H ρ W V)(ha:Paid B A):Evergreens K Q F H ρ W A:= launch p (fun i=> (P.large i).need) h ha
lemma lyre_log {x y:ℝ}(h:1≤x)(hy:x≤y):Real.log y≤ Real.log x + (y-x) := by
   have hx :0<x:= zero_lt_one.trans_le h; have h' : y/x ≤ 1+(y-x):= by rw [div_le_iff₀ hx]; nlinarith only [hy,h]
   have hp:=Real.log_le_sub_one_of_pos (div_pos (hx.trans_le hy) hx); rw [Real.log_div (hx.trans_le hy).ne' hx.ne'] at hp;linarith
lemma lyre_z {x y:ℝ}(h:Real.exp 1≤x)(hy:x≤y):1 ≤ ageZ x ∧ ageZ x ≤ ageZ y ∧ ageZ y ≤ ageZ x + (y-x):= by
   have hx:= (Real.exp_pos _).trans_le h; have hp:1≤Real.log x:= (Real.le_log_iff_exp_le hx).2 h; have h':=Real.log_le_log hx hy; have he:= lyre_log hp h'; have ht:=lyre_log (le_trans (show 1≤Real.exp 1 by exact (Real.one_le_exp (by norm_num))) h) hy; refine ⟨progZ h,add_le_add_right (Real.log_le_log (zero_lt_one.trans_le hp) h') _,?_⟩
   unfold ageZ; linarith
lemma ages (G:Gauge)(A:Levels G)(h:G.Simple)(hw:∀ i,Real.exp 1≤A.clock.hatBeta i){m n:ℕ}(hi:m≤n) :
    let s:= sowing A.S m n; 1 ≤ ageZ (A.clock.hatBeta m) ∧ ageZ (A.clock.hatBeta m) ≤ ageZ (A.clock.hatBeta n) ∧ ageZ (A.clock.hatBeta n) ≤ ageZ (A.clock.hatBeta m) + G.slopeConstant*s := by
    intro s; have hs (x:ℕ): A.clock.hatBeta x=A.clock.bar + G.slopeConstant*A.S.scale x:= rfl; let b:= A.clock.hatBeta; have he:b n=b m+G.slopeConstant*s:=by unfold b; rw [hs,hs]; unfold s sowing; ring
    have hy:b m≤b n:= by rw [he]; exact le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos h).le (sowing_plus _ hi))
    obtain ⟨hz,hq,hb⟩:=lyre_z (hw m) hy; exact ⟨hz,hq,hb.trans_eq (by congr 1; change b n-b m=_; rw [he];ring)⟩
end YM.FormalBulk08.Borough

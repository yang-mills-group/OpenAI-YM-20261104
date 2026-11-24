import YM.MS.Vibe.Dart
/-!
# Finite perturbative horizon argument: choose same ε radius regardless of t
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Emit
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{s u:ℝ→ T (Mob G)}{f g p q U: T (Mob G)}{S:GridR (Mob G)}{b c:Bool}{t r:ℤ}{a h n m k ℓ:ℕ}{i:ℂ}
def crop (p:T (Mob G))(n:ℕ):T (Mob G):= fun i=>if i≤n then p i else 0
abbrev Agree (n:ℕ)(p q:T (Mob G)): Prop:=∀ i≤n,p i=q i
lemma cropA (p:T (Mob G))(n:ℕ): Agree n (crop p n) p:= fun _ h=> if_pos h
namespace Agree
variable (hp:Agree n f g)(hv:Agree n p q)
include hp hv
lemma add : Agree n (f+p) (g+q):= fun i h=> by rw [Pi.add_apply,Pi.add_apply,hp i h,hv i h]
omit hv in lemma scale (x:ℂ): Agree n (x • f) (x • g):= fun i h=> by simp only [Pi.smul_apply,hp i h]
lemma pair (M:Signal.Pair (Mob G)): Agree n (pairW M f p) (pairW M g q):= by intro i he; rw [paired,paired]; refine Finset.sum_congr rfl fun k hk=>?_ ; obtain hv':= Finset.mem_antidiagonal.mp hk; rw [hp k.1 (by omega),hv k.2 (by omega)]
omit hv in lemma mode (M:MH (Mob G)): Agree n (promote M f) (promote M g):= fun i h=> congr_arg _ (hp i h) -- calc
omit hv in lemma grow (X:GridR (Mob G)): Agree n (X.grow f) (X.grow g):= add (mode hp X.P) (scale (pair hp hp X.X) _)
omit hv in lemma mat (X:GridR (Mob G)): Agree n (X.matCont f) (X.matCont g):= add (mode hp X.J) (scale (pair hp hp X.C) _)
lemma lives (X:GridR (Mob G)) : Agree n (X.lives f p) (X.lives g q):= add (mode hv X.P) (pair hp hv X.X)
lemma res (X: GridR (Mob G)) : Agree n (X.res f p) (X.res g q) := add (mode hv X.J) (pair hp hv X.C)
end Agree
lemma castR (hp:∀ i≤ n,Form0 false (f i))(h:∀ i≤n,Collar 0 (f i))(hv:∀ i≤n,Form0 false (g i))(hr:∀ i≤n, Collar t (g i)): Cast (crop f n) (crop g n) where
    f i:= by unfold crop; split; exact hp _ (by assumption); exact Form0.zero
    g i:= by unfold crop; split; exact hv _ (by assumption); exact Form0.zero
    order i:= by unfold crop; split; exact h i (by assumption)|>.sym; exact (show Collar 0 _ from (collar 0 G).zero_mem).sym
    order' i:= by unfold crop; split; exact hr i (by assumption)|>.sym; exact (show Collar 0 _ from (collar 0 G).zero_mem).sym
    level i:= railZero (by unfold crop; split; exact h i (by assumption)|>.ghost; exact (show Collar 0 _ from (collar 0 G).zero_mem).ghost)
variable (y:ℝ)
variable (F X:ℝ→ℝ→ T (Mob G))(hs:∀ j≤n,Sip i F (fun s y=> (Grid i y s G).grow (F s y)) j 0)(hv: ∀ j ≤n,Sip i X (fun s y=> (Grid i y s G).lives ( F s y) (X s y)) j t)
include hs
local notation "V" t => Grid i y t G
lemma trunc_m (hi:i∈Town)(s:ℝ)(w:Legs (Shore G m))(hp:net w=0): HasDerivAt (fun t=> (V t).matCont ( F t y) n m w) ((V s).lives (F s y) ((V s).matCont (F s y)) n m w) s:= by
    let f(t:ℝ):=F t y; let v(t:ℝ):=crop (f t) n; have hu(t) : Agree n (v t) (f t):=cropA _ _; have hc(t:ℝ)(j)(h:j≤n): Form0 false ( f t j):= (hs _ h).food t y; have hC(j)(h:j≤n): Collar 0 ( f s j):=(hs j h).mold s y;
    have H:= mat0 (x:=i) (tenorK i y) s n w hp hi (F:=v) (castR (hc s) hC (hc s) hC) ( fun r j =>?_) (fun j h=> ?_) (fun j h=> ?_); rotate_left
    · by_cases h:j≤ n; rw [hu r _ h]; exact hc r _ h; rw [show v r j= _ from if_neg h]; exact Form0.zero -- h expression implicit danger
    · obtain ht:=Agree.grow ( hu s) ( V s) j h; rw [ht]; exact (hs j h).myst s y
    · simp_rw [Agree.grow (hu s) ( V s) j h,hu _ _ h]; exact ( hs j h ).head s y
    have he:=Agree.lives ( hu s) ( Agree.mat ( hu s) (V s)) ( V s) n le_rfl; simp_rw [he, Agree.mat (hu _) ( V _) n le_rfl] at H; exact H
include hv
lemma trunc_q (hi:i∈Town)(s:ℝ): speed (fun t=> ( V t ).res ( F t y ) (X t y) n) (( ( V s ).lives ( F s y ) ( ( V s ).res ( F s y ) ( X s y ) ) + pairW ( V s ).X (( V s ).matCont ( F s y )) ( X s y ) ) n) s := by
    let f(t:ℝ):=F t y; let g(t:ℝ):=X t y; let Vt(t:ℝ):= crop (f t) n; let W(t:ℝ):= crop (g t) n; have hF(t) : Agree n ( Vt t) (f t):= cropA _ _; have hM(t): Agree n ( W t) (g t):=cropA _ _; have hp:= res0 (x:=i) (tenorK i y) s n hi (F:=Vt) (H:=W) (castR (fun j h=>(hs _ h).food ..) (fun j h=>(hs _ h).mold ..) (fun j h=>(hv _ h).food ..) (fun j h=>(hv _ h).mold .. )) (fun t j=>?_) (fun j h=>?_) (fun j h=>?_) (fun j h=>?_); rotate_left
    · by_cases hx:j≤n; rw [hM t j hx]; exact (hv j hx).food t y; rw [show W t j=0 from if_neg hx]; exact Form0.zero
    · rw [Agree.lives ( hF s) ( hM s) (V s) _ h]; exact (hv _ h).myst ..
    · simp_rw [hF _ j h, Agree.grow (hF s) (V s) j h]; exact (hs j h).head s y
    · simp_rw [hM _ j h, Agree.lives (hF s) (hM s) (V s) _ h]; exact (hv j h).head s y
    have hm t := Agree.res (hF t) (hM t) (V t); have hx:= Agree.add (Agree.lives (hF s) ( hm s) ( V s)) (Agree.pair (Agree.mat (hF s) (V s)) ( hM s) ( V s).X) n le_rfl; simp_rw [hx,hm _ n le_rfl] at hp; exact hp
end YM.MS.Emit

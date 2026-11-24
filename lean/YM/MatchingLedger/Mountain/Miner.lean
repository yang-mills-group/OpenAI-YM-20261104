import YM.MatchingLedger.Mountain.Youth
import YM.Push.STATIONARY_UNIFORM.Entries

/-! # Pay real principal. Segments of true paths through the torus.
 Interpolation strip here spends HALF of path width for the Taylor bills.
 Φ position for full (non-schur) log fieldDir, no root stencil support
 truncation. Adaptation of Work.F02 and Push.Uniform.Entries. `entry` already
 signed for whole pull; twist applies also to its support. Budget does *not*
 assert a new Forecast mask norm, it consumes the lengths actually rendered.
 At the following clients; no `Plenty` presumed.
 -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.MatchingLedger.Mountain
open Set Function Filter Precision RG MeasureTheory Lattice Wilson Metric Push.Uniform Exterior
open Work.F02
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace Classical
namespace Miner
variable {G:Gauge} {n:Side} (p:Clip) (W:PathData G) {σ C Λ:ℝ}
local notation "E"=> fieldDir G n 1
variable (q : Signed)(a:Site n)
def fortune (q:Signed)(v:fieldDir G n 1) := pull q 0 (represent v)
def ore (x:Site n)(b:PlaqAxes)(i:ℕ)(v:E) := W.ellTerms (x,b) i (fortune q v)
abbrev high (i:PlaqAxes)(R:PathData G)(k:ℕ):= (R.row i k).2.length
variable {z μ:ℝ} (hp:0<μ)(ht:2*μ≤σ)
variable (k:ℕ) (hW:W.Bounds p σ C Λ)
def paintCharge (G: Gauge) (k:ℕ):= (paint_supply G k).choose
lemma paintStamp (G: Gauge)(k:ℕ): PaintSupply G k (paintCharge G k):= (paint_supply G k).choose_spec

def amount (G: Gauge)(k:ℕ):= outerCost G k (paintCharge G k)
lemma allows_signed (x : E)(hx : x∈ball 0 1)(i:Edge (Site n)): Allows k (fun z:E=> G.mat ((fortune q z) i)) x (amount G k):= by
   have h(_i:Edge (Site n)): Allows k (fun z:E=> G.mat (represent z _i)) x (amount G k):= by
       let e:=(_i.1,coord _i.2); let L:E→L[ℝ]G.Color:= ContinuousLinearMap.proj e
       have hA : ‖L x‖≤ shade G:= (show ‖L x‖≤ ‖x‖ from norm_le_pi_norm x e).trans ((mem_ball_zero_iff.mp hx).le.trans (shade_one G))
       have hq: ‖L‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound L zero_le_one fun x=> (norm_le_pi_norm x e).trans_eq (one_mul _).symm
       simp_rw [Work.F03.represent_link]; exact ((paintStamp G k).2 (L x) hA).comp (f:=L) (allows_linear (hq.trans (shade_one G)) hA)
   unfold fortune pull Step.read; split <;> (first | exact (h _).inverse (f:=fun x => _) | exact h _)

def richness (G:Gauge)(k:ℕ)(μ:ℝ):= composeCost k ((1+2^k/radius μ)^k) (amount G k)
lemma richness_pos (G:Gauge)(k:ℕ){μ:ℝ}(hm:0<μ) : 0<richness G k μ:= by
   have h:0<amount G k:= outer_pos G k (paintStamp G k).1; unfold richness composeCost; positivity [radius_pos hm]
def height (G:Gauge)(k:ℕ)(μ:ℝ):= |slotConst G| * ‖colorReal G‖ * richness G k μ
lemma height_nn (G:Gauge)(k:ℕ) (hp:0<μ): 0≤ height G k μ:=by unfold height; positivity [richness_pos G k hp]
def value (G:Gauge)(k j:ℕ)(μ:ℝ):= |slotConst G|^j* richness G k μ
lemma value_nn (G:Gauge)(k j:ℕ) (hp:0<μ): 0≤ value G k j μ:=by unfold value; positivity [richness_pos G k hp]
include hp
lemma miners {x : E}(hx:x∈ball 0 1)(c:Slot)(s:ℝ): Allows k (fun z:E=> s • c.atSite (fortune q z) a) x (|s| * Real.exp (μ*c.length)*height G k μ):=by
   let T (v:E) := physical (fortune q v); have he:= allows_ambient (U:=fun y=> fortune q y) (allows_signed q k _ hx)
   have hh:= allows_real_of_entire k (Work.F02.slotExt_contDiff c (G:=G) a) (x:=T x) (radius_pos hp)
     (fun y hy=> (slotExt_bound (fortune q x) hp y (ball_subset_closedBall hy) c a).trans (show _≤ |slotConst G| * Real.exp (μ*c.length) from mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le))
   have hr:= (((hh.comp (f:=T) he).linear (colorReal G) le_rfl).smul s); have hz(v:E): colorReal G (slotExt c a (T v))= c.atSite (fortune q v) a:=by unfold T; rw [slotExt_physical,colorReal_up]
   simp_rw [hz] at hr; exact hr.mono (le_of_eq (by unfold height richness composeCost; ring))
lemma atoms {t:ℕ}{x:E}(hx:x∈ball 0 1)(c:Atom G t): Allows k (fun z:E=> c.unmasked (fortune q z) a) x (c.budget μ * value G k t μ):=by
   let P (v:E):=physical (fortune q v)
   have hs{v:E} : Complex.reCLM (atomExt c a (P v))= c.unmasked (fortune q v) a:= by unfold P; rw [atomExt_physical]; rfl
   let ht:= allows_real_of_entire k (atomExt_contDiff c a) (x:=P x) (radius_pos hp) (fun y hv=> (atomExt_bound c _ hp y (ball_subset_closedBall hv) a).trans
       (mul_le_mul_of_nonneg_left (show _ ≤ |slotConst G|^t from (le_abs_self _).trans_eq (abs_pow ..)) (show 0≤ c.budget μ by unfold Atom.budget Atom.magnitude; positivity)))
   have hx:= (ht.comp (f:=P) (allows_ambient (U:=fun y=> fortune q y) (allows_signed q k x hx))).linear Complex.reCLM Complex.reCLM_norm.le
   simp_rw [hs,one_mul] at hx; exact hx.mono (le_of_eq (by unfold value richness composeCost; ring))
include ht
lemma atom_price {j:ℕ}(F:ℕ→Atom G j)(M:ℝ)(hf:SumBudget (fun i=> (F i).budget σ) M):
    revenue 1 k μ (fun i=>(F i).length) (fun i (z:E)=> (F i).unmasked (fortune q z) a) (M*value G k j μ) := by
   let s:=value G k j μ; have hv : 0≤ s:= value_nn G k j hp -- syntax
   let f(i:ℕ):=(F i).budget μ *s; have hφ(i:ℕ):0 ≤ (F i).budget μ:= by unfold Atom.budget Atom.magnitude; positivity
   let p(i:ℕ):=Real.exp (μ*(F i).length)* f i
   have hpv i : p i ≤ (F i).budget σ *s:= by
      let L:ℝ:=(F i).length; unfold p f Atom.budget
      have hh : 0≤ (F i).magnitude:=by unfold Atom.magnitude; positivity
      have hx : Real.exp (μ*L)*Real.exp (μ*L) ≤ Real.exp (σ*L):= by rw [←Real.exp_add]; exact Real.exp_monotone (by nlinarith only [mul_le_mul_of_nonneg_right ht (show 0≤L from by unfold L; positivity)])
      calc
        _=((F i).magnitude*(Real.exp (μ*L)*Real.exp (μ*L)))* s:=by unfold L; ring
        _ ≤ _:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx hh) hv
   have hF(i:ℕ):0≤p i:= mul_nonneg (Real.exp_pos _).le (mul_nonneg (hφ i) hv); have hy:= hf.2.1.mul_right s
   have hV := hy.of_nonneg_of_le hF hpv
   refine ⟨f,fun i=>mul_nonneg (hφ i) hv,⟨hF,hV,(hV.tsum_le_tsum hpv hy).trans ?_⟩,fun i x hx=> atoms q a hp k hx (F i)⟩
   rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hf.2.2 hv
end Miner
end YM.MatchingLedger.Mountain

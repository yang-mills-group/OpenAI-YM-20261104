import YM.RGComparison.Core16.Forge.Escape
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Entropic delayed purchases after postblock costs, planner-L independent tails in torus period.

Internal far cost flat by tower-of-distance, NOT boundary-vacuum economic estimate with Volume weight.
Use estimates on this exp-vs-poly planner (variable `s` LARGE log inverse coupling).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Forge
open Filter Function Finset Lattice RG Tree Wilson MeasureTheory Push.AbsoluteSums.Animals Asymptotics
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {X:Prices}

def stride (X:Prices) (k:ℕ) := k*(2*X.b)
def lode (X:Prices):= Real.log (1+incline X)
lemma lode_pos: 0<lode X:=by unfold lode; apply Real.log_pos; have :=@incline_pos X; linarith
def rungs (X:Prices) (s:ℝ) := ⌈3*s/lode X⌉₊
def dollar (s:ℝ):= Real.exp (-s)
def fare (s:ℝ):= dollar s * s^4
lemma dollar_pos (s:ℝ):0<dollar s:=Real.exp_pos _
lemma dollar_bound {s:ℝ}(h:0≤s): dollar s ≤ 1:= Real.exp_le_one_iff.mpr (by linarith)

private abbrev tabs (x:ℝ→ℝ)(p:ℕ): Prop:= x =O[atTop] fun s:ℝ=>s^p
private theorem cheaper {a b: ℕ}(h:a<b) : (fun s:ℝ=>s^a)=o[atTop] (fun s:ℝ=> s^b):= Asymptotics.isLittleO_pow_pow_atTop_of_lt h -- check
private lemma widen {x : ℝ → ℝ} {a b:ℕ} (hx:tabs x a) (h:a<b) : tabs x b:=hx.trans (cheaper h).isBigO
private lemma const_tab (c:ℝ):tabs (fun _=> c) 1:=
    widen (show tabs (fun _=>c) 0 from by simpa [tabs] using isBigO_const_const c (show (1:ℝ)≠0 from one_ne_zero) (atTop:Filter ℝ)) (by omega)
private lemma grow : tabs (fun s=> ((rungs X s):ℝ)) 1:=by
   refine isBigO_iff.mpr ⟨(3/lode X+1),?_⟩; have hx:=@lode_pos X
   filter_upwards [eventually_ge_atTop (1:ℝ)] with x h
   have hv:0<x:=by linarith
   simp only [Real.norm_natCast,pow_one,Real.norm_of_nonneg hv.le]
   have hk:= Nat.ceil_lt_add_one (a:=(3*x/lode X)) (by positivity)
   apply hk.le.trans; calc
     _ = 3/lode X*x+1 := by ring
     _ ≤ _ := by linarith
private lemma tabScale {x y:ℝ→ℝ} (h:x=O[atTop] y)(c : ℝ): (fun s=> x s * c)=O[atTop] y:=by simpa only [mul_comm c] using h.const_mul_left c
private lemma allot : tabs (fun s=> weights X (stride X (rungs X s)+X.b)) 4 := by
   simp only [weights,stride,Nat.cast_add,Nat.cast_mul, Push.AbsoluteSums.Animals.ballCost, Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat]
   have hh (c:ℝ):tabs (fun _=>c) 1:=const_tab c
   let C:=(Nat.cast (R:=ℝ) X.b)
   have hz: (tabs (fun s => ((rungs X s:ℕ):ℝ)*(2*C)+C) 1):= (tabScale (@grow X) _).add (hh _)
   convert! (tabScale (((hz.add hz).add (hh 1)).pow 4) ((X.K:ℝ))) using 1; simp

private lemma arrives {f: ℝ→ ℝ}{a:ℕ} (h:tabs f 4)(ha:4<a)(c:ℝ)(hc:0<c): ∀ᶠ x in atTop,f x ≤ c*x^a:=by
   filter_upwards [((h.trans_isLittleO (cheaper ha)).def hc),eventually_ge_atTop (0:ℝ)] with x hx hv
   exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hv a)] using hx)

-- ringing: require violation cost > (#ball-bound times 4) / (1+α)^M.
theorem last (X:Prices) : ∀ᶠ s:ℝ in atTop, 4 * weights X (stride X (rungs X s)) <
    (1+incline X)^(rungs X s) * (fare s)^2:=by
   have hl:1<1+incline X:= (lt_add_iff_pos_right ..).2 incline_pos
   filter_upwards [eventually_gt_atTop (1:ℝ),arrives (@allot X|>.const_mul_left 4) (show 4<5 by norm_num) 1 zero_lt_one] with x hv hg
   have hx:0<x:=by linarith
   let a:=1+incline X; let y:= rungs X x; let l:=lode X
   have h:Real.exp (3*x) ≤ a^y:=by
      unfold a; rw [← Real.exp_log (show 0<1+incline X from zero_lt_one.trans hl)]; change Real.exp (3*x) ≤ (Real.exp l)^y; rw [← Real.exp_nat_mul]; rw [Real.exp_le_exp]; exact (div_le_iff₀ (show 0<l from lode_pos)).1 (Nat.le_ceil (3*x/l))
   apply lt_of_le_of_lt (show 4*weights X (stride X (rungs X x)) ≤ x^5 from ?_) (lt_of_lt_of_le ?_ (mul_le_mul_of_nonneg_right h (sq_nonneg ((fare x)))))
   · exact ((mul_le_mul_of_nonneg_left (weights_mono X (show stride X y ≤ _ from Nat.le_add_right (stride X y) X.b)) (show (0:ℝ)≤4 by norm_num)).trans hg).trans_eq (one_mul _)
   rw [fare,mul_pow,dollar,←Real.exp_nat_mul,←mul_assoc,← Real.exp_add, show 3*x+(↑(2:ℕ):ℝ)* -x=x by push_cast; ring]; refine lt_trans (by gcongr; first|exact hv|norm_num : x^5 < x^8) ((lt_mul_iff_one_lt_left (show 0<x^8 from by positivity)).2 (Real.one_lt_exp_iff.mpr hx)|>.trans_eq ?_); ring

-- tail price AFTER shell occupation and horizon growth. expose paid terms for use at all expansions.
private lemma roof : tabs (fun x=> weights X (stride X (rungs X x))) 4:=by
    refine IsBigO.trans ?_ (@allot X); refine isBigO_iff.mpr ⟨1,Eventually.of_forall (fun x=>?_)⟩
    rw [Real.norm_of_nonneg (weights_pos ..|>.le), Real.norm_of_nonneg (weights_pos ..|>.le),one_mul]; exact weights_mono X (Nat.le_add_right _ _)

private lemma linear (a:ℕ) (b c:ℝ) (ha: 1≤a): tabs (fun s:ℝ=> b*s+c) a:=by
    have h: tabs (fun _:ℝ=>c) 1:= const_tab c
    have hx: tabs (fun x:ℝ=>x) 1:=by simpa [tabs] using (isBigO_refl (fun x:ℝ=>x) atTop)
    rcases eq_or_lt_of_le ha with hh|hh
    · exact hh ▸ (hx.const_mul_left b).add h
    exact widen ((hx.const_mul_left b).add h) hh

lemma cost_late (X:Prices)(G:Gauge) :
    ∀ᶠ s:ℝ in atTop, rider X*weights X (stride X (rungs X s)+X.b) - (fare s)^2/(2*dam X*(dollar s)^2) +
      (s+Real.log 4)*(burn G)*weights X (stride X (rungs X s)) ≤ -(s^7) :=by
    have hx : tabs (fun s=> (s+Real.log 4)*(burn G)*weights X (stride X (rungs X s))) 5:= by
        convert! ((tabScale (linear 1 1 (Real.log 4) (le_refl _)) (burn G:ℝ)).mul (@roof X)) using 1 <;> simp
        ext x; ring
    let v (s:ℝ):= rider X*weights X (stride X (rungs X s)+X.b)
    have hd:0<dam X:=dam_pos
    have hP:0<1/(2*dam X):= by positivity
    have hm:=@allot X
    have he: ((fun s:ℝ=> s^7+ (v s+(s+Real.log 4)*(burn G)*weights X (stride X (rungs X s)))))=o[atTop] (fun s=> s^8):=(cheaper (by norm_num)).add (((hm.const_mul_left (rider X)).trans_isLittleO (cheaper (by norm_num))).add (hx.trans_isLittleO (cheaper (by norm_num))))
    filter_upwards [eventually_gt_atTop (0:ℝ), he.def hP] with x h hx'
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (pow_nonneg h.le 8)] at hx'
    have ht : (fare x)^2/(2*dam X*(dollar x)^2)=1/(2*dam X)*x^8:=by unfold fare; have := dollar_pos x; field_simp
    rw [ht]; change v x- _ + _ ≤ _; linarith only [(le_abs_self _).trans hx']

def riotFee (s:ℝ):=Real.exp (-(s^7))
def ruin (s:ℝ):= Real.exp (-(s^6))
lemma ruin_rings (X:Prices) : ∀ᶠ s:ℝ in atTop,(rungs X s:ℝ)*riotFee s ≤ ruin s:=by
    have h:= arrives (widen (@grow X) (by norm_num)) (show 4<5 by norm_num) 1 zero_lt_one
    filter_upwards [h,eventually_ge_atTop (3:ℝ)] with x hx hv
    have hh:0<x:=by linarith
    rw [one_mul] at hx; unfold riotFee ruin
    have he : Real.exp (-(x^6))= Real.exp (-(x^7)) * Real.exp (x^7-x^6):= by rw [← Real.exp_add]; congr 1; ring
    rw [mul_comm,he]; gcongr; apply (hx.trans ?_).trans (Real.add_one_le_exp (x^7-x^6))
    have hy:= show x^6 ≥ x^5 by gcongr <;> linarith
    nlinarith only [mul_le_mul_of_nonneg_right hv (show 0≤x^6 by positivity), hy, show 0≤x^6 by positivity]

end YM.RGComparison.Core16.Forge

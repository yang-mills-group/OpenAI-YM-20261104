import YM.MSbar.Scale.Resolve
/-! One and only one common near-zero regulator domain per finite total loop demand.
Dimension shift is in MOMENTUM loops `v` evaluated after high-pass, lower than
ℏ count when poles have been inserted. Pole order cost independent of local degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Scale
open Dim Symbol Domain Diagram Super Flight Function Set Filter Counter Complex Inertia
open scoped Classical Topology BigOperators
variable {C:Type}{W:Edition C}{m n v:ℕ}{U:Set ℂ}{M:Multiset C→ℤ}{F:Functionals C}{t:Multiset C}{d:Bit}{z:ℂ}

abbrev SizeLaw (C:Type) := Multiset C→ℤ
def hood (n:ℕ):Set ℂ:= Metric.ball 0 ((2*(n+1):ℝ))⁻¹
instance (n:ℕ) : Profit (hood n):=
    ⟨fun e=> by
         have hm:= mem_ball_zero_iff.mp (show (1:ℂ)∈hood n from e ▸ mem_univ _); rw [norm_one, ← one_div, lt_div_iff₀] at hm; push_cast at hm; linarith [show (0:ℝ) ≤ ↑n by positivity]; positivity,Metric.mem_ball_self (by positivity), Metric.isOpen_ball⟩
lemma deeper (he:m≤n): hood n⊆hood m:= Metric.ball_subset_ball (inv_anti₀ (by positivity) (by exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.succ_le_succ he) zero_le_two)) -- with cast?
-- v actual integrated loops
def slope (v:ℕ)(z:ℂ):ℂ:= 2*v*z
def mass (M:SizeLaw C)(v:ℕ)(z:ℂ): Mass C:= fun t=> (M t:ℂ)+slope v z
@[simp] lemma slope_add {i j:ℕ}{z:ℂ}: Scale.slope (i+j) z=Scale.slope i z+Scale.slope j z:=by unfold Scale.slope; push_cast; ring
@[simp] lemma slope_zero : Scale.slope 0 z=0 := by simp [Scale.slope]
@[simp] lemma no_add(M:SizeLaw C): Scale.mass M 0 z=(fun t=>(M t:ℂ)):=by ext; simp [Scale.mass]
lemma holistic (U:Set ℂ)(v:ℕ): DifferentiableOn ℂ (Scale.slope v) U:=(show Differentiable ℂ (Scale.slope v) from differentiable_id.const_mul _).differentiableOn
lemma coverage (v:ℕ): DifferentiableOn ℂ (fun z=>Scale.mass M v z t) U:= differentiableOn_const _|>.add (holistic _ _)
lemma near (he:z∈hood n)(hn:v≤n): ‖Scale.slope v z‖ < 1:=by
   have h:‖z‖< (2*(v+1):ℝ)⁻¹:= mem_ball_zero_iff.mp (deeper hn he); rw [ ← one_div,lt_div_iff₀] at h; swap; positivity
   unfold Scale.slope; simp; nlinarith [norm_nonneg z]
lemma out (hz:z∈hood n)(hn:v≤n){i:ℕ}(h:(M t:ℤ)≠(i:ℤ)): Scale.mass M v z t≠(i:ℂ):=by
    intro hx; have he:=abs_lt.mpr (abs_lt.mp ((abs_re_le_norm _).trans_lt (near hz hn))); have h1 := congr_arg Complex.re hx; simp only [Scale.mass,add_re,intCast_re,natCast_re] at h1; obtain ⟨hl,hU⟩:=abs_lt.mp he
    rcases lt_or_gt_of_ne h with H|H
    · have hh : (M t:ℤ)+1 ≤ i := (by omega); have he:(M t:ℝ)+1 ≤ (i:ℝ):= (by exact_mod_cast hh); linarith
    have hh : ((i:ℤ)+1)≤ M t:= (by omega); have he:(i:ℝ)+1 ≤ (M t:ℝ):= (by exact_mod_cast hh); linarith
lemma shifted_out (hz:z∈rim (hood n))(hn:v≤n)(hv:0<v)(i:ℕ): Scale.mass M v z t ≠(i:ℂ):=by
   by_cases h:(M t:ℤ)= (i:ℤ)
   · unfold Scale.mass Scale.slope; rw [h]; simp [hv.ne',show z≠0 from hz.2]
   exact out hz.1 hn h
-- Choose N strictly > a.re+1
def cap (M:SizeLaw C)(t:Multiset C):ℕ:= (M t).toNat+4
lemma clears (he : z∈ hood n)(hn:v≤n): Apert (Scale.mass M v z) (cap M):= by
    intro t; have hc:= ((abs_re_le_norm _).trans_lt (near he hn)); simp only [Land, Scale.mass, cap,sub_re, add_re, intCast_re,natCast_re]; have hv:M t ≤ ((M t).toNat:ℤ):= Int.self_le_toNat ..; push_cast; linarith [(abs_lt.mp hc).2,show (M t:ℝ) ≤ ↑(M t).toNat by exact_mod_cast hv]
lemma true_pass (hv:0<v)(hn:v≤n): Pass (hood n) (cap M) (Scale.mass M v) 1:= by
   refine ⟨fun t=> coverage _, fun c z hz=> clears hz hn c,?_⟩; let L(t:Multiset C)(i:ℕ)(z:ℂ):= if M t=(i:ℤ) then (2*(v:ℂ))⁻¹ else z/(Scale.mass M v z t-i)
   refine ⟨L,fun c i _=> ?_,fun c i _ z hz=>?_⟩
   · unfold L; split_ifs with h
     exact differentiableOn_const _
     exact differentiableOn_id.div ((coverage v).sub (differentiableOn_const _)) (fun z hz=>sub_ne_zero_of_ne (out hz hn h))
   unfold L; split_ifs with h; swap; simp
   simp only [Scale.mass,Scale.slope,h,Int.cast_natCast,pow_one,add_sub_cancel_left]; field_simp [show z≠0 from hz.2,hv.ne']
lemma tree_pass : Pass (hood n) (cap M) (Scale.mass M 0) 0:=
   ⟨fun _=> coverage _, fun t z hz=> clears hz (Nat.zero_le n) t, ⟨fun t i z=>((M t:ℂ)-(i:ℂ))⁻¹,fun t i _=> differentiableOn_const _,by intros; simp⟩⟩
end YM.MSbar.Scale

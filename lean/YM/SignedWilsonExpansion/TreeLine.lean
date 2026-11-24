import YM.SignedWilsonExpansion.HighRank
import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.Park

/-! # High part of the Landau line in the archive
`chi` uses the **actual** heat cutoff, monetary logarithm set separately.
The line integrator has no IR singularity (including at zero momentum) on any
finite heat length, and its orientation and factor of 1/2 are fixed by the
Polchinski heat equation. -/
set_option autoImplicit false
noncomputable section
namespace YM.SignedWilsonExpansion.TreeLine
open Function Filter Set MeasureTheory
open MS MS.Plane MS.Koszul MS.Landau MS.Landau.Detect MS.Pearl MS.Rake MS.High
open MS.Logarithm MS.Alps MS.Outlook MS.Emit MS.Plane.Wire MS.Plane.Domain MS.Plane.Flux MS.Heat MS.Port
open HighScale
open scoped Topology BigOperators ContDiff Interval
variable {G : Gauge}
local notation "Σk" => (Branch G Axis)
abbrev Line (G:Gauge) := Flux (Branch G Axis) FourP ℂ
-- Laplace parameter u=length^2 and square momentum x.
def src (z : ℝ×ℝ):ℝ:= (z.1/2)*Real.exp (-(z.1*z.2))
def gain (r x:ℝ):ℝ:= desk src (r,x)
def amp (s x:ℝ) : ℝ:= gain ((Real.exp s)^2) x

def base : Atom Axis → Atom Axis → FourP→ℂ
| (some i,false), (some j,false), p=> (precision i j p:ℂ)
| (some i,true), (none,false), p=> Complex.I * (p.sq * (p i):ℝ)
| (none,false), (some i,true), p=> Complex.I * (p.sq * (p i):ℝ)
| _,_,_=>0
abbrev BLine (G:Gauge):Line G := choir base id
def chi (G:Gauge)(s:ℝ): Line G:= fun i j p=> amp s p.sq • BLine G i j p
local notation "κ" => PlanetD G
local notation "χ" => chi G

lemma gain_smooth : ContDiff ℝ ∞ (Function.uncurry gain):= park (show ContDiff ℝ ∞ src from by unfold src; fun_prop)
lemma amp_smooth : ContDiff ℝ ∞ (Function.uncurry amp):=
  gain_smooth.comp (f:=fun z:ℝ×ℝ=>((Real.exp z.1)^2,z.2)) (by fun_prop)
lemma amp_deriv (t x :ℝ) : HasDerivAt (fun t=>amp t x) ((Real.exp t)^4 * Real.exp (-((Real.exp t)^2*x))) t:= by
  let r:=Real.exp t; have hx: HasDerivAt (fun s=>desk src (s,x)) ((r^2/2)*Real.exp (-(r^2*x))) (r^2):= deskD (show Continuous src from by unfold src; fun_prop) ..
  convert! hx.comp t ((Real.hasDerivAt_exp t).pow 2) using 1; unfold r; ring
lemma amp_cold (p:ℝ): Tendsto (fun t=>amp t p) atBot (𝓝 0):= by
  have he:Continuous fun r:ℝ=>gain r p:=gain_smooth.continuous.comp (continuous_id.prodMk continuous_const)
  have hu:= (he.tendsto (0^2)).comp (Real.tendsto_exp_atBot.pow 2)
  simpa only [Function.comp_def,gain,amp,zero_pow (by decide : 2≠0),desk,intervalIntegral.integral_same] using hu

lemma sq_time (r:ℝ)(p:FourP): Momentum.sq (r • p)=r^2*p.sq:= Momentum.scaling ..
lemma line_cost (t:ℝ)(p: FourP)(a b : Atom Axis):
    line t a b p = ((t^4*Real.exp (-(t^2*p.sq)) :ℝ)) • base a b p:= by
  rcases a with ⟨_|i,_|_⟩ <;> rcases b with ⟨_|j,_|_⟩ <;>
    simp [line,base,coat, k_scale,sq_time,Complex.real_smul] <;> ring
lemma rolled (i j:Σk)(p:FourP)(t:ℝ): κ t i j p = (Real.exp t^4*Real.exp (-((Real.exp t)^2*p.sq))) • BLine G i j p := by
  unfold PlanetD spaceD zD BLine choir; dsimp only; split; exact line_cost _ _ _ _; rw [smul_zero]
@[local fun_prop] lemma cast_smooth : ContDiff ℝ ∞ ((↑) :ℝ →ℂ):= Complex.ofRealCLM.contDiff
lemma c_cost_pack : ∀ i j:Σk, ContDiff ℝ ∞ (BLine G i j):= by
  intro ⟨a,i⟩ ⟨b,j⟩; unfold BLine choir; dsimp only; split
  · rcases a with ⟨_|i,_|_⟩ <;> rcases b with ⟨_|j,_|_⟩ <;> dsimp only [id,base] <;> first | exact contDiff_const | skip
    all_goals simp only [precision,delta,Momentum.sq]; first | fun_prop | (split_ifs <;> fun_prop)
  exact contDiff_const
lemma chi_smooth (i j:Σk) : ContDiff ℝ ∞ (Function.uncurry fun t p=>χ t i j p):=by
  apply ContDiff.smul (f:=fun x:ℝ×FourP=> amp x.1 (Momentum.sq x.2)) (g:=fun x:ℝ×FourP=> BLine G i j x.2)
  · exact amp_smooth.comp (f:=fun z:ℝ×FourP=>(z.1,Momentum.sq z.2)) (by unfold Momentum.sq; fun_prop)
  exact (c_cost_pack i j).comp contDiff_snd
lemma chi_deriv (i j:Σk)(p:FourP)(t:ℝ): HasDerivAt (fun t=>χ t i j p) (κ t i j p) t:=by rw [rolled]; exact (amp_deriv t (Momentum.sq p)).smul_const (BLine G i j p)
lemma chi_cold (i j:Σk) (p:FourP): Tendsto (fun s=>χ s i j p) atBot (𝓝 0):=by simpa only [zero_smul,chi] using (amp_cold (Momentum.sq p)).smul_const (BLine G i j p)
lemma chi_closed (t:ℝ): closed (chi G t) parity false:= by
  rintro ⟨⟨_|i,_|_⟩,c⟩ ⟨⟨_|j,_|_⟩,d⟩ p h <;> first | rfl | skip
  all_goals simp [chi,BLine,base,choir] at h
lemma chi_reverse (t:ℝ): Reverse (chi G t) parity:=by
  rintro ⟨⟨_|i,_|_⟩,c⟩ ⟨⟨_|j,_|_⟩,d⟩ p <;>
    simp [chi,BLine,choir,base,MS.Landau.sq_neg, parity, Landau.p, eq_comm (a:=d) (b:=c)]
  rw [realK]

lemma chi_scale (i j:Σk)(p:FourP)(t s:ℝ): χ t i j p=τ ((4:ℤ)-wfield i-wfield j) s* χ (t-s) i j (Real.exp s • p):= by
  let V:= τ ((4:ℤ)-wfield i-wfield j) s
  let f a:= χ a i j p-V*χ (a-s) i j (Real.exp s • p)
  have hf a: HasDerivAt f 0 a:= by
    have H: HasDerivAt (fun x=>χ (x-s) i j (Real.exp s • p)) (κ (a-s) i j (Real.exp s • p)) a:= by
      simpa only [one_smul,Function.comp_def] using (chi_deriv i j (Real.exp s • p) (a-s)).scomp a ((hasDerivAt_id' a).sub_const s)
    have h2:=(chi_deriv i j p a).sub (H.const_mul V)
    simp only [← show κ a i j p=V*κ (a-s) i j (Real.exp s • p) from figure .., sub_self] at h2
    exact h2
  have he:= Filter.tendsto_atBot_add_const_right atBot (-s) tendsto_id
  have right : Tendsto (fun x=>χ (x-s) i j (Real.exp s • p)) atBot (𝓝 0):=
    (chi_cold ..).comp he
  have hz : Tendsto f atBot (𝓝 0):= by simpa only [f,mul_zero,sub_zero] using (chi_cold i j p).sub (right.const_mul V)
  apply sub_eq_zero.mp
  exact tendsto_nhds_unique tendsto_const_nhds (hz.congr fun v=> is_const_of_deriv_eq_zero (fun i=>(hf i).differentiableAt) (fun i=>(hf i).deriv) v t)

open MS.Latch Finset
variable {F H:Law G}
lemma trees_time (t s:ℝ)(h k:ℤ) : tree parity (χ t) (Port.shift h s F) (Port.shift k s H) = Port.shift (h+k-4) s (tree parity (χ (t-s)) F H):= by
    funext l; apply totalζ; intro x y hp; unfold attaches; simp_rw [ net_sr, degree_sr, neg_neg, Finset.mul_sum ]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [mul_add]; simp_rw [β_shift]
    rw [ chi_scale i j _ t s, chi_scale i j _ t s ]
    simp only [ smul_neg ]; have he:= w_mass hp; refine congr_arg₂ (·+·) (Port.χ _ _ _ _ _ _ _ _ ?_) (Port.χ _ _ _ _ _ _ _ _ ?_); rw [P_ψ _ _ _ _ _ _ _ _ he, show 4+pitch l-h-k= pitch l-(h+k-4) from (by omega) ]; rw [show (4:ℤ)-wfield i-wfield j= 4-wfield j-wfield i from sub_right_comm ..,P_ψ _ _ _ _ _ _ _ _ he, show 4+pitch l-h-k=pitch l-(h+k-4) from (by omega) ]

section
variable {A I J : Type}{r:I→ℂ}{a e:I→A}{s:Finset I}{u w:J→ A}{v:J→ ℂ}{k:Finset J} {p: Sector A}
    (hx:Balanced p false r a e s)(hy:Balanced p false v u w k)
local notation "B" => loop r a e s
local notation "C" => loop v u w k
local notation "P0"=>link (loop r a e s) false p
local notation "C0"=>link (loop v u w k) false p
local infixl:70 " ⋄ " => product p
include hx hy
/-- Symmetrisation of the iterated tree with **even** line choices, using the finite Koszul slabs. -/
lemma second {f g:Raw A ℂ}(hf:Pure p false f)(H:Symm p f)(hv:Symm p g) : C0 (P0 f f) g+(2:ℕ) • C0 f (P0 f g)=P0 (C0 f f) g+(2:ℕ) • P0 f (C0 f g):= by
    have he (F) (h:Symm p F): C (B F)=B (C F):= by simpa using loop_loop hy hx h
    have mix (f g:Raw A ℂ)(hf:Symm p f)(hg:Symm p g): C (P0 f g) + C0 (B f) g + C0 f (B g)= B (C0 f g)+P0 (C f) g+P0 f (C g):= by
      have h := he (f ⋄ g) (hf.times hg)
      rw [link_apply (b:=false) (p:=p) (C) f g,link_apply (b:=false) (p:=p) (B) f g] at h
      simp only [map_add,sign_id] at h
      rw [link_apply (C) (B f) g (b:=false),link_apply (C) f (B g) (b:=false),link_apply (B) (C f) g (b:=false), link_apply (B) f (C g) (b:=false)] at h
      simp only [sign_id,he f hf,he g hg] at h
      linear_combination (norm:=abel) h
    have hm := mix (f ⋄ f) g (H.times H) hv; have hxF:=hx.pure hf; have hyF:=hy.pure hf
    rw [hx.paired_left (v:=g) hf hf, hy.paired_left (v:=g) hf hf, hy.paired_left (v:=B g) hf hf,hx.paired_left (v:=C g) hf hf,link_even B hf (b:=false),link_even C hf (b:=false)] at hm
    simp only [link_add_left,map_add] at hm
    rw [show B (f ⋄ C0 f g)= _ from link_even B hf (b:=false), show C (f ⋄ P0 f g)= _ from link_even C hf (b:=false)] at hm
    rw [← hf.central (B f),← hf.central (C f)] at hm; simp_rw [hy.paired_left hxF hf, hx.paired_left hyF hf] at hm
    have hh:= congr_arg (fun x : Raw A ℂ=> f ⋄ x) (mix _ _ H hv); simp only [map_add] at hh
    linear_combination (norm:=abel) hm - hh - hh
end
lemma orbit_even_pair {K L:Line G}{F H:Law G} (h:closed K parity false)(hh:closed L parity false)(hf: Symm (field parity) F)(hp:Pure (field parity) false F)(hH:Symm (field parity) H):
    tree parity L (tree parity K F F) H + (2:ℕ) • tree parity L F (tree parity K F H) = tree parity K (tree parity L F F) H + (2:ℕ) • tree parity K F (tree parity L F H):= by
    suffices he:∀ (F:Law G),Symm (field parity) F →Pure (field parity) false F→Conserved F→tree parity L (tree parity K F F) H + (2:ℕ) • tree parity L F (tree parity K F H) = tree parity K (tree parity L F F) H + (2:ℕ) • tree parity K F (tree parity L F H) by
      have ht:= he (translate F) (sym_trans hf) (pure_trans hp) (trans_off F)
      have hu (L K:Line G):tree parity L (tree parity K (translate F) (translate F)) H= tree parity L (tree parity K F F) H := tree_agrees _ _ _ _ _ (treesa K F F)
      rw [hu,hu] at ht; simpa only [tree_trans] using ht
    intro F hf hp hC; ext1 l
    let t:=atTop (α:=Finset FourP); have hr (K L:Line G): ∀ᶠ i in t, tree parity (trim i K) F (tree parity (trim i L) F H) l=tree parity K F (tree parity L F H) l ∧ tree parity (trim i L) (tree parity (trim i K) F F) H l=tree parity L (tree parity K F F) H l:= by
      exact (event_tree (f:=fun _=>F) (g:=fun i=>tree parity (trim i L) F H) (s:=t) (fun _=>by simp) (roll_tree parity F H L) (fun a b i=> trims i a b) l).and (event_tree (g:=fun _=>H) (f:=fun i=>tree parity (trim i K) F F) (s:=t) (roll_tree parity F F K) (fun _=>by simp) (fun a b i=> trims i a b) l)
    obtain ⟨i,⟨h1,h2⟩,h3,h4⟩:= ((hr K L).and (hr L K)).exists
    have he := second ((cl_trim i h).balanced i) ((cl_trim i hh).balanced i) hp hf hH
    simp_rw [← is_loop, ← stickT h i hC, ← stickT hh i hC, ← stickT hh i (conserved_tree _ _ hC F), ← stickT h i (conserved_tree _ _ hC F)] at he
    simp only [Pi.add_apply,Pi.smul_apply,← h1,← h2,← h3,← h4]; exact congr_fun he l
end YM.SignedWilsonExpansion.TreeLine

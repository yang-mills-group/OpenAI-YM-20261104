import YM.OPE.Measuring.Toric

/-!
# Coefficient and associator prices of regular singleton tree charts

Proof uses only the actual `Uniform` estimates plus the separated-position
smoothness *including* when all points coincide in a trivial cluster readout,
and cashes that extension via integer corner-jet tests. A different argument
would be needed for actual singular germs. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Measuring.Tree
open Orbits Orbits.Reader Nesting Nesting.Tree Function Filter Set Table
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {n:ℕ}{f:Fin n→Tree}
local notation "tree" => Fork f
variable {B:Type*}[NormedAddCommGroup B][NormedSpace ℝ B] (g:(Fork f).Plot→B)
variable {m:ℕ}(d:Bool)(D:(Fork f).Inner→ℕ) (w:(Fork f).Leaf → ℕ)
variable (ht: Narrow (Fork f))
include ht
lemma restore {M η:ℝ} (hM:0≤M) (hS:∀ z a, g (fun i=> z i + a) = g z) (he : ∀ x:E4,∀ᶠ z in 𝓝 (fun _:(Fork f).Positions=>x),ContDiffAt ℝ ∞ g z)
       (h0 : ∀ μ:ℝ,0≤μ→∀ ε>0,∀ᶠ x:ℝ in 𝓝[>]0,∀ s:(Fork f).Inner→ℝ,∀ z:(Fork f).Plot, Accept x μ η s z → ‖g z‖ ≤ (toll (fun i=>(w i:ℝ)) ε m s) * allowance d D ((Fork f).ratios 1 s)) :
        ∃ C:ℝ, 0<C ∧ ∀ᶠ x:ℝ in 𝓝[>]0,∀s:(Fork f).Inner→ℝ,∀ z:(Fork f).Plot, Accept x M η s z → ‖g z‖ ≤ C*(toll (fun i=>(w i:ℝ)) 0 m s) * allowance d D ((Fork f).ratios 1 s):=by
      have hN : ∀ {a b:ℝ}{s:(Fork f).Inner→ℝ}{z:(Fork f).Plot}, Relative a b (Fork f) s z → Relative a η (Fork f) s z:=by
        intro a b s z hh; clear he h0 hS
        exact adjust (t:=Fork f) ht hh
      obtain ⟨c,hc⟩:=wedge_price d w D g M ht he (fun a ha ε hε=>by filter_upwards [h0 a ha ε hε] with x hx s z hz; exact hx s z ⟨hz.levels,hN hz.relative,hz.scale⟩)
      refine ⟨max 1 c,lt_of_lt_of_le zero_lt_one (le_max_left ..),?_⟩
      filter_upwards [hc,h0 M hM 1 one_pos, eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds (zero_lt_one' ℝ))] with x hx hq h'x s z hg
      have hT := hg.levels.mono le_rfl h'x
      have hs:=tempered hT zero_lt_one
      have hp(i):= hT.positive i
      by_cases he' : d=true→Nonempty (Nonroot f)
      swap
      · obtain ⟨hd,h₀⟩:=Classical.not_imp.mp he'; specialize hq s z hg; haveI:IsEmpty (Nonroot f):= not_nonempty_iff.mp h₀
        unfold allowance at *; simp_rw [if_pos hd, Fintype.sum_empty,mul_zero] at hq ⊢; exact hq
      let u:=(Fork f).ratios 1 s
      have hs':u (Sum.inl ())=x:=(div_one _).trans hg.scale
      obtain ⟨y,hY,q,hQ,hθ,hπ⟩:=rent d D (u:=u) ((show 0<s (Sum.inl ()) from hp _).trans_eq hg.scale) hs' (fun j=> hs (.inr j)) he'
      let φ:=Tree.inverse tree 1 s z (anchor z)
      have hw:φ∈Metric.closedBall (0:(Fork f).Plot) (max M 1):=by
            rw [Metric.mem_closedBall,dist_zero_right]
            exact (pi_norm_le_iff_of_nonneg (hM.trans (le_max_left ..))).mpr fun i=> fit (u:=anchor z) one_pos hT (immediate_of_relative hg.relative) (by simpa using hM) i
      specialize hx y hY.1 hY.2 ⟨q,φ⟩ ⟨⟨⟨fun k=>le_of_lt ((hQ k).1),fun k=>(hQ k).2⟩,hw⟩,fun k=>(hQ k).1⟩
      have hu: (Fork f).ratios 1 s = parametrise (pace d D) x y q:=hθ
      have hg':g (model tree 1 u φ)=g z:=(congr_arg g (centered tree z _ one_ne_zero (fun i=>(hp i).ne'))).trans (hS z (-anchor z))
      change ‖whole tree w (parametrise _ _ _ _) • g (model tree _ _ _)‖ ≤ _ at hx
      rw [← hθ] at hx
      let p:= whole tree w u; rw [hg',norm_smul,Real.norm_of_nonneg (whole_good _ (fun i=>(hs i).1) |>.le)] at hx
      have htq : p * toll (fun i=>(w i:ℝ)) 0 m s = x^m := by rw [← Real.rpow_natCast]; exact (whole_offset _ hp).trans (congr_arg (·^(m:ℝ)) hg.scale)
      change p*‖g z‖ ≤ _ at hx; have Hx:0≤ x:= ((hp (.inl ())).le.trans_eq hg.scale); refine ((le_of_mul_le_mul_left (?_) (whole_good (u:=w) _ (fun i=>(hs i).1)))) -- check args
      rw [← htq] at hx; refine hx.trans (?_)
      have hb : 0≤allowance d D u:= le_trans (pow_nonneg hY.1.le _) hπ
      calc _ ≤ (max 1 c)*(p*toll (fun i=>(w i:ℝ)) 0 m s)* allowance d D u := mul_le_mul ((mul_le_mul_of_nonneg_right (le_max_right ..) (by rw [htq]; exact pow_nonneg Hx _))) hπ (pow_nonneg hY.1.le _) (mul_nonneg (by positivity) (by rw [htq]; exact pow_nonneg Hx _))
           _ = _ := by change _ = p*((max 1 c)* _ * allowance d D u); ring
where adjust {a b t z s} (h: Narrow t)(he:Nesting.Tree.Relative a b t s z): Relative a η t s z:=by induction t with
     | bud=>exact True.intro
     | fork n f ih=>exact ⟨he.1,fun i j _ _ hab=> (hab (branch_sub h |>.allEq ..)).elim, fun i=> ih i (h.2 i) (he.2.2 i)⟩
end YM.OPE.Measuring.Tree

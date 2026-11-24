import YM.RG16.Unmasked.Pace
import YM.RG16.Unmasked.Cluster
import YM.Frontier6.Multi.Toll.Stamps

/-!
# Plot geometry at the actual shell

Transport from the cover to **ALL periods** using placement not an
approximation, cost for wrapped separations/narrow panels prepaid once at k
never with N. Layout sufficient for outgoing joins. Continuum-profile version
needs addressed smearing; this is the literal configuration at those r scales.
All interacting support hypotheses occur in the same Family, no unknown
winding cost left. In particular even though spacing is specified in real
physical configuration space and slots all live on the physical torus, it
will imply the needed separation for marker restoration before capture (both
in replica and in origin).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG16.Literal
open Function Filter Set Lattice RG OPE MergeProof MergeProof.Ribbons
open Function Set Filter Bid Cells Next.Rank Push GridApprox
open scoped Topology BigOperators Classical
variable {G:Gauge} (C:Family G) (hG:G.Simple) (J K:ℕ)
  {I:Type}
set_option quotPrecheck false
local notation "P" => C.path.levels
local notation "Λ" => Lambda C.path.levels
local notation "σ" => C.S.scale
local notation "a!" => C.S.a

/-- Layout for the output mesh. `M`, `B`, `η` are finite demands chosen first.
`r_physical = a(k) ρ` exactly. All configurations on this grid at every
sufficiently fine k, and all periods are included, subject to this layout.
Distinct slots (same fields allowed). Relative positions in cover-grid units before
wrap and WITH engine; lifts via real exact birth stencils. (Later proofs may use
actual snap-all partial lattice grids. Not setting center anywhere else yet.) -/
structure Tuple (M η B:ℝ)(k:ℕ) (ρ:ℝ) (u:I → Cover) : Prop where
    lo : (Lambda C.path.levels k)^B ≤ ρ
    hi : ρ ≤ (Lambda C.path.levels k)^(B+1)
    contour (i) : ‖C.S.gridPoint k (u i)‖ ≤ M*(C.S.a k *ρ)
    missing : Pairwise fun i j=> η*(C.S.a k*ρ) ≤ ‖C.S.gridPoint k (u i)-C.S.gridPoint k (u j)‖

def snap (k p:ℕ)(u:I → Cover) := fun i=> wrap (C.side k p) (u i)

-- Adapt `faraway` & `weeds` to pointwise & translated uniformity;
-- avoid late period-only extraction.
lemma inside {u:Cover}(k p:ℕ) (he: ‖C.S.gridPoint k u‖≤1) :
    C.S.place (wrap (C.side k p) u) = C.S.gridPoint k u := by
    apply congr_arg (C.S.gridPoint _)
    apply lift_eq_iff.mpr ⟨rfl,fun i=>?_⟩
    let q:= C.S.a k
    let r:ℝ:=(C.side k p).val
    have hu:= C.S.span_side k p
    have ha := C.S.a_pos k
    have hp : 4 ≤ q*r:= hu.symm ▸ by exact_mod_cast (Nat.le_of_dvd (C.S.period p).property (C.S.period_four p))
    have hs : |q * (u i)| ≤ 1 := by
       change |↑((C.S.gridPoint k u) i)| ≤ _
       exact le_trans (show ‖(C.S.gridPoint k u) i‖≤ _ from PiLp.norm_apply_le _ _) he
    have ht : -(r:ℝ) < 2*(u i:ℝ):= by apply lt_of_mul_lt_mul_left (a:=q) _ ha.le; linarith only [hp,(abs_le.mp hs).1]
    have hw : (2:ℝ)*(u i:ℝ) ≤ r:= by apply le_of_mul_le_mul_left (a:=q) _ ha; linarith only [hp,(abs_le.mp hs).2]
    unfold r at ht hw
    constructor
    · exact_mod_cast ht
    exact_mod_cast hw

lemma cover_geometric (k:ℕ) : ((C.path.levels.budget k).B:ℝ) ≤ 2*(Λ k)^ (2:ℕ) := by
    let b:= Real.log (C.path.levels.clock.hatBeta k)
    have he : ((P|>.budget k).B:ℝ) ≤ b^ (2:ℕ)+1 := (Nat.ceil_lt_add_one (sq_nonneg b)).le
    have hx : 0 < b := Real.log_pos (P|>.fits.delayed k)
    exact he.trans (by change _ ≤ 2*(2+b)^2; nlinarith)

variable (M η B:ℝ) (hM:0<M) (hη:0<η) (hB:20<B)
local notation "en" => 8*M
local notation "capture" => port C (8*M) B (mul_pos (by norm_num) hM)

include hη hG hB
lemma rooted_layout : ∀ᶠ k in atTop, (capture k+1) < k ∧
    ∀ (μ:ℝ) (u:I → Cover) p, Tuple C M η B k μ u →
    (∀ i, C.S.place (snap C k p u i) = C.S.gridPoint k (u i)) ∧
    (∀ i, 8* ‖C.S.place (snap C k p u i)‖ ≤ C.S.a (capture k+1)) ∧
    (∀ i, loops C k p (snap C k p u i) (capture k+1)=0) ∧
      Edition.Spaced (P|>.budget k).B (snap C k p u) := by
    let b_(i):= capture i
    have hg0 : 0<B:= by linarith only [hB]
    have hp:(0:ℝ)<8*M:=mul_pos (by norm_num) hM
    have hspan : ∀ᶠ k in atTop, 2*(((P).budget k).B:ℝ)^2 ≤ η*(Λ k)^B := by
       have hh : Tendsto (fun k=> (Λ k)^(B-4)) atTop atTop:=
          (tendsto_rpow_atTop (show 0<B-4 by linarith only [hB])).comp (lambda_leads C hG)
       filter_upwards [(hh.const_mul_atTop hη).eventually_ge_atTop 8] with k hk
       let m:= (((P).budget k).B:ℝ); have ht :0<Λ k:=lambda_pos C k
       have hv : (Λ k)^B = (Λ k)^(B-4)*(Λ k)^ (4:ℕ):= by
          nth_rw 1 [show B=B-4+4 from by ring]
          rw [Real.rpow_add ht]; norm_cast
       rw [hv]; change _ ≤ η*(_ * _)
       have hu : m^2 ≤ (2*(Λ k)^ (2:ℕ))^2:= pow_le_pow_left₀ (by positivity) (cover_geometric C k) _
       have hx:= mul_le_mul_of_nonneg_right (show 8 ≤ η*(Λ k)^(B-4) from hk) (show 0≤(Λ k)^ (4:ℕ) from by positivity)
       nlinarith only [hx,hu]
    filter_upwards [port_small C hG (8*M) B hp hg0, inner_bound C hG (8*M) B hp, hspan]
       with k hk hu hv
    refine ⟨hk,fun μ u p hc=>?_⟩
    have hy : ∀ i, 8*‖C.S.gridPoint k (u i)‖ ≤ C.S.a (capture k+1) := by
       intro i
       have hw: (8*M)*(a! k*μ) ≤ (Upper C (8*M) B k)*(a! k) := by
          unfold Upper; linarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc.hi (C.S.a_pos k).le) hp.le]
       linarith only [hc.contour i, hw, hu]
    have hs : ∀ i, ‖C.S.gridPoint k (u i)‖≤1/8:= by
       intro i; have hw := (C.S.strictAnti.antitone (Nat.zero_le _) : a! (capture k+1) ≤ a! 0).trans_eq (C.S.a_zero)
       linarith only [hy i, hw]
    have hp(i) : C.S.place (snap C k p u i)= C.S.gridPoint k (u i) := inside C k p ((hs i).trans (by norm_num))
    have hm (i) : 8* ‖C.S.place (snap C k p u i)‖ ≤ C.S.a (capture k+1) := (hp i).symm ▸ hy i
    have hf : 2*(C.S.a k)*(((P).budget k).B:ℝ)^2 ≤ η*(C.S.a k*μ) := by
       have hh : 2*(((P).budget k).B:ℝ)^2 ≤ η*μ := hv.trans (mul_le_mul_of_nonneg_left hc.lo hη.le)
       linarith only [mul_le_mul_of_nonneg_left hh (C.S.a_pos k).le] -- Cast of Nat?
    refine ⟨hp,hm,fun i=>?_ ,fun i j h=>?_⟩
    · apply Frontier6.Road.loops_zero C p k (capture k+1) (snap C k p u i) hk.le
      linarith only [hm i,norm_nonneg (C.S.place (snap C k p u i))]
    have he := (normC C k p (wrap (C.side k p) (u i-u j))).2
    have hz : ‖C.S.gridPoint k (u i-u j)‖ ≤ 1 := by
       rw [Frontier6.Road.grid_sub C k]; exact (norm_sub_le ..).trans ((add_le_add (hs i) (hs j)).trans (by norm_num))
    rw [inside C k p hz,Frontier6.Road.grid_sub C k,map_sub] at he
    simp only [separation,sub_zero] at he
    exact_mod_cast (le_of_mul_le_mul_left ((hf.trans (hc.missing h)).trans he) (mul_pos zero_lt_two (C.S.a_pos _)) :
       (((P).budget k).B:ℝ)^2 ≤ (separation (snap C k p u i) (snap C k p u j) : ℝ))
end YM.RG16.Literal

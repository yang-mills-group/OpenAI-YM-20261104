import YM.AllOrder.Ink.Echo
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Divisors

/-!
# Repeated stencils on *all* multiples of a period

The comparisons use the ordinary Fk calculation (common vacuum and marks) on the
cover. Evaluate it periodically by taking the connected log in bigger volumes, then
taking the thermodynamic limit per repeat. Important: at each step we ask also for
the answer at fields of *any multiple period*. An identity just for period-n external
fields would throw away information needed by the next step.

This file sets up the limiting indices, over the periods of the SAME Run, and the
geometry of the repeated stencils.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Lattice Filter Finset Function RG Supply AllOrder.Ker
open Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Topology BigOperators Classical

variable {S : Schedule} {i j : ℕ} {c n f m N F M : Side} {p : ℕ}

/-- A (possibly identity) finite cover, literal centred convention. -/
abbrev coverWin (h : n.val ∣ N.val) : Window n N ((N.val/n.val)^4) :=
  normal h (Nat.mul_div_cancel' h).symm

@[simp] theorem coverWin_cut (h : n.val ∣ N.val) : (coverWin h).cut = splitter h := rfl

theorem splitter_comp (h : n.val ∣ N.val) (H : N.val ∣ M.val) (x : Site M) :
    splitter h (splitter H x) = splitter (h.trans H) x := by
  obtain ⟨z, rfl⟩ : ∃ z : Cover, x = wrap M z := ⟨_, (wrap_lift _).symm⟩
  rw [branch, branch, branch]

theorem repeat_comp {α : Type} (h : n.val ∣ N.val) (H : N.val ∣ M.val)
    (x : rule α n) :
    convey (coverWin H) (convey (coverWin h) x) = convey (coverWin (h.trans H)) x := by
  funext v
  change x (splitter h (splitter H v.1), v.2) = x (splitter _ v.1,v.2)
  rw [splitter_comp]

theorem subdiv_dvd (r : Ratio n f) (R : Ratio N F) (e : R.count = r.count) (h : n.val∣N.val) :
    f.val ∣ F.val := by
  rw [R.exact_size,r.exact_size,e]
  exact mul_dvd_mul_right h _

theorem subdiv_embed {r : Ratio n f} {R : Ratio N F} (e : R.count = r.count)
    (h : n.val∣N.val) (x : Site N) :
    splitter (subdiv_dvd _ _ e h) (R.embed x) = r.embed (splitter h x) := by
  obtain ⟨z, rfl⟩ : ∃ z : Cover, x = wrap N z := ⟨_, (wrap_lift _).symm⟩
  rw [R.embed_wrap,branch,branch,r.embed_wrap]
  exact congr_arg (fun m : Side => wrap f (m.val • z)) e

/-- Mark at subdivision offset `y` of a mesh point `x` maps to the same offset downstairs. -/
theorem subdiv_seat {ℓ : Side} (u : f.val = n.val*ℓ.val) (v : F.val = N.val*ℓ.val)
    (h : n.val ∣ N.val) (H : f.val ∣ F.val) (x : Site N) (y : Site ℓ) :
    splitter H ((Ratio.mk ℓ v).assemble (x,y)) =
      (Ratio.mk ℓ u).assemble (splitter h x,y) := by
  simp only [Ratio.assemble,map_add,branch]
  congr 1
  exact subdiv_embed (r:=Ratio.mk _ u) (R:=Ratio.mk _ v) rfl h x

/-- All lifts of a fine marker, written using its centre on the fine torus.
Used also for mixed modes, with each fine centre independent. -/
theorem subdiv_marks {ℓ : Side} (u : f.val = n.val*ℓ.val) (v : F.val = N.val*ℓ.val)
    (h : n.val ∣ N.val) (H : f.val ∣ F.val) (z : Site f) :
    let r := Ratio.mk ℓ u
    parcel (splitter H) z = (parcel (splitter h) (r.parent z)).image
      (fun w => (Ratio.mk ℓ v).assemble (w,r.residue z)) := by
  intro r
  ext x
  obtain ⟨⟨w,y⟩,rfl⟩ := (Ratio.mk ℓ v).assemble_bijective.2 x
  rw [posted,subdiv_seat u v h H w y,Finset.mem_image]
  constructor
  · intro he
    replace he : r.assemble (splitter h w, y) = z := he
    rw [← he,Ratio.assemble_parent]
    exact ⟨w,(posted ..).2 rfl,by rw [Ratio.assemble_res]⟩
  rintro ⟨w', hw, he⟩
  have hp := (Ratio.mk ℓ v).assemble_bijective.1 he
  have e₁ : w' = w := congr_arg Prod.fst hp
  have e₂ : r.residue z = y := congr_arg Prod.snd hp
  rw [← e₁, ← e₂, (posted ..).1 hw]
  exact r.unpack_at z

/-- Covers are taken over the actual periods of this schedule. Base for the cover
limit can be ANY testing period (the physical period itself, or any multiple used for
testing a periodized output). -/
abbrev Covers (S : Schedule) (i : ℕ) (n : Side) :=
  {b : ℕ // n.val ∣ (S.side i b).val}

def coverFilter (S : Schedule) (i : ℕ) (n : Side) : Filter (Covers S i n) :=
  comap Subtype.val atTop

-- Keep the limit nontrivial (choose multiple-of-n periods arbitrarily far out).
theorem coverFilter_neBot (h : AsDivisors S) (i : ℕ) (n : Side) :
    NeBot (coverFilter S i n) := by
  apply comap_neBot
  intro s hs
  obtain ⟨k,hk⟩:=mem_atTop_sets.mp hs
  obtain ⟨b,hb,q⟩:=h n k
  exact ⟨⟨b,dvd_mul_of_dvd_left q _⟩,hk b hb⟩

theorem side_strict (S : Schedule) (i : ℕ) : StrictMono fun b => (S.side i b).val :=
  fun _ _ hb => Nat.mul_lt_mul_of_pos_right (S.period_strict hb) (S.denominator i).pos

theorem cover_size (S : Schedule) (i : ℕ) (n : Side) :
    Tendsto (fun b : Covers S i n => (S.side i b).val) (coverFilter S i n) atTop :=
  (side_strict S i).tendsto_atTop.comp tendsto_comap

end YM.Integration.FVA1Physical.TwoReset

namespace YM.Integration.FVA1Physical.TwoReset
open Lattice Filter Finset Function RG Supply AllOrder.Ker AllOrder.Ink
open Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Topology BigOperators Classical

variable {ι : Type*} {l : Filter ι} {g : ι → Side} {rate : Side → ℝ} {σ : ℝ}
    (t : Tendsto (fun b => (g b).val) l atTop)
    (hr : Echo.Pulsed rate) (hs : 0 < σ)

include t hr hs in
theorem plugged_crest : Tendsto (fun b => rate (g b)*Money.dearth σ (g b)) l (𝓝 0) := by
  obtain ⟨c,k,hc,h⟩ := hr
  let z (b : ι) : ℝ := (g b).val
  have ht : Tendsto (fun b => z b^k * Money.dearth σ (g b)) l (𝓝 0) := by
    have he : Tendsto (fun x : ℝ => x^k / Real.exp (σ*x)) atTop (𝓝 0) :=
      (isLittleO_pow_exp_pos_mul_atTop k hs).tendsto_div_nhds_zero
    unfold Money.dearth
    simp only [neg_mul,Real.exp_neg, ← div_eq_mul_inv]
    exact he.comp (tendsto_natCast_atTop_atTop.comp t)
  refine squeeze_zero (fun i=> mul_nonneg (h (g i)).1 (Real.exp_pos _).le)
    (fun i=> (mul_le_mul_of_nonneg_right (h (g i)).2 (Real.exp_pos _).le).trans_eq
      (show (c*((g i).val:ℝ)^k)*Real.exp (-σ*(g i).val)=c*(z i^k*Money.dearth σ (g i)) from mul_assoc ..)) ?_
  simpa using Tendsto.const_mul c ht

include t hr hs in
/-- Use a seam estimate to IDENTIFY a periodized cover kernel. This is an exact
formal graded statement, not the estimate in the physical norm. -/
theorem seam_limit {n : Side} {C : ℝ} {α : Type*}
    [NormedAddCommGroup α] [NormedSpace ℝ α]
    {f : ι → α} {a : α}
    (h : ∀ i, n.val ∣ (g i).val) (hm : ∀ᶠ i in l,
    ‖f i-((((g i).val/n.val)^4:ℕ):ℝ) • a‖ ≤ (rate (g i)*Money.dearth σ (g i))*C) :
    Tendsto (fun i => (((((g i).val/n.val)^4:ℕ):ℝ)⁻¹) • f i) l (𝓝 a) := by
  let m (i : ι) := (g i).val / n.val
  let u (i : ι) : ℝ := ↑(m i ^ 4)
  have hc : Tendsto (fun i => (rate (g i)*Money.dearth σ (g i))*C) l (𝓝 0) := by
    simpa using (plugged_crest t hr hs).mul_const C
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hc
  filter_upwards [hm] with i hi
  have hp : 0 < m i := Nat.div_pos (Nat.le_of_dvd (g i).pos (h i)) n.pos
  have hr : 1 ≤ u i := by unfold u; exact_mod_cast (show 1 ≤ m i ^ 4 from pow_pos hp _)
  change ‖(u i)⁻¹ • f i - a‖ ≤ _
  rw [show (u i)⁻¹ • f i - a = (u i)⁻¹ • (f i - u i • a) by
    rw [smul_sub,inv_smul_smul₀ (zero_lt_one.trans_le hr).ne'], norm_smul]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans hi
  rw [Real.norm_of_nonneg (by positivity)]
  exact inv_le_one_of_one_le₀ hr
end YM.Integration.FVA1Physical.TwoReset

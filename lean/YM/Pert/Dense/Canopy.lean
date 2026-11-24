import YM.Pert.Dense.Portal

/-! One can enlarge a wait *before the schedule* so that at its actual Paid.run points for stage j, the preceding wait holds also throughout the stage for a slab of increasing size. No inference that those successive slab centers are consecutive or comparable. -/

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Dense
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec Supply PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n D k N p m:ℕ}
variable {Θ: Sheet G} {L:Rolls Θ}{E:Protection L}{H:Delays E}{Z:Bar H}

def span (s:ℝ) := Nat.floor (Real.sqrt s)
def canopy (U : Wait Z) (j:ℕ) (u:ℝ) := sSup (insert 0 (U.window j '' Set.Icc u (2*u))) + U.window j u
lemma on_space (U : Wait Z) (j : ℕ) {ε:ℝ} (he:0<ε) :
   ∀ᶠ s:ℝ in atTop,0<s ∧ (canopy U j s:ℝ) ≤ ε*s ∧
     ∀ y∈Set.Icc s (2*s), U.window j y ≤ canopy U j s := by
   obtain ⟨a,ha⟩:= Filter.eventually_atTop.mp (U.sublin j|>.eventually (gt_mem_nhds (a:=ε/4) (by positivity))) -- wrong lemma
   filter_upwards [eventually_ge_atTop a,eventually_gt_atTop 0] with s hs hS
   let k:=insert (0:ℕ) (U.window j '' Set.Icc s (2*s))
   have hz (r)(hr : r∈ k) : (r:ℝ) ≤ ε*s/2 := by
     rcases Set.mem_insert_iff.mp hr with h|⟨y,⟨hy,hl⟩,rfl⟩; rw [h]; push_cast; positivity
     have hu := (div_le_iff₀ (hS.trans_le hy)).mp (ha y (hs.trans hy)).le
     nlinarith only [hu,he,hl]
   have h1:sSup k ≤ Nat.floor (ε*s/2):= csSup_le (by exact Set.insert_nonempty _ _) fun i hi=> Nat.le_floor (hz _ hi)
   have hb : BddAbove k := ⟨_,fun i hi=>Nat.le_floor (hz i hi)⟩
   refine ⟨hS,(show ((canopy U j s:ℕ):ℝ) ≤ (ε*s/2+ε*s/2) from ?_).trans_eq (by ring),fun y hy=> (le_csSup hb (Set.mem_insert_of_mem _ ⟨y,hy,rfl⟩)).trans (Nat.le_add_right ..)⟩
   unfold canopy; push_cast; exact add_le_add (le_trans (Nat.cast_le.mpr h1) (Nat.floor_le (by positivity))) (hz _ (Set.mem_insert_of_mem _ ⟨_,⟨le_rfl,by linarith⟩,rfl⟩))

lemma canopy_admitted (U:Wait Z) (j:ℕ) : Tendsto (fun s : ℝ=> (canopy U j s:ℝ)/s) atTop (𝓝 0) := by
   refine tendsto_order.2 ⟨fun r hr=> ?_,fun r hr=>?_⟩
   · filter_upwards [on_space U j (show (0:ℝ)<1 by norm_num)] with y h; exact hr.trans_le (div_nonneg (by positivity) h.1.le)
   filter_upwards [on_space U j (half_pos hr)] with x hx
   exact (div_le_iff₀ hx.1).mpr hx.2.1 |>.trans_lt (by linarith)
lemma span_admitted : Tendsto (fun s:ℝ => (span s:ℝ)/s) atTop (𝓝 0) := by
   refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g:=fun _:ℝ=>0) (h:=fun s=>(Real.sqrt s)⁻¹) tendsto_const_nhds
       (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop) ?_ ?_
   · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; positivity
   filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
   refine (div_le_div_of_nonneg_right (Nat.floor_le (Real.sqrt_nonneg _)) hx.le).trans ?_
   rw [show Real.sqrt x/x=(Real.sqrt x)⁻¹ by have he:=Real.mul_self_sqrt hx.le; have : Real.sqrt x ≠ 0:= (Real.sqrt_pos_of_pos hx).ne'
                                             field_simp; simpa only [pow_two] using he]

def barrier (U:Wait Z) (j : ℕ) := max (1+ Real.log ((L.L j).val)^2) (max (U.readyHere j) (Filter.eventually_atTop.mp (on_space U j (show (0:ℝ)<1 by norm_num))).choose)
def inflate (U : Wait Z) : Wait Z := {
   U with window := fun j s=>canopy U j s + span s
          readyHere := barrier U
          sublin := fun j=> by simpa only [Nat.cast_add, add_div,zero_add] using (canopy_admitted U j).add span_admitted }
lemma thicker (U:Wait Z) : Thicker U (inflate U) :=
    ⟨by exact le_rfl,fun j=> (le_max_left ..).trans (le_max_right ..),fun j s => (Nat.le_add_left ..).trans (Nat.le_add_right ..)⟩
end YM.Pert.Dense

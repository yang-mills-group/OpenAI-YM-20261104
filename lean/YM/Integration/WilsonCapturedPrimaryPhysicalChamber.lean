import YM.Integration.WilsonCapturedPrimaryPhysicalArray

/-! At a fixed reflection date the actual minimum-image positions of all submitted
children lie in its central chamber, including after a common microscopic shift. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPhysicalChamber
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Source Extraction
open Extra.Histories Motion PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Ribbons MergeProof.Ribbons.ManyCopies Cells
open Next.Rank WilsonCapturedPrimaryPhysicalArray
open private supported from YM.Integration.WilsonCapturedPrimaryPhysicalArray
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) {n N per b:ℕ}
local notation "CF" => R.family

theorem scale (live:b ≤ N) (z:Fin n→Site ((CF).side N per)) (axis:Option (Fin n)) (D:ℕ)
    (home:∀j, separation (((CF).S.toDepth live per).parent (z j)) 0 ≤ D) (t:Fin n) :
    8*‖(CF).S.place (registered z axis t)‖ ≤ 16*(CF).S.a b*(2*(D:ℝ)+1) :=by
  let g:=(CF).S.toDepth live per
  let o:=axis.elim 0 z
  have zeroHome:separation (g.parent o) 0 ≤ D :=by
    cases axis with
    | none => simp [o,WilsonCapturedPrimarySubcellOrigin.origin]
    | some i => exact home i
  have coarse:separation (g.parent (z t)) (g.parent o) ≤ 2*D :=by
    have tri:=separation_triangle (g.parent (z t)) 0 (g.parent o)
    rw [separation_comm 0] at tri
    have first:=home t
    change separation (g.parent (z t)) 0 ≤ D at first
    omega
  have grown:=(OPE.Log.Trunk.Canvas.expands (C:=CF) (z t) o live).2
  change separation (z t) o < g.count.val*separation (g.parent (z t)) (g.parent o)+g.count.val at grown
  have fine : separation (registered z axis t) 0 ≤ g.count.val*(2*D+1) :=by
    change separation (z t-o) 0 ≤ _
    rw [← OPE.Loom.separation_alt]
    rw [Nat.mul_succ]
    exact grown.le.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ coarse) _)
  have bounds:= (Ribbons.normC (CF) N per (registered z axis t)).2
  have realFine:((separation (registered z axis t) 0:ℕ):ℝ) ≤
      (g.count.val:ℝ)*(2*(D:ℝ)+1) := by exact_mod_cast fine
  have sc:(CF).S.a N*(g.count.val:ℝ)=(CF).S.a b := (CF).S.embeds_scale g
  have cost:=(mul_le_mul_of_nonneg_left realFine ((CF).S.a_pos N).le)
  rw [← mul_assoc,sc] at cost
  linarith only [bounds,cost]

theorem original (J:ℕ) (φ:Test n) :
    ∀ᶠ r:ℝ in 𝓝[>]0, let cutoff:=WilsonCapturedPrimarySupportedHalo.date R r
    ∀N per,cutoff ≤ N → ∀z:Fin n→Site ((CF).side N per),
    WilsonCenteredCompactBooking.mass R φ r (N,per) z ≠ 0 →
    ∀axis:Option (Fin n),∀t:Fin n,8*‖(CF).S.place (registered z axis t)‖ ≤ (CF).S.a J :=by
  obtain ⟨M,diameter⟩:=φ.hasCompactSupport.exists_bound_of_continuousOn
    (continuous_id (X:=Points n)).continuousOn
  let K:=⌈M⌉₊
  let D:=K+2
  have denom:0 < 16*(2*(D:ℝ)+1) := by positivity
  obtain ⟨l,small⟩:=((CF).S.shrinks.eventually (gt_mem_nhds (div_pos ((CF).S.a_pos J) denom))).exists
  change (CF).S.a l < (CF).S.a J/(16*(2*(D:ℝ)+1)) at small
  have chamber:16*(CF).S.a l*(2*(D:ℝ)+1) ≤ (CF).S.a J :=by
    rw [lt_div_iff₀ denom] at small
    linarith only [small]
  filter_upwards [Ioc_mem_nhdsGT ((CF).S.a_pos l)] with r radius
  have valid:=radius.2.trans ((CF).S.strictAnti.antitone (Nat.zero_le l))
  have bracket:=WilsonCloseCaptureDate.bracket (CF).S radius.1 valid
  have late:l ≤ WilsonCapturedPrimarySupportedHalo.date R r :=by
    by_contra! early
    exact (not_lt_of_ge ((CF).S.strictAnti.antitone (Nat.succ_le_of_lt early))) (bracket.1.trans_le radius.2)
  dsimp only
  intro N per live z paid axis t
  obtain ⟨x,hx,rfl⟩:=supported R φ r z paid
  apply (scale R (late.trans live) (WilsonCenteredCompactBooking.site R r (N,per) x) axis D _ t).trans chamber
  intro v
  apply WilsonCapturedPrimaryCompactSites.ancestor (CF).S (late.trans live) (r • x) (K+1) _ v
  intro u a
  have one:|x u a| ≤ ‖x u‖ :=by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (x u) a
  have cap : |x u a| ≤ (K:ℝ) :=one.trans ((PiLp.norm_apply_le x u).trans ((diameter x hx).trans (Nat.le_ceil M)))
  change |r*x u a|+(CF).S.a l ≤ ((K+1:ℕ):ℝ)*(CF).S.a l
  rw [abs_mul,abs_of_pos radius.1,Nat.cast_succ,add_mul,one_mul]
  exact add_le_add ((mul_le_mul radius.2 cap (abs_nonneg _) ((CF).S.a_pos l).le).trans_eq (mul_comm _ _)) le_rfl

end YM.Integration.WilsonCapturedPrimaryPhysicalChamber

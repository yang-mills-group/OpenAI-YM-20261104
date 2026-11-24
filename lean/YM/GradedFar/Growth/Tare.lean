import YM.GradedFar.Growth.Winding

/-!
# G.1 uniform growing assertion from compact assertion
-/
namespace YM.FVA2.GradedFar.Growth
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open Continuation
open scoped Topology BigOperators Classical ContDiff
open MS.Book.Program
variable {G : Gauge} {n d : ℕ} {I J E : Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G

abbrev Court (r : ℝ) (C B : ℝ) := Icc (0:ℝ) (log (C*g r^(-B)))
def Tree (G : Gauge) {C B : ℝ} (c0:0<C) (b0:0<B): Loft G ℝ:=⟨τ,id,C,c0,B,b0,tendsto_id⟩
lemma intoCourt (r : ℝ) (C B : ℝ) (hg : 0 < g r) (hc : 0<C) (s:ℝ) (hs : 0 ≤ s) : s ∈ Court (G:=G) r C B ↔ exp s≤ C*g r^(-B) := by
    unfold Court; constructor
    · intro h; have he:= Real.exp_le_exp.mpr h.2
      rwa [exp_log (show 0 < C*g r^(-B) by positivity)] at he
    intro h; exact ⟨hs, (Real.exp_le_exp).mp (by rw [exp_log ((exp_pos _).trans_le h)]; exact h)⟩
lemma tree (G : Gauge) {C B : ℝ} (c0:0<C) (b0:0<B) :
    (packer (Tree G c0 b0) (fun z:Stays (fun r=> Court (G:=G) r C B)=> z.val.1)).Mid (fun z=> z.val.2) :=
    Eventually.of_forall fun i=> i.property

variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable (Z : Coven G d) (θ : ℝ→ℝ) (ht : Tendsto (fun r=>θ r/gYM G r) τ (𝓝 1)) (hv : travels Z)
  (pc : ∀ p : ℕ, 1≤p → PFrame N M Z θ p) (pt : ∀ p : ℕ,1≤p → PTheta N M θ p)
include H ht hv pt pc
lemma for_year (Q : Loft G I) (s : I→ℝ) (hs : Q.Mid s) (q : ℕ) :
    ∀ᶠ p : ℕ in atTop, ∀ᶠ i in Q.path, theta_err N M θ p (Q.r i) (s i)+frame_err N M Z θ p (Q.r i) (s i)≤ g (Q.r i)^q := by
  obtain ⟨Y,hy,hY⟩:=kind_choice N M H Z θ ht (pc 1 le_rfl)
  let D:ℝ:=-(d:ℝ) + -(d:ℝ) + -piled Y
  filter_upwards [eventually_ge_atTop 1, (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (q-Q.B*D : ℝ)] with p hp hk
  have hw : q < ((p+1:ℕ):ℝ)+Q.B*D := by push_cast; linarith only [hk]
  obtain ⟨C,hC,k,h⟩:= chain N M H Q Z θ ht s hs p Y hy hY hv (pc p hp) hp (pt p hp)
  filter_upwards [h,Q.eventual_power simple hw k C hC] with i h' hk
  exact (show theta_err N M θ p (Q.r i) (s i)+frame_err N M Z θ p (Q.r i) (s i) ≤ _ from le_abs_self _).trans (h'.trans hk)

/-- Statement varying T (s variable is `log T`) in growing aperture beginning even at 1.
Continuity of inputs θ and Z **not needed**. Key p can be chosen arbitrarily high, after B,
for every required accuracy L. -/
theorem growing {C B : ℝ} (c0:0<C) (b0:0<B) (q : ℕ) :
    ∀ᶠ p : ℕ in atTop, ∀ᶠ r in τ,∀ s≥0, exp s ≤ C*g r^(-B) → theta_err N M θ p r s+frame_err N M Z θ p r s≤ g r^q := by
  filter_upwards [for_year N M H Z θ ht hv pc pt _ _ (tree G c0 b0) q] with i hi
  filter_upwards [eventually_comap.mp hi,positive_g simple] with r hr pr s hs h
  exact hr ⟨(r,s),(intoCourt r C B pr c0 s hs).mpr h⟩ rfl

-- derive ReplacementAt (Z in actual module via chairs), not assuming basis equality.
def reshape (Z : ChangeAt G) (d : ℕ) : Coven G d:= fun r s=> chairs G d (Z d (r,s))

variable (Z' : ChangeAt G) (hz : Z=reshape Z' d)
include hz
/-- QScale growing component needed in First. -/
theorem replacement {C B : ℝ} (c0:0<C) (b0:0<B) (p : ℕ) :
    ReplacementAt N M d Z' (upper G C B) θ p := by
  intro L
  obtain ⟨q, hq, hh⟩:= ((eventually_ge_atTop (p+5)).and (growing N M H Z θ ht hv pc pt c0 b0 (p+2))).exists
  let L':= max L 1
  have hL : 0<L':=zero_lt_one.trans_le (le_max_right ..)
  refine ⟨q,hq,L',hL,?_⟩
  apply Window.windows_eventually .. |>.mpr; refine ⟨0,?_⟩
  filter_upwards [hh, positive_g simple] with r h hr s hs hz' v hl
  have he:0 ≤ L'*g r^(p+2):= by positivity
  apply (chair_ball _ he).mpr
  let Y:=atColumn (Kseries N M d (-s)) q (θ r)
  change ‖chair G d (Z' d (r,s) v-Y v)‖ ≤ _
  rw [map_sub,← appointed, ← appointed, ← sub_apply]; apply le_trans (ContinuousLinearMap.le_opNorm _ _)
  rw [column_by]
  refine le_trans (mul_le_mul ?_ ((chair_ball v hL.le).1 (show Ball L' v from fun i=> (hl i).trans (le_max_left ..))) (norm_nonneg _) (show 0 ≤ g r^(p+2) by positivity)) (mul_comm _ _).le
  apply le_trans (show ‖chairs G d (Z' d (r,s))-blend _ _ _‖ ≤ theta_err N M θ q r s+frame_err N M Z θ q r s by rw [hz]; exact le_add_of_nonneg_left (show 0 ≤ theta_err .. from norm_nonneg _)) (h s hs hz')
end
end YM.FVA2.GradedFar.Growth

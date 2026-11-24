import YM.GradedFar.Physical.Links

/-! Choose T equal to `θ r ^ (-B)` even before evaluating. -/
namespace YM.FVA2.GradedFar.Physical.Address
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open OPE Orbits Logged Physical.Round
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k j t p : ℕ} {I V:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (K : FramesH P)
    (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) (θ:ℝ→ℝ)
variable {X:Set (Points n)}{Y:Set (Points m)}
    {B C c η L L':ℝ}
def thetaWindow (θ:ℝ→ℝ)(B:ℝ)(r:ℝ): Continuation.Window := (r,Real.log (θ r ^(-B)))
local notation "W"=>thetaWindow θ B
lemma stretch (r:ℝ)(h:0<θ r) : Window.Stretch (thetaWindow θ B r)= θ r^(-B):= exp_log (rpow_pos_of_pos h _)
variable (ht:Tendsto (fun i=>θ i/gYM G i) τ (𝓝 1))(hC:1<C)(hc:c<1)(hB:0<B)
include simple ht hC hc hB
lemma ticketed_window : Tendsto (thetaWindow θ B) τ (windows (band G c C B)) := by
   have hx := paid_reading simple θ ht
   have hp: Tendsto θ τ τ:= by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_,hx.mono fun _ h=> h.2.1⟩
      apply squeeze_zero' ((hx.mono fun i h=>h.2.1.le)) (hx.mono (fun i h=> show θ i ≤ 2*g i from (le_abs_self _).trans h.2.2.2)); simpa using (shrink simple).const_mul 2
   have h := ht.rpow_const (p:=-B) (Or.inl (one_ne_zero)); rw [one_rpow] at h
   apply tendsto_inf.mpr; refine ⟨Filter.Tendsto.prodMk (show Tendsto (fun i:ℝ=>i) τ τ from tendsto_id) (tendsto_log_atTop.comp ((tendsto_rpow_neg_nhdsGT_zero (by linarith : -B<0)).comp hp)),tendsto_principal.mpr ?_⟩
   filter_upwards [hx,h.eventually (lt_mem_nhds hc),h.eventually_lt_const hC] with i hp hi hr
   have hh:= Real.rpow_pos_of_pos hp.1 (-B); rw [Real.div_rpow hp.2.1.le hp.1.le] at hi hr
   refine ⟨?_,?_⟩
   · change Window.Stretch (thetaWindow θ B i) ≤ C*g i^(-B); rw [stretch _ i hp.2.1]; exact ((div_lt_iff₀ hh).mp hr).le
   change c*g i^(-B) ≤ Window.Stretch (thetaWindow θ B i); rw [stretch _ i hp.2.1]; exact ((lt_div_iff₀ hh).mp hi).le
omit hB
include H
set_option linter.unusedSectionVars false in
/-- At `T=theta^(-B)`.
 Still compare physical stretch with `v` in every term and t(r) spent AFTER crop.
-/
lemma accuracy_at_theta (hp: Towards N M U K θ Q)(hn:0<n) (hX:IsCompact X)(hx:X⊆conf n)(hY:IsCompact Y)(hy:Y⊆Outside m)(hη:η<1)
    (hc0:0<c) (d:Fin n→ℕ)(e:Fin m→ℕ)(L L':ℝ)(p h:ℕ) :
     ∀ᶠ B:ℝ in atTop,∀ᶠ k:ℕ in atTop,
       Tolerates N M U K Q θ d e X Y p h k c C η B L L' ∧
       let v := thetaWindow θ B
       ∃ C' : ℝ,0<C' ∧ ∀ᶠ r in τ,∀ i:View U,∀x∈X,∀y∈Y,
         ∀u:Inputs G d, Within L u →∀z:Inputs G e, Within L' z →
         let w:=v r; let E:=delta_operator N M U K θ w i y z k h
         let F:=Ywide U K w i x y u z; let D:=Dwide U K w i y z; let R:= cActual N x u h k (θ r)
         let δ:=F-crop k (θ r) (Yx N M x y u z w.sep)
         ‖δ‖+weigh h E+‖δ-E R‖+‖F-D (packet U K Q d h r i x u)‖+‖F-D R‖ ≤ C'* g r^p * (θ r ^(-B))^(-(h+η)) := by
   filter_upwards [hp.advanced n m d e X Y hn hX hx hY hy p h L L' c C η hc0 (le_trans hc.le hC.le) hη,eventually_gt_atTop 0] with B h hB
   refine h.mono fun k h'=> ⟨h',?_⟩; intro v; obtain ⟨D,hD,hA⟩:=h'
   refine ⟨D,hD,?_⟩; filter_upwards [(ticketed_window (simple:=simple) θ ht hC hc hB).eventually hA,paid_reading simple θ ht] with r hr hp i x hx y hy u hu z hz w E F D' R δ
   rw [← stretch θ r hp.2.1]; change _ ≤ D*g r^p* w.Stretch ^(_ : ℝ)
   rw [mul_assoc]; apply le_trans _ (hr i _ hx _ hy u hu z hz (0:Sec G _) (by intro i; rw [map_zero,norm_zero]; norm_num))
   unfold δ R D' E F w; unfold weigh; simp_rw [connected]; dsimp only [len,thetaWindow,v];
   gcongr (?_ + _) + _ + _ + _; exact le_add_of_nonneg_right (norm_nonneg _)
end
end YM.FVA2.GradedFar.Physical.Address

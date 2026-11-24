import YM.GradedFar.Physical.Terms
import YM.GradedFar.Physical.G1

/-!
# Operator and structure links, claims to apply at the actual readings
-/
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
    {B C L L':ℝ}
local notation "Q₀"=>upper G C B

def delta_operator (w:Continuation.Window) (t: View U)(y:Points m)(s:Inputs G e)(p h:ℕ) : Sec G h→ₗ[ℂ]ℂ :=
     receive U K w t y s h - ∑ j: Toon G h,crop p (θ w.len) (DX N M j y s w.sep) • coord j
lemma connected (w:Continuation.Window)(t: View U)(y:Points m)(s:Inputs G e)(a:Sec G h) :
     delta_operator N M U K θ w t y s p h a= Dwide U K w t y s a - crop p (θ w.len) (Dx N M y s w.sep a):= by
    unfold delta_operator; rw [LinearMap.sub_apply,receive_leg]; unfold Dx responses; rw [crop_sum,LinearMap.sum_apply]
    simp_rw [LinearMap.smul_apply,smul_eq_mul,crop_C_mul]; congr 1; exact Finset.sum_congr rfl (fun i _=> mul_comm _ _)

variable (hB:0<B)(hC:0<C)(hX:IsCompact X)(hx:X ⊆ conf n)(hY:IsCompact Y)(hy:Y⊆ Outside m)
local notation "t₀"=>∑ j,e j
include simple hB hC
include H hX hx hY hy
set_option linter.unusedSectionVars false in
/-- (M.2).1 also as a single complete estimate (with any one unit operator input for δD).
-/
lemma first_M2 {d:Fin n→ℕ}{e:Fin m→ℕ}(ht:Towards N M U K θ Q)(p h:ℕ) : ∃ T:ℝ, 0<T ∧ ∃ j:ℕ, ∀ᶠ (w:Continuation.Window) in windows (upper G C B), ∀ t:View U,
    ∀x∈X,∀y∈Y,∀u:Inputs G d, Within L u →∀v:Inputs G e, Within L' v→ ∀ a:Sec G h,Ball 1 a→
       let D:=(delta_operator N M U K θ w t y v p h)
       ‖Ywide U K w t x y u v-crop p (θ w.len) (Yx N M x y u v w.sep)‖+‖D a‖+weigh h D ≤
         T*w.Stretch^(∑ j, e j)*g w.len^(p+1)*(1+w.sep)^j := by
    obtain ⟨T,hT,j,Ht⟩:= ht.first_line n m d e X Y B C hB hC hX hx hY hy p L L'
    let X' := ({0} : Set (Points 1)); have h0 : X'⊆conf 1:= singleton_subset_iff.mpr fun _ _ _=> Subsingleton.elim ..
    obtain ⟨D,hD,k,Hd⟩:= ht.first_line 1 m (fun _=>h) e X' Y B C hB hC isCompact_singleton h0 hY hy p 1 L'
    let n':= ∑ j, e j; let M':ℝ:= Fintype.card (Toon G h)
    refine ⟨T+D+M'*D,by unfold M'; positivity,j+k,?_⟩
    filter_upwards [Ht,Hd,(windows_short _).eventually (positive_g simple),(windows_separation _).eventually_ge_atTop 0] with w hw he hp hz t x hx y hy u hu v hv a ha DL
    let c := (Window.Stretch w)^n'*g (Window.len w)^(p+1); have hc:0< c:=mul_pos (pow_pos (Real.exp_pos _) _) (pow_pos hp _)
    let C':=1+Window.sep w; have hf:1 ≤ C':= by unfold C'; linarith
    have hA : ‖Ywide U K w t x y u v-crop p (θ (Window.len w)) (Yx N M x y u v (Window.sep w))‖≤ T*c*C'^(j+k):= by rw [full_same]; apply le_trans (hw t x hx y hy u hu v hv); rw [mul_assoc T ((Window.Stretch w)^n')]; gcongr; omega
    have hB (b : Sec G h) (hb:Ball 1 b) : ‖DL b‖ ≤ D*c*C'^(j+k) := by
       obtain h:=he t _ (mem_singleton _) y hy (fun _ : Fin 1=>b) (fun _=>hb) v hv
       unfold DL; rw [connected,center_same,Dx,responses_eq]; apply h.trans; rw [mul_assoc D ((Window.Stretch w)^n')]; gcongr; omega
    have hu:weigh h DL ≤ M'* (D*c*C'^(j+k)) := by
      apply (Finset.sum_le_sum (fun (i:Toon G h) (_:i∈ Finset.univ)=> hB (theory i) (ball_basis i))).trans_eq _
      simp [M']
    apply (add_le_add (add_le_add hA (hB a ha)) hu).trans_eq; unfold C' c; ring -- congr ∑ equality n'
end
end YM.FVA2.GradedFar.Physical.Address

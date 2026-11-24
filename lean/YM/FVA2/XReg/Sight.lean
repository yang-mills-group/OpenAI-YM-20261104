import YM.FVA2.XReg.Sum
/-!
# Passing the near-free Fray solution through coefficientwise limit of Reports

Use the layout recipe at every report (`frames`, with all the stated
Fray/preparation and initial hypotheses). Nothing here about bounding
errors on any nonperturbative reports; these are for formal coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Reg.Higher
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open Normalize.Fray Reg.Point Reg.Unique CoverTest Photo
open scoped Topology ContDiff BigOperators Classical
variable {n d k:ℕ}{G:Gauge} {I:Type*} {F:Filter I}
local notation "Π"=> Press.portDeck G
local notation "ℒ"=> Normalize.Change G d
local notation "𝒮"=> XSpace.Structure1.Point G d n
local notation "μ"=> (PowerSeries.mk (R:=ℂ))
local notation "W"=> Fin n
-- uniform scope.Fixed world.Family.R
local notation "S"=> Normalize.Screen G d
variable {T: Screen G d}(V:Fray T)(H:T.Prepared)
def ChangeVia (F:Filter I)(x:I→ Normalize.Change G d)(a:Normalize.Change G d): Prop:= Tendsto (fun i=> guide G d (x i)) F (𝓝 (guide G d a))
abbrev Formulas (F:Filter I)(x:I→ Pick G d)(b:Pick G d): Prop:= ∀ n, ChangeVia F (fun i=> x i n) (b n)
abbrev HasAll (F:Filter I)(x:I→ Reports G d)(a:Reports G d): Prop:= ∀ n, Calls F (fun i=> x i n) (a n)
abbrev Pieces (F:Filter I)(x:I→ℕ→ Structure1.Point G d n)(a:ℕ→ Structure1.Point G d n): Prop :=∀ k (p:Tags G d n), Tendsto (fun i=> x i k p) F (𝓝 (a k p))
section generalFrame
variable (v:I→ Pick G d)(b: Pick G d)(h: Formulas F v b)
include h
lemma establishes (k:ℕ)(p:Sec G d): Reads d (F:=F) (fun i=> coeff k (deck (v i)) p) (coeff k (deck b) p):= by
 unfold Reads; simp_rw [decked, pulling]; split_ifs with he; · simp_rw [stood,map_add]; exact tendsto_const_nhds.add ( light_cost d (h k) p )
 exact light_cost d (h k) p
lemma respected₂ (x:I→ℕ→ Structure1.Point G d n)(a:ℕ→ Structure1.Point G d n)(hp: Pieces F x a): Pieces F (fun i=> status (deck ( v i )) (x i)) (status (deck b) a):= by
 intro k p; simp_rw [seen]; apply tendsto_finsetSum; intro l _; apply Photo.lights d (pulseU l (deck b) p) _ _ _ _ ( hp (l none) ); intro j; exact establishes v b h _ _
lemma respected (x:I→Reports G d)(a:Reports G d)(hp:HasAll F x a): HasAll F (fun i=> realm (deck (v i)) (x i)) (realm (deck b) a) := by intro k n t p; simp_rw [ ← restT ]; exact respected₂ v b h (fun i j=> x i j n t) (fun i=> a i n t) (fun k p=> hp k n t p) k p
end generalFrame
lemma crux (P: Prediction G d): guide G d (T.D P)= ( V.stamps (fun i=> watch (V.scope i) P)):= by rw [ ← V.equal ]; rfl
lemma compass {P:Reports G d}(h:P 0=reference G d): (Lays V H P) 0=0:= by rw [leads,h,pass_free]
variable (P:Reports G d)(h0:P 0= reference G d)(z:I→Reports G d)(hp: HasAll F z P)
include h0
lemma force_title : Executed V H P:= by
    have he := ( V.happy (u:=pure ()) H ( show V.Via (u:=pure ()) (fun _:Unit=> P 0) from ?_ ) ); exact eventually_pure.mp he -- event method
    unfold Via opening; rw [h0]; exact tendsto_const_nhds
lemma uniqueness_title (b: Pick G d)(hu:T.Solved b P)(hv:b 0=0): b=Lays V H P:= Eq.symm ( Screen.shift_unique T P (Lays V H P) b (( compass V H h0 ).trans hv.symm) (force_title V H P h0).2.1 hu (force_title V H P h0).2.2.1 )
include hp
lemma cost_est : Via V (u:=F) (fun i=> z i 0):= by
    unfold Via; apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j; rw [opening, ← h0 ]; exact hp 0 _ _ _
local notation "P₀"=> Lays V H P
local notation "X"=> MoveSpace G d
private lemma h_c : Tendsto (fun i=> guide G d ( Lays V H (z i) 0 )) F (𝓝 0):= by simp_rw [leads]; exact V.turns_approach H ( cost_est V P h0 z hp )
lemma launch (k:ℕ) : ChangeVia F (fun i=> Lays V H (z i) k) (P₀ k):= by
    let Z i:= Lays V H (z i); let L:=guide G d; let t(i:I):= V.delta (V.purse (z i 0), L ( Z i 0 )); let f(p:Prediction G d):= L ( -( T.D p ) ); have he:= V.happy (P:=z) H ( cost_est V P h0 z hp ); have hz: Tendsto (fun i=> (t i).inverse) F (𝓝 1):= by unfold t L Z; simp_rw [leads]; exact V.toll H ( cost_est V P h0 z hp )
    have hu : ∀ᶠ i in F,(t i).IsInvertible:=( Tendsto.prodMk_nhds ( cost_est V P h0 z hp ) ( h_c V H P h0 z hp ) ).eventually ( V.unhit H )
    induction k using Nat.strong_induction_on with
    | _ k ih=>
      by_cases hv:k=0; · subst k; unfold ChangeVia; rw [compass V H h0,map_zero]; exact h_c V H P h0 z hp
      let b(i:I):= Screen.blind ( Z i ) k; let A(i:I):= realm (deck (b i)) (z i); let B:= Screen.blind P₀ k; let a:= realm (deck B) P; have hpB: Formulas F b B:= by
          intro i; by_cases ht:i<k; · unfold ChangeVia b B; simp_rw [Screen.blind_low _ _ i ht]; exact ih i ht
          unfold ChangeVia b B; unfold Screen.blind; simp only [ ht,↓reduceIte ]; exact tendsto_const_nhds
      have hF(p:Prediction G d): f p= -(V.stamps (fun i=> watch (V.scope i) p)):= by unfold f L; rw [ map_neg, crux V ];
      have ht := respected b B hpB z P hp; have ha:Tendsto (fun i=> f ( A i k )) F (𝓝 (f (a k))) := by simp_rw [hF]; exact ( V.stamps.continuous.continuousAt.tendsto.comp ( tendsto_pi_nhds.mpr (fun i=> ht k (V.scope i).n (V.scope i).t _ )) ).neg -- _
      unfold ChangeVia; change Tendsto (fun i=> L ( Z i k )) _ _; have hx := (T.bare_price (T:=P₀) (l:=k) _ hv ( force_title V H P h0 ).2.1) -- check order and time
      rw [compass V H h0,h0,XSpace.Normalize.regular T H] at hx; rw [hx]; apply ((show Tendsto (fun i=> (t i).inverse (f (A i k))) F (𝓝 (f (a k))) from ((Continuous.clm_apply continuous_fst continuous_snd).continuousAt (x:=((1:X→L[ℝ]X), f (a k)))).tendsto.comp ( hz.prodMk_nhds ha ))|>.congr'); filter_upwards [he,hu] with i hi hy; apply hy.inverse_apply_eq.mpr; unfold t L; rw [ V.order, align, LinearEquiv.symm_apply_apply, T.bare_price (R:=z i) (T:=Z i) hv hi.2.1 ] -- he proof simp rw no <$
theorem frames : Formulas F (fun i=> Lays V H ( z i )) (Lays V H P):= fun i=> launch V H P h0 z hp i
theorem acts : HasAll F (fun i=> fit V H (z i)) (fit V H P):= respected _ _ (frames V H P h0 z hp) z P hp
end YM.FVA2.Reg.Higher

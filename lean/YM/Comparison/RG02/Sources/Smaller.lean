import YM.Comparison.RG02.Sources.Naming
/-!
# Retention of named costs under same-protocol restriction

 N.b. the served mask footprint(s) is/are on the same high-horizon step. No assertion that when
 changing derivative demands or any budget from outside, the same cut or lower denominator
 bounds could be used. The theorem provides slicing on a given estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Sources
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open YM.Marker YM.Multi YM.Comparison.RG02.Order Integral Actual Local
open YM.Extra.Trajectories (Names Names.look connected pass_connected connected_quiet)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V V' : Type} [DecidableEq V'] [DecidableEq V] [Fintype V] [Fintype V'] {C : Census V} {C' : Census V'}
  (u : Names C C')
variable {c f : Side} {G : Gauge} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
variable (K : Bulk.Kernel S p P O) (t : S.Choices) (F : Forest S.ratio) (x : fieldDir G c 1)
   (W : Bulk.Colors C' G f) (g w₀ : ℝ) (X : Lit C' (Config G f)) (A : Set (F.Slice G)) (r : ℕ)
local notation "I"=> Function.Embedding.refl (Fin r)
local notation "X'"=>remap u X
local notation "W'"=>pin u W
lemma model_trim : remap u (model g w₀ W K)=model g w₀ W' K := by
   funext v; unfold remap model; rw [comp_apply,u.smul,u.pass_restrict (a:=markedLog g v W) (by apply part_lit_quiet)]; exact congrArg ( (Complex.ofReal (weight g w₀ v W p P)) • Poly.pass ·) (restrict_lit u _)
lemma trim_ambient : remap u (ambient K F t g x W)=ambient K F t g x W' := by
   funext v; unfold ambient Assembly.numeric; simp only [Poly.product_bead]; rw [remap,comp_apply,u.smul,u.pass_restrict (a:=Assembly.smoothMark W.power (Bulk.markFn S F W) g (Bulk.translated K F x v)) (by apply part_lit_quiet)]; congr 2
   exact restrict_lit u _
lemma trim_desired : remap u (desired K F t g x W r)=desired K F t g x W' r := by
   funext v; unfold desired remap Assembly.evaluated; simp_rw [comp_apply, Assembly.exponent_identity]
   let a : Grade C' r:= series _ _ (Assembly.affine W.power (Bulk.markFn S F W) (Bulk.geometric K F t W) (Bulk.translated K F x v))
   have h0 : a.part (Board C' r).quiet=0:= Assembly.driver_quiet ..
   rw [value_restrict u (Poly.pass a) (Symmetric.pass (Symmetric.known _)) _]
   unfold truncate; rw [Extra.Trajectories.Names.pass_restrict _ h0]
   congr 2; exact Assembly.compatible (W').power _ _ u _ W.power (Bulk.markFn S F W) _ (fun _ _ _=>rfl) (fun _ _ _ _=>rfl) _
lemma trim_drift : remap u (drift K F t g x W A r)=drift K F t g x W' A r := by
   unfold drift; rw [masked,remap_sub,trim_ambient,trim_desired]
lemma trim_removed : remap u (removed K F t g x W A r)=removed K F t g x W' A r := by unfold removed; rw [masked,trim_desired]
lemma trim_older : remap u (older K F t g w₀ x W A X)=older K F t g w₀ x W' A X' := by unfold older; rw [masked, remap_comp,retains,olderInput,remap_sub,model_trim]; rfl
omit [Fintype V] [Fintype V'] in
lemma trim_outside : remap u (outside F t g x A X)=outside F t g x A X' := by unfold outside; rw [masked,remap_comp,retains]
lemma trim_shortage : u.restriction (shortage K F t g w₀ x W A X r) = shortage K F t g w₀ x W' A X' r := by
   unfold shortage
   simp_rw [map_add,u.smul,map_sub,charge_remap, trim_drift,trim_removed,trim_outside,trim_older]
lemma trim_leftover (y : S.Choices → Set (F.Slice G)) : u.restriction (leftover K F g w₀ x W X r y) = leftover K F g w₀ x W' X' r y := by unfold leftover; simp_rw [map_sum,trim_shortage]

variable (R : Rep G f) (U : Config G f) (K : Bulk.Kernel S R.clip R.path O)
local notation "F'" => Bulk.Fk K F t W x r
local notation "T'" => Bulk.Fk K F t W' x r
lemma trims_mass : u.restriction (value (g:ℂ) (denominator (F')))=value (g:ℂ) (denominator (T')) := by rw [denominator,value_restrict u _ (Symmetric.vacant (Bulk.fk_sym ..)) (g:ℂ),trunc_bottom,criterion]; rfl
lemma trims_ratio : u.restriction (value (g:ℂ) (Order.ratio (F')))=value (g:ℂ) (Order.ratio (T')) := by rw [value_restrict u _ (sym_ratio (Bulk.fk_unit ..) (Bulk.fk_sym ..)) _,trunc_ratio u _ (Bulk.fk_unit ..),criterion]
lemma trims_mark : u.restriction (value (g:ℂ) (logMarked (F')))=value (g:ℂ) (logMarked (T')) := by rw [value_restrict u _ (sym_logMarked (Bulk.fk_unit ..) (Bulk.fk_sym ..)) _,trunc_marked u _ (Bulk.fk_unit ..),criterion]
lemma exponent : exponentPrice (F') g = exponentPrice (T') g := by
   unfold exponentPrice; congr 1;
   have he:= congrArg (·.part C.quiet) (value_restrict u _ (sym_logVac (Bulk.fk_unit K F t W x r) (Bulk.fk_sym ..)) (g:ℂ))
   rwa [part_restrict,u.quiet,trunc_logVac u _ (Bulk.fk_unit ..),criterion] at he

section
variable (J : Config G c) (L : Opened R K X g W)
include L
omit [Fintype V] [Fintype V'] in
lemma still_opened : Opened R K X' g W' := ⟨floor u X R L.fine,L.strong,well u W L.kin,L.eye,L.beta⟩
omit L in
omit [Fintype V] [Fintype V'] in
lemma normal_trim : u.restriction (normalized R X S J)=normalized R X' S J := by unfold normalized yield; rw [unit]; rfl
lemma trim_incoming : u.restriction (errorLog X W U g R) = errorLog X' W' U g R := by
  unfold errorLog markWeight; rw [map_sub,u.connected_restrict (a:=(↑(R.eval U) : ℂ)⁻¹ • X U) ?_, u.smul]; exact congrArg (_-·) (restrict_lit u _)
  rw [Poly.part_smul,L.fine.vacancy]; exact inv_mul_cancel₀ (by exact_mod_cast (L.strong.positive U).ne')
lemma trim_cumulant : u.restriction (Local.cumulant R X S J)=Local.cumulant R X' S J := by rw [Local.cumulant,u.connected_restrict (a:=normalized R X S J) (unitScore (L.none_zero J)),normal_trim]; rfl
variable (y : S.Choices → Set (F.Slice G)) (h : ∀ t,MeasurableSet (y t)) (H : ∀ t,y t⊆zone K R.p F g x)
include h H
local notation "H'"=> still_opened u W g X R K L
-- permit different cuts in RG1 analysis; need then specialize on true quantities & rebudget.
lemma trim_vac : vacuumError R X K g F t W y x r = vacuumError R X' K g F t W' y x r := by
  unfold vacuumError proceed; rw [← L.money_total F t y x r (Opened.trustworthy F y x h H),← (H').money_total F t y x r (Opened.trustworthy F y x h H),exponent u t F x W g r R K]
lemma trim_normalization : u.restriction (normalizeError R X K g F t W y x r)= normalizeError R X' K g F t W' y x r := by
   have hp:=(normal_trim u X R (S:=S) (sample g x)); rw [L.normalized_eq F t y x r h H,(H').normalized_eq F t y x r h H,map_add,trims_ratio] at hp
   exact add_left_cancel hp
lemma trim_connected (n : ℕ) (hs : ∀ i:C'.Mode, i.val.card≤n) : u.restriction (markingError R X K g F t W y x r n)=markingError R X' K g F t W' y x r n := by
   have he:= trim_cumulant u W g X R K (sample g x) L; rw [L.marked_eq F t y x r h H n hs,(H').marked_eq F t y x r h H n (fun i=>share_card u i ▸ hs (u.share i)),map_add,trims_mark] at he
   exact add_left_cancel he
end
end YM.Comparison.RG02.Sources

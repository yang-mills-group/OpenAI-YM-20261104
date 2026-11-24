import YM.Juniper.OrbitPrice.Curves
/-!
 # Actual orbit prices

 Compare inside Charm, arbitrary volume with SAME permutations. Mix the
 E part of one input (model) with the actual K part of another. Do not
 compare the K part at the price of 1/w when the model is made on actual K.
 This projector and algebraic step use the structure of UV-extension's Hall,
 preserve all budget data needed in the next step and let the model adapt
 across true output supports (not shorter supports for norm).
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Native
open UVExtension Lattice RG Wilson Pressure Set Function Filter MeasureTheory
open Tabernacle Charm Dales Camp Whirl Concert Lamppost BoundedContinuousFunction
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {p : BudgetPoint} {d:Tabernacle.Charm G p n}

section
local notation "E" => ↑(d.Shed p)
local notation "floor!" => Tabernacle.floor p
variable (x y : ↑(d.Shed p))
-- typ synonym (Carr accepts), preserve validity at allocated δ and w because
-- X is locally complete. No permutation choice at comparison time.
def merge : ↑(d.Shed p) := ⟨(x.val.1,y.val.2),by
    obtain ⟨⟨a,b,h⟩,f⟩:= income p d x; obtain ⟨⟨t,v,h'⟩,g⟩:= income p d y
    let k: Tabernacle.Field G n:=(x.val.1,y.val.2)
    have hh (s b) : ∃ F:(floor! k).Moves s b, Twins F (d.run s b) := by
      obtain ⟨e,hj⟩:= f s b; obtain ⟨u,ht⟩:= g s b; exact ⟨⟨e.ep,u.kp,e.reg_site,e.reg_support,u.forced_support,u.forced_inventory,u.forced_tests,e.valuesE,u.valuesK⟩,hj.1,ht.2⟩
    exact ⟨⟨a,v,⟨h.regular.smooth,h.regular.at_flat,h.regular.vanish⟩,⟨h'.forced.sym,h'.forced.symtest,h'.forced.meas,h'.forced.meas_test,h'.forced.reads,h'.forced.reads_test,h'.forced.permit⟩,fun s b=> ⟨(hh s b).choose⟩,h.boundE,h'.boundK⟩,hh⟩⟩
lemma bind_E : (floor! (merge x y).val).E=(floor! x.val).E:= rfl
lemma bind_K : (floor! (merge x y).val).K=(floor! y.val).K:= rfl
lemma pay_E {δ:ℝ} : (floor! (merge x y).val).EBound p δ ↔ (floor! x.val).EBound p δ := Iff.rfl
lemma pay_K {δ:ℝ} : (floor! (merge x y).val).KBound p δ ↔ (floor! y.val).KBound p δ := Iff.rfl
lemma bare_E : (floor! (merge x y).val).additive p=(floor! x.val).additive p:= rfl
lemma bare_K : (floor! (merge x y).val).gas p=(floor! y.val).gas p:= rfl
-- Allocation correspondence to actual budget. Includes affine null.

lemma minus (σ τ:ℝ) : tuning p σ τ (x-y).val = tuning p σ τ x.val-tuning p σ τ y.val:=
  map_sub (hue p d σ τ) ..

lemma reconcile (δ : ℝ) (hδ : 0≤δ) (σ τ:ℝ) (hσ:0<σ) :
    ‖(tuning p σ τ x.val).1-(tuning p σ τ y.val).1‖≤δ ↔ (floor! (x-y).val).EBound p (δ*σ):= by
  let U:=x-y; let M:=ChimeE G p n; let k:= sheetE p U.val
  have he : (floor! U.val).EBound p (δ*σ) ↔ M.MeasureP k (δ*σ):=(Above.floorE p _).symm
  obtain ⟨a,b,h⟩:= income p d U|>.1
  rw [show (tuning p σ τ x.val).1-(tuning p σ τ y.val).1=(tuning p σ τ U.val).1 from congr_arg Prod.fst (minus x y σ τ).symm,he]
  unfold tuning; rw [norm_smul,norm_inv,Real.norm_of_nonneg hσ.le, inv_mul_le_iff₀ hσ,mul_comm]
  exact ⟨fun hu=>Tabernacle.paper M ⟨a,(Above.floorE p _).2 h.boundE⟩ hu,fun hu=> Tabernacle.ticks M hu (mul_nonneg hδ hσ.le)⟩

lemma packet (U : Config G n): (floor! y.val).additive p U=(floor! x.val).additive p U+(floor! (y-x).val).additive p U:= by
  obtain ⟨a,b,H⟩:= income p d x |>.1; obtain ⟨t,v,h⟩:= income p d y|>.1
  unfold Activities.additive; nth_rw 1 [show (floor! (y-x).val).regularOccurrence p = fun i V=> (floor! y.val).regularOccurrence p i V-(floor! x.val).regularOccurrence p i V from ?_]
  · rw [Summable.tsum_sub ((Activities.ESeries h).summable U) ((Activities.ESeries H).summable U)]; ring
  funext i V; unfold Activities.regularOccurrence
  simp only [Tabernacle.floor, masked, Set.indicator]; split <;> first|rfl| abel
end

section course
variable {A : Levels G} {p' j : ℕ} {d : Cham A j p'}
local notation "L" => Dales.place A j p' d
local notation "σ" => A.clock.allowance j
local notation "τ" => A.clock.forcedAllowance j
variable (x y : Valve j p' A d)

-- all prices in grip sizes (<rim), only for defect comparisons along this consumer.
def trueE (x : Valve j p' A d) := (tuning (A.budget j) (A.clock.allowance j) (A.clock.forcedAllowance j) x.val).1
def trueK (x : Valve j p' A d) := (tuning (A.budget j) (A.clock.allowance j) (A.clock.forcedAllowance j) x.val).2
lemma pay_total (δ:ℝ) : ‖L x‖ ≤δ ↔ (Tabernacle.floor (A.budget j) x.val).Valid (A.budget j) (δ*σ) (δ*τ):= tickP _ σ τ (fundedP j A).1 (fundedP j A).2 (income _ d x).1
lemma total (x: Valve j p' A d) : ‖L x‖=max ‖trueE x‖ ‖trueK x‖:= Prod.norm_def _
lemma total_two : ‖(L (merge x y))‖=max ‖trueE x‖ ‖trueK y‖:= rfl
lemma total_split : ‖(L x)-(L y)‖=max ‖trueE x-trueE y‖ ‖trueK x-trueK y‖:= rfl
lemma total_diff : ‖(L y)-(L (merge x y))‖=‖trueE y-trueE x‖:= by rw [total_split]; change max ‖trueE y-trueE x‖ ‖trueK y-trueK y‖= _; simp
lemma standard_le_emission (δ : ℝ) (hδ : 0≤δ) : ‖trueE x-trueE y‖≤δ ↔ (Tabernacle.floor (A.budget j) (x-y).val).EBound (A.budget j) (δ*σ):= reconcile x y _ hδ _ _ (fundedP j A).1
end course
end YM.Juniper.Native

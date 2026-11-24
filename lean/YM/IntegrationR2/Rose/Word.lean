import YM.IntegrationR2.Rose.Top
import YM.Extra.WILSON_STARTUP.Ink
import YM.FullVolume.Rise.Lemon

/-! Prices along actual receipt and address. Generalizes `Ink`; work at SAME
    labels as any `Berry` production and projection already lives there. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Rose
open Function Filter RG Wilson Lattice Design Work Ac Padded Start
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {b : BudgetPoint} {θ:ℕ} {v β :ℝ}
open Ovens Ovens.Pipes Quad.Rose
variable (M:Berry G θ)
variable (c:Clip)
def word (i: Sheet n) (β:ℝ): Config G n → ℝ:= i.elim (fun p=> Start.weight c β • M.bud p.positive) (fun _=>0)
abbrev leader (β:ℝ) : ℕ → Config G n → ℝ:= fun i=> if fixed (Start.Sheet n) i then word M c (name (Sheet n) i) β else 0
abbrev raw (n:Side) (β:ℝ): Tap G n:= ⟨leader M c β,0,0⟩
variable {c}
def payload (n:Side)(c:Clip)(β:ℝ):Activities G n:= (dictionary G n).pours (raw M c n β)
abbrev colors (i: Key n):= M.bud i.positive
lemma allowance (i : Key n) : b.Regular i.skin (colors M i):= (Key.skin_positive ..).symm ▸ M.bud_regular i.positive b
lemma accrual_null (ht: 2<θ) (i : Key n) (β : ℝ) : (β • colors M i) (1:Config G n) = 0 ∧ ∀ x y,
      logHessian (β • colors M i) x y = 0 := by
  unfold colors; refine ⟨by simp [M.bud_one (by omega)], fun x y => ?_⟩
  change iteratedFDeriv ℝ 2 (β • (M.bud i.positive ∘ increment 1)) 0 ![x,y] = 0
  rw [iteratedFDeriv_const_smul_apply ((M.bud_smooth _ _).contDiffAt.of_le le_top),smul_apply]
  exact (congr_arg (β • ·) (M.bud_hess (by omega) i.positive x y)).trans (smul_zero ..)

lemma regularFamily (ht: 2<θ) (c:Clip) (β : ℝ) : (payload M n c β).RegularFamily b := by
  have he (i : ℕ) : b.Regular ((dictionary G n).reg i).support ((payload M n c β).E i) ∧
      ((payload M n c β).E i) 1=0 ∧ ∀ x y,logHessian ((payload M n c β).E i) x y = 0 := by
    change b.Regular (eInfo _).support _ ∧ _
    simp only [payload,Ovens.Pipes.pours,leader]; split
    · rcases name (Start.Sheet n) i with p|s
      · exact ⟨times_reg _ (allowance ..),accrual_null M ht ..⟩
      exact ⟨zero_reg,rfl,fun x y => by simp [word,logHessian]⟩
    exact ⟨zero_reg,rfl,fun x y => by simp [logHessian]⟩
  exact ⟨fun i => (he i).1,fun i => (he i).2.1,fun i _ x y _ _ => (he i).2.2 x y⟩

def price (k P : ℕ) := (M.bud_price k P).choose
def threshold (k P : ℕ) := (M.bud_price k P).choose_spec.choose

theorem constants (k P : ℕ) : 0 < price M k P ∧ 0 < threshold M k P ∧ threshold M k P ≤ 1 :=
  let h := (M.bud_price k P).choose_spec.choose_spec; ⟨h.1,h.2.1,h.2.2.1⟩

def item (b : BudgetPoint) := price M b.order b.power * b.threshold^θ

lemma item_pos (b : BudgetPoint) : 0 < item M b := mul_pos (constants ..).1 (pow_pos b.threshold_pos _)

theorem accrual_fit (i : Key n) (ht : b.threshold ≤ threshold M b.order b.power) : b.supBounds i.native i.skin (colors M i) (item M b) := by
  rw [Key.skin_positive]
  exact ((M.bud_price b.order b.power).choose_spec.choose_spec.2.2.2 b rfl rfl ht n i.positive i.native (i.skin_positive ▸ i.native_mem))


def ledger (b : BudgetPoint) (β : ℝ) := (Fintype.card Signed:ℝ)*Fintype.card PlaqAxes*(overhead b*(β*item M b))
lemma mass_item (i : Key n) (y : ℝ) (hy : ‖β‖ ≤ y) (hc : c.direct ≤ 1) :
    b.mass i.skin (‖weight c β‖ * item M b) ≤ overhead b * (y * item M b) := by
  unfold BudgetPoint.mass overhead
  have h := item_pos M b; have hs := b.exponent_pos
  have he : (coverNumber b.B i.skin : ℝ) ≤ 5^4 := by exact_mod_cast skin_cost i
  gcongr; exact (weight_le β hc).trans hy

theorem sum_items (o : Site n) {y : ℝ} (hy : ‖β‖ ≤ y) (hc : c.direct ≤ 1) : (∑ i : Sheet n,
      if (eInfo i).site = o then b.mass (eInfo i).support (i.elim (fun _ => ‖weight c β‖ * item M b) (fun _ => 0)) else 0) ≤ ledger M b y := by
  rw [Fintype.sum_sum_type]; simp only [Sum.elim_inl,Sum.elim_inr,BudgetPoint.mass,mul_zero,ite_self,Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type (fun _ : Cell n => _)]
  unfold ledger
  rw [show (Fintype.card Signed:ℝ)*Fintype.card PlaqAxes*(overhead b*(y*item M b)) = ∑ _s : Signed, ∑ x : Site n,
      ∑ _i : PlaqAxes, (if x=o then overhead b*(y*item M b) else 0) from by simp; ring]
  gcongr ∑ _, ∑ _, ∑ _, ?_ with s _ x _ i _
  change (if x=o then _ else _) ≤ _
  split <;> first | exact mass_item M (s,x,i) _ hy hc | exact le_rfl

theorem ink (ht : b.threshold ≤ threshold M b.order b.power) (hc : c.direct ≤ 1) {q : ℝ} (hy : ‖β‖ ≤ v)
    (hp : ledger M b v ≤ q) : (payload M n c β).EBound b q := by
  let E := fun i : Sheet n => i.elim (fun _ => ‖weight c β‖*item M b) (fun _ => (0:ℝ))
  let T := fun i : ℕ => if fixed (Sheet n) i then E (name (Sheet n) i) else 0
  have he : ∀ i, b.supBounds ((payload M n c β).reg i).site ((payload M n c β).reg i).support ((payload M n c β).E i) (T i) := by
    intro i
    simp only [T,payload,Ovens.Pipes.pours,leader,dictionary]; split
    · cases h : name (Sheet n) i with
      | inl p => exact times_bound _ (accrual_fit M p ht)
      | inr s => exact zero_bound
    exact zero_bound
  refine ⟨T,he,fun x => Padded.budget (α:=Sheet n) ?_ (fun i => ?_) ((sum_items M x hy hc).trans hp)⟩
  · intro i; change (if _ then b.mass _ (ite ..) else _) = _; by_cases h : fixed (Sheet n) i
    · rw [if_pos h,if_pos h]; rfl
    rw [if_neg h,if_neg h]; simp [BudgetPoint.mass]
  split
  · apply mul_nonneg (Real.exp_pos _).le
    simpa only [T,E,name_index,fixed_index,if_true] using (show 0 ≤ T (index i) from (he _).1)
  exact le_rfl

section
open PhysicalNext.Repeat
-- moving first label alone is not enough; specify dried E. K same as launch
abbrev city (n:Side)(b: BudgetPoint)(c: Clip)(β:ℝ):Tap G n:=
    let f:= Start.payload c b G n β
    { f with regular := f.regular - (leader M c β) }
lemma worded (i:Key n)(U:Config G n): colors M i U=M.bud i.root (i.frame U):= M.bud_send ..
-- subtraction, motion, preserving *ALL* future support
lemma spinning (b:BudgetPoint) (c:Clip) (s:Signed)(x:Site n)(β:ℝ): Apse.duet ⟨Tent.kinE n s x,Tent.kinK n s x⟩ (Padded.sends (Start.reachAction s x)) (Start.dictionary G n) (city M n b c β) s x:=by
   obtain ⟨⟨U,hU,hz⟩,ht⟩:= Tent.whirlN G b c n s x β -- order
   refine ⟨⟨⟨_,_,U.reg_site,U.reg_support,U.forced_support,U.forced_inventory,U.forced_tests,?_,U.valuesK⟩,hU,hz⟩,ht⟩
   intro i V; apply congr_arg₂ (·-·) (U.valuesE i V) (show leader M c β (U.ep i) V=leader M c β i (pull s x V) from ?_); rw [hU]; unfold Tent.kinE; simp only [leader,name_sends,fixed_sends]; split
   · cases name (Sheet n) i with
     | inr j=>rfl
     | inl j=>
        change Start.weight c β * colors M (Key.perm s x j) V=Start.weight c β * colors M j _; rw [worded M j,worded, Key.oriented]; rfl
   rfl
end
end YM.WilsonStartup.Rose

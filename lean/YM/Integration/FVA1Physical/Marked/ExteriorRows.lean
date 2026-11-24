import YM.Integration.FVA1Physical.Marked.ForcedCollar
import YM.Integration.FVA1Physical.Marked.ColorSummable

/-! Change all exterior links and their flags, keeping a finite collar around
one source. Every regular ordered jet common to the two tests and every
divided forced row has an exponentially small total variation after reserving
part of its own support exponent. All arrays allow independent readers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Lattice RG YM.Wilson Marker LocalComparison RG3.Script.Picnic Push.AbsoluteSums
open Push.GridApprox.Attach
open scoped Classical BigOperators
variable {I X : Type} [DecidableEq I] {B : Census I} {G : Gauge} {n : Side}
    {P : Rep G n} {o : I → Site n} {T : Taste X o P B} {w : I → ℝ} {κ a b : ℝ}

private theorem small_readout {M r : ℕ} {S : Support n} {j : Site n} (origin : j∈S)
    (short : coverNumber M S < r) : inspected S ⊆ halo (r*leg M+8) {j} := by
  intro y hy
  obtain ⟨s,hs,dist⟩ := halo_spec.mp (Next.Scheduling.flag_layer S hy)
  have inner : s∈halo (r*leg M) {j} := by
    by_contra outside
    exact short.not_ge (LocalLTE.Sail.Round2.cover_of_flag_outside origin (Finset.mem_singleton_self j) hs outside)
  obtain ⟨z,hz,close⟩ := halo_spec.mp inner
  exact halo_spec.mpr ⟨z,hz,(separation_triangle z s y).trans (Nat.add_le_add close dist)⟩

private theorem jet_local_pair {S C : Support n} {f : Config G n → ℂ} (h : LocalOn S f) (sub : S ⊆ C)
    {l l' : List (Directions G n)} (dirs : List.Forall₂ (fun A B : Directions G n=>Agrees C A B) l l') :
    ∀ U V, Agrees C U V → leftDerivs f l U=leftDerivs f l' V := by
  induction dirs with
  | nil=>exact fun U V agree=>h U V (agrees_mono agree sub)
  | cons same _ ih=>
    intro U V eq
    apply congrArg (fun k : ℝ → ℂ=>deriv k 0)
    funext t
    exact ih _ _ (fun e he ht=>by
      dsimp only [increment,Pi.smul_apply]
      rw [same e he ht,eq e he ht])

private theorem exterior_total {J : Type*} {m : J → B.Mode} {S : J → Support n} {p : BudgetPoint}
    {c f : J → ℝ} (v : I) {r : ℕ} {σ C : ℝ} (hσ : 0 ≤ σ) (hw : ∀ j,0 < w j)
    (paid : SumBudget (fun i=>if v∈(m i).val then Poly.toll w (m i)*p.mass (S i) (c i) else 0) C)
    (pos : ∀ i,0 ≤ f i) (positive : ∀ i,0 ≤ c i)
    (cost : ∀ i,v∈(m i).val → f i ≤ 2*c i)
    (zero : ∀ i,v∈(m i).val → coverNumber p.B (S i) < r → f i=0) :
    SumBudget (fun i=>if v∈(m i).val then Poly.toll w (m i)*
      (Real.exp ((p.supportExponent-σ)*coverNumber p.B (S i))*f i) else 0) ((2*Real.exp (-σ*r))*C) := by
  let k := 2*Real.exp (-σ*r)
  have hk : 0 ≤ k := mul_nonneg zero_le_two (Real.exp_nonneg _)
  apply budget_mono (budget_scale hk paid) (fun i=>by split <;> first | exact mul_nonneg (Poly.worth hw _).le (mul_nonneg (Real.exp_nonneg _) (pos i)) | exact le_rfl)
  intro i
  by_cases hv:v∈(m i).val
  · simp only [if_pos hv,BudgetPoint.mass]
    let d := coverNumber p.B (S i)
    by_cases tiny:d < r
    · rw [zero i hv tiny,mul_zero,mul_zero]
      exact mul_nonneg hk (mul_nonneg (Poly.worth hw _).le (mul_nonneg (Real.exp_nonneg _) (positive i)))
    have far : (r:ℝ) ≤ d := Nat.cast_le.mpr (le_of_not_gt tiny)
    have gain : Real.exp ((p.supportExponent-σ)*d) ≤ Real.exp (-σ*r)*Real.exp (p.supportExponent*d) := by
      rw [←Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left far hσ])
    exact (mul_le_mul_of_nonneg_left (mul_le_mul gain (cost i hv) (pos i)
      (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))) (Poly.worth hw _).le).trans_eq (by dsimp only [k,d]; ring)
  simp [hv]

/-- The variation of the complete factorial regular test in an arbitrary
exterior background. The directions need agree only inside the collar. Both fields and the
regular readers vary independently for every countable label. -/
theorem regular_exterior (H : FullBudget P.p T w κ a b) (j : I) (r : ℕ) (σ : ℝ)
    (hσ : 0 ≤ σ) (test : ℕ → X) (L R : ∀ i,DerivativeTest P.p (T.menu.branch i) (o j) G)
    (vectors : ∀ i k,k ≤ P.p.order → List.Forall₂ (fun A B : Directions G n=>Agrees (halo (r*leg P.p.B+8) {o j}) A B)
      ((L i).directions k) ((R i).directions k))
    (same : ∀ i k,k ≤ P.p.order → Agrees (halo (r*leg P.p.B+8) {o j}) ((L i).field k) ((R i).field k)) :
    let v := fun i k=>leftDerivs (T.menu.regular (test i) i) ((L i).directions k) ((L i).field k)
    let u := fun i k=>leftDerivs (T.menu.regular (test i) i) ((R i).directions k) ((R i).field k)
    SumBudget (fun i=>if j∈(T.menu.rays i).val then Poly.toll w (T.menu.rays i)*
      (Real.exp ((P.p.supportExponent-σ)*coverNumber P.p.B (T.menu.branch i))*
        (∑ k∈Finset.range (P.p.order+1), ‖v i k-u i k‖/k.factorial)) else 0)
        ((2*Real.exp (-σ*r))*a) := by
  intro v u
  obtain ⟨C,D,regular,captions,total⟩ := H.regularTotal j
  have ca : C ≤ a := by
    have t0 := mul_nonneg (H.radii j).le (H.unit_nonnegative j)
    have d0 := budget_nonneg captions
    linarith only [t0,d0,total]
  have capped : SumBudget _ a := ⟨regular.1,regular.2.1,regular.2.2.trans ca⟩
  apply exterior_total j hσ H.radii capped (fun i=>Finset.sum_nonneg fun _ _=>div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) H.white_nonnegative
  · intro i hi
    let F := T.menu.regular (test i) i
    have hL := (L i).read_le ((H.regular i).controls (test i) j hi)
    have hR := (R i).read_le ((H.regular i).controls (test i) j hi)
    calc
      _ ≤ ∑ k∈Finset.range (P.p.order+1),(‖v i k‖+‖u i k‖)/k.factorial :=
        Finset.sum_le_sum fun k _=>div_le_div_of_nonneg_right (norm_sub_le ..) (Nat.cast_nonneg _)
      _ = (L i).read F+(R i).read F := by simp only [DerivativeTest.read,add_div,Finset.sum_add_distrib]; rfl
      _ ≤ _ := (add_le_add hL hR).trans_eq (two_mul _).symm
  intro i mark short
  apply Finset.sum_eq_zero
  intro k hk
  have bound := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have home : o j∈T.menu.branch i :=
    (congrArg (fun a : Site n=>a∈T.menu.branch i) (congrFun T.root j)).mp ((H.active (test i)).articles.pins i j mark)
  have sub : T.menu.branch i ⊆ halo (r*leg P.p.B+8) {o j} := fun z hz=>
    (small_readout home short) (Finset.mem_union_left _ hz)
  have val : v i k=u i k := jet_local_pair (H.regular_law (test i) i).sites sub
    (vectors i k bound) _ _ (same i k bound)
  rw [val,sub_self,norm_zero,zero_div]

/-- The forced family admits arbitrary interior or exterior flags. The true
force reads its support including the measured flag layer and carries κ. -/
theorem forced_exterior (H : FullBudget P.p T w κ a b) (j : I) (r : ℕ) (σ : ℝ) (hσ : 0 ≤ σ)
    (test : ℕ×ℕ → X) (L R : ℕ×ℕ → Config G n)
    (same : ∀ i,Agrees (halo (r*leg P.p.B+8) {o j}) (L i) (R i)) :
    SumBudget (fun i : ℕ×ℕ=>if j∈(T.menu.marks i.1 i.2).val then Poly.toll w (T.menu.marks i.1 i.2)*
      (Real.exp ((P.p.supportExponent-σ)*coverNumber P.p.B (P.activities.forced i.1).support)*
        ‖T.menu.force (test i) i.1 i.2 (L i)-T.menu.force (test i) i.1 i.2 (R i)‖) else 0)
        ((2*Real.exp (-σ*r))*(κ*b)) := by
  apply exterior_total j hσ H.radii (H.forcedTotal j) (fun _=>norm_nonneg _) H.black_nonnegative
  · intro i hi
    exact (norm_sub_le ..).trans ((add_le_add (H.forced (test i) i.1 i.2 (L i))
      (H.forced (test i) i.1 i.2 (R i))).trans_eq (two_mul _).symm)
  intro i mark short
  let f := T.menu.force (test i) i.1 i.2
  by_cases dead : f=0
  · change ‖f (L i)-f (R i)‖=0
    rw [dead]; simp
  let act := (H.active (test i)).articles
  have home : o j∈(P.activities.forced i.1).support := by
    rw [←T.root]
    exact act.retained i.1 i.2 dead j mark
  have equal : f (L i)=f (R i) := UsesFinal.allReads P.p.threshold _ f (act.inspects i.1 i.2)
    _ _ (agrees_mono (same i) (small_readout home short))
  exact norm_eq_zero.mpr (sub_eq_zero.mpr equal)
end YM.Integration.FVA1Physical.Marked

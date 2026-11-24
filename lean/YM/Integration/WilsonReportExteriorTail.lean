import YM.Agora26.Marks.Tail
import YM.OPE.Log.Plans

/-! The finite-radius cutoff of each actual coarse marked field is uniformly
small pointwise, so this part of the pre-report carries an arbitrary integrable
coarse Wilson spectator. Each separately paid signed input keeps its own price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportExteriorTail
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi
open Next.Rank Next.Rank.Spindle OPE OPE.Yarn OPE.Strobe OPE.Strobe.Vista26
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open scoped BigOperators Classical
variable {G : Gauge} {C : Family G} {W r D} {V : Type} [DecidableEq V]

omit [DecidableEq V] in
private theorem product_size (s : Finset V) (f : V → ℂ) (c : V → ℝ)
    (hf : ∀ j, ‖f j‖ ≤ 4*c j) : ‖∏ j ∈ s, f j‖ ≤ 4^s.card*∏ j ∈ s, c j := by
  calc
    _ ≤ ∏ j ∈ s, ‖f j‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ j ∈ s, 4*c j := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hf j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const]

private theorem product_tail (s : Finset V) (f g : V → ℂ) (c : V → ℝ) {z : ℝ}
    (hz : 0≤z) (hc : ∀j,0≤c j) (hf : ∀j,‖f j‖≤4*c j) (hg : ∀j,‖g j‖≤4*c j)
    (hd : ∀j,‖f j-g j‖≤z*c j) :
    ‖(∏ j ∈ s,f j)-(∏ j ∈ s,g j)‖ ≤ z*(s.card*4^s.card*(∏ j ∈ s,c j)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    let A := ∏ j ∈ s,f j
    let B := ∏ j ∈ s,g j
    let P := ∏ j ∈ s,c j
    let X := z*c i*4^s.card*P
    have hP : 0≤P := Finset.prod_nonneg (fun j _ => hc j)
    have hX : 0≤X := mul_nonneg (mul_nonneg (mul_nonneg hz (hc _)) (by positivity)) hP
    have gprod : ‖B‖≤4^s.card*P := product_size s g c hg
    change ‖A-B‖ ≤ z*(s.card*4^s.card*P) at ih
    simp only [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one]
    change ‖f i*A-g i*B‖ ≤ z*((s.card+1)*4^(s.card+1)*(c i*P))
    calc
      _ = ‖f i*(A-B)+(f i-g i)*B‖ := congrArg norm (by ring)
      _ ≤ ‖f i‖*‖A-B‖+‖f i-g i‖*‖B‖ := by
        simpa only [norm_mul] using norm_add_le (f i*(A-B)) ((f i-g i)*B)
      _ ≤ (4*c i)*(z*(s.card*4^s.card*P))+(z*c i)*(4^s.card*P) := add_le_add
        (mul_le_mul (hf i) ih (norm_nonneg _) (mul_nonneg (by norm_num) (hc i)))
        (mul_le_mul (hd i) gprod (norm_nonneg _) (mul_nonneg hz (hc i)))
      _ = (4*s.card+1)*X := by dsimp only [X]; ring
      _ ≤ (4*(s.card+1))*X := mul_le_mul_of_nonneg_right (by linarith) hX
      _ = _ := by rw [pow_succ]; dsimp only [X]; ring

/-- Native coarse fields truncated at exactly radius A about each marked origin. -/
def cut {k N p : ℕ} (d : V→ℕ) (A : ℕ) (x : V→Site (C.side k p))
    (v : (j:V)→C.label (d j)) (j : V) (U : Config G (C.side k p)) : ℂ :=
  bead C (d j) k N p A (v j) (x j) U

/-- Product of actual original paid column budgets, with the finite arity factor. -/
def price {k N p : ℕ} (d : V→ℕ) (v : (j:V)→C.label (d j)) (s : Finset V) : ℝ :=
  s.card*4^s.card*∏ j ∈ s, (C.path.levels.params k).columns*Spindle.paid C (d j) k N p (v j)

/-- No separation or translation condition on the finite positions is used. -/
theorem point (hG : G.Simple) (hC : C.Makes) (citizen : Citizen C W r D)
    {k N p : ℕ} (hk : k<N) (d : V→ℕ) (refs : ∀j,C.ref (d j)≤k) (A : ℕ)
    (x : V→Site (C.side k p)) (v : (j:V)→C.label (d j)) (s : Finset V)
    (U : Config G (C.side k p)) :
    ‖fineJob (regularPack (N:=N) d x v) s U-fineJob (cut (N:=N) d A x v) s U‖ ≤
      Real.exp (-2*(A:ℝ))*price (k:=k) (N:=N) (p:=p) d v s := by
  obtain ⟨σ,χ,H⟩ := Yarn.enroll citizen.toSharper hC hG
  let c := fun j => (C.path.levels.params k).columns*Spindle.paid C (d j) k N p (v j)
  have hc (j) : 0≤c j := mul_nonneg (zero_le_one.trans (C.path.levels.params k).columns_ge)
    (paid_pos C (d j) k N p (v j))
  apply product_tail s _ _ c (Real.exp_nonneg _) hc
  · intro j
    exact (wholeSize H citizen (v j) (x j) hk (refs j) U).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (3:ℝ)≤4) (hc j))
  · intro j
    exact beadSize H citizen (v j) (x j) A hk (refs j) U
  · intro j
    exact (crown H citizen (v j) (x j) A hk (refs j) U).trans_eq (mul_assoc ..)

/-- Both original signed products exist against the same gauge spectator,
and their difference retains the full exponential radius factor. -/
theorem integrated (hG : G.Simple) (hC : C.Makes) (citizen : Citizen C W r D)
    {k N p : ℕ} (hk : k<N) (d : V→ℕ) (refs : ∀j,C.ref (d j)≤k) (A : ℕ)
    (x : V→Site (C.side k p)) (v : (j:V)→C.label (d j)) (s : Finset V)
    (X : Config G (C.side k p)→ℂ) (hX : Integrable X (Therm.scene C.path N p k)) :
    let μ := Therm.scene C.path N p k
    let F := fineJob (regularPack (N:=N) d x v) s
    let E := fineJob (cut (N:=N) d A x v) s
    Integrable (fun U => X U*F U) μ ∧ Integrable (fun U => X U*E U) μ ∧
    ‖(∫ U, X U*F U ∂μ)-(∫ U, X U*E U ∂μ)‖ ≤
      (∫ U, ‖X U‖ ∂μ)*(Real.exp (-2*(A:ℝ))*price (k:=k) (N:=N) (p:=p) d v s) := by
  obtain ⟨σ,χ,H⟩ := Yarn.enroll citizen.toSharper hC hG
  let μ := Therm.scene C.path N p k
  letI : IsProbabilityMeasure μ := Therm.probability hC.wilson hk.le (p:=p)
  let F := regularPack (N:=N) d x v
  let E := cut (N:=N) d A x v
  let c := fun j => (C.path.levels.params k).columns*Spindle.paid C (d j) k N p (v j)
  let rate := Real.exp (-2*(A:ℝ))*price (k:=k) (N:=N) (p:=p) d v s
  have hc (j) : 0≤c j := mul_nonneg (zero_le_one.trans (C.path.levels.params k).columns_ge)
    (paid_pos C (d j) k N p (v j))
  have hf (U) : ‖fineJob F s U‖ ≤ 4^s.card*∏ j∈s,c j :=
    product_size s _ c (fun j => (wholeSize H citizen (v j) (x j) hk (refs j) U).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (3:ℝ)≤4) (hc j)))
  have he (U) : ‖fineJob E s U‖ ≤ 4^s.card*∏ j∈s,c j :=
    product_size s _ c (fun j => beadSize H citizen (v j) (x j) A hk (refs j) U)
  have iF : Integrable (fineJob F s) μ :=
    (Envelope.prodC s F (fun j _ => wholeEnv H citizen (v j) (x j) hk (refs j))).integrableC _
  have iE : Integrable (fineJob E s) μ :=
    (Envelope.prodC s E (fun j _ => Push.GridApprox.cylinder_env
      (Strobe.bead_local H _ (v j) (refs j) hk.le _))).integrableC _
  have jF := hX.mul_bdd iF.aestronglyMeasurable (Eventually.of_forall hf)
  have jE := hX.mul_bdd iE.aestronglyMeasurable (Eventually.of_forall he)
  refine ⟨jF,jE,?_⟩
  change ‖(∫ U, X U*fineJob F s U ∂μ)-(∫ U, X U*fineJob E s U ∂μ)‖ ≤ (∫ U,‖X U‖ ∂μ)*rate
  rw [← integral_sub jF jE]
  have major : ∀ U, ‖X U*fineJob F s U-X U*fineJob E s U‖ ≤ ‖X U‖*rate := by
    intro U
    rw [← mul_sub,norm_mul]
    exact mul_le_mul_of_nonneg_left (point hG hC citizen hk d refs A x v s U) (norm_nonneg _)
  exact (norm_integral_le_of_norm_le (hX.norm.mul_const rate) (Eventually.of_forall major)).trans_eq
    (integral_mul_const rate _)

end YM.Integration.WilsonReportExteriorTail
end


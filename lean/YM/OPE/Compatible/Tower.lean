import YM.OPE.Compatible.Projection

/-!
# One tower of detectors

Independently decoding at each `d` and then simply using the coefficients
of that decoding at weight `d` need not give a coherent series. We choose
the splitting simultaneously with the detector conventions. Choose both by
induction: at d+1 honor all lower projections, which are at the same
fixed O(4) detector orbits. On `Field (d+1)` the read into `Field d`
defines our step retraction, and the rest of the projection is into the
*kernel* of this retraction. We then get *exact* compatibility/covariance
of each vector of reads with filtration projection whenever these readouts
are in domain.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov
open Function Set Filter Table Survey MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L} {T : Table L}
  {I J : Type} [Fintype I] [Fintype J]

-- Actual formal germ data independent of height truncation, orientation and phase
abbrev Sheets (S : Table L) := ∀ d, Prism (S:=S) (d:=d)

def supplies (S : Table L) : Sheets S := fun d => Classical.choice (MultipleContact.detector_exists d S)

variable (D : Sheets S)

def Visible (n : ℕ) (x : I → E4) : Prop := ∀ d ≤ n, sized (D d) x
lemma centered (n) : Visible D n (sole 0) := fun _ _ => sized_zero _

omit [Fintype I] in
lemma Visibility (n) {x : I → E4} (h : Injective x) :
    (∀ d ≤ n, ∀ i, ‖x i‖ < gap (D d)) → Visible D n x := fun p i hi => ⟨h,p i hi⟩

variable (P : DiffPlan S) (R : S.Rotation) (ρ : S.RealSpin)

/-- Ungated horizon Q_d, coordinates x relative to the product center. -/
def ascend : (n : ℕ) → {I : Type} → [Fintype I] → (I → E4) → (I → S.Tag) → S.Field n
  | 0, _, _, x, p => projection R (D 0) ρ x p
  | n+1, _, _, x, p =>
    let k := projection R (D (n+1)) ρ x p
    k + P.rise (Nat.le_succ n)
      (ascend n x p - ascend n (sole 0) (sole (⟨n+1,k⟩:S.Tag)))

-- prove straight first, using just the hierarchy symmetries and laws
variable {P R ρ} (H : R.Laws P ρ) (hs : S.Hierarchy) (hr : R.Oriented S)
  (ho : P.Orientation ρ) (hc : P.Inclusions S)

lemma asLinear {n k : ℕ} (h : ∃ q : MultilinearMap ℂ (fun i : Unit => S.Field ((sole k) i)) (S.Field n),
    ∀ v, q v = ascend D P R ρ n (sole 0) (stockTag (d:=sole k) v)) :
    ∃ r : S.Field k →ₗ[ℂ] S.Field n, ∀ v, r v = ascend D P R ρ n (sole 0) (sole ⟨k,v⟩) := by
  obtain ⟨q,hq⟩ := h
  refine ⟨q.toLinearMap 0 (),fun v => ?_⟩
  let f : Slots S (sole k) := fun _ => v
  have he : update (0 : Slots S (sole k)) () v = f := by
    funext i; cases i; simp only [f,update_self]
  change q _ = _
  rw [he]
  exact hq f

include H hs
lemma ascend_straight {x : I → E4} {k : ℕ} (hx : Visible D k x) (n : I → ℕ) :
    ∃ q : MultilinearMap ℂ (fun i => S.Field (n i)) (S.Field k),
      ∀ v, q v = ascend D P R ρ k x (stockTag (d:=n) v) := by
  induction k generalizing I with
  | zero => simpa only [ascend] using (proj_straight _ H hs (hx _ le_rfl) n)
  | succ k ih =>
    obtain ⟨a,ha⟩ := ih (fun i hi => hx i (hi.trans (Nat.le_succ k))) n
    obtain ⟨b,hb⟩ := asLinear D (ih (centered D k) (sole (k+1)))
    obtain ⟨c,hC⟩ := proj_straight _ H hs (hx _ le_rfl) n
    refine ⟨c + (P.rise (Nat.le_succ k)).compMultilinearMap (a - b.compMultilinearMap c),fun v => ?_⟩
    change c v + _ = _
    rw [ascend]
    dsimp only
    change c v + P.rise _ (a v - b (c v)) = _
    rw [hC,ha,hb]

lemma one_lin (n : ℕ) :
    ∃ r : S.Field (n+1) →ₗ[ℂ] S.Field n,
      ∀ v, r v = ascend D P R ρ n (sole 0) (sole ⟨n+1,v⟩) :=
  asLinear D (ascend_straight D H hs (centered D n) (sole (n+1)))

omit H hs in
lemma same_ascend (k : ℕ) (x : I → E4) (y : J → E4) (p : I → S.Tag) (q : J → S.Tag)
    (h : ∀ n≤k, projection R (D n) ρ x p = projection R (D n) ρ y q) :
    ascend D P R ρ k x p = ascend D P R ρ k y q := by
  induction k with
  | zero => simpa only [ascend] using h 0 le_rfl
  | succ k ih =>
    rw [ascend,ascend,h _ le_rfl, ih (fun n hn => h n (hn.trans (Nat.le_succ k)))]

omit H in
lemma ascend_filter {x : I → E4} {k : ℕ} (hc' : P.Inclusions S) (hx : Visible D k x) (p : I → S.Tag)
    {n m : ℕ} (he : n ≤ m) (v : S.Field n) (j : I) :
    ascend D P R ρ k x (update p j ⟨m,P.rise he v⟩) = ascend D P R ρ k x (update p j ⟨n,v⟩) :=
  same_ascend D _ _ _ _ _ (fun n hn => proj_filter _ hs hc' (hx n hn) p he v j)

include hr
lemma ascend_fix (k : ℕ) (v : S.Field k) : ascend D P R ρ k (sole 0) (sole ⟨k,v⟩) = v := by
  cases k <;> simp [ascend,proj_fix _ H hs hr]

include hc
/-- Actual chosen system of retractions; not an arbitrary chosen physical basis
with no known kernel formula. -/
def splitting (D : Sheets S) {P : DiffPlan S} {R : S.Rotation} {ρ : S.RealSpin}
    (H : R.Laws P ρ) (hs : S.Hierarchy) (hr : R.Oriented S) (hc : P.Inclusions S) : MultipleContact.Splitting P :=
  { down := fun n => (one_lin D H hs n).choose
    left := fun n v => by
      rw [(one_lin D H hs n).choose_spec]
      have hf [DecidableEq Unit] (p q : S.Tag) : update (sole p) () q = sole q := funext fun i => by cases i; simp [sole]
      have he := ascend_filter (ρ:=ρ) (R:=R) D hs hc (centered D n) (sole (⟨n,v⟩:S.Tag)) (Nat.le_succ n) v ()
      rw [@hf (Classical.decEq Unit),@hf (Classical.decEq Unit)] at he; exact he.trans (ascend_fix D H hs hr n v) }

lemma splitting_down (n : ℕ) (v : S.Field (n+1)) :
    (splitting D H hs hr hc).down n v = ascend D P R ρ n (sole 0) (sole ⟨n+1,v⟩) :=
  (one_lin D H hs n).choose_spec v

/-- Step coherence. Inputs not assumed in this lemma to be in Conf (the
algebraic identity even for totalized values). -/
lemma return_ascend (n : ℕ) (x : I → E4) (p : I → S.Tag) :
    (splitting D H hs hr hc).down n (ascend D P R ρ (n+1) x p) = ascend D P R ρ n x p := by
  rw [ascend]
  rw [map_add,(splitting D H hs hr hc).left,splitting_down]; abel

lemma weight_ascend {w k : ℕ} (hw : w ≤ k) (x : I → E4) (p : I → S.Tag) :
    (splitting D H hs hr hc).part w k (ascend D P R ρ k x p) =
      (splitting D H hs hr hc).part w w (ascend D P R ρ w x p) := by
  induction k, hw using Nat.le_induction with
  | base => rfl
  | succ k he ih =>
    rw [MultipleContact.Splitting.part,dif_neg (by omega : k+1≠w),LinearMap.comp_apply,
      return_ascend,ih]

omit hr hc in
lemma ascend_smooth {x : I → E4} {k : ℕ} (hx : Visible D k x) (p : I → S.Tag) :
    ContDiffAt ℝ ∞ (fun x => ascend D P R ρ k x p) x := by
  induction k with
  | zero => simpa only [ascend] using projection_smooth _ H hs.smooth p (hx _ le_rfl)
  | succ k ih =>
    obtain ⟨r,hr⟩ := one_lin D H hs k
    have hg := projection_smooth _ H hs.smooth p (hx _ le_rfl)
    let M := LinearMap.toContinuousLinearMap (r.restrictScalars ℝ)
    let T := LinearMap.toContinuousLinearMap ((P.rise (Nat.le_succ k)).restrictScalars ℝ)
    let u := fun y => projection R (D (k+1)) ρ y p
    conv => arg 3; ext y; rw [ascend]; dsimp only; rw [← hr]
    have he := (ih (fun j hj => hx j (hj.trans (Nat.le_succ k)))).sub
      (ContDiffAt.comp (g:=M) x M.contDiff.contDiffAt (show ContDiffAt ℝ ∞ u x from hg))
    exact hg.add (ContDiffAt.comp (g:=T) x T.contDiff.contDiffAt he)
omit hc in
lemma ascend_rotated {x : I → E4} {k : ℕ} (hx : Visible D k x) (p : I → S.Tag) (g : Ortho) :
    R.act k g (ascend D P R ρ k x p) = ascend D P R ρ k (Ortho.move g ∘ x) (R.label g ∘ p) := by
  induction k generalizing I with
  | zero => rw [ascend,ascend,proj_rotated _ H hs hr (hx _ le_rfl)]
  | succ k ih =>
    rw [ascend,ascend]
    let u := projection R (D (k+1)) ρ x p
    have hg := ih (centered D k) (sole (⟨k+1,u⟩:S.Tag))
    rw [show R.label g ∘ sole (⟨k+1,u⟩:S.Tag) = sole ⟨k+1,R.act (k+1) g u⟩ from rfl,
      show Ortho.move g ∘ sole (0:E4) = sole 0 from funext fun i => (Ortho.motion g).map_zero] at hg
    rw [map_add,H.filtered, map_sub,hg,ih (fun n hn => hx n (hn.trans (Nat.le_succ k))) p]
    unfold u
    rw [proj_rotated _ H hs hr (hx _ le_rfl)]
omit hr hc H hs in
lemma ascend_conjugate (ho : P.Orientation ρ) (k : ℕ) (x : I → E4) (p : I → S.Tag) :
    S.conj ρ k (ascend D P R ρ k x p) = ascend D P R ρ k x (conjugate ρ ∘ p) := by
  induction k generalizing I with
  | zero => rw [ascend, ascend, proj_conjugated]
  | succ k ih =>
    rw [ascend,ascend]
    rw [map_add, ho.realInc,map_sub, ih, ih,
      show conjugate ρ ∘ sole (⟨k+1,projection R (D (k+1)) ρ x p⟩:S.Tag) =
        sole ⟨k+1,S.conj ρ (k+1) (projection R _ ρ x p)⟩ from rfl, proj_conjugated]

include ho
lemma covariant : (splitting D H hs hr hc).Covariant R ρ := by
  constructor
  · intro n x
    rw [splitting_down,splitting_down,ascend_conjugate D ho]; rfl
  intro n K x
  rw [splitting_down,splitting_down,ascend_rotated D H hs hr (centered D n),
    show Ortho.move K ∘ sole (0:E4) = sole 0 from funext fun i => (Ortho.motion K).map_zero]
  rfl
end YM.OPE.Cov

import YM.OPE.Frame.Invariance
/-!
# Axes and scalar coordinates. Real O(4) tensor convention.

True homogeneous outputs in an invariant complement with real axes;
truncation uses these axes (in an inhomogeneous splitting the interpretation
of omission of rows would need adjustment).
-/
set_option autoImplicit false
noncomputable section

open Set Function
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
namespace YM.OPE.Frame
open Table
open MultipleContact (Detector Splitting)
variable {G : Gauge} {L : Register G} {S : Table L} {P : DiffPlan S} {X : Rotation S} {ρ : S.RealSpin} {d m : ℕ}
    (B : Splitting P) (A : ∀ d : ℕ, Detector S d) (Z : ∀ d : ℕ, S.Field d)

abbrev RowAt (d : ℕ) := Fin (Module.finrank ℂ (B.stratum d))
abbrev Row := (d : ℕ) × RowAt B d

def limits (d : ℕ) : Finset (Row B) := (Finset.range (d+1)).sigma fun _ => Finset.univ
lemma bracket (u : Row B) : u ∈ limits B d ↔ u.fst ≤ d := by simp [limits]

/-- Preserves the physical real form, unit horizon not excluded. Basis and tomography sampled once. -/
structure Grid (B : Splitting P) (ρ : S.RealSpin) where
  axes (d : ℕ) : Module.Basis (RowAt B d) ℂ (B.stratum d)
  real (d : ℕ) (i : RowAt B d) : S.conj ρ d (axes d i).val = (axes d i).val

def sheaf (d k : ℕ) : S.Field k →ₗ[ℂ] B.stratum d := (B.part d k).codRestrict (B.stratum d) B.top_mem

lemma thick_real (h : B.Covariant X ρ) (v : B.stratum d) : S.conj ρ d v.val ∈ B.stratum d := by
  cases d with
  | zero => trivial
  | succ d => change B.down d _ = 0; rw [← h.real, show B.down d v.val = 0 from v.property, map_zero]
lemma thick_spin (h : B.Covariant X ρ) (K : Ortho) (v : B.stratum d) : X.act d K v.val ∈ B.stratum d := by
  cases d with
  | zero => trivial
  | succ d => change B.down d _ = 0; rw [← h.act, show B.down d v.val = 0 from v.property, map_zero]
lemma spin_part (h : B.Covariant X ρ) (hX : X.Laws P ρ) (K : Ortho) (v : S.Field d) :
    X.act d K (B.part d d v) = B.part d d (X.act d K v) := by
  rw [B.top_part]; cases d with
  | zero => rfl
  | succ d => simp only [Splitting.top,LinearMap.sub_apply,LinearMap.id_apply,LinearMap.comp_apply,map_sub,hX.filtered,h.act]
lemma real_part (h : B.Covariant X ρ) (hp : P.Orientation ρ) (v : S.Field d) :
    S.conj ρ d (B.part d d v) = B.part d d (S.conj ρ d v) := by
  rw [B.top_part]; cases d with
  | zero => rfl
  | succ d => simp only [Splitting.top,LinearMap.sub_apply,LinearMap.id_apply,LinearMap.comp_apply,map_sub,hp.realInc,h.real]

/-- always possible to choose *real* axes (physical label conjugation), not a claim rotations fix
axis vectors. -/
lemma grid_exists (h : B.Covariant X ρ) : Nonempty (Grid B ρ) := by
  have hs (d : ℕ) : ∃ b : Module.Basis (RowAt B d) ℂ (B.stratum d), ∀ i, S.conj ρ d (b i).val = (b i).val := by
    let F : Set (B.stratum d) := {v | S.conj ρ d v.val = v.val}
    obtain ⟨f,hf,-,hs,hl⟩ := exists_linearIndepOn_id_extension (linearIndepOn_empty ℂ id) (empty_subset F)
    let U := Submodule.span ℂ f
    have hp (x : B.stratum d) : x ∈ U := by
      let y : B.stratum d := ⟨_, thick_real B h x⟩
      have he : x+y ∈ U := hs (show x+y ∈ F from by
        change S.conj ρ d (x.val + S.conj ρ d x.val) = _; rw [map_add,S.reflect_star, add_comm]; rfl)
      have hv : Complex.I • (x-y) ∈ U := hs (show Complex.I • (x-y) ∈ F from by
        change S.conj ρ d (Complex.I • (x.val - S.conj ρ d x.val)) = _
        rw [map_smulₛₗ, map_sub, S.reflect_star]; simp [y, smul_sub]; abel)
      have hb := U.smul_mem (1/2:ℂ) (U.add_mem he (U.smul_mem (-Complex.I) hv))
      rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul,show x+y+(x-y)=(2:ℂ) • x by rw [two_smul]; abel,
        smul_smul,div_mul_cancel₀ _ (by norm_num),one_smul] at hb; exact hb
    let b := Module.Basis.mk (show LinearIndependent ℂ (Subtype.val : f → _) from hl.linearIndependent_restrict)
      (show ⊤ ≤ Submodule.span ℂ (Set.range (Subtype.val : f → _)) by simpa only [Subtype.range_val] using (show ⊤ ≤ U from fun x _ => hp x))
    haveI : Finite f := Module.Finite.finite_basis b; letI := Fintype.ofFinite f
    let r := (Fintype.equivFin f).trans (finCongr (Module.finrank_eq_card_basis b).symm); let W := b.reindex r
    refine ⟨W,fun i => ?_⟩; exact hf (show W i ∈ f by rw [show W i = (r.symm i).val by simp [W,b]]; exact (r.symm i).property)
  choose b he using hs; exact ⟨b,he⟩
namespace Grid
variable {B} (R : Grid B ρ)

def field (r : Row B) : S.Field r.fst := (R.axes r.fst r.snd).val
def label (r : Row B) : S.Tag := ⟨r.fst,R.field r⟩
def coord (r : Row B) (m : ℕ) : S.Field m →ₗ[ℂ] ℂ := ((R.axes r.fst).coord r.snd).comp (sheaf B r.fst m)
/-- Axis as field at a given horizon (if occurs there). -/
def upper (r : Row B) (m : ℕ) : S.Field m := if h : r.fst ≤ m then P.rise h (R.field r) else 0
lemma lower_weight (r : Row B) (hr : r ∈ limits B m) : R.upper r m = P.rise ((bracket ..).mp hr) (R.field r) := dif_pos ((bracket ..).mp hr)
lemma all_real (r : Row B) : bar ρ (R.label r) = R.label r := congrArg (fun a=> (⟨r.fst,a⟩ : S.Tag)) (R.real ..)
lemma accounts (v : S.Field m) : ∑ a : RowAt B d, R.coord ⟨d,a⟩ m v • R.field ⟨d,a⟩ = B.part d m v := by
  let F (a : RowAt B d) := R.axes d a
  change ∑ a : RowAt B d, ((R.axes d).coord a (sheaf B d m v)) • (F a).val = _
  have hp : ∀ a : RowAt B d, (R.axes d).coord a (sheaf B d m v) • (F a).val=(B.stratum d).subtype ((R.axes d).repr (sheaf B d m v) a • F a) := fun a => rfl
  simp_rw [hp]; rw [← map_sum]; unfold F; rw [(R.axes d).sum_repr]; rfl
lemma coord_spin (h : B.Covariant X ρ) (hX : X.Laws P ρ) (K : Ortho) (v : S.Field d) (a : RowAt B d) :
    R.coord ⟨d,a⟩ d (X.act d K v) = ∑ b : RowAt B d,
      R.coord ⟨d,b⟩ d v * ((R.axes d).coord a ⟨_,thick_spin B h K (R.axes d b)⟩) := by
  let f (b : RowAt B d) : B.stratum d := ⟨_,thick_spin B h K (R.axes d b)⟩
  change (R.axes d).coord a (sheaf B d d (X.act d K v)) = _
  have hv : sheaf B d d (X.act d K v)=∑ b : RowAt B d, R.coord ⟨d,b⟩ d v • f b := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]; change B.part d d _ = _
    rw [← spin_part B h hX, ← R.accounts v (d:=d),map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_; rw [map_smul]; rfl
  rw [hv,map_sum]; simp only [map_smul]; rfl
lemma coord_bars (h : B.Covariant X ρ) (hp : P.Orientation ρ) (v : S.Field d) (i : RowAt B d) :
    R.coord ⟨d,i⟩ d (S.conj ρ d v) = star (R.coord ⟨d,i⟩ d v) := by
  let c (b : RowAt B d) := R.coord ⟨d,b⟩ d v
  change (R.axes d).coord i (sheaf B d d (S.conj ρ d v)) = star (c i)
  have hv : sheaf B d d (S.conj ρ d v) = ∑ b : RowAt B d, star (c b) • R.axes d b := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]; change B.part d d _ = _
    rw [← real_part B h hp, ← R.accounts v (d:=d),map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_; rw [map_smulₛₗ]; exact congrArg (fun a=> star (c b) • a) (R.real d b)
  rw [hv,map_sum]; simp [Module.Basis.coord_apply, Finsupp.single_apply, mul_ite]
lemma beyond_zero (i : Row B) (h : m < i.fst) : R.coord i m = 0 := by
  apply LinearMap.ext; intro a; rw [coord, LinearMap.comp_apply, show sheaf B i.fst m a = 0 from Subtype.ext (LinearMap.congr_fun (B.beyondZero h) a),map_zero,LinearMap.zero_apply]
lemma coord_lift (H : S.Hierarchy) (hr : P.Inclusions S) (i : Row B) (he : d ≤ m) (v : S.Field d) :
    R.coord i m (P.rise he v) = R.coord i d v := congrArg ((R.axes i.fst).coord i.snd) (show sheaf B i.fst m (P.rise he v)=sheaf B i.fst d v from
      Subtype.ext (B.part_rise H.laws.toSymmetric hr he v)) -- reducibility
lemma balance (H : S.Hierarchy) (hr : P.Inclusions S) (v : S.Field m) :
    ∑ i ∈ limits B m, R.coord i m v • R.upper i m = v := by
  rw [limits, Finset.sum_sigma]
  -- no `fin` hardcoded in definitions except the view
  trans ∑ k : Fin (m+1), P.rise (show k.val ≤ m from Nat.le_of_lt_succ k.isLt) (B.part k.val m v)
  swap; exact B.recombine H.laws.toSymmetric hr m v
  rw [← Fin.sum_univ_eq_sum_range]; apply Finset.sum_congr rfl; intro i _
  have h : i.val ≤ m := Nat.le_of_lt_succ i.isLt
  rw [← R.accounts v, map_sum]; refine Finset.sum_congr rfl fun a _ => ?_; rw [upper,dif_pos h,map_smul]
end Grid
end YM.OPE.Frame

import YM.OPE.Splitting.Detector
import YM.Work.A01.Mirror
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Quotient-field and product readings

Use `S.Field d`, the true quotient fields of the theory whose OPE we're
constructing, also when reading in each character state T.  A `S.Tag`
permits a mixed horizon input.  A basis vector in this file, if any, may
belong to lower filtration; only later (`Compatible.Tower` etc.) do we
select the real equivariant filtration splitting and the physical basis for
the OPE.

As in `YM.OPE.Splitting.Detector`, all applications of evaluation are on
Conf, the separated configurations; no meaning assigned to junk off Conf.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov
open Function Set Filter Table
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L} {T : Table L} {R : S.Rotation}
variable {I J : Type} [Fintype I] [Fintype J] {n : ℕ}

/-- Read on true fields at named positions. No test product deletion (e.g.
not connected parts). Use when `T` respects the same fields. -/
def kernel (T : Table L) (x : I → E4) (p : I → S.Tag) : ℂ :=
  S.useAt T (points (x ∘ runNames I)) (p ∘ runNames I)

lemma kernel_expose (T : Table L) (x : I → E4) (p : I → S.Tag) :
    kernel T x p = observe T x (Ward.expose ∘ p) := by
  unfold kernel observe worded
  rw [T.readAt]; rfl

lemma kernel_observe (hT : T.Symmetric) (ht : T.respects S) {x : I → E4}
    (hx : Injective x) (p : I → L.Token) : kernel T x (S.classTokens ∘ p) = observe T x p := by
  unfold kernel observe worded
  rw [T.readAt]
  exact S.at_project T hT ht (runs_conf.mpr hx) (p ∘ runNames I)

lemma kernel_order (H : T.Symmetric) (e : J ≃ I) {x : I → E4}
    (p : I → S.Tag) (hx : Injective x) : kernel T (x ∘ e) (p ∘ e) = kernel T x p := by
  rw [kernel_expose, kernel_expose]
  exact perm_observe T H e (Ward.expose ∘ p) hx

lemma kernel_filter (P : DiffPlan S) (hP : P.Inclusions T) (H : T.Symmetric)
    {x : I → E4} (hx : Injective x) (p : I → S.Tag) {d m : ℕ} (h : d ≤ m)
    (v : S.Field d) (j : I) :
    kernel T x (update p j ⟨m,P.rise h v⟩) = kernel T x (update p j ⟨d,v⟩) := by
  obtain ⟨j,rfl⟩ := (runNames I).surjective j
  unfold kernel
  have he (a : S.Tag) : update p (runNames I j) a ∘ runNames I = update (p ∘ runNames I) j a := by
    ext1 i
    by_cases hi : i=j
    · subst i; simp
    simp [hi]
  rw [he, he]
  exact P.inclusion_slot hP H h (runs_conf.mpr hx) j _ v

lemma kernel_shift (H : T.Homogeneous) {x : I → E4} (p : I → S.Tag) (hx : Injective x)
    (a : E4) : kernel T (fun i => x i + a) p = kernel T x p := by
  rw [kernel_expose, kernel_expose]
  exact observe_carry T H _ hx a

lemma kernel_move (H : R.Oriented T) {x : I → E4} (p : I → S.Tag) (hx : Injective x)
    (K : Ortho) : kernel T (Ortho.move K ∘ x) (R.label K ∘ p) = kernel T x p := by
  exact H (Fintype.card I) _ (points (x ∘ runNames I)) (runs_conf.mpr hx) K

abbrev conjugate (ρ : S.RealSpin) := YM.Work.A01.realTag ρ

lemma kernel_conj (H : T.Symmetric) (ρ : S.RealSpin) (ρ' : T.RealSpin) (hr : T.respects S)
    {x : I → E4} (p : I → S.Tag) (hx : Injective x) :
    kernel T x (conjugate ρ ∘ p) = star (kernel T x p) := by
  rw [kernel_expose T x p]
  -- use S.conj representative
  let v := Ward.expose ∘ p
  have he : conjugate ρ ∘ p = S.classTokens ∘ (L.conjugate ∘ v) := by
    ext1 i
    change conjugate ρ _ = S.classTokens _
    have hh (p : L.Token) : S.classTokens (L.conjugate p) = conjugate ρ (S.classTokens p) := rfl
    simp [hh,v,Function.comp]
  rw [he,kernel_observe H hr hx]
  unfold observe worded
  rw [T.readAt,T.readAt]
  exact ρ'.real (runs_conf.mpr hx) _

lemma conjugate_twice (ρ : S.RealSpin) (p : S.Tag) : conjugate ρ (conjugate ρ p) = p := by
  change ⟨p.1,S.conj ρ _ (S.conj _ _ p.2)⟩ = p
  rw [S.reflect_star ρ]

lemma conjugate_label_comm {P : DiffPlan S} {ρ : S.RealSpin} (H : R.Laws P ρ)
    (K : Ortho) (p : S.Tag) : conjugate ρ (R.label K p) = R.label K (conjugate ρ p) := by
  unfold conjugate YM.Work.A01.realTag Rotation.label; simp only [H.real]

/-- Reader for linearity in one field at its center with full spectators. -/
def insert (S T : Table L) (o : E4) (y : J → E4) (p : J → S.Tag) (d : ℕ) :
    S.Field d →ₗ[ℂ] ℂ := observeOne S T o y (Ward.expose ∘ p) d

lemma insert_apply (S : Table L) (H : T.Symmetric) (hr : T.respects S)
    (o : E4) (y : J → E4) (p : J → S.Tag) (d : ℕ) (v : S.Field d)
    (hx : Injective (beside (sole o) y)) :
    Cov.insert S T o y p d v = kernel T (beside (sole o) y) (beside (sole ⟨d,v⟩) p) := by
  rw [kernel_expose]
  -- arbitrary rep by Ward.expose
  unfold insert
  let u : L.Ref d := S.representative d v
  rw [beside_commutes]
  have hf := projectedOne T (Ward.expose ∘ p) d u H hr hx
  rw [show S.project d u = v from S.rep d v] at hf
  exact hf

/-- Exterior at fixed horizon as an actual test in relative coordinates. -/
lemma kernel_center (H : S.Hierarchy) (p : Exterior L) (v : S.Field n) :
    kernel S (beside (sole (0:E4)) (bearing p))
      (beside (sole ⟨n,v⟩) (S.classTokens ∘ p.letter)) = S.spectra n v p := by
  obtain ⟨v,rfl⟩ := S.onto n v
  rw [← Prescription.one_test n p v H]
  unfold Prescription.reading
  dsimp only
  simp only [sub_zero, if_pos (bearing_clear p)]
  have he := kernel_observe H.laws.toSymmetric (show S.respects S from fun _ => le_rfl)
    (bearing_clear p) (beside (sole ⟨n,v⟩) p.letter)
  rw [beside_commutes] at he
  exact he

lemma kernel_unit (S : Table L) {T : Table L} (H : T.Basic) (hr : T.respects S) (p : I → S.Tag)
    (x : I → E4) (z : E4) (d : ℕ) (hx : Injective (beside (sole z) x)) :
    kernel T (beside (sole z) x) (beside (sole (⟨d,S.unit d⟩:S.Tag)) p) = kernel T x p := by
  let v := Ward.expose ∘ p
  have he := kernel_observe H.toSymmetric hr hx (beside (sole (L.one d)) v)
  have heu : S.classTokens ∘ v = p := funext fun i => Ward.sends_back _
  rw [beside_commutes, heu] at he
  rw [show sole (⟨d,S.unit d⟩:S.Tag) = S.classTokens ∘ sole (L.one d) from rfl, he,kernel_expose T x]
  -- use ordered laws directly
  rw [head_observe (e:=runNames I) T v _ H.toSymmetric hx,
      H.unital ((consIn z x (e:=runNames I)).2 hx)]
  unfold observe worded
  rw [T.readAt]; congr 1

section Multilinear
abbrev Slots (S : Table L) (d : I → ℕ) := ∀ i, S.Field (d i)
def stockTag {d : I → ℕ} (v : Slots S d) (i : I) : S.Tag := ⟨d i,v i⟩
/-- Keep all the arity and naming but allow field labels to vary in their
finite stages. Includes the zero-input constant multilinear convention. -/
def press (S T : Table L) (d : I → ℕ) (x : I → E4) : MultilinearMap ℂ (fun i => S.Field (d i)) ℂ :=
  (MultilinearMap.domDomCongrLinearEquiv' ℂ ℂ (fun i => S.Field (d i)) ℂ
    (runNames I).symm).symm (S.classMoment T (d ∘ runNames I) (points (x ∘ runNames I)))

lemma press_apply (S T : Table L) (d : I → ℕ) (x : I → E4) (v : Slots S d) :
    press S T d x v = kernel T x (stockTag v) := by
  rfl

/-- One exterior block multilinearity, for varying its labels but keeping
same physical inputs. -/
def withExterior (T : Table L) (x : I → E4) (p : I → S.Tag) (d : J → ℕ) (y : J → E4) :
    MultilinearMap ℂ (fun j => S.Field (d j)) ℂ :=
  (press S T (beside (Sigma.fst ∘ p) d) (beside x y)).currySum (fun i => (p i).2)

lemma exterior_apply (T : Table L) (x : I → E4) (p : I → S.Tag) (d : J → ℕ) (y : J → E4)
    (v : Slots S d) :
    withExterior T x p d y v = kernel T (beside x y) (beside p (stockTag v)) := by
  let M := beside (Sigma.fst ∘ p) d
  let w : Slots S M := Sum.rec (motive:=fun i => S.Field (M i)) (fun i => (p i).2) v
  change press S T M (beside x y) w = _
  rw [press_apply]
  congr 1; ext1 i; cases i <;> rfl

lemma smooth_fixed (H : T.Smooth) {x : I → E4} (hx : Injective x) (v : I → S.Tag) :
    ContDiffAt ℝ ∞ (fun x => kernel T x v) x := by
  let f : (I → E4) →L[ℝ] Points (Fintype.card I) :=
    { toFun := fun x => points (x ∘ runNames I)
      map_add' := fun _ _ => by ext; rfl
      map_smul' := fun _ _ => by ext; rfl
      cont := by unfold points; fun_prop }
  have hh : f x ∈ conf _ := runs_conf.mpr hx
  unfold kernel
  exact ((S.class_smooth T H _ _ hh).contDiffAt ((conf_open _).mem_nhds hh)).comp
    (f:=f) x f.contDiff.contDiffAt

/-- Uniformization used on detector orbits: no extra smoothness in motion
of the group assumed, just full field linearity and position kernel
smoothness. -/
lemma decompose (S : Table L) (d : I → ℕ) (M : MultilinearMap ℂ (fun i => S.Field (d i)) ℂ)
    (y : Slots S d) :
    let b := fun i => Module.finBasis ℂ (S.Field (d i))
    M y = ∑ u : ∀ i, Fin (Module.finrank ℂ (S.Field (d i))),
            (∏ i, (b i).coord (u i) (y i)) * M (fun i => b i (u i)) := by
  intro b
  have he (i) : (∑ j, (b i).coord j (y i) • b i j) = y i := (b i).sum_repr _
  conv_lhs => rw [show y = fun i => ∑ j, (b i).coord j (y i) • b i j from funext fun i => (he i).symm]
  rw [MultilinearMap.map_sum]; simp_rw [MultilinearMap.map_smul_univ]; rfl

lemma smooth_joint (S : Table L) (H : T.Smooth) (d : I → ℕ) (x : I → E4) (hx : Injective x)
    (v : Slots S d) :
    ContDiffAt ℝ ∞ (fun z : (I → E4) × Slots S d => kernel T z.1 (stockTag z.2)) (x,v) := by
  conv => arg 3; ext z; rw [← press_apply, decompose]
  apply ContDiffAt.sum (f:=fun _ _ => _)
  intro u _; apply ContDiffAt.mul
  · apply contDiffAt_prod; intro i _
    let a := ((Module.finBasis ℂ (S.Field (d i))).coord (u i)).restrictScalars ℝ
    exact ((LinearMap.toContinuousLinearMap a).contDiff.comp (f:=fun z : (I → E4) × Slots S d => z.2 i)
      (contDiff_pi.mp (show ContDiff ℝ ∞ (Prod.snd : (I → E4) × Slots S d → Slots S d) from contDiff_snd) i)).contDiffAt
  simp_rw [press_apply]
  exact (smooth_fixed H hx (stockTag (d:=d) (fun i => Module.finBasis ℂ (S.Field (d i)) (u i)))).comp (f:=Prod.fst) (x,v) contDiffAt_fst -- may need press_apply

end Multilinear
end YM.OPE.Cov

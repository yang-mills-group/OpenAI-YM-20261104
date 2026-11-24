import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeEdgeRows
import YM.Integration.WilsonCenteredNestedOrbitWallet
import YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeWholeWord

/-! The logarithmic matrix of the same elected reader pays the original
whole coefficient and its signed full-tree defect on a common rotation
and reality branch. Only terminal modes of the desired grade enter the price. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeEdgeTickets
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Nesting OPE.Nesting.Atom OPE.Log OPE.Arboreal OPE.Arboreal.Mountain
open WilsonCenteredNestedProjectedShadow WilsonCenteredNestedTerminalOrbit
open WilsonSharpPhysicalTreeEdgeRows
open WilsonCenteredNestedShadowBasis (Slot axis coeff mass)
open WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeWholeWord (word filled)
open scoped Classical Topology BigOperators ComplexConjugate

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  {I : Type} [Fintype I] (tree : Arboreal I) (d : I → ℕ)

def projected (v : Labels S d) (D : I → ℕ) (m : ℕ) (c : Q.channels m) (x : I → E4)
    (K : Ortho) (b : Bool) : ℂ :=
  ∑ w ∈ bands F.sector.derivatives m,
    scalar b (factorization Q.port tree tree.zones (Ortho.move K⁻¹ ∘ x)
      (names (fun i => into F (d i) K b (v i))) w D) *
    read F Q m m c (out F m K b (Q.port.loaded w m))

def direct (v : Labels S d) (m : ℕ) (c : Q.channels m) (x : I → E4)
    (K : Ortho) (b : Bool) : ℂ :=
  raw F Q m m c (crop x tree.leaves) (fun i => (tags v) i.val) (x tree.root) K b

theorem direct_eq (v : Labels S d) (m : ℕ) (c : Q.channels m) (x : I → E4)
    (K : Ortho) (b : Bool) :
    direct F Q tree d v m c x K b = ∑ w ∈ bands F.sector.derivatives m,
      scalar b (coalesce Q.port tree.leaves (Ortho.move K⁻¹ ∘ x)
        (names (fun i => into F (d i) K b (v i))) tree.root w) *
      read F Q m m c (out F m K b (Q.port.loaded w m)) := by
  unfold direct WilsonSharpPhysicalTreeEdgeRows.raw
  rw [currency F]
  unfold shadowOld shadow
  rw [add_smul F,map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [map_smul]
  rfl

private theorem weighted {B : Type} (s : Finset B) (w g : B → ℂ) {A P : ℝ}
    (mass : ∑ i ∈ s, ‖w i‖ ≤ A) (each : ∀ i, ‖g i‖ ≤ P) (pos : 0 ≤ P) :
    ‖∑ i ∈ s, w i * g i‖ ≤ A * P := by
  calc
    _ ≤ ∑ i ∈ s, ‖w i * g i‖ := norm_sum_le ..
    _ ≤ ∑ i ∈ s, ‖w i‖ * P := Finset.sum_le_sum fun i _ =>
      (norm_mul ..).trans_le (mul_le_mul_of_nonneg_left (each i) (norm_nonneg _))
    _ = (∑ i ∈ s, ‖w i‖) * P := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right mass pos

/-- A rotation-uniform, simultaneous ticket for the two original signed
raw expressions. The basis arrays and their thresholds are finite. -/
theorem rotated (log : LogTrace F Q.port) (v : Labels S d) (D : I → ℕ)
    (w : Mode F.sector.derivatives) {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃ B, 0 ≤ B ∧ ∃ p : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ x s, s tree.root = r →
      tree.Convoy M η s x → ∀ j, p ≤ j → ∀ K : Ortho,
      let y := Ortho.move K⁻¹ ∘ x
      let labels := names (roll F.sector.turns K⁻¹ v)
      let P := tree.listPrice (names v) s w.1 j
      ‖coalesce Q.port tree.leaves y labels tree.root w‖ ≤ B * P ∧
      ‖coalesce Q.port tree.leaves y labels tree.root w -
        factorization Q.port tree tree.zones y labels w D‖ ≤ B * (P * tree.grace s D) := by
  let deg := fun i : tree.leaves => d i.val
  let leaves : Labels S deg := fun i => v i.val
  let subject (i : Slot S deg) := filled tree d v (axis S deg i)
  have on_leaves (i : Slot S deg) : (fun a : tree.leaves => subject i a.val) = axis S deg i := by
    funext a
    simp [subject,filled,a.property]
  choose start pay using fun i : Slot S deg =>
    log.tickets tree (names (subject i)) w D M η Mn ηp
  obtain ⟨h,orig⟩ := log.tickets tree (names v) w D M η Mn ηp
  obtain ⟨B,Bn,angular⟩ := WilsonCenteredNestedRotation.inputs F Q leaves
  refine ⟨B,Bn,h+∑i,start i,?_⟩
  filter_upwards [orig,eventually_all.mpr pay] with r live admitted x s home near j later K y labels P
  have motion (u q : E4) : ‖Ortho.move K⁻¹ u - Ortho.move K⁻¹ q‖ = ‖u-q‖ := by
    change ‖(Ortho.motion K⁻¹) u - (Ortho.motion K⁻¹) q‖ = _
    rw [← map_sub,LinearIsometryEquiv.norm_map]
  have moved : tree.Convoy M η s y :=
    ⟨near.sizes, fun i => by simpa only [y,Function.comp_apply,motion] using near.travel i,
      fun i a b fork => by simpa only [y,Function.comp_apply,motion] using near.spread i a b fork⟩
  have old := live y s home moved j (by omega)
  have seen (i : Slot S deg) := admitted i y s home moved j
    (by have hi : start i ≤ ∑ q,start q := Finset.single_le_sum (f := start)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        omega)
  let entrants := roll F.sector.turns K⁻¹ leaves
  have buy (A : MultilinearMap ℂ (fun i : tree.leaves => S.Field (deg i)) ℂ) (Z : ℝ)
      (each : ∀ i, ‖A (axis S deg i)‖ ≤ Z) (Zn : 0 ≤ Z) : ‖A entrants‖ ≤ B * Z := by
    rw [WilsonCenteredNestedShadowBasis.expand A entrants]
    apply weighted _ (coeff entrants) (fun i => A (axis S deg i)) _ each Zn
    apply le_trans _ (angular K⁻¹)
    unfold mass
    exact le_of_eq (Finset.sum_congr (by ext i; simp) (fun _ _ => rfl))
  let directRow := checkRow (d := deg) Q.port w (crop y tree.leaves) (y tree.root)
  let signedRow := word Q.port tree d Q.continuum y v w D
  have root_value (u : Labels S d) :
      directRow (fun i : tree.leaves => u i.val) = coalesce Q.port tree.leaves y (names u) tree.root w :=
    (WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeRawFaces.root Q.port tree d Q.continuum y u w).symm
  have signed_value (u : Labels S d) :
      signedRow (fun i : tree.leaves => u i.val) =
        coalesce Q.port tree.leaves y (names u) tree.root w - factorization Q.port tree tree.zones y (names u) w D :=
    WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeWholeWord.original Q.port tree d Q.continuum y v w D u
  constructor
  · change ‖coalesce Q.port tree.leaves y (names (roll F.sector.turns K⁻¹ v)) tree.root w‖ ≤ _
    rw [← root_value (roll F.sector.turns K⁻¹ v)]
    exact buy directRow P (fun i => by rw [← on_leaves i,root_value (subject i)]; exact (seen i).direct)
      ((norm_nonneg _).trans old.direct)
  · change ‖coalesce Q.port tree.leaves y (names (roll F.sector.turns K⁻¹ v)) tree.root w -
      factorization Q.port tree tree.zones y (names (roll F.sector.turns K⁻¹ v)) w D‖ ≤ _
    rw [← signed_value (roll F.sector.turns K⁻¹ v)]
    exact buy signedRow (P*tree.grace s D)
      (fun i => by rw [← on_leaves i,signed_value (subject i)]; exact (seen i).combination)
      ((norm_nonneg _).trans old.combination)

private lemma scalar_sub (b : Bool) (x y : ℂ) : scalar b (x-y) = scalar b x - scalar b y := by
  cases b <;> simp [scalar]

theorem original (fac : Facilities C f S) {l : Filter (ℕ × ℕ)} [l.NeBot] (lo : l ≤ f.fuse)
    (ticket : MatrixTicket (C := C) S F.sector.derivatives l) (v : Labels S d)
    (D : I → ℕ) (m : ℕ) (c : Q.channels m) {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃ A, 0 ≤ A ∧ ∃ p : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ x s, s tree.root = r →
      tree.Convoy M η s x → ∀ j, p ≤ j → ∀ K b,
      ‖direct F Q tree d v m c x K b‖ ≤ A * tree.listPrice (names v) s m j ∧
      ‖direct F Q tree d v m c x K b - projected F Q tree d v D m c x K b‖ ≤
        A * (tree.listPrice (names v) s m j * tree.grace s D) := by
  let log := tickets_suffice F fac lo ticket Q.spans
  let E := (bands F.sector.derivatives m).filter (fun w => w.1=m)
  let label (b : Bool) : Labels S d := if b then bar F.room.kernel.spin v else v
  choose B Bn start bought using fun i : E × Bool =>
    rotated F Q tree d log (label i.2) D i.1.val Mn ηp
  obtain ⟨L,Ln,output⟩ := WilsonCenteredNestedOrbitWallet.output F Q m c
  let limit := ∑ i : E × Bool, start i
  let cost (i : E × Bool) := B i * (L * ‖Q.port.loaded i.1.val m‖)
  let A := ∑ i : E × Bool, cost i
  have costn (i) : 0 ≤ cost i := mul_nonneg (Bn i) (mul_nonneg Ln (norm_nonneg _))
  refine ⟨A, Finset.sum_nonneg (fun i _ => costn i),limit,?_⟩
  filter_upwards [eventually_all.mpr bought,
    mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with r all small x s home near j later K b
  let P := tree.listPrice (names v) s m j
  let V := P * tree.grace s D
  let y := Ortho.move K⁻¹ ∘ x
  let labels := names (fun i => into F (d i) K b (v i))
  let X w := coalesce Q.port tree.leaves y labels tree.root w
  let Y w := factorization Q.port tree tree.zones y labels w D
  let fee w := read F Q m m c (out F m K b (Q.port.loaded w m))
  have paid (w : E) : ‖X w.val‖ ≤ B (w,b) * P ∧ ‖X w.val-Y w.val‖ ≤ B (w,b) * V := by
    have late : start (w,b) ≤ j := (Finset.single_le_sum (f := start)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (w,b))).trans later
    have h := all (w,b) x s home near j late K
    have degree := (Finset.mem_filter.mp w.property).2
    have labels_eq : names (roll F.sector.turns K⁻¹ (label b)) = labels := by
      cases b <;> rfl
    dsimp only at h
    rw [labels_eq,degree] at h
    exact h
  have sum_paid (X' : Mode F.sector.derivatives → ℂ) (Z : ℝ)
      (each : ∀ w : E, ‖X' w.val‖ ≤ B (w,b) * Z) (Zn : 0 ≤ Z) :
      ‖∑ w ∈ bands F.sector.derivatives m, scalar b (X' w) * fee w‖ ≤ A * Z := by
    rw [terminal F Q m c K b (fun w => scalar b (X' w))]
    change ‖∑ w ∈ E, scalar b (X' w) * fee w‖ ≤ _
    rw [← Finset.sum_coe_sort]
    have term (w : E) : ‖scalar b (X' w.val) * fee w.val‖ ≤ cost (w,b) * Z := by
      rw [norm_mul,WilsonCenteredNestedOrbitWallet.scalar_norm]
      exact (mul_le_mul (each w) (output K b _) (norm_nonneg _)
        ((norm_nonneg _).trans (each w))).trans_eq (by unfold cost; ring)
    have enough : (∑ w : E, cost (w,b)) ≤ A := by
      unfold A
      rw [Fintype.sum_prod_type]
      exact Finset.sum_le_sum (fun w _ => Finset.single_le_sum (f := fun q => cost (w,q))
        (fun q _ => costn (w,q)) (Finset.mem_univ b))
    exact (norm_sum_le ..).trans ((Finset.sum_le_sum (fun w _ => term w)).trans
      ((Finset.sum_mul ..).symm.trans_le (mul_le_mul_of_nonneg_right enough Zn)))
  have pn : 0 ≤ P := by
    unfold P Arboreal.listPrice Arboreal.prestige
    exact mul_nonneg (Graduated.worth m (names v) near.sizes tree.initial).le
      (pow_nonneg (Finset.prod_nonneg fun i hi => add_nonneg zero_le_one
        (neg_nonneg.mpr (Real.log_nonpos (near.sizes.allowed i hi).le
          (((near.sizes.bound (tree.closure i) hi).trans_eq home).trans small)))) _)
  have vn : 0 ≤ V := mul_nonneg pn (Finset.sum_nonneg fun w hw =>
    pow_nonneg (near.sizes.qFine (Finset.mem_erase.mp hw).2).le _)
  constructor
  · rw [direct_eq]
    exact sum_paid X P (fun w => (paid w).1) pn
  · rw [direct_eq]
    unfold projected
    rw [← Finset.sum_sub_distrib]
    change ‖∑ w ∈ bands F.sector.derivatives m, (scalar b (X w)*fee w - scalar b (Y w)*fee w)‖ ≤ _
    simp_rw [← sub_mul, ← scalar_sub]
    exact sum_paid (fun w => X w-Y w) V (fun w => (paid w).2) vn

end YM.Integration.WilsonSharpPhysicalTreeEdgeTickets

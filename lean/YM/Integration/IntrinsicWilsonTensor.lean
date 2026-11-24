import YM.Integration.SharedIntrinsicWilsonGrid

/-! A single physical regulator subfilter and an intrinsic multilinear
continuum counterterm for all independent inputs on the chosen grid. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.IntrinsicWilsonTensor
open Function Filter MeasureTheory Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards
open Frontier6.Road Trace.Pilot Trace.Physical.GermGraph RG16.Literal MultilinearCellCapture
open FilteredIntrinsicGramReadout FilteredWilsonProduct IntrinsicProductCompactness SharedIntrinsicWilsonGrid
open ContinuumIntrinsicWilsonProduct
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

abbrev Input (C : Family G) (m : ℕ) := (Climb.Bel C.book).Field m
abbrev Columns (C : Family G) (d : I → ℕ) := Next.UVStress.Code (fun i => Input C (d i))
abbrev Tensor (C : Family G) (d : I → ℕ) (D : ℕ) := MultilinearMap ℂ (fun i => Input C (d i)) (C.label D)

private def vector (k : Option (Columns C d)) (i : I) : Input C (d i) :=
  match k with | none => 0 | some q => Module.finBasis ℂ (Input C (d i)) (q i)

private def coefficient (v : (i : I) → Input C (d i)) (k : Option (Columns C d)) : ℂ :=
  match k with | none => 0 | some q => ∏ i, (Module.finBasis ℂ (Input C (d i))).repr (v i) (q i)

private theorem expand {Y : Type*} [AddCommMonoid Y] [Module ℂ Y]
    (M : MultilinearMap ℂ (fun i => Input C (d i)) Y) (v : (i : I) → Input C (d i)) :
    M v = ∑ k : Option (Columns C d), coefficient v k • M (vector k) := by
  let b (i : I) := Module.finBasis ℂ (Input C (d i))
  rw [Fintype.sum_option]
  simp only [coefficient,zero_smul,zero_add]
  have full : v = fun i => ∑ q, (b i).repr (v i) q • b i q := funext fun i => ((b i).sum_repr _).symm
  conv_lhs => rw [full]
  rw [M.map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact M.map_smul_univ _ _

private def slot (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (t : ℝ) (j : ℕ) (x : I → Cover) (w : ℕ × ℕ) (i : I) :
    Input C (d i) →ₗ[ℂ] (Config G (C.side w.1 w.2) → ℂ) :=
  ∑ k : Fin (d i+1), ((C.linearO w.1 w.2 k.val (location C.S j w.1 w.2 (x i))).mk' _).comp
    ((S.representative k.val).comp ((R.cutTest k.val (d i)).comp (J t (d i)).toLinearMap))

private def fieldTensor (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (t : ℝ) (j : ℕ) (x : I → Cover) (w : ℕ × ℕ) :
    MultilinearMap ℂ (fun i => Input C (d i)) (Config G (C.side w.1 w.2) → ℂ) :=
  (MultilinearMap.mkPiAlgebra ℂ I (Config G (C.side w.1 w.2) → ℂ)).compLinearMap (slot F R J t j x w)

private theorem tensor_field (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (t : ℝ) (j : ℕ) (x : I → Cover) (w : ℕ × ℕ) (v : (i : I) → Input C (d i)) :
    fieldTensor F R J t j x w v = field F R J v t j x w := by
  simp only [fieldTensor,slot,MultilinearMap.compLinearMap_apply,MultilinearMap.mkPiAlgebra_apply,
    LinearMap.sum_apply,LinearMap.comp_apply]
  rfl

private theorem field_cont (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → Input C (d i)) (t : ℝ) (j : ℕ) (x : I → Cover) (w : ℕ × ℕ) :
    Continuous (field F R J v t j x w) := by
  have eq : field F R J v t j x w = fun U => ∏ i, ∑ k : Fin (d i+1), C.O w.1 w.2
      (S.representative _ (R.cutTest k.val (d i) (J t (d i) (v i)))) (location C.S j w.1 w.2 (x i)) U := by
    funext U
    simp only [field,Finset.sum_apply,Finset.prod_apply]
  rw [eq]
  exact continuous_finsetProd _ fun i _ => continuous_finsetSum _ fun k _ => C.continuousO ..

private def reconstruct (Z : Option (Columns C d) → C.label D) : Tensor C d D :=
  ∑ q : Columns C d, ((MultilinearMap.mkPiAlgebra ℂ I ℂ).compLinearMap
    (fun i => (Module.finBasis ℂ (Input C (d i))).coord (q i))).smulRight (Z (some q))

private theorem reconstruct_apply (Z : Option (Columns C d) → C.label D) (v : (i : I) → Input C (d i)) :
    reconstruct Z v = ∑ k : Option (Columns C d), coefficient v k • Z k := by
  rw [Fintype.sum_option]
  simp only [reconstruct,coefficient,zero_smul,zero_add,_root_.sum_apply,MultilinearMap.smulRight_apply,
    MultilinearMap.compLinearMap_apply,MultilinearMap.mkPiAlgebra_apply,Module.Basis.coord_apply]

/-- A physical tensor comes from the actual finite intrinsic family on a
single regulator subfilter shared by all independent input vectors. -/
def Common (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (t : ℝ) (b j : ℕ) (x : I → Cover) (Z : Tensor C d D) : Prop :=
  ∃ l : Filter (ℕ × ℕ), l.NeBot ∧ l ≤ f.fuse ∧
    ∀ v : (i : I) → Input C (d i), Tendsto
      (fun w => value (D:=D) F.room.cutoff b w (field F R J v t j x w)) l (𝓝 (Z v))

theorem Common.cluster {F : Spec.Final C f S} {R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J : ℝ → PhysMS.tower S} {t : ℝ} {b j : ℕ} {x : I → Cover} {Z : Tensor C d D} (h : Common F R J t b j x Z)
    (v : (i : I) → Input C (d i)) : Cluster F R J v t b j x (Z v) := by
  obtain ⟨l,hl,sub,hz⟩ := h
  exact ⟨l,hl,sub,hz v⟩

/-- Extract one multilinear reference-label tensor from the original
Wilson counterterms before choosing any exterior detector. -/
theorem common (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i, d i))
    (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J) :
    ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (P.b t) (P.middle t) (P.j t) x →
      ∃ Z : Tensor C d D, Common F R J t (P.b t) (P.j t) x Z := by
  let U := Classical.choice (has_detectors F.room.kernel D)
  let K := Option (Columns C d)
  have stocks := eventually_all.mpr fun k : K => bounded F facility anchor R J (vector k)
    P.coarse P.mid P.fine P.pos P.before (P.low.trans P.high) D
  choose fee rate order paid using fun k : K => graded F facility anchor R P U J H (vector k)
  filter_upwards [stocks,eventually_all.mpr paid] with t stocks served
  intro x hx
  choose A normed using fun k : K => stocks k x hx
  let X (w : ℕ × ℕ) (k : K) := value (D:=D) F.room.cutoff (P.b t) w (field F R J (vector k) t (P.j t) x w)
  have boundedFamily : ∀ᶠ w in f.fuse, ‖X w‖ ≤ ∑ k : K, |A k| := by
    filter_upwards [eventually_all.mpr normed] with w h
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun k _ => abs_nonneg (A k)))).2
    intro k
    exact ((h k).trans (le_abs_self _)).trans (Finset.single_le_sum (fun i _ => abs_nonneg (A i)) (Finset.mem_univ k))
  obtain ⟨l,sub,live,Z,hZ⟩ := Next.UVStress.finite_extract X _ boundedFamily
  refine ⟨reconstruct Z,l,live,sub,?_⟩
  intro v
  rw [reconstruct_apply]
  have h := tendsto_finsetSum Finset.univ (fun k _ => (tendsto_pi_nhds.mp hZ k).const_smul (coefficient v k))
  apply h.congr'
  filter_upwards [(eventually_all.mpr (fun k : K => served k x hx)).filter_mono sub] with w ready
  obtain ⟨ho,live,_,_,_,_⟩ := ready none
  let V (k : K) := field F R J (vector k) t (P.j t) x w
  have book (k : K) : Booked C w.1 w.2 D (V k) (P.b t) live := by
    obtain ⟨_,_,good,_,_,_⟩ := ready k
    exact good
  have closed := IntrinsicProductLinearity.booked_sum C w.1 w.2 D (P.b t) F.room.cutoff ho live
    (coefficient v) V (fun k => field_cont ..) book
  have eq : field F R J v t (P.j t) x w = ∑ k : K, coefficient v k • V k := by
    simpa only [tensor_field] using expand (fieldTensor F R J t (P.j t) x w) v
  change _ = value (D:=D) F.room.cutoff (P.b t) w (field F R J v t (P.j t) x w)
  simp_rw [show ∀ k, X w k = label F.room.cutoff ho live (V k) from fun _ => value_eq ..]
  rw [value_eq F.room.cutoff ho live,eq]
  unfold label
  rw [closed.2,map_sum]
  exact Finset.sum_congr rfl fun k _ => (map_smul (C.factory D w.1 w.2).terminal (coefficient v k) _).symm

end YM.Integration.IntrinsicWilsonTensor

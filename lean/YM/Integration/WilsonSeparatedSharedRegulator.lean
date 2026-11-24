import YM.Integration.IntrinsicWilsonTensor

/-! Fix one ultrafilter refining the original physical regulator *before*
any times, sites, or input vectors. Original intrinsic compactness supplies
boundedness in a real closed ball at each plotted site. The actual
finite label is multilinear eventually, by the booked complete product.
The independent site choices of an arbitrary family of cluster points
need not have this simultaneous property. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedSharedRegulator
open Function Filter MeasureTheory Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards
open Frontier6.Road Trace.Pilot Trace.Physical.GermGraph RG16.Literal MultilinearCellCapture
open FilteredIntrinsicGramReadout FilteredWilsonProduct IntrinsicProductCompactness SharedIntrinsicWilsonGrid
open ContinuumIntrinsicWilsonProduct IntrinsicWilsonTensor
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

/- Finite basis evaluation of the complete field, as in original
`IntrinsicWilsonTensor`; a new simultaneous extraction requires making
the same regulator, including its limit, explicit in the buyer. -/
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

/-- Actual whole cutoff convergence along a specified common regulator. -/
def Along (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (t : ℝ) (b j : ℕ) (x : I → Cover)
    (U : Ultrafilter (ℕ × ℕ)) (Z : Tensor C d D) : Prop :=
  ∀ v : (i : I) → Input C (d i), Tendsto
    (fun w => value (D:=D) F.room.cutoff b w (field F R J v t j x w)) U.toFilter (𝓝 (Z v))

theorem Along.common {F : Spec.Final C f S} {R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J : ℝ → PhysMS.tower S} {t : ℝ} {b j : ℕ} {x : I → Cover}
    {U : Ultrafilter (ℕ × ℕ)} {Z : Tensor C d D} (h : Along F R J t b j x U Z)
    (sub : U.toFilter ≤ f.fuse) : Common F R J t b j x Z :=
  ⟨U.toFilter,inferInstance,sub,h⟩

/-- Any one fixed refining ultrafilter simultaneously selects the
complete physical tensor on every legitimate spatial roster, for all
independent tests and every sufficiently small reporting length. -/
theorem refinements (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i, d i))
    (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J) :
    ∀ᶠ t in trail, ∀ U : Ultrafilter (ℕ × ℕ), U.toFilter ≤ f.fuse → ∃ Z : (I → Cover) → Tensor C d D, ∀ x : I → Cover,
      Plot C (P.b t) (P.middle t) (P.j t) x → Along F R J t (P.b t) (P.j t) x U (Z x) := by
  let E := Classical.choice (has_detectors F.room.kernel D)
  let K := Option (Columns C d)
  have stocks := eventually_all.mpr fun k : K => bounded F facility anchor R J (vector k)
    P.coarse P.mid P.fine P.pos P.before (P.low.trans P.high) D
  choose fee rate order paid using fun k : K => graded F facility anchor R P E J H (vector k)
  filter_upwards [stocks,eventually_all.mpr paid] with t stocks served U sub
  have get (x : I → Cover) (hx : Plot C (P.b t) (P.middle t) (P.j t) x) :
      ∃ Z : Tensor C d D, Along F R J t (P.b t) (P.j t) x U Z := by
    choose A normed using fun k : K => stocks k x hx
    let X (w : ℕ × ℕ) (k : K) := value (D:=D) F.room.cutoff (P.b t) w (field F R J (vector k) t (P.j t) x w)
    have boundedFamily : ∀ᶠ w in f.fuse, ‖X w‖ ≤ ∑ k : K, |A k| := by
      filter_upwards [eventually_all.mpr normed] with w h
      apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun k _ => abs_nonneg (A k)))).2
      intro k
      exact ((h k).trans (le_abs_self _)).trans (Finset.single_le_sum (fun i _ => abs_nonneg (A i)) (Finset.mem_univ k))
    obtain ⟨Z,_,hZ⟩ := (isCompact_closedBall (0 : K→C.label D) (∑ k : K, |A k|)).ultrafilter_le_nhds' (U.map X)
      (by rw [Ultrafilter.mem_map]; exact (boundedFamily.mono (fun w hw=>Metric.mem_closedBall.mpr
        (by simpa using hw))).filter_mono sub)
    have hz : Tendsto X U.toFilter (𝓝 Z) := hZ
    refine ⟨reconstruct Z,?_⟩
    intro v
    rw [reconstruct_apply]
    have h := tendsto_finsetSum Finset.univ (fun k _ => (tendsto_pi_nhds.mp hz k).const_smul (coefficient v k))
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
  let Z (x : I → Cover) : Tensor C d D :=
    if h : Plot C (P.b t) (P.middle t) (P.j t) x then (get x h).choose else 0
  refine ⟨Z,fun x hx=>?_⟩
  simpa only [Z,dif_pos hx] using (get x hx).choose_spec

theorem original (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i, d i))
    (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (U : Ultrafilter (ℕ × ℕ)) (sub : U.toFilter ≤ f.fuse) :
    ∀ᶠ t in trail, ∃ Z : (I → Cover) → Tensor C d D, ∀ x : I → Cover,
      Plot C (P.b t) (P.middle t) (P.j t) x → Along F R J t (P.b t) (P.j t) x U (Z x) :=
  (refinements F facility anchor R P J H).mono (fun _ h=>h U sub)

end YM.Integration.WilsonSeparatedSharedRegulator

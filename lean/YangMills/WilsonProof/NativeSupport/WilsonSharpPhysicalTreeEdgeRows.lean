import YM.Integration.WilsonCenteredNestedPairHaar
import YM.Integration.WilsonCenteredNestedTerminalOrbit
import YangMills.WilsonProof.NativeSupport.MatchingNesting
import YangMills.WilsonProof.NativeSupport.HierarchyBridge

/-! The one-vertex comparison on the finite input set used by the public
fusion tree, with the actual through-cutoff field and the actual public
coefficient.  The root is integrated only after its incoming coefficients
have been made independent of the common rotation and reality branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeEdgeRows
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Nesting OPE.Nesting.Atom OPE.Log MeasureTheory
open WilsonCenteredNestedLoggedRow WilsonCenteredNestedGross WilsonCenteredNestedProjectedShadow
open WilsonCenteredNestedRealOrbit WilsonCenteredNestedProducts WilsonCenteredNestedPairHaar
open scoped Classical Topology BigOperators
attribute [local instance] measO borelO YM.Work.A15.compact_ortho
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {I J : Type} [Fintype I] [Fintype J]

def raw (H m : ℕ) (c : Q.channels m) (x : I → E4) (v : I → S.Tag)
    (o : E4) (k : Ortho) (b : Bool) : ℂ :=
  read F Q m H c (restored F Q.port H x (voices v) o k b)

lemma spinning_perm {d : I → ℕ} (H : ℕ) (x : I → E4) (v : Labels S d) (o : E4)
    (e : J ≃ I) (k : Ortho) :
    spinning Q.port F.sector.turns H (x ∘ e) o k (d := d ∘ e) (fun j => v (e j)) =
      spinning Q.port F.sector.turns H x o k v := by
  apply congrArg (F.sector.turns.act H k)
  unfold shadow
  apply Finset.sum_congr rfl
  intro w _
  apply congrArg (· • Q.port.loaded w H)
  exact Q.port.coefficient_perm (x := Ortho.move k⁻¹ ∘ x)
    (names (roll F.sector.turns k⁻¹ v)) Q.continuum.laws.toSymmetric e w

lemma raw_perm (H m : ℕ) (c : Q.channels m) (x : I → E4) (v : I → S.Tag)
    (o : E4) (e : J ≃ I) (k : Ortho) (b : Bool) :
    raw F Q H m c (x ∘ e) (v ∘ e) o k b = raw F Q H m c x v o k b := by
  apply congrArg (read F Q m H c)
  cases b with
  | false => exact spinning_perm F Q H x (voices v) o e k
  | true =>
    exact congrArg (S.conj F.room.kernel.spin H)
      (spinning_perm F Q H x (bar F.room.kernel.spin (voices v)) o e k)

def rowPrice (v : I → S.Tag) (m : ℕ) (r : ℝ) :=
  r ^ m / ∏ i, r ^ (v i).1

theorem original (fac : Facilities C f S) (foundation : Foundation F Q)
    {l : Filter (ℕ × ℕ)} [l.NeBot] (lo : l ≤ f.fuse)
    (ticket : MatrixTicket (C := C) S F.sector.derivatives l)
    (v : I → S.Tag) (H m : ℕ) (mh : m ≤ H) (c : Q.channels m)
    {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃ j A, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ x o, WithinRoom r M η x o →
      ∀ k b, Priced (raw F Q H m c x v o k b) (express Q m c x v o)
        (wage j A r * rowPrice v m r) (r ^ (H+1-m)) := by
  let e := (Fintype.equivFin I).symm
  obtain ⟨j,A,An,rows⟩ := WilsonCenteredNestedRawRows.original F Q Q.spans
    fac foundation lo ticket (v ∘ e) H Mn ηp
  refine ⟨j,A,An,?_⟩
  filter_upwards [rows] with r atR x o fit k b
  have fit' : WithinRoom r M η (x ∘ e) o :=
    ⟨fun i => fit.span (e i), fun i j ne => fit.spaced _ _ (e.injective.ne ne)⟩
  obtain ⟨diff,pub,src⟩ := atR (x ∘ e) o fit' k b ⟨m,Nat.lt_succ_of_le mh⟩ c
  change ‖raw F Q H m c (x ∘ e) (v ∘ e) o k b - express Q m c (x ∘ e) (v ∘ e) o‖ ≤ _ at diff
  change ‖raw F Q H m c (x ∘ e) (v ∘ e) o k b‖ ≤ _ at src
  rw [raw_perm, express_perm] at diff
  rw [raw_perm] at src
  rw [express_perm] at pub
  have fee (w : ℕ) : WilsonCenteredNestedEdge.port r w
      (WilsonCenteredNestedRawRows.degree (v ∘ e)) = rowPrice v w r := by
    unfold WilsonCenteredNestedEdge.port WilsonCenteredNestedRawRows.degree rowPrice
    rw [←Finset.prod_pow_eq_pow_sum]
    congr 1
    exact e.prod_comp (fun i => r ^ (v i).1)
  rw [fee] at src pub diff
  refine ⟨src,pub,diff.trans_eq ?_⟩
  unfold rowPrice
  rw [show r^(H+1) = r^m * r^(H+1-m) by rw [←pow_add]; congr 1; omega]
  ring

lemma integrable_raw (H m : ℕ) (c : Q.channels m) (x : I → E4) (v : I → S.Tag)
    (o : E4) (live : orbitMargin Q.port H x o) (b : Bool) :
    Integrable (fun k => raw F Q H m c x v o k b) haar := by
  let L := ((read F Q m H c).toContinuousLinearMap).restrictScalars ℝ
  let J := (conjugateR F.room.kernel.spin H).toContinuousLinearMap
  cases b
  · exact L.integrable_comp (WilsonCenteredNestedRootMean.checkable F Q H x o live (voices v))
  · exact L.integrable_comp (J.integrable_comp
      (WilsonCenteredNestedRootMean.checkable F Q H x o live (bar F.room.kernel.spin (voices v))))

/-- Integrate only the root coefficient. Every other coefficient in the
summand is public and therefore independent of both integration variables. -/
theorem root_mean {U : Type} [Fintype U] (m : ℕ) (c : Q.channels m) (x : I → E4)
    (v : U → I → S.Tag) (o : E4) (live : orbitMargin Q.port m x o) (fixed : U → ℂ) :
    mean (fun k b => ∑ u, fixed u * raw F Q m m c x (v u) o k b) =
      ∑ u, fixed u * express Q m c x (v u) o := by
  have row (b : Bool) :
      (∫ k, ∑ u, fixed u * raw F Q m m c x (v u) o k b ∂haar) =
      ∑ u, fixed u * ∫ k, raw F Q m m c x (v u) o k b ∂haar := by
    rw [integral_finsetSum _ (fun u _ => (integrable_raw F Q m m c x (v u) o live b).const_mul _)]
    exact Finset.sum_congr rfl fun u _ => integral_const_mul _ _
  unfold mean
  rw [row, row, ←Finset.sum_add_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro u _
  have h := WilsonCenteredNestedRootMean.original F Q m c x o live (voices (v u))
  change _ = fixed u * Q.coef m c x (voices (v u)) o
  rw [h, ←mul_add, Algebra.mul_smul_comm]
  rfl

/-- Before the grade-m rate is used, discard exactly the terminal terms
annihilated by the elected detector. The retained child fields stay intact. -/
theorem terminal (m : ℕ) (c : Q.channels m) (k : Ortho) (b : Bool)
    (z : Mode F.sector.derivatives → ℂ) :
    (∑ w ∈ bands F.sector.derivatives m, z w *
      read F Q m m c (WilsonCenteredNestedTerminalOrbit.out F m k b (Q.port.loaded w m))) =
    ∑ w ∈ (bands F.sector.derivatives m).filter (fun w => w.1=m), z w *
      read F Q m m c (WilsonCenteredNestedTerminalOrbit.out F m k b (Q.port.loaded w m)) := by
  symm
  apply Finset.sum_subset (Finset.filter_subset ..)
  intro w hw hn
  have low : w.1 < m := lt_of_le_of_ne ((full_bands ..).mp hw) (fun eq => hn (Finset.mem_filter.mpr ⟨hw,eq⟩))
  rw [WilsonCenteredNestedTerminalOrbit.lower F Q c w low k b, mul_zero]

end YM.Integration.WilsonSharpPhysicalTreeEdgeRows

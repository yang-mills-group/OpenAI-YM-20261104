import YM.Integration.WilsonPublicOutputCubic
import YM.RG17.Gathers
import YM.Pier.Lair.Bank

/-! A finite normalized detector reading on the original lattice. The physical
input columns and the whole output basis are chosen on one reporting layout.
The independent far date changes only the numerical combination of the paid columns. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicOutputRegulators
open Function Filter Set MeasureTheory Extraction Table Spec OPE OPE.Orbits RG17
open PhysMS Trace.Pilot Climb PhysicalNext.Repeat.Legato FVA2 FVA2.Register
open Next.Rank RG12 SharpGram
open WilsonPositionHomogeneousFrame WilsonMSDictionaryVector
open scoped Classical BigOperators Topology
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→tower S) (Z:WilsonPrescription G) (L:Layout F)

/-- The genuine paid reports at a fixed grade may be chosen on the whole public basis
before any far regulator, source amplitude, or signed observation is chosen. -/
theorem columns (h:ℕ) (paid:Pier.Lair.Paying F (Pier.Lair.tender F L J) h) :
    ∃ k:ℕ, ∀ᶠ r in home, ∀ e:Free R.family h, ∃ y:R.family.label h,
      mass R.family h (L.shift h r y) ≤ R.family.path.levels.clock.hatBeta (L.level r)^k*
        ‖(J r h).symm (homogeneous F J Z r h e)‖ ∧
      master L h r y = homogeneous F J Z r h e := by
  obtain ⟨k,fee⟩:=paid.affordability
  refine ⟨k,?_⟩
  filter_upwards [fee] with r fits e
  obtain ⟨y,cost,placed⟩:=fits.1 ((J r h).symm (homogeneous F J Z r h e))
  refine ⟨y,cost,?_⟩
  change master L h r y = J r h ((J r h).symm (homogeneous F J Z r h e)) at placed
  simpa only [LinearEquiv.apply_symm_apply] using placed

variable {I:Type} [Fintype I] (X:I→External R.family S) {h n:ℕ} (d:Fin n→ℕ)
    (ins:(i:Fin n)→R.family.label (d i))
    (out:Dframe.Toon G h→R.family.label h) (r:ℝ) (ψ:Test n)

/-- The original ordinary marked product and true two-point entries at the same cutoff;
every output direction, including the unit, participates in this sum. -/
def contrast (e:Free R.family h) (i:UVIndex) (j:I) : ℂ :=
  packMark L (X j) d ins r ψ i - ∑ k,
    (WilsonMSDictionaryVector.basis R.family h).repr e k * headMark L (X j) h r i (out k)

variable (a:Labels S d) (first:∀ i,master L (d i) r (ins i)=a i)
    (admitted:∀ i,R.family.ref (d i)≤L.level r)
    (last:∀ k,master L h r (out k)=homogeneous F J Z r h (WilsonMSDictionaryVector.basis R.family h k))
    (href:R.family.ref h≤L.level r) (rp:0<r)
    (covered:∀ j,packs (X j) r ψ)
    (integrable:∀ j,Integrable (fun z:Points ((X j).n+1)=>
      (X j).test z * query F a ((X j).offset z) (X j).labels none r ψ))
include first admitted last href rp covered integrable

omit [Fintype I] in
theorem limit (e:Free R.family h) :
    Tendsto (contrast F L X d ins out r ψ e) L.lens
      (𝓝 (fun j=>appeared F a (X j) r ψ - (X j).charge F h (homogeneous F J Z r h e))) := by
  letI := L.notbot
  apply tendsto_pi_nhds.mpr
  intro j
  have full:=limitPack (r:=r) L (X j) le_rfl ins ψ admitted
  have same:(fun i=>master L (d i) r (ins i))=a:=funext first
  rw [same, chargedShape (X j) a ψ rp (covered j) (integrable j)] at full
  have heads (k:Dframe.Toon G h):=
    limitHead (r:=r) L (X j) le_rfl (v:=fun _=>out k) tendsto_const_nhds href
  have equality : (X j).charge F h (homogeneous F J Z r h e) =
      ∑ k,(WilsonMSDictionaryVector.basis R.family h).repr e k * (X j).charge F h (master L h r (out k)) := by
    conv_lhs => rw [←(WilsonMSDictionaryVector.basis R.family h).sum_repr e,map_sum,map_sum]
    simp only [map_smul,smul_eq_mul,last]
  rw [equality]
  exact full.sub (tendsto_finsetSum _ fun k _=>
    (tendsto_const_nhds (x:=(WilsonMSDictionaryVector.basis R.family h).repr e k)).mul (heads k))

/-- A bound with the ultraviolet threshold allowed to depend on the physical period
passes first through the original extraction, then to the independent outer cutoff. -/
theorem original (e:ℝ→Free R.family h) (δ:ℝ)
    (signed:∃ᶠ s:ℝ in atTop, f.late (fun N per=>
      ‖contrast F L X d ins out r ψ (e s) (N,per)‖ ≤ δ)) :
    ∃ᶠ s:ℝ in atTop, ‖(fun j=>appeared F a (X j) r ψ) -
      (fun j=>(X j).charge F h (homogeneous F J Z r h (e s)))‖ ≤ δ := by
  letI := L.notbot
  refine signed.mono fun s cash=>?_
  have physical : ∀ᶠ i in f.fuse, ‖contrast F L X d ins out r ψ (e s) i‖ ≤ δ :=
    (f.fused _).mpr cash
  exact le_of_tendsto (limit F J Z L X d ins out r ψ a first admitted last href rp covered integrable (e s)).norm
    (physical.filter_mono L.certified)
end YM.Integration.WilsonPublicOutputRegulators

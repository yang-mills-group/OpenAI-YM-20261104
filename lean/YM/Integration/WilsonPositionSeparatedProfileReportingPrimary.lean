import YM.Integration.WilsonPositionSeparatedProfileReportingWindow
import YM.Work.E01

/-! The accepted reported field is the actual primary insertion on each
occupied physical footprint. All basis and plaquette sums use the same held
configuration and the same cutoff-dependent threshold. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileReportingPrimary
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open OPE.Therm RG05Readout Address Native Pulse MergeProof Accent
open PhysicalNext.Repeat.Legato RGComparison.Core16.Spool WilsonReportingPlaquetteWindows
open WilsonPositionSeparatedProfileReportingWindow WilsonReportingRegisteredWindows
open private order from YM.Integration.WilsonReportingRegisteredWindows
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {I : Type} [Fintype I] [DecidableEq I] (D : I→ℕ)

/-- All plaquettes incident upon this source footprint, within two lattice steps. -/
def cover {v : Side} (X : Support v) : Finset (Face (Per v)) := halo 2 X ×ˢ Finset.univ

theorem healthy {v : Side} {U : Config G v} {σ θ : ℝ} (X : Support v)
    {A : Finset (Face (Per v))} (contains : cover X⊆A) (late : σ≤θ) (cold : U∈House.chilly A σ) : Healthy θ X U := by
  apply Finset.disjoint_left.mpr
  intro x hx hot
  obtain ⟨p,touch,off⟩:=(flags_spec θ U x).mp hot
  have root : p.1∈halo 2 X:=halo_spec.mpr ⟨x,hx,(separation_comm x p.1).trans_le (Work.E01.sep_touched p x touch)⟩
  exact (not_lt_of_ge ((cold p (contains (Finset.mem_product.mpr ⟨root,mem_univ _⟩))).trans late)) off

theorem footprint {v : Side} (d : ℕ) (x : Site v) :
    (cover ((R.family.localSection d).footprint x)).card≤
      (R.family.localSection d).stencil.card*5^4*Fintype.card PlaqAxes := by
  rw [cover,Finset.card_product,Finset.card_univ]
  apply Nat.mul_le_mul_right
  exact (Lattice.Corona.halo_size _ 2).trans (Nat.mul_le_mul_right _ Finset.card_image_le)

private theorem basis {v:Side} (d:ℕ) (y:R.family.label d) (o:Site v) (U:Config G v) (θ:ℝ) :
    Push.Local.presented (R.family.localSection d) o θ y U=
    ∑b, (((θ⁻¹:ℝ):ℂ)^((R.family.labels.level d).grades b).2*y b)*
      (R.family.localSection d).places (Pi.single b 1) o U := by
  let F:=R.family.labels.level d
  let T:=R.family.localSection d
  let L:F.Coeff→ₗ[ℂ] ℂ:=
    { toFun:=fun b=>T.places b o U
      map_add':=fun a b=>congr_fun (T.eval_linear.map_add a b) _
      map_smul':=fun a b=>congr_fun (T.eval_linear.map_smul a b) _ }
  let z:=F.scaled θ⁻¹ y
  have h:z=∑b:F.Index,z b • (Pi.single b 1:F.Coeff):=by
    funext i;simp [Pi.single_apply]
  have measured:=congrArg L h
  simp only [map_sum,map_smul,smul_eq_mul] at measured
  change L z=_
  rw [measured];apply sum_congr rfl;intro b _
  simp only [z,Frame.scaled_apply,Complex.ofReal_pow,L,F,T]
  rfl

theorem gathered (k N per : ℕ) (y : (i:I)→R.family.label (D i)) (o : I→Site (R.family.side k per)) (U:Config G (R.family.side k per)) :
    (∏i,Push.Local.presented (R.family.localSection (D i)) (o i) (R.family.path.rep N per k).p.threshold (y i) U)=
      ∑a:rows R D,price R D k N per y a*∏i,(R.family.localSection (D i)).places (Pi.single (a i) 1) (o i) U := by
  simp_rw [basis]
  rw [Fintype.prod_sum]
  apply sum_congr rfl;intro a _
  simp only [Finset.prod_mul_distrib,price,order,Finset.prod_pow_eq_pow_sum]
  ring

def read (k N per t : ℕ) (y:(i:I)→R.family.label (D i)) (φ:Wave I) (r:ℝ) (ξ:Cloud I)
    (U:Config G (R.family.side k per)) : ℂ :=
  ∑z:placements (V:=I) R.family k per t,φ.val (fun i=>r⁻¹ • (R.family.S.place (z.val i)-ξ i))*
    ∏i,Push.Local.presented (R.family.localSection (D i)) (z.val i) (R.family.path.rep N per k).p.threshold (y i) U

def primary (k N per t : ℕ) (y:(i:I)→R.family.label (D i)) (φ:Wave I) (r:ℝ) (ξ:Cloud I)
    (cells:placements (V:=I) R.family k per t→I→Finset (Face (Per (R.family.side k per)))) (U:Config G (R.family.side k per)) : ℂ :=
  ∑z:placements (V:=I) R.family k per t,(⋂i,House.chilly (cells z i) (cool R.family.path.levels k)).indicator
    (fun W=>φ.val (fun i=>r⁻¹ • (R.family.S.place (z.val i)-ξ i))*
      ∏i,Push.Local.primary (R.family.localSection (D i)) (z.val i) (R.family.path.rep N per k).p.threshold (y i) W) U

theorem compared (k N per t : ℕ) (y:(i:I)→R.family.label (D i)) (φ:Wave I) (r:ℝ) (ξ:Cloud I)
    (cells:placements (V:=I) R.family k per t→I→Finset (Face (Per (R.family.side k per))))
    (all : ∀z i,cover ((R.family.localSection (D i)).footprint (z.val i))⊆cells z i)
    (late : cool R.family.path.levels k≤(R.family.path.rep N per k).p.threshold) (U:Config G (R.family.side k per)) :
    read R D k N per t y φ r ξ U-primary R D k N per t y φ r ξ cells U=
      fault R D k per t (fun a=>φ.val (fun i=>r⁻¹ • (R.family.S.place (a.1.val i)-ξ i))*price R D k N per y a.2)
        (fun a=>cells a.1) U := by
  unfold read primary fault
  rw [←Finset.sum_sub_distrib,Fintype.sum_prod_type]
  apply sum_congr rfl;intro z _
  let A (i:I):=House.chilly (G:=G) (cells z i) (cool R.family.path.levels k)
  by_cases yes:U∈⋂i,A i
  · have good:=Set.mem_iInter.mp yes
    have clean:U∉⋃i,(A i)ᶜ:=by simpa only [Set.mem_iUnion,Set.mem_compl_iff,not_exists,not_not] using good
    dsimp only [A] at clean
    rw [Set.indicator_of_mem yes]
    simp only [Set.indicator_of_notMem clean,Finset.sum_const_zero,sub_eq_zero]
    apply congrArg (fun w:ℂ=>φ.val (fun i=>r⁻¹ • (R.family.S.place (z.val i)-ξ i))*w)
    apply prod_congr rfl;intro i _
    exact (Push.Local.presented_primary _ (R.makes.sections (D i)) _ U (healthy _ (all z i) late (good i))).symm
  · have hot:U∈⋃i,(A i)ᶜ:=by simpa only [Set.mem_iUnion,Set.mem_compl_iff,Set.mem_iInter,not_forall] using yes
    dsimp only [A] at hot
    rw [Set.indicator_of_notMem yes,sub_zero,gathered R D]
    simp only [Set.indicator_of_mem hot,Finset.mul_sum,mul_assoc]

end YM.Integration.WilsonPositionSeparatedProfileReportingPrimary

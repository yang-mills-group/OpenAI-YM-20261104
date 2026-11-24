import YM.Integration.WilsonAddressedWeakRankHearing
import YM.Integration.WilsonMatrixOriginalDeckColumns
import YM.MergeProof.West.Mooncake

/-! The compensated independent Maxwell response on the actual projected parents of the submitted cutoff fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakMaxwellPositions
open Function Filter Set MeasureTheory Lattice Wilson RG Source Cells RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox PhysicalNext.Repeat.Legato
open MergeProof Accent Motion Bandage Extra.Multi Menu
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone
open Extraction Table Spec OPE OPE.Orbits PhysMS XSpace XSpace.Normalize Trace Trace.Pilot
open Next.Rank Next.Rank.Station Next.Rank.Read
open WilsonAddressedWeakCalibration WilsonAddressedWeakPackedCertificate
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {B:Local.Physical.Deck G} {O:Booked B} (M:MS_Data G O)
variable {N p k n d:ℕ}
local notation "A" => R.family.path.levels
local notation "S" => Cells.standard R.family

/-- The true submitted fine-cell parents, even at a tie, give the exact integer placements for the independent position program. -/
theorem stations (live:k≤N) (b:ℝ) (x:Points 2) :
    let ρ:=gap (A) b k
    let h:=gap_pos (A) b k
    let v:=projected R (p:=p) live ρ h x
    let Z:=lifts R (p:=p) live ρ h x
    v=tag (mag (A) b k)⁻¹ Z ∧
      choose (A) b k v=Z ∧ tested (A) b k v=v := by
  let h:=gap_pos (A) b k
  let Z:=lifts R (p:=p) live (gap (A) b k) h x
  have scale : projected R (p:=p) live (gap (A) b k) h x=tag (mag (A) b k)⁻¹ Z := by
    ext i j
    change ((R.family.S.a k*mag (A) b k)⁻¹:ℝ)*(R.family.S.a k*(Z i j:ℝ))=(mag (A) b k)⁻¹*(Z i j:ℝ)
    field_simp [(mag_pos (A) b k).ne',(R.family.S.a_pos k).ne']
  have cells : choose (A) b k (tag (mag (A) b k)⁻¹ Z)=Z := by
    funext i j
    change ⌈((mag (A) b k)⁻¹*(Z i j:ℝ))/(mag (A) b k)⁻¹⌉=Z i j
    rw [mul_div_cancel_left₀ _ (inv_ne_zero (mag_pos (A) b k).ne'),Int.ceil_intCast]
  dsimp only
  refine ⟨scale,scale ▸ cells,?_⟩
  rw [scale]
  change (gap (A) b k)⁻¹ • tag ((A).S.a k) (choose (A) b k (tag (mag (A) b k)⁻¹ Z))=_
  rw [cells]
  exact scale

/-- The independent weights are fixed before the detector, on the original Maxwell quotient. -/
def tags (B:Local.Physical.Deck G) (mark:Fin n→Glyph B d) : Fin n→(S).Tag :=
  fun i=>⟨d,WilsonMatrixOriginalDeckColumns.basis R.family B d (mark i)⟩

def representatives (B:Local.Physical.Deck G) (a:Glyph B d) : R.family.label d :=
  (S).representative d (WilsonMatrixOriginalDeckColumns.basis R.family B d a)

theorem placed (mark:Fin n→Glyph B d) (x:Points n) (hx:x∈conf n) (μ:ℝ) :
    (S).useAt (S) x (tags R B mark)=MSDeckProbeGram.raw M mark x μ 0 := by
  exact (WilsonMatrixOriginalDeckColumns.free R.family B M mark x hx μ).symm

theorem projected_tags (mark:Fin n→Glyph B d) :
    (fun i=>(⟨d,(S).project d (representatives R B (mark i))⟩:(S).Tag))=tags R B mark := by
  funext i
  change (⟨d,(S).project d ((S).representative d (WilsonMatrixOriginalDeckColumns.basis R.family B d (mark i)))⟩:(S).Tag)=_
  rw [(S).rep]
  rfl

/-- Both actual proper Maxwell means and the complete ordinary pair at the booked labels and coordinates. -/
theorem profile (mark:Fin 2→Glyph B d) (x:Points 2) (hx:x∈conf 2) (μ:ℝ) :
    let F:=maxProfile R.family x (tags R B mark)
    (∀i:Fin 2,F.part (Next.Rank.Glyph.slot i)=WilsonAddressedWeakShapeFees.mean M (mark i) x i μ) ∧
      F.part (Next.Rank.Glyph.scene {(0:Fin 2),1}) = MSDeckProbeGram.raw M mark x μ 0 := by
  constructor
  · intro i
    change (Read.profile (S) (tags R B mark) x).part (Next.Rank.Glyph.scene {i})=_
    rw [Read.profile_single (S) (Maxwell.table_regular R.family.labels).toSymmetric x hx]
    let u:=points (fun _:Fin 1=>x i)
    have hu:u∈conf 1:=fun _ _ _=>Subsingleton.elim ..
    exact placed R M (fun _:Fin 1=>mark i) u hu μ
  · have all : ({(0:Fin 2),1}:Finset (Fin 2))=Finset.univ:=by decide
    rw [all]
    change (Read.profile (S) (tags R B mark) x).part (Next.Rank.Glyph.scene Finset.univ)=_
    rw [Read.profile_full (S) (Maxwell.table_regular R.family.labels).toSymmetric x hx]
    exact placed R M mark x hx μ

/-- The physical source can be any coupled group test. The independent correction uses its own placed Wick table. -/
theorem cylinder {E:Type} (F:Fin 2→E→ℂ) (U:E) (mark:Fin 2→Glyph B d)
    (x:Points 2) (hx:x∈conf 2) (μ:ℝ) :
    let m:=fun i=>WilsonAddressedWeakShapeFees.mean M (mark i) x i μ
    let q:=MSDeckProbeGram.raw M mark x μ 0
    let L:=Read.cumulants R.family x (tags R B mark) hx
    (∀i:Fin 2,(Read.cylinder L F U).part (Next.Rank.Glyph.slot i)=F i U-m i) ∧
    (Read.cylinder L F U).part (Next.Rank.Glyph.scene {(0:Fin 2),1})=(F 0 U-m 0)*(F 1 U-m 1)-(q-m 0*m 1) := by
  dsimp only
  have h:=Read.cumulative R.family x (tags R B mark) hx
  obtain ⟨single,pair⟩:=profile R M mark x hx μ
  constructor
  · intro i
    rw [Read.cylinder_single h F i U,single]
  · rw [Read.cylinder_pair h F 0 1 (by decide) U,single,single,pair]

end YM.Integration.WilsonAddressedWeakMaxwellPositions

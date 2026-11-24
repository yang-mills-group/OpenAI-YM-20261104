import YM.Integration.WilsonPositionProgramVisitedTest
import YM.WilsonCoeffUV.Marked.Capture.AtSensor

/-! The complete finite incoming table on the nominated normalized programme,
with the original four-dimensional child measure and the true common center. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace YM.Integration.WilsonPositionProgramHearthBirth
open Filter Finset Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open scoped Classical BigOperators
variable {G : Gauge} {a h D k u e : ℕ}

theorem raw (Q : Fin (a+1) → SealR G) (L : Levels G) (O : ChartRatio G) (m N : ℕ)
    (X : Herit Q) (φ : Wilt Q) (y : ℝ) (c : CellR) (n : Side) :
    let θ:=paceT L.S m N
    let Y := fun i=>centralL L O N m N (Q i) (X i)
    (∀ i,On (asp Q i) (Y i)) →
      flash ((locale c (HearthC Q L O φ X m N N y)).1 n) =
        ∑ z ∈ Fintype.piFinset (fun i=>VisitsT (φ i) θ y c),
          (∏ i,drumB (asp Q i) θ) • ∏ i,flash ((locale c (shoe (Y i) (φ i) θ y (z i))).1 n) := by
  intro θ Y on
  let H := fun i=>locale c ((Q i).spins L O (φ i) m N N y (X i))
  let V := fun i=>VisitsT (φ i) θ y c
  let Z := fun i (z : Cover)=>locale c (shoe (Y i) (φ i) θ y z)
  have hv (i) (z) : Auth (asp Q i) (Z i z) := locale_val _ (((On_auth (on i)).tuft _).shifted _) _
  have hh i : Auth (asp Q i) (H i) := locale_val _ (Mer.placed _ _ (on i) θ y) _
  have each i : flash ((H i).1 n) = ∑ z∈ V i, drumB (asp Q i) θ • flash ((Z i z).1 n) := by
    have placed : H i = ∑ z∈V i, drumB (asp Q i) θ • Z i z :=
      pupil_eye (asp Q i) (Y i) (φ i) θ y c (pace_pos ..)
    rw [placed]
    exact embodied (V i) (fun z _=>hv i z)
  rw [show locale c (HearthC Q L O φ X m N N y)=MassP G ℝ a H from PortalHome ..,
    poly_agate a H (asp Q) hh]
  simp_rw [each]
  rw [Finset.prod_univ_sum]
  exact Finset.sum_congr rfl (fun z _=>(smulk (fun i=>drumB (asp Q i) θ)
    (fun i=>flash ((Z i (z i)).1 n))).symm)

theorem original (R : Run G) (simple : G.Simple) (v : ℕ→Gear G→ℝ)
    (funded : FundedMarkedCoverRows.prices v R.kit) (big : h<D) (rails : Rails h k u e)
    (l d : Fin (a+1)→ℕ) (fit : ∀ i,l i<d i) (cap : capP (deck (G:=G) l d fit)≤k) :
    let Q := deck (G:=G) l d fit
    let L := R.family.path.levels
    ∀ᶠ f:ℕ in atTop, ∀ m N, f ≤ m → m ≤ N → ∀ X : Herit Q, ∀ φ : Wilt Q,
      ∀ (y:ℝ) (c:CellR) (n:Side), let x:=normalized L R.metals.O Q X m N
      let θ:=paceT L.S m N
      let Y := fun i=>centralL L R.metals.O N m N (Q i) (x i)
      flash ((locale c (HearthC Q L R.metals.O φ x m N N y)).1 n) =
        ∑ z∈ Fintype.piFinset (fun i=>VisitsT (φ i) θ y c),
          (∏ i,drumB (l i) θ) • ∏ i,flash ((locale c (shoe (Y i) (φ i) θ y (z i))).1 n) := by
  intro Q L
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded big rails l d fit cap]
    with f filed
  obtain ⟨W,Y,lv,rt,_,first,_,_,_,frames,_⟩ := filed
  intro m N fm mN X φ y c n x θ Z
  apply raw Q L R.metals.O m N x φ y c n
  intro i
  obtain ⟨t⟩ := frames i
  let A := t.p.f.arch
  have hl : A.V.draws=L := t.p.lands.trans lv
  have hr : A.V.paid=R.metals.O := t.p.modes.trans rt
  have hf : A.V.anchor ≤ N := (t.p.tap.trans first).symm ▸ fm.trans mN
  have issued := tournure (m:=m) A (x i) hf (le_refl N)
  rwa [hl,hr] at issued

end YM.Integration.WilsonPositionProgramHearthBirth
end

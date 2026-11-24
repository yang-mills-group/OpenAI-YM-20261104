import YM.FVA2.Arrival.Born
/-!
# Plugging the Wilson coefficients into MS

`M : MS.Land.Prescription`: parent matching data (functions of log spacing/mass etc.).
`x` below is the MS log calibration argument in lattice units (`η`). For the compensated
fields, the full expectation of the designated `u` labels at `L+d` combines:

* the external W pieces of the *underlying* Wilson stencils: `Birth.words`, from `Folio`
* the prefactors (drop operation there) and the bare action coupling conversion
  `Program.shift M.team x`
* the physical operator change (mark coefficients from `M.fees` as encoded by
  `Dictionary.paid`; not taking any limit of these matrices here).

`Top.value` in the MS variable (at this `x`) is precisely this combination. `tallies_aux`,
`tallies`, `identifies`: the **literal** MS `PhysicalSum`, not just proving there exists
some presentation. Includes positive mark cases. Later, in `Arrival/Net`, see the use of
both unmarked and marked canonical changes for these same readings. Note: `tallies`
works with no admissibility of `M` for the continuum comparison. To get that too, with
one choice of concrete `M` and estimates all-orders, see `YM/FVA2/Main.lean`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Arrival
open Function Set Filter Finset MeasureTheory Lattice Wilson Press XPos Change Slice
open MS MS.Koszul MS.Book Convolve Program MS.Native MS.Theater MS.Menus MS.Rake
open MS.Orbit MS.Fleet MS.Tide MS.Swirl MS.Swirl.Near
open FormalOPE.RG10.MultiGauge Splice Maxwell Maxwell.Free
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {W: Type} {k:ℕ} (Y:XSpace.Initialize G)
local notation "B"=> portDeck G
namespace Top
variable (u:W→Label (portDeck G))(M: Land.Prescription (portDeck G))
local notation "f"=> Dictionary.factors u
local notation "V"=> Dictionary.vertices u
variable (L:Cover)(d:W→Cover)
def declares (v:Dictionary.vertices u) : Birth G := ⟨ (u v.1).h, v.2, L+d v.1⟩
local notation "r"=> declares u L d
local notation "ν"=> wickInput Y
variable (n:Side)
local notation "φ"=> MS.Tide.ApplyMF (wickInput Y) ( MS.Swirl.Near.Stripped M.team ) M u
def cards (x: Dictionary.vertices u) := Birth.broad Y (r x) n
def usual (x : Dictionary.vertices u) : MS.Book.Convolve.T ( Raw (FixedMode G n) ℂ ) :=
    ∑ j : Glyph.Bundle x.2, Change.Stencil.verse (n:=n) (Folio.entry Y ((r x).chooses j))
      L (d x.1) (x.2.tally j)
local notation "H"=> usual Y u L d n
variable (x:ℝ)
lemma literal (w : W) :
      promote (Mark_T G n L (d w)) (φ w x) =
        Change.mixed M.team x (Dictionary.paid u M x) H w := by
    let h := (u w).h
    let S := M.fees h (u w).item
    let T := M.team; let q := Stripped T; let A := promote (Mark_T G n L (d w))
    have hu : φ w x = ∑ i:Glyph B h, Change.scale (Dot G Cover) (Dictionary.paid u M x ⟨w,i⟩)
                (Glyph.preambleF (wickInput Y) q i x) := by
        funext v; rw [Finset.sum_apply]; exact sum_congr rfl fun _ _=>rfl
    rw [hu,map_sum]; unfold Change.mixed; apply sum_congr rfl; intro i _
    rw [Change.promote_scale,Glyph.preambleF, strip_wobble, Program.comm]
    unfold Glyph.gallery; rw [map_sum,usual]
    refine congr_arg (fun z=> Change.scale ( Raw (FixedMode G n) ℂ )
      (Dictionary.paid u M x ⟨w,i⟩) (substitute (Program.shift M.team x) z)) ?_
    exact (Finset.sum_congr rfl fun a _=> congr_arg (fun z=> A (Book.levels (i.tally a) z)) (stampF Y i a))

variable [LinearOrder W] (v : Finset W)

/-- Use the mark fees and coupling shift of the chosen comparison, at this logarithmic scale,
and assemble from the same `Birth` stencil words in bare coupling. -/
def value : MS.Book.Convolve.T ℂ :=
    Change.convertSources (Dictionary.paid u M x) v.toList (fun l=>
      substitute (Program.shift M.team x) (record (Birth.words Y n (l.map (declares u L d)))))

variable (ev : Even n.val)
include ev
lemma tallies_aux {A J:Type} [Fintype A][DecidableEq A] [Fintype J][DecidableEq J]
      (a : Axes G n A J) (μ : Measure (Transverse G n)) [Measure.IsAddHaarMeasure μ] :
        PhysicalSum G M.team x n true v d L
          (ApplyMF (wickInput Y) (Stripped M.team) M u) (value Y u M L d n x v) := by
    unfold value; let X := cards Y u L d n
    simp_rw [ Birth.priced Y n a μ ev ]
    have hx l : Birth.kVector Y n (l.map (r)) = Change.positions X l:= by
        rw [Birth.kVector,List.map_map]; rfl
    simp_rw [hx]; apply Change.evaluated M.team x a μ («v»:=H)
    · intro i; exact Submodule.sum_mem _ (fun j _=> Stencil.money _ (Folio.leaf Y ((r i).chooses j)) _ _ _)
    · intro i; unfold usual; change _= Wick.Boson.bills a.X (Birth.broad Y (r i) n)
      unfold Birth.broad; rw [map_sum,map_sum]
      exact sum_congr rfl fun j _=> ( Folio.leaf Y ((r i).chooses j)).landed ..
    · exact literal Y u M L d n x
    intro i; exact Submodule.sum_mem _ fun j _=> Stencil.even _ (Folio.leaf Y ((r i).chooses j)) _ _ _
lemma tallies :
        PhysicalSum G M.team x n true v d L
          (ApplyMF (wickInput Y) (Stripped M.team) M u) (value Y u M L d n x v) :=
    tallies_aux Y u M L d n x v ev ( Change.Dictionary.picked G n ) Measure.addHaar
lemma identifies {z : ℕ → ℂ} :
        PhysicalSum G M.team x n true v d L φ z ↔ z=value Y u M L d n x v :=
    ⟨ fun h=> classicalμ (τ_nil ..) h (tallies Y u M L d n x v ev),
      fun h=> h.symm ▸ (tallies Y u M L d n x v ev) ⟩
end Top
end YM.FVA2.Arrival

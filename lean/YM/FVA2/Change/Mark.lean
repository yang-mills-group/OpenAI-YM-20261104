import YM.FVA2.Change.Leg
import YM.MS.Tide.Coi
/-! # Physical basis marks in the MS Landau-gauge Wilson comparison

A single dictionary of **real group stencils** with the insertion exactly that of the MS
regulator (not just the cotangent/dimension observable). `Stencil.billable`
states compatibility of the two readings; see `Change/Address.lean`. Cost terms
in PUBLIC coupling: no powers of g attached to them afterwards.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Change
open Function Set Filter Finset Lattice MeasureTheory
open MS MS.Koszul MS.Plane MS.Orbit Cog Orbit.LogReal MS.Swirl MS.Book Convolve Program
open MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.Actors
open MS.Swirl.Near MS.Native Wilsonian Chart MS.Bare MS.Landau MS.Cylinder Lab Taylor
open MS.Menus MS.Fleet MS.Tide MS.Land MS.Local.Physical MS.Rake
open Slice Fourier Wilson
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge Splice
open PertExtension.Series.Radial
open scoped BigOperators Topology ContDiff Matrix
variable {G:Gauge} {n:Side} {F:Dot G Cover} {k:ℕ} {J W A:Type}
local notation "V" => FixedMode G n
local notation "Z" => Transverse G n
local notation "p" => σbranch (G:=G) (n:=n)

namespace Stencil
variable (F:Dot G Cover) (X: Stencil F) (q d:Cover) (v:ℕ)
abbrev verse (F:Dot G Cover) (q d:Cover)(v:ℕ) : Wick.Formal.Table (FixedMode G n) := promote (Mark_T G n q d) (levels v F)
local notation "g" => X.placed n (q+d) ∘ nation
local notation "f" => verse (n:=n) F q d v
include X
private lemma read (i:ℕ) : f i=Wick.pull (toSite G n) (mask (i+(v:ℤ)) (reads g)):= by
  rw [verse,promised, mark_cover]; unfold levels; rw [← mode, show enters n (model _ _)= mask _ (enters n (Lab.Shift (q+d) F)) from enterShim (b:=false) n (i+(v:ℤ)),X.travel_bill]
lemma money : f∈ Wick.Formal.OK p := by
  intro i _; rw [read _ X]; refine ⟨ Wick.pull_symm (unpack_tie G n) ?_, minH (Wick.pull_limit _ (Limit.mod _ _)) ⟩
  exact Wick.sym_mask (ink_s direction ((glow G (Site n)).never) (X.crease _)) _
lemma even : f∈ Wick.Formal.even p := by
  intro i _; rw [read _ X]; apply Wick.pull_pure (unpack_tie G n); intro l h
  by_cases hl : (l.length:ℤ)= i+(v:ℤ)
  · rw [enough l hl]; exact ink_p direction (glow G (Site n)|>.never) g l h
  exact strange l hl
end Stencil

variable {B:Deck G}{P:LitBook B}
/-- One set of actual physical stencil witnesses for the mark lift `P`. Constructed later, e.g.
by covariantized stencils. This includes *all* labels, used throughout regulator schedule. -/
structure Dictionary (P : LitBook B) where
  stamp (x y:ℕ) (i:B.BIndex (x:ℤ) y) : Stencil (P.stamp x y i)

namespace Dictionary
variable (X:Dictionary P)

def node (v:Glyph B k) := X.stamp v.size v.grade v.2.2
variable (u:W→Label B) (M:Land.Prescription B)
variable (L:Cover) (d:W→Cover)
abbrev factors (u:W→Label B) : W → Type := fun i=> Glyph B (u i).h
abbrev vertices (u:W→Label B) := Sigma (factors u)
instance instFactorFintype (i : W) : Fintype (factors u i):= inferInstanceAs (Fintype (Glyph B _))

def edge (n:Side)(x: vertices u) := (X.node x.2).onLandau n (L+d x.1) x.2.grade

def paid (S:Land.Prescription B) (x:ℝ) (v:vertices u) (j:ℕ): ℂ := oil (S.fees (u v.1).h (u v.1).item) v.2 j x

def ordinary (P: LitBook B)(c : vertices u) : T (Raw (FixedMode G n) ℂ):= Stencil.verse (c.2.lit P) L (d c.1) c.2.grade
local notation "hT" => ordinary (n:=n) u L d P
variable [LinearOrder W]
variable (x : ℝ)
local notation "v" => ApplyM P ( Stripped M.team ) M u
omit X [LinearOrder W] in
lemma shearing (a:W) : promote (Mark_T G n L (d a)) ( v a x)=mixed M.team x (paid u M x) hT a:= by
  let h:= (u a).h; let S:= M.fees h (u a).item; let F(i: Glyph B h):= i.lit P; let T:=M.team; let q := Stripped T; let ζ:=Program.shift T x; let k := Mark_T G n L (d a)
  have he : v a x=∑ i:Glyph B h,scale (Dot G Cover) (paid u M x ⟨a,i⟩) (Glyph.preamble P q i x):= by funext p'; rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun _ _=>rfl -- check
  rw [he,map_sum]; unfold mixed; refine Finset.sum_congr rfl fun i _=> ?_
  rw [promote_scale,Glyph.preamble, strip_wobble]; rw [Program.comm]; rfl

variable [Fintype A][DecidableEq A][Fintype J][DecidableEq J]
variable (b:Axes G n A J)(μ:Measure (Transverse G n))[Measure.IsAddHaarMeasure μ]

/-- Tune application on the true regulator stencils. To be used with tree-LPT connection and the
implemented MS continuum prescription matching `M` via `TaylorOK`. -/
lemma at_parameters (S:Finset W) : PhysicalSum G M.team x n true S d L v
   (convertSources (paid u M x) S.toList (fun l=> substitute (Program.shift M.team x) (record (b.sumBody μ (positions (X.edge u L d n) l))))) := by
    apply evaluated M.team x b μ («v»:=hT)
    · intro i; exact Stencil.money _ (X.node i.2) L _ _
    · intro i; exact (X.node i.2).landed ..
    · exact shearing u M L d x
    intro i; exact Stencil.even _ (X.node i.2) L _ _
end Dictionary
end YM.FVA2.Change

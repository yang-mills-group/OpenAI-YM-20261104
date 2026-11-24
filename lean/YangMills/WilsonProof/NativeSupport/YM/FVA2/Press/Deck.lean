import YM.FVA2.Press.Deck
import YM.FVA2.Press.Panels
import YangMills.WilsonProof.NativeSupport.YM.XSpace.OnShell
/-!
# The physical continuation uses the same lift as XSpace.Initialize

Choose the MS deck by the ALLOWED complement corresponding to the fixed real equivariant
sectionMap. This permits verbatim use of XSpace KPos & physical coupling. (Use `Maxwell.reduceEq`
as in the supplied framework.) This file doesn't re-prove any direction computations of that
section, just certifies the choice on MS side is possible. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Press
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Source.Drops Bid Work XSpace
open MS MS.Koszul MS.Cylinder Lab MS.Native MS.Native.Sew MS.Book MS.Local.Physical MS.Rake MS.Lifting MS.Theater
open Maxwell Maxwell.Free
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge} {d:ℕ} {H:Hol G}
local notation "P" => Labels.Pol G
local notation "W" => WickPol G
local notation "µ" => On.lifting
-- needed transfer through real structures: before mixing any labels
variable {v : Labels.Pol G} {w r:ℕ}


-- range in Ambient Law. Can use rank lift per word; no non-unit scalings at this step.
local notation "A" => Allowed G w r
local notation "N" => Null G w r
local notation "γ" => Theater.orbit G
local notation "B" => born G w r
local notation "Q" => portDeck G
lemma level (G:Gauge) (w r:ℕ): (portDeck G).carries w r=born G w r:= by simp [portDeck]
lemma stageF (p:(Q).carries w r): refineF G w r (Resume (Q) w r p)=Resume (Q) w r p:= by
    obtain ⟨x,h⟩:= (level G w r ▸ p.property : p.val∈born G w r); let f:=Resume (Q) w r p; let a:=refineF G w r x; have he: γ f.val = γ a.val := (honor ..).trans h.symm; have H:f=a:= (craftK G w r).injective (Subtype.ext he); change refineF _ _ _ f=f; rw [H]; exact Subtype.ext (congr_arg (µ) (On.lift_recover (reduceEq (x.val))))
theorem film_eq (i:(Q).BIndex w r): film (portDeck G) i (h:=w) (r:=r)= µ (reduceEq (film (portDeck G) i (h:=w))) := by
    let p:= Resume (portDeck G) w r (Module.finBasis ℝ _ i); exact congr_arg Subtype.val (stageF (w:=w) (r:=r) (Module.finBasis ℝ _ i)).symm
end YM.FVA2.Press

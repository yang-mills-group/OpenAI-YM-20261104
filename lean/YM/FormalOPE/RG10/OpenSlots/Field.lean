import YM.FormalOPE.RG10.MarkovChain.Scope
/-!
 # Coordinates on all inversion link orbits, compared to the currently integrated slice.
 The truss pins only the interior forest at a stage (except at the terminal step).
 Use these coordinates for representing output polynomials on OFF-truss values as needed.
 No IR claims.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.OpenSlots
open MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side}
variable {L:Fabric G n}
abbrev Flats (G: Gauge)(n: Side):= Direction G (Orb.OEdge n)
 def castAt (T:Cloth L) : Field T.choose →ₗ[ℝ] Flats G n := LinearMap.pi fun i=> if h:¬ T.choose.Branch (Sum.inl i) then LinearMap.proj (Subtype.mk (Sum.inl i) h) else 0
lemma accord_top (T:Cloth L)(u:Field T.choose) : expLinks G (Orb.OEdge n) (castAt T u)= L.principal (T.choose.board (expLinks G _ u)):= by rw [Line.portrayed]; ext1 i; by_cases h:T.choose.Branch (Sum.inl i) <;> simp [castAt, Line.headline,h,expLinks]; rfl
section
variable {S: StepData c f} {L: Fabric G c} {P:Inside S.ratio}
variable {H:S.patch.Branches S.kernel G} {hf:_root_.Even f.val}{t:S.Choices} {C:Cloth L}
local notation "T0"=> Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
local notation "d"=> Pathway (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "Ω"=> Field (Cloth.choose T0)
local notation "F"=> Cross (G:=G) S P
local notation "B"=> Field C.choose
 def extend (P:Inside S.ratio): Cross (G:=G) S P→ₗ[ℝ] Flats G f:= LinearMap.pi fun i=> if h:P.Innate i then 0 else LinearMap.proj (Subtype.mk i h : Index S P)
lemma moored (x:F)(y:B): castAt T0 (d (x,y))=extend P x:= by
 ext1 i; by_cases h:P.Innate i
 · have h' : (T0).choose.Branch (.inl i):= ((P.inner_only H t hf C.choose i).mpr h); simp [castAt,h,extend,h']
 have he: ¬ (T0).choose.Branch (.inl i):= h ∘ ((P.inner_only H t hf C.choose i).mp)
 simp [castAt,h,extend,he]; rfl
 def spool : Ω→ₗ[ℝ] B:= LinearMap.snd ℝ F B ∘ₗ (d).symm.toLinearMap
local notation "π" => spool (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
@[simp] lemma spinning (x y): π (d (x,y))=y:= by simp [spool]
 def exchange : Ω→ₗ[ℝ] F × Flats G c := ((LinearMap.fst ℝ F B) ∘ₗ (d).symm.toLinearMap).prod (castAt C ∘ₗ π)
local notation "κ"=> exchange (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
@[simp] lemma trade (x y): κ (d (x,y))=(x,castAt C y):= by simp [exchange]
 def blankRight (P:Inside S.ratio) : Cross (G:=G) S P × Flats G c →ₗ[ℝ] Flats G f:= extend (S:=S) P ∘ₗ LinearMap.fst _ _ _ -- P implicit notation wrong bind
end
end YM.FormalOPE.RG10.OpenSlots

import YM.Integration.WilsonOlderFreshSoftSocketPhases
import YM.Integration.WilsonReceivedCanonicalSocketLevels

/-! Every actual occupied and proper face of the physical K-planted board, on the genuine geometric Era, with a single measured product of signed original socket charges. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketFaces
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonThermometerDeclaredSeeds (Choice)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketInitial (charge)
open WilsonOlderFreshSoftSocketGeometry (row)
open WilsonCoeffUV.Winding
open private dark from YM.Integration.IndependentSourcePathFamily
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(d:I→ℕ)(b:Columns R d)
  {D:I→ℕ}(κ:(i:I)→Knob (D i))(pt:I→Chamber){N per K:ℕ}
local notation "P_" => WilsonOlderFreshSoftFigures.seed R D d b κ pt
local notation "part_" => IndependentSourcePathFamily.single
local notation "figure_" => WilsonOlderFreshSoftFigures.stencil R D d b κ pt
abbrev RawChoice:= (i:I)→Choice R d i
def raw (q:RawChoice R d):Outerm G D:=independent (WilsonOlderFreshSoftSocketPole.raw R d κ pt q)
variable (z:I → Cover)
private theorem legalF:Eu d (figure_ z):=legal _ _ fun _ _=>Nat.le_add_left _ _
private theorem legalQ (q:RawChoice R d):Eu d (raw R d κ pt q z):=
  legal _ _ fun _ _=>Nat.le_add_left _ _

omit [Fintype I] in
private theorem seat (j:I)(c:Choice R d j):Auth 0 (row R d κ pt j c (z j)):=by
  let g:=WilsonReceivedCanonicalVerseBasis.basis R d κ pt j c
  exact certified D j (colour g.path g.color 1 Complex.reCLM)
    (OriginalMarkedSourceComet.invariant _ _ _ _) (κ j) (pt j) g.rank 0 (by omega) (z j)

private theorem registered (live:K≤N)(i:I)(L:ℂ→L[ℝ]ℝ)(A:Case D)(n:Side):
    L 1 • readO A (part_ P_ i (z i)) n=
      ∑c:Choice R d i,L (charge R d b N per K i c) • readO A (row R d κ pt i c (z i)) n:=by
  classical
  have filed:=legalF R d b κ pt z {i}
  rw [WilsonOlderFreshSoftFigures.stencil,IndependentSourcePathFamily.singleton] at filed
  have h:=congrArg (fun E=>readO A E n) (WilsonOlderFreshSoftSocketInitial.original R d b κ pt (per:=per) live L i (z i))
  rw [read_rho _ _ _ filed] at h
  have paid (c:Choice R d i):Auth 0 (L (charge R d b N per K i c) • row R d κ pt i c (z i)):=
    (seat R d κ pt z i c).tuft ((L (charge R d b N per K i c)) • ContinuousLinearMap.id ℝ _)
  rw [read_Sum A n (fun c _=>paid c)] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro c _
  exact read_rho _ _ _ (seat R d κ pt z i c) _

variable (S:Finset I)
def fill (q:(i:S)→Choice R d i)(i:I):Choice R d i:=if h:i∈S then q ⟨i,h⟩ else .inl ()
def cash (N per K:ℕ)(q:(i:S)→Choice R d i):ℂ:=∏i:S,charge R d b N per K i (q i)
def print (q:(i:S)→Choice R d i):Era G (Pen D S):=levelsO (raw R d κ pt (fill R d S q) z) S

private theorem actual (q:(i:S)→Choice R d i)(A:Case D)(n:Side):
    readO A (print R d κ pt z S q) n=∏i:S,readO A (row R d κ pt i (q i) (z i)) n:=by
  rw [print,WilsonReceivedCanonicalSocketLevels.original _ (legalQ R d κ pt z _) (dark _ _) A n S,
    ←Finset.prod_coe_sort S]
  apply Finset.prod_congr rfl
  intro i _
  unfold raw
  rw [IndependentSourcePathFamily.singleton]
  unfold IndependentSourcePathFamily.single
  rw [Fintype.sum_unique]
  change readO A (row R d κ pt i (fill R d S q i) (z i)) n=_
  rw [show fill R d S q i=q i from dif_pos i.property]

theorem original (live:K≤N)(L:ℂ→L[ℝ]ℝ):
    L 1 • levelsO (figure_ z) S=
      ∑q:(i:S)→Choice R d i,L (cash R d b S N per K q) • print R d κ pt z S q:=by
  classical
  have hf:=placedO _ (legalF R d b κ pt z) S
  have hq (q:(i:S)→Choice R d i):Auth (mass d S) (print R d κ pt z S q):=
    placedO _ (legalQ R d κ pt z _) S
  have hm (q:(i:S)→Choice R d i):Auth (mass d S) (L (cash R d b S N per K q) • print R d κ pt z S q):=
    (hq q).tuft ((L (cash R d b S N per K q)) • ContinuousLinearMap.id ℝ _)
  have left:Auth (mass d S) (L 1 • levelsO (figure_ z) S):=hf.tuft ((L 1) • ContinuousLinearMap.id ℝ (Pen D S))
  have right:Auth (mass d S) (∑q:(i:S)→Choice R d i,L (cash R d b S N per K q) • print R d κ pt z S q):=Auth.sum fun q _=>hm q
  apply read_ext _ _ left right
  intro A n
  rw [read_rho _ _ _ hf,read_Sum A n (fun q _=>hm q),
    WilsonReceivedCanonicalSocketLevels.original _ (legalF R d b κ pt z) (dark _ _) A n S,
    ←Finset.prod_coe_sort S]
  have h:=WilsonOlderFreshSoftSocketPhases.original
    (fun i:S=>readO A (part_ P_ i (z i)) n)
    (fun (i:S) c=>readO A (row R d κ pt i c (z i)) n)
    (fun (i:S) c=>charge R d b N per K i c)
    (fun i L=>registered R d b κ pt z live i L A n) L
  unfold WilsonOlderFreshSoftFigures.stencil
  simp_rw [IndependentSourcePathFamily.singleton]
  rw [h]
  apply Finset.sum_congr (by ext q;simp)
  intro q _
  rw [read_rho _ _ _ (hq q),actual]
  rfl

end YM.Integration.WilsonOlderFreshSoftSocketFaces
end

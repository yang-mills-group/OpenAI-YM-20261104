import YM.Integration.WilsonSeparatedPrefixCanonicalPublic

/-! The exact cutoff-transport value of each of the reported coefficients, on the same group
field as the full marked public reading. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalDensity
open Function Finset Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.GermGraph Marker MergeProof MergeProof.Accent RG05Readout RG05Readout.Address RG12 Push Push.Local PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] {J:Census I} (R:Run G)
variable {N p f:ℕ} (live:f≤N) (d:I → ℕ) (o support:I → Site (R.family.side f p))
  (q:(v:I) → Coefficient (R.family.labels.level (d v)) (R.family.side f p))
local notation "P" => R.family.path.rep N p f
variable {φ:I → Config G (R.family.side f p) → ℂ}
  {k:I → Box (R.family.side f p) → Config G (R.family.side f p) → ℂ}
  {X:Config G (R.family.side f p) → Poly J} {w:I → ℝ} {a b κ:ℝ} {B:I → ℝ}
include live in
theorem original (stock:Served (P) φ k X support w a b)
    (soft:∀v,φ v=(q v).exponentialEntry (o v) (R.family.localSection (d v)) (P))
    (hard:∀v,k v=profile (P).activities (q v).forced)
    (fee:∀v,(q v).remBound (o v) (P) κ (B v)) (v:I) (U:Config G (R.family.side f p)):
    (q v).density (o v) (R.family.localSection (d v)) (P) U=(X U).part (J.fire v):=by
  rw [funext soft,funext hard] at stock
  exact (stock.relay (fun i=>rem_dominated (fee i)) ((R.T.sticks N p).prices f (Nat.zero_le f) live).1.valid.labels U).1 v |>.symm

theorem with_cutoff (stock:Served (P) φ k X support w a b)
    (soft:∀v,φ v=(q v).exponentialEntry (o v) (R.family.localSection (d v)) (P))
    (hard:∀v,k v=profile (P).activities (q v).forced)
    (fee:∀v,(q v).remBound (o v) (P) κ (B v))
    (W:I → Config G (R.family.side N p) → ℂ)
    (law:∀s:J.Mode,∀U,(X U).part s=(P).eval U • actualTransport R.family (N:=N)
       (fun V=>∏i∈s.val,W i V) live U) (v:I) (U:Config G (R.family.side f p)):
    (q v).density (o v) (R.family.localSection (d v)) (P) U
      =(P).eval U • actualTransport R.family (N:=N) (W v) live U:=by
  rw [original R live d o support q stock soft hard fee,law]
  congr 2
  funext V
  simp [Census.fire]

end YM.Integration.WilsonSeparatedPrefixCanonicalDensity
end

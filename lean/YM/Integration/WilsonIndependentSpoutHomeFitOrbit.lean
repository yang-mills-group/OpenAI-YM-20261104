import YM.Integration.WilsonIndependentSpoutRosterCashier
import YM.Integration.WilsonIndependentSpoutVisitFootprint
import YM.Integration.WilsonIndependentMatchedOpeningHomes

/-! Each fitted field keeps its own engineering grade, reporting home and original filed coefficients on the prescribed finite orbit. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutHomeFitOrbit
open Lattice Wilson Tree RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus Precision Exterior Gauge
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Shard
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Bank
open WilsonCoeffUV.StableStrip WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Ticket
open PhysicalNext PhysicalNext.Repeat Next.Foundations
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit WilsonIndependentRawRosterWord
open WilsonIndependentMatchedOpeningComposite (branch)
open WilsonIndependentMatchedOpeningHomes (rent name site pitch)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentSpoutRosterCashier (complex)
open scoped BigOperators Classical
variable {G:Gauge}{n k u e:ℕ}
local notation "C" => Credit.leanC
variable (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(K:KernelChoices)
    (Y:Program K)(Z:∀P:Patch,P.Branches K G)(V:XSpace.Run)(ell j:ℕ)(ha:0<ell)(late:4≤j)
    (land:Requests ell → Levels G)(first:Requests ell → ℕ)(F:Tent (M V ell))(P:ℕ)
variable (kind:Fin (n+1)→Bool)(d D:Fin (n+1)→ℕ)(cut:∀i,d i<D i)
    (φ:Requests ell → (i:Fin (n+1)) → Rarity (D i))(x:Requests ell → Fin (n+1) → ℝ)(y:Requests ell→ℝ)(o:Requests ell → Fin (n+1)→CellR)

abbrev Labels:=(i:Fin (n+1)) → (R.family.labels.level (d i)).Index
abbrev Visits (w:Requests ell):=(i:Fin (n+1))→WilsonIndependentMatchedOpeningHomes.Visits R d D (φ w) (x w) (y w) (o w) i
def load (w:Requests ell)(c:(i:Fin (n+1))→Verse (R.family.labels.level (d i)))(a:Fin (n+1)→ℝ)(z:Visits R ell d D φ x y o w):Blue.Cost:=
  ∏i,rent R d D cut c (φ w) (x w) (y w) (o w) a d i (z i)
def filmAt (sample:Requests ell→Sample 2)(w:Requests ell)(z:Visits R ell d D φ x y o w):PowerSeries ℂ:=
  Bare.normalized (W.tree (sample w).F.p) G (film R W kind d (name R d D (φ w) (x w) (y w) (o w) z)
    (sample w) (site R d D (φ w) (x w) (y w) (o w) z) (branch n id))

def pointsAt (ρ:Requests ell → Room)(w:Requests ell):Option (Visits R ell d D φ x y o w) → Fin (n+1) → Cover
  | none=>fun _=>WilsonIndependentSpoutVisitFootprint.anchor (ρ w)
  | some z=>site R d D (φ w) (x w) (y w) (o w) z

theorem extent (ρ:Requests ell → Room)(live:∀w i,0<x w i)(w:Requests ell)(z:Option (Visits R ell d D φ x y o w)):
    WilsonIndependentRawRosterBudget.span (ρ w) (pointsAt R ell d D φ x y o ρ w z) (branch n id)≤
      ∑i,(dist (ρ w) ((y w/x w i) • (o w i).val) + ((φ w i).radius+x w i)/(x w i)):=by
  rw [WilsonIndependentMatchedOpeningExtent.gather]
  apply Finset.sum_le_sum
  intro i _
  cases z with
  | some z=>exact (dist_triangle _ _ _).trans (add_le_add le_rfl (WilsonIndependentMatchedOpeningExtent.near (z i) (live w i)))
  | none=>
    have rad:=(φ w i).markG
    have one:1 ≤ ((φ w i).radius+x w i)/(x w i):=by
      apply (le_div_iff₀ (live w i)).mpr;linarith
    exact (WilsonIndependentSpoutVisitFootprint.close (ρ w)).trans (one.trans (le_add_of_nonneg_left dist_nonneg))

theorem original (simple:G.Simple)(O:ChartRatio G)(ratio:LocalRatio O)(γ:ℝ)(ap:Requests ell→ℝ)
    (priced:WilsonIndependentPublicRosterBook.Priced R W K Y Z V ell j ha late P γ ap F)
    (read:∀f,WilsonIndependentNotebookMarkedEdge.Reads (S V ell ha j late) Y Z F land first P f)
    (sample:Requests ell→Sample 2)(ρ:Requests ell→Room)(c₀:ℝ)(board:∀w,(sample w).F=V.step w.val)
    (live:∀w i,0<x w i)
    (reach:∀w,∑i,(dist (ρ w) ((y w/x w i) • (o w i).val) + ((φ w i).radius+x w i)/(x w i))≤ap w)(small:0<c₀)
    (safe:((S V ell ha j late).dialect Y G Z (sheet F)).cushion c₀ ρ)(q:ℕ)(hq:q≤P):
    ∃r:ℕ,∃H₀:ℝ,0≤H₀ ∧ ∀(w:Requests ell)(c:(i:Fin (n+1))→Verse (R.family.labels.level (d i)))(a:Fin (n+1)→ℝ)
      (own:(i:Fin (n+1))→Rails (d i) k u e)(X:(i:Fin (n+1))→CutsP (hol G) ((deck (G:=G) d D cut) i).ans
        ((deck (G:=G) d D cut) i).path (own i) C C C C)(α:(i:Fin (n+1))→Alma (R.family.labels.level (d i))→ℝ)
      (Z₀ B₀:Fin (n+1)→Credit)(m b N:ℕ), pitch d D cut own X=x w →
      WilsonPositionProgramTrialHomeFaces.Filed R W d D cut kind own c α Z₀ B₀ m b N X →
      ‖PowerSeries.coeff q (∑z:Visits R ell d D φ x y o w,complex (load R ell d D cut φ x y o w c a z)*
          filmAt R W ell kind d D φ x y o sample w z)-
        PowerSeries.coeff q (complex (WilsonIndependentSpoutDoseBoundary.measure (land w) O (first w+M V ell w)
          (∑i,d i) (first w+M V ell w) (first w) (MassP G ℝ n
          (WilsonIndependentMatchedOpeningHomes.raw d D cut (φ w) (y w) (o w) a own X))))‖≤
      (∑z:Visits R ell d D φ x y o w × Fin (q+1),‖PowerSeries.coeff z.2.val (load R ell d D cut φ x y o w c a z.1)‖) *
       (H₀*(1+ap w+Real.log ((V.step w.val).p.side.val:ℝ))^r*((V.step w.val).p.side.val:ℝ)^(-(γ/2))):=by
  let B (w:Requests ell):=Option (Visits R ell d D φ x y o w)
  letI (w:Requests ell):Nonempty (B w):=⟨none⟩
  have inside (w:Requests ell)(z:B w):WilsonIndependentRawRosterBudget.span (ρ w) (pointsAt R ell d D φ x y o ρ w z)
      (branch n id)≤ap w:=(extent R ell d D φ x y o ρ live w z).trans (reach w)
  obtain ⟨r,H₀,pos,cash⟩:=WilsonIndependentSpoutRosterCashier.original R W K Y Z V ell j ha late land first F P
    (fun _:Labels R d=>kind) d (fun t=>t) cut (branch n id) sample (pointsAt R ell d D φ x y o ρ) (fun w _=>ρ w)
    simple O ratio γ ap priced read c₀ board inside small (fun _=>safe) q hq
  refine ⟨r,H₀,pos,?_⟩
  intro w c a own X α Z₀ B₀ m b N homes file
  let label (z:Visits R ell d D φ x y o w):Labels R d:=name R d D (φ w) (x w) (y w) (o w) z
  have cap (z:Visits R ell d D φ x y o w):(branch n id).accounts (degree R d (label z)) ≤ ∑i,d i:=by
    rw [WilsonIndependentMatchedOpeningComposite.ranks]
    exact Finset.sum_le_sum fun i _=>valence_cap _ ((z i).2)
  have booked:=WilsonIndependentMatchedOpeningHomes.original R W kind d D cut c (φ w) (y w) (o w) a own X α Z₀ B₀ m b N file
  dsimp only at booked
  rw [homes] at booked
  exact cash w (Visits R ell d D φ x y o w) some label (load R ell d D cut φ x y o w c a) (∑i,d i) cap _ booked

end YM.Integration.WilsonIndependentSpoutHomeFitOrbit

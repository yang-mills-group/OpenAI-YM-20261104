import YM.Integration.WilsonIndependentSpoutHomeFitOrbit
import YM.Integration.WilsonIndependentSpoutVisitPrice

/-! The complete finite Wilson comparison charges the authentic single-arm profile price once on each enrolled leaf. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutHomePaidOrbit
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

open WilsonIndependentSpoutHomeFitOrbit (Visits load filmAt pointsAt)
theorem profile (w:Requests ell)(c:(i:Fin (n+1))→Verse (R.family.labels.level (d i)))(a M₀:Fin (n+1)→ℝ)
    (paid:∀i,Amplitude (φ w i) (M₀ i))(live:∀i,0<x w i)(fine:∀i,x w i≤1)(q:ℕ):
    (∑z:WilsonIndependentSpoutHomeFitOrbit.Visits R ell d D φ x y o w × Fin (q+1),‖PowerSeries.coeff z.2.val (load R ell d D cut φ x y o w c a z.1)‖) ≤
    ∏i,WilsonIndependentMatchedOpeningMenu.charge R (cut i) q (d i) (a i • c i) (φ w i) (x w i) (y w) (M₀ i):=by
  rw [Fintype.sum_prod_type]
  simp_rw [WilsonIndependentSpoutVisitPrice.thermal]
  have h:=WilsonIndependentMatchedOpeningMenu.original R d D cut (fun i=>a i • c i) (φ w) (x w)
    (fun _=>y w) (o w) d M₀ paid live fine q
  dsimp only at h
  apply le_trans _ h
  apply le_of_eq
  refine Finset.sum_congr ?_ ?_
  · ext z; simp only [Finset.mem_univ]
  intro z _
  congr 1

theorem settled {A s t L:ℝ}(b:A ≤ s * L)(p:s ≤ t)(hL:0 ≤ L):A ≤ t * L:=b.trans (mul_le_mul_of_nonneg_right p hL)

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
      (Z₀ B₀:Fin (n+1)→Credit)(m b N:ℕ)(budget:Fin (n+1)→ℝ), (∀i,Amplitude (φ w i) (budget i)) →
      pitch d D cut own X=x w →
      WilsonPositionProgramTrialHomeFaces.Filed R W d D cut kind own c α Z₀ B₀ m b N X →
      ‖PowerSeries.coeff q (∑z:WilsonIndependentSpoutHomeFitOrbit.Visits R ell d D φ x y o w,complex (load R ell d D cut φ x y o w c a z)*
          filmAt R W ell kind d D φ x y o sample w z)-
        PowerSeries.coeff q (complex (WilsonIndependentSpoutDoseBoundary.measure (land w) O (first w+M V ell w)
          (∑i,d i) (first w+M V ell w) (first w) (MassP G ℝ n
          (WilsonIndependentMatchedOpeningHomes.raw d D cut (φ w) (y w) (o w) a own X))))‖≤
      (∏i,WilsonIndependentMatchedOpeningMenu.charge R (cut i) q (d i) (a i • c i) (φ w i) (x w i) (y w) (budget i)) *
       (H₀*(1+ap w+Real.log ((V.step w.val).p.side.val:ℝ))^r*((V.step w.val).p.side.val:ℝ)^(-(γ/2))) :=by
  obtain ⟨r,H₀,nn,actual⟩:=WilsonIndependentSpoutHomeFitOrbit.original (k:=k) (u:=u) (e:=e)
    R W K Y Z V ell j ha late land first F P kind d D cut φ x y o simple O ratio γ ap priced read
    sample ρ c₀ board live reach small safe q hq
  refine ⟨r,H₀,nn,?_⟩
  intro w c a own X α Z₀ B₀ m b N budget paid homes file
  have fine (i:Fin (n+1)):x w i≤1:=by
    rw [←homes]
    exact pace_le _ (Nat.le_add_right ..)
  apply settled (actual w c a own X α Z₀ B₀ m b N homes file)
    (profile R ell d D cut φ x y o w c a budget paid (live w) fine q)
  have inc:0≤ap w:=(WilsonIndependentRawRosterBudget.extent (ρ w) (pointsAt R ell d D φ x y o ρ w none)
    (branch n id)).trans ((WilsonIndependentSpoutHomeFitOrbit.extent R ell d D φ x y o ρ live w none).trans (reach w))
  have side:1≤((V.step w.val).p.side.val:ℝ):=by exact_mod_cast (V.step w.val).p.side.pos
  have log:=Real.log_nonneg side
  positivity

end YM.Integration.WilsonIndependentSpoutHomePaidOrbit

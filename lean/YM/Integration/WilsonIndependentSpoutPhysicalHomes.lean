import YM.Integration.WilsonIndependentSpoutPhysicalClock
import YM.Integration.WilsonIndependentSpoutPhysicalVisits
import YM.Integration.WilsonIndependentSpoutHomePaidOrbit
import YM.Integration.WilsonOriginalPublicNodalSafeCopies

/-! Sum the submitted ordinary group field with its own home tariff on the previously approved physical variable-block circuit. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.Integration.WilsonIndependentSpoutPhysicalHomes
open Lattice Wilson Tree RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus Precision Exterior Gauge
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Shard
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Bank
open WilsonCoeffUV.StableStrip WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Ticket
open PhysicalNext PhysicalNext.Repeat Next.Foundations
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration
open WilsonIndependentRawRosterWord
open WilsonIndependentMatchedOpeningComposite (branch)
open WilsonIndependentMatchedOpeningHomes (rent name site pitch)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentSpoutRosterCashier (complex)
open scoped BigOperators Classical ENNReal NNReal
open WilsonIndependentSpoutPhysicalClock (station)
open WilsonIndependentSpoutPhysicalOrbit (amount)
variable {G:Gauge}{J:Type}{n k u e:ℕ}
local notation "C" => Credit.leanC
variable (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(V:XSpace.Run)
    (m j:J → ℕ)(w:J → ℕ → ℕ)(blocks:∀v l,(R.family.S.block (m v+l)).val=V.ratio^(w v l))
    (Z:∀p:Patch,p.Branches R.family.path.levels.clock.kernel G){p:ℕ}{F:Tent j}
    (issued:WilsonOriginalPublicNodalPhysicalMerBook.Issued R V m j w blocks Z p F)
local notation "sky" => (WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks).dialect
    (Oracle.books R.family.path.levels.clock.kernel) G Z (sheet F)
variable (kind:Fin (n+1)→Bool)(d D:Fin (n+1)→ℕ)(cut:∀i,d i<D i)
    (φ:J → (i:Fin (n+1)) → Rarity (D i))(x:J → Fin (n+1) → ℝ)(y:J→ℝ)(o:J → Fin (n+1)→CellR)

abbrev Labels:=(i:Fin (n+1)) → (R.family.labels.level (d i)).Index
abbrev Visits (w:J):=(i:Fin (n+1))→WilsonIndependentMatchedOpeningHomes.Visits R d D (φ w) (x w) (y w) (o w) i
def load (w:J)(c:(i:Fin (n+1))→Verse (R.family.labels.level (d i)))(a:Fin (n+1)→ℝ)(z:Visits R d D φ x y o w):Blue.Cost:=
  ∏i,rent R d D cut c (φ w) (x w) (y w) (o w) a d i (z i)
def filmAt (sample:J→Sample 2)(w:J)(z:Visits R d D φ x y o w):PowerSeries ℂ:=
  Bare.normalized (W.tree (sample w).F.p) G (film R W kind d (name R d D (φ w) (x w) (y w) (o w) z)
    (sample w) (site R d D (φ w) (x w) (y w) (o w) z) (branch n id))

def pointsAt (ρ:J → Room)(w:J):Option (Visits R d D φ x y o w) → Fin (n+1) → Cover
  | none=>fun _=>WilsonIndependentSpoutVisitFootprint.anchor (ρ w)
  | some z=>site R d D (φ w) (x w) (y w) (o w) z

theorem extent (ρ:J → Room)(live:∀w i,0<x w i)(w:J)(z:Option (Visits R d D φ x y o w)):
    WilsonIndependentRawRosterBudget.span (ρ w) (pointsAt R d D φ x y o ρ w z) (branch n id)≤
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


theorem profile (w:J)(c:(i:Fin (n+1))→Verse (R.family.labels.level (d i)))(a M₀:Fin (n+1)→ℝ)
    (paid:∀i,Amplitude (φ w i) (M₀ i))(live:∀i,0<x w i)(fine:∀i,x w i≤1)(q:ℕ):
    (∑z:Visits R d D φ x y o w × Fin (q+1),‖PowerSeries.coeff z.2.val (load R d D cut φ x y o w c a z.1)‖) ≤
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


variable (sample:J → Sample 2)(ρ:J → Room)(ip:J → ℕ)(H c₀:ℝ)

def quoted (q:ℕ)(stop:Choice j)(tail:J → ℝ)(r:ℕ)(H₀:ℝ):Prop:=
  ∀(v:J)(c:(i:Fin (n+1)) → Verse (R.family.labels.level (d i)))(a:Fin (n+1) → ℝ)
    (own:(i:Fin (n+1)) → Rails (d i) k u e)(X:(i:Fin (n+1)) → CutsP (hol G) ((deck (G:=G) d D cut) i).ans
      ((deck (G:=G) d D cut) i).path (own i) C C C C)(α:(i:Fin (n+1)) → Alma (R.family.labels.level (d i)) → ℝ)
    (Z₀ B₀:Fin (n+1) → Credit)(m₀ b N:ℕ)(cap:Fin (n+1) → ℝ), (∀i,Amplitude (φ v i) (cap i)) →
    pitch d D cut own X=x v → WilsonPositionProgramTrialHomeFaces.Filed R W d D cut kind own c α Z₀ B₀ m₀ b N X →
    ‖PowerSeries.coeff q (∑z:Visits R d D φ x y o v,complex (load R d D cut φ x y o v c a z)*
        filmAt R W kind d D φ x y o sample v z)-
      PowerSeries.coeff q (complex (WilsonIndependentSpoutDoseBoundary.measure R.family.path.levels R.metals.O (m v+j v)
        (∑i,d i) (m v+j v) (station j m stop v) (MassP G ℝ n
        (WilsonIndependentMatchedOpeningHomes.raw d D cut (φ v) (y v) (o v) a own X))))‖ ≤
      (∏i,WilsonIndependentMatchedOpeningMenu.charge R (cut i) q (d i) (a i • c i) (φ v i) (x v i) (y v) (cap i)) *
        (H₀*(amount R V m j w ip H v)^r*tail v)

private theorem collect (simple:G.Simple)(live:∀v i,0<x v i)(q:ℕ)(stop:Choice j)(tail:J → ℝ)(nn:∀v,0≤tail v)
    (r:ℕ)(H₀:ℝ)(hn:0≤H₀)(paid:WilsonIndependentSpoutPhysicalVisits.price R W V m j w (fun _:Labels R d=>kind)
      d (fun l=>l) cut (branch n id) (pointsAt R d D φ x y o ρ) sample ip H q stop tail r H₀):
    quoted (k:=k) (u:=u) (e:=e) R W V m j w kind d D cut φ x y o sample ip H q stop tail r H₀:=by
  intro v c a own X α Z₀ B₀ m₀ b N budget funded homes file
  let label (z:Visits R d D φ x y o v):Labels R d:=name R d D (φ v) (x v) (y v) (o v) z
  have cap (z:Visits R d D φ x y o v):(branch n id).accounts (degree R d (label z)) ≤ ∑i,d i:=by
    rw [WilsonIndependentMatchedOpeningComposite.ranks]
    exact Finset.sum_le_sum fun i _=>valence_cap _ ((z i).2)
  have booked:=WilsonIndependentMatchedOpeningHomes.original R W kind d D cut c (φ v) (y v) (o v) a own X α Z₀ B₀ m₀ b N file
  dsimp only at booked
  rw [homes] at booked
  let term:=load R d D cut φ x y o v c a
  have whole:=WilsonIndependentSpoutPhysicalClock.book R W m j d cut (branch n id) simple v stop
    (fun _:Visits R d D φ x y o v=>kind) label (fun z=>pointsAt R d D φ x y o ρ v (some z)) term
    (∑i,d i) cap _ booked
  have cost:=paid v (Visits R d D φ x y o v) some label (fun z=>complex (term z))
  rw [whole] at cost
  have norm(u:ℝ):‖algebraMap ℝ ℂ u‖=‖u‖:=Complex.norm_real u
  simp only [complex,PowerSeries.coeff_map,norm] at cost
  have fine (i:Fin (n+1)):x v i≤1:=by
    rw [←homes]
    exact pace_le _ (Nat.le_add_right ..)
  apply WilsonIndependentSpoutHomePaidOrbit.settled cost
  · exact profile R d D cut φ x y o v c a budget funded (live v) fine q
  · exact mul_nonneg (mul_nonneg hn (pow_nonneg (zero_le_one.trans
      (WilsonPositionProgramInfraredMeter.lower R V m j w ip H v)) r)) (nn v)

variable (simple:G.Simple)(side:∀v,TopF (WilsonPositionProgramInfraredCircuit.count V j w) v=(sample v).F.p.side)
    (live:∀v i,0<x v i)
    (homes:∀v,1+∑i,(dist (ρ v) ((y v/x v i) • (o v i).val)+((φ v i).radius+x v i)/(x v i)) ≤ amount R V m j w ip H v)
    (clear:0<c₀)(safe:((WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks).dialect
      (Oracle.books R.family.path.levels.clock.kernel) G Z (sheet F)).cushion c₀ ρ)
include issued simple side live homes clear safe

theorem stopped (q:ℕ)(hq:q ≤ p)(stop:Choice j):
    ∃r:ℕ,∃H₀:ℝ,0≤H₀ ∧ quoted (k:=k) (u:=u) (e:=e) R W V m j w kind d D cut φ x y o sample ip H
      q stop (fun v=>(sky).modifyErr 0 1 (1/2) stop v) r H₀:=by
  letI (v:J):Nonempty (Option (Visits R d D φ x y o v)):=⟨none⟩
  have inside (v:J)(z:Option (Visits R d D φ x y o v)):1+WilsonIndependentRawRosterBudget.span (ρ v)
    (pointsAt R d D φ x y o ρ v z) (branch n id) ≤ amount R V m j w ip H v:=
    (add_le_add (le_refl 1) (extent R d D φ x y o ρ live v z)).trans (homes v)
  obtain ⟨r,H₀,hn,cash⟩:=WilsonIndependentSpoutPhysicalVisits.stopped R W V m j w blocks Z issued
    (fun _:Labels R d=>kind) d (fun l=>l) cut (branch n id) (pointsAt R d D φ x y o ρ) sample
    (fun v _=>ρ v) ip H c₀ simple side inside clear (fun _=>safe) q hq stop
  refine ⟨r,H₀,hn,collect R W V m j w kind d D cut φ x y o sample ρ ip H simple live q stop _ ?_ r H₀ hn cash⟩
  intro v
  apply add_nonneg ((sky).transfer_pos v).le
  exact inv_nonneg.mpr (Real.rpow_nonneg ((sky).hl _).le _)

theorem terminal (q:ℕ)(hq:q ≤ p):
    ∃r:ℕ,∃H₀:ℝ,0≤H₀ ∧ quoted (k:=k) (u:=u) (e:=e) R W V m j w kind d D cut φ x y o sample ip H
      q (WilsonIndependentRawPeriodPower.terminal j) (fun v=>(sky).P v ^ (-(1/4:ℝ))) r H₀:=by
  letI (v:J):Nonempty (Option (Visits R d D φ x y o v)):=⟨none⟩
  have inside (v:J)(z:Option (Visits R d D φ x y o v)):1+WilsonIndependentRawRosterBudget.span (ρ v)
    (pointsAt R d D φ x y o ρ v z) (branch n id) ≤ amount R V m j w ip H v:=
    (add_le_add (le_refl 1) (extent R d D φ x y o ρ live v z)).trans (homes v)
  obtain ⟨r,H₀,hn,cash⟩:=WilsonIndependentSpoutPhysicalVisits.terminal R W V m j w blocks Z issued
    (fun _:Labels R d=>kind) d (fun l=>l) cut (branch n id) (pointsAt R d D φ x y o ρ) sample
    (fun v _=>ρ v) ip H c₀ simple side inside clear (fun _=>safe) q hq
  refine ⟨r,H₀,hn,collect R W V m j w kind d D cut φ x y o sample ρ ip H simple live q (WilsonIndependentRawPeriodPower.terminal j) _ ?_ r H₀ hn cash⟩
  intro v
  exact Real.rpow_nonneg ((WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks).synchronize v).le _

end YM.Integration.WilsonIndependentSpoutPhysicalHomes

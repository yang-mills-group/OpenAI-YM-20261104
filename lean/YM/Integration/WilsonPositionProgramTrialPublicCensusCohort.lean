import YM.Integration.WilsonPositionProgramTrialPublicCensusReturn
import YM.Integration.WilsonIndependentMatchedPhysicalCohort
import YM.Integration.WilsonPositionProgramTrialHomeFaces

/-! One original K source and one optical buffer pay the signed, ranked physical census on all occupied subfamilies at once. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicCensusCohort
open Precision Function Finset Lattice Laurent Wilson RG Source Labels Marker Tree Exterior PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Soil WilsonCoeffUV.Shard
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.StableStrip WilsonCoeffUV.Power
open RG.Supply Next.Foundations PhysicalNext.Repeat
open WilsonFiniteMarkedHistoryStep
open WilsonOriginalPublicNodalChildSites (digits here)
open WilsonPositionProgramTrialPublicPulse (choices frame sites survey)
open WilsonReceivedCanonicalSocketSeed (contact)
open WilsonPositionProgramTrialPublicGather (gather)
open WilsonPositionProgramTrialPublicOldReturn (portfolio)
open WilsonIndependentMatchedOpeningFiled (planted)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentRawPhysicalFaces (ordered entered)
open WilsonOriginalPhysicalFruitVerse (written)
open WilsonPositionProgramTrialHomeFaces (Filed)
open WilsonMarkedIndependentNormalizedElection (deck)
open PertExtension RegulatorIR RegulatorIR.Cluster XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
open WilsonIndependentMatchedPhysicalReturn (ordinary)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonPositionProgramTrialAccrued (home)

variable {G:Gauge}{n k u e:ℕ}
local notation "Lib" => Fin (n+1)
local notation "C" => Credit.leanC

open WilsonIndependentMatchedPhysicalCohort (Paid)
open WilsonIndependentMatchedBufferGate (first demand distance)
open WilsonIndependentMatchedFiledIncome (charge)
open WilsonIndependentMatchedPhysicalOrdinary (price)
open WilsonPositionProgramTrialPublicCensusReturn (logged)
open WilsonCoeffUV.Bank.Ticket (zz)
variable {Menu:Type*} [Fintype Menu]

def legs (S:Menu→Finset Lib)(size:Menu→ℕ)(idx:∀t,Fin (size t+1)≃S t)(t:Menu)(i:Fin (size t+1)):Lib:=
  idx t i

theorem original (R:Run G)(W:Initialize G)(D d:Lib→ℕ)(cut:∀i,d i<D i)
    (own:∀i,Rails (d i) k u e)(S:Menu→Finset Lib)(size:Menu→ℕ)(idx:∀t,Fin (size t+1)≃S t)
    (α:∀i,Alma (R.family.labels.level (d i))→ℝ)(Z B:Lib→Credit)(cash rate:Menu→Credit)
    (floor:ℕ)(V:Realm G (e+1) C)(low b out:ℕ)(primary:∀t,Fin (size t+1)→Credit)
    (mid last:∀t,(Fin (size t+1)→Bool)→Credit)
    (bought:Paid R W d D cut (fun _=>false) own size (legs S size idx) α Z B cash rate floor V low b out primary mid last)
    (simple:G.Simple)(ratio:LocalRatio R.metals.O)(m K:ℕ)(mature:floor ≤ m)(mk:m ≤ K)
    (host:Menu→ℕ)(tests:∀t,Fin (size t+1)→ℝ)(wage:Lib→ℝ)(depth ε:Menu→ℝ)
    (awake:∀t,floor ≤ host t)(older:∀t,host t ≤ m)(warm:1 ≤ zz R.family.path.levels m)
    (large:∀t,Compar R.family.S (zz R.family.path.levels) (host t) m ≤ depth t)(positive:∀t,0<ε t):
    let Q:=deck (G:=G) d D cut
    let L:=R.family.path.levels
    let leg:=legs S size idx
    let income i:=|WilsonPositionProgramTrialStationHome.chargeAt L (Q i) e (B i) (Z i) m K| *wage i
    let bills t:=WilsonIndependentMatchedBufferSalary.price (cash t) (rate t) (zz L) m (depth t) (tests t) (income∘leg t)
    let w:=demand bills ε
    let U:=first L.S K w
    K ≤ U ∧ L.S.scale U-L.S.scale K ≤ distance w+(if U=K then 0 else Real.log (L.S.block (U-1)).val) ∧
      ∀N N',U ≤ N→U ≤ N'→∀(v:∀i,(R.family.labels.level (d i)).Coeff)(φ:Lib→ℂ→L[ℝ]ℝ),
      (∀i,charge e (written _ (v i) (φ i)) (α i) ≤ wage i)→
      ∃X:∀i,CutsP (hol G) (Q i).ans (Q i).path (own i) C C C C,
        Filed R W d D cut (fun _=>false) own (fun i=>written _ (v i) (φ i)) α Z B m K N X ∧
        ∀t (split:ℕ),host t ≤ split→split ≤ K→∀(fill:∀i,(R.family.labels.level (d i)).Index)
        (F:(i:Lib)→Rarity (D i))(y:ℝ)(o:CellR),
        Bough (Q∘leg t) (fun i=>F (leg t i)) y (depth t) (tests t)→
        response e low (logged R D d m K N (host t) split (S t) fill v φ F y o-
          stopped L R.metals.O (Q∘leg t) (fun i=>F (leg t i))
            (fun i=>home (Q (leg t i)) (X (leg t i))) m K N' (host t) y o)
          (price (Q:=Q∘leg t) (v:=fun i=>own (leg t i)) V (fun i=>X (leg t i)) low b out (host t) m K
            (primary t) (mid t) (last t) (depth t) (tests t)+ε t):=by
  intro Q L leg income bills w U
  obtain ⟨ku,width,ready⟩:=bought m K mature mk host tests wage depth ε awake older warm large positive
  refine ⟨ku,width,?_⟩
  intro N N' un un' v φ fare
  obtain ⟨X,file,table⟩:=ready N N' un un' (fun i=>written _ (v i) (φ i)) fare
  refine ⟨X,file,?_⟩
  intro t split early late fill F y o shape
  letI:Nonempty (S t):=⟨(idx t) 0⟩
  rw [WilsonPositionProgramTrialPublicCensusReturn.quoted R W D d cut own α Z B N m split K (host t)
    early late (ku.trans un) simple ratio fill v φ (S t) (idx t) X file F y o]
  exact (table t).2.2 _ y o shape

end YM.Integration.WilsonPositionProgramTrialPublicCensusCohort
end


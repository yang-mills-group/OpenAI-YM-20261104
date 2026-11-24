import YM.Integration.WilsonSeparatedPrefixMovingFiledApproach
import YM.Integration.WilsonSeparatedPrefixMovingFiledInventory

/-! Previously measured original fields at both cutoffs of one moving Y−ΣcM.
One true exterior profile and one true exterior purse occur on every sheet. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingFiledContrast
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMovingRosterAllFineSeats (Named Elected needed)
open WilsonIndependentMatchedOwnHomeProfile (scaled)
open WilsonIndependentSpoutMasterArms (basis)
open WilsonMarkedIndependentNormalizedElection (normalized)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonMovingForkSharpSections (publicFrame)
open WilsonSeparatedPrefixMovingPinnedPupil (Clear)
open WilsonIndependentMatchedOwnHomeKShell (Coins cost)
open WilsonSeparatedPrefixMovingCorrectedField (full field)
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Next.Foundations WilsonLimitConstruction XSpace
open scoped BigOperators Classical
open WilsonSeparatedPrefixMovingCorrectedSum (sign)
open WilsonSeparatedPrefixMovingFiledInventory (read)
open WilsonSeparatedPrefixMovingFiledApproach (pupil purse)
variable {G:Gauge}{height seats e d:ℕ}{I:Type*}[Fintype I]
local notation "C" => Credit.leanC
local notation "Film" => PowerSeries ℂ
local notation "into" => PowerSeries.map Complex.ofRealHom

def roster {k:ℕ}(F:SealR G)(Q:Fin (k+1) → SealR G):Fin ((k+1)+1) → SealR G:=Fin.cons F Q

def paints {k:ℕ}(F:SealR G)(Q:Fin (k+1) → SealR G)(ψ:Rarity F.D)(φ:Wilt Q):Wilt (roster F Q):=
  Fin.cases ψ φ

def offered {k:ℕ}(F:SealR G)(Q:Fin (k+1) → SealR G)(E:F.Rider)(X:Herit Q):Herit (roster F Q):=
  Fin.cases E X

def axes {k:ℕ}(F:SealR G)(Q:Fin (k+1) → SealR G):Type:=∀i,Alma ((roster F Q i).F)
noncomputable instance {k:ℕ}(F:SealR G)(Q:Fin (k+1) → SealR G):Fintype (axes F Q):=Pi.instFintype

private theorem product (L:Levels G)(O:ChartRatio G)(N m u:ℕ)(up:u ≤ m)(p q:Cost):
    clock L O N m u (p*q)=clock L O N m u p*clock L O N m u q:=by
  induction up using Nat.decreasingInduction with
  | self=>
    have doneAt (x:Cost):clock L O N m m x=x:=by rw [clock,dif_neg (lt_irrefl m)]
    rw [doneAt,doneAt,doneAt]
  | of_succ i hi ih=>
    conv_lhs=>rw [clock,dif_pos hi,ih,map_mul]
    conv_rhs=>rw [clock,dif_pos hi]
    congr 1
    conv_rhs=>rw [clock,dif_pos hi]

theorem common {k:ℕ}(F:SealR G)(Q:Fin (k+1) → SealR G)(R:Realm G (e+1) C)
    (E:F.Rider)(X:Herit Q)(a:axes F Q)(u m N:ℕ)(up:u ≤ m):
    purse (roster F Q) R (offered F Q E X) m u N a=
      clock R.draws R.paid N m u (E (a 0))*clock R.draws R.paid N m u (∏i,X i (a i.succ)):=by
  rw [WilsonSeparatedPrefixMovingFiledApproach.purse,Fin.prod_univ_succ,product R.draws R.paid N m u up];rfl

theorem original (P:Run G)(n:Option I → ℕ)(Q:∀s,Fin (n s+1) → SealR G)(F:SealR G)(e p ex:ℕ)
    (pos:0<p)(gain:2 ≤ F.h+ex)(near:∀s i,Named (publicFrame P) height seats (Q s i))(far:Named (publicFrame P) height seats F)
    (aperture:∀s,needed (F.h+capP (Q s)) 0 p ≤ seats)(reserve:∀s,capP (Q s)+F.h+ex ≤ seats):
    ∃book:Option I → Coins,∀(R:Realm G (e+1) C)(_stock:Elected (publicFrame P) R height seats)
    (_frames:WilsonIndependentCutJoinNativeFrames.Funded (publicFrame P) R height seats)(old t c m K N:ℕ),
    R.anchor ≤ old → old ≤ t → t ≤ c → c ≤ m → m ≤ K → K ≤ N →
    ∀(α:∀s,Wilt (Q s))(ψ₀:Rarity F.D)(X:∀s,Herit (Q s))(E:F.Rider)(r gap:Option I → ℝ)(farGap DF:ℝ)
      (B:∀s,Fin (n s+1) → ℝ)(Φ:Rarity d)(y amp:ℝ)(o:CellR)(ω:Fin 0 → YForest G),
    let ψ:=scaled ψ₀ (paceT R.draws.S m t) (pace_pos ..)
    (∀s,Clear R (Q s) F (α s) ψ old t c m (r s) (gap s) farGap DF (B s)) → Amplitude Φ amp →
    ∀(ρ:ℝ)(coef:I → Film),
    let U:=fun L s=>full R (roster F (Q s)) (paints F (Q s) ψ₀ (α s)) (offered F (Q s) E (X s)) Φ y o t m c old L N ρ
    let posFee:=fun s (a:axes F (Q s))=>purse (roster F (Q s)) R (offered F (Q s) E (X s)) m old N a
    let native:=fun u s (a:axes F (Q s))=>field R (roster F (Q s)) (paints F (Q s) ψ₀ (α s))
      (WilsonIndependentSpoutMasterArms.basis (roster F (Q s)) a) u Φ y o t m c old K N ρ ω
    let bill:=fun s (a:axes F (Q s))=>cost (book s) (hol G) R (Q s) F (pupil (roster F (Q s)) R m N a) (a 0) ψ Φ y amp
      old t c m K N p ex (r s) (gap s) farGap DF (B s) ρ 0
    (∀s (a:axes F (Q s)),posFee s a=clock R.draws R.paid N m old (E (a 0))*
       clock R.draws R.paid N m old (∏i,X s i (a i.succ))) ∧
    read coef (U N)-read coef (U K)=∑s,∑a:axes F (Q s),(sign coef s*into (posFee s a))*
         into (native .upper s a-native .planted s a) ∧
    ∀q ≤ e, ‖coeff q (read coef (U N)-read coef (U K))‖ ≤
      ∑s,∑a:axes F (Q s),∑uv∈Finset.HasAntidiagonal.antidiagonal q,‖coeff uv.1 (sign coef s*into (posFee s a))‖*bill s a:=by
  choose book earned using fun s=>WilsonSeparatedPrefixMovingOrdinarySwitch.original (d:=d) (publicFrame P) (Q s) F e p ex pos gain
    (near s) far (aperture s) (reserve s) C
  refine ⟨book,?_⟩
  intro R stock frames old t c m K N awake home outer mid cut top α ψ₀ X E r gap farGap DF B Φ y amp o ω ψ geometry money ρ coef U posFee native bill
  obtain ⟨afar⟩:=frames F far
  have named (s)(i):Named (publicFrame P) height seats ((roster F (Q s)) i):=Fin.cases far (near s) i
  have issued (s):U N s-U K s=∑a:axes F (Q s),posFee s a*(native .upper s a-native .planted s a):=by
    have all:=WilsonIndependentCutJoinNativeFrames.roster frames (roster F (Q s)) (named s)
    exact WilsonSeparatedPrefixMovingCorrectedField.original R (roster F (Q s)) (paints F (Q s) ψ₀ (α s)) (offered F (Q s) E (X s)) all.2
      Φ y o t m c old K N ρ (home.trans (outer.trans mid)) (awake.trans home) (outer.trans mid) cut top ω
  refine ⟨fun s a=>common F (Q s) R E (X s) a old m N (home.trans (outer.trans mid)),?_,?_⟩
  · exact WilsonSeparatedPrefixMovingFiledInventory.coupled coef (U N) (U K) posFee _ issued
  · apply WilsonSeparatedPrefixMovingFiledInventory.price coef (U N) (U K) posFee _ issued e bill
    intro s a j hj
    exact (earned s R stock afar old t c m K N awake home outer mid cut top (α s) ψ
      (pupil (roster F (Q s)) R m N a) (a 0) (r s) (gap s) farGap DF (B s) Φ y amp o ω (geometry s) money ρ).2 j hj

end YM.Integration.WilsonSeparatedPrefixMovingFiledContrast
end

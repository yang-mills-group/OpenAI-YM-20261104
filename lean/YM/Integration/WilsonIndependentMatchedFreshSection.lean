import YM.Integration.WilsonIndependentMatchedFreshWhole
import YM.Integration.WilsonIndependentMatchedFreshPriceBook

/-! A funded compact right inverse and its literal finite-board Wilson word on
one elected original schedule. The entire ordinary source is retained on each
tested board. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedFreshSection
open Function Filter Finset Matrix Lattice RG Wilson Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PertExtension
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring PowerSeries
open WilsonPositionProgramTrialReverseLens (received)
open WilsonIndependentMatchedFreshGroupFilm (named)
open WilsonIndependentMatchedFreshInverseIncome (age)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedOrdinaryProfile (stems)
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramTrialFittedLens (ticket)
open WilsonIndependentMatchedFreshInlet (bank)
open Push.CutoffProjectors (Lens)
open scoped BigOperators Classical

variable {G:Gauge}{n h D H k u e:ℕ}(R:Run G)(W:Initialize G)(d:Fin (n+1) → ℕ)(fit:∀i,d i<D)
local notation "Q" => named R W (fun _=>false) d fit
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "CC" => Credit.leanC

theorem original (simple:G.Simple)(v:ℕ → Gear G → ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (big:h<H)(rails:Rails h k u e)(cap:capP (deck (G:=G) d (fun _=>D) fit) ≤ k):
    ∃ A B:Fin (n+1) → Credit,
    (∀i,∃(tests:Finset (Lens G (d i)))(c:ℝ),0<c ∧ ∀v:(R.family.labels.level (d i)).Coeff,
      c*‖v‖ ≤ ∑t∈tests,‖bank R (d i) v t‖) ∧
    ∀ᶠ j:ℕ in atTop,∀m K,j ≤ m → m ≤ K → ∀b:Herit Q,
    let x:=fun i=>received L O (Q i) m K K (b i)
    (∀i,ticket L O (Q i) K m K (x i)=b i) ∧
    (∀i r,d i ≤ r → projected L O (Q i) m K r (Shrine (plate (R.family.localSection (d i)) (fit i)) (x i))=b i) ∧
    (∀i (S:ℝ),0 ≤ S → (∀t ≤ e,∀a,‖coeff t (b i a)‖ ≤ S) → ∀t ≤ e,∀a,
      ‖coeff t (x i a)‖ ≤ (A i).buy (age L (zz L) m K)*((Fintype.card (Alma (Q i).F):ℝ)*(B i).buy (zz L m)*S)) ∧
    ∀(φ:Wilt Q)(y:ℝ)(o:CellR)(side:Side),
    flash ((Ashore Q L O φ (normalized L O Q b m K) m K K y o).1 side)=
      ∏i,stems R W side false (fit i) (x i) (φ i) (paceT R.family.path.levels.S m K) y o (d i):=by
  obtain ⟨A,B,price⟩:=WilsonIndependentMatchedFreshPriceBook.original R W d fit simple v funded big rails cap
  refine ⟨A,B,fun i=>WilsonIndependentMatchedFreshInlet.original R (d i),?_⟩
  filter_upwards [price,WilsonIndependentMatchedFreshCompact.original R W d fit simple v funded big rails cap,
    WilsonMarkedIndependentNormalizedElection.original R simple v funded big rails d (fun _=>D) fit cap] with j fees compact sale
  obtain ⟨_,chair,levels,ratio,_,base,_,_,_,frames,_⟩:=sale
  intro m K awake before b x
  obtain ⟨inverse,film⟩:=compact m K awake before b
  refine ⟨inverse,?_,fees m K awake before b,film⟩
  intro i r cap'
  let f:AheadT (hol G) chair.L.V CC CC (Q i) CC := (frames i).some
  have en:f.p.f.arch.V.anchor ≤ m:=by rw [f.p.tap,base];exact awake
  have actual:=WilsonIndependentMatchedFreshWhole.returned (hol G) (Q i) f.p.f.arch m K en before cap' (b i)
  change projected L O (Q i) m K r (Shrine (plate (Q i).ans (Q i).path)
    (received L O (Q i) m K K (b i)))=b i
  simpa only [f.p.lands,f.p.modes,levels,ratio] using actual

end YM.Integration.WilsonIndependentMatchedFreshSection

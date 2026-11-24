import YM.Integration.WilsonIndependentMatchedFreshInverseIncome
import YM.Integration.WilsonIndependentMatchedFreshCapSix

/-! The reports buy the two genuine matrices on their own original research
course before either K or the measured vector. The bound is on every
coefficient of the fresh compact inlet with the whole finite native sum
of all incoming grades retained. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedFreshPriceBook
open Next.Foundations XSpace PertExtension WilsonCoeffUV.Wheel.Flooring
open Function Filter Finset Matrix Lattice RG Wilson Precision Source Labels
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Mark PowerSeries
open WilsonPositionProgramTrialReverseLens (received)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentMatchedFreshGroupFilm (named)
open WilsonIndependentMatchedFreshInverseIncome (slope measured age)
open scoped BigOperators Classical

variable {G:Gauge}{n h D H k u e:ℕ}(R:Run G)(W:Initialize G)(d:Fin (n+1) → ℕ)(fit:∀i,d i<D)
local notation "Q" => named R W (fun _=>false) d fit
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "CC" => Credit.leanC

theorem original (simple:G.Simple)(v:ℕ → Gear G → ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (big:h<H)(rails:Rails h k u e)(cap:capP (deck (G:=G) d (fun _=>D) fit) ≤ k):
    ∃ A B:Fin (n+1) → Credit,∀ᶠ j:ℕ in atTop,∀m K,j ≤ m → m ≤ K → ∀(b:Herit Q)(i:Fin (n+1))(S:ℝ),0 ≤ S →
    (∀t ≤ e,∀a,‖coeff t (b i a)‖ ≤ S) → ∀t ≤ e,∀a,
    ‖coeff t (received L O (Q i) m K K (b i) a)‖ ≤
      (A i).buy (age L (zz L) m K)*((Fintype.card (Alma (Q i).F):ℝ)*(B i).buy (zz L m)*S):=by
  choose A paid using fun i=>slope (hol G) (Q i) e
  choose B bound using fun i=>belt (H:=hol G) (C:=CC) (T:=(Q i).ans) (p:=(Q i).path) (e:=e) (E:=CC) (W:=CC)
  refine ⟨A,B,?_⟩
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded big rails
    d (fun _=>D) fit cap] with j sale
  obtain ⟨_,chair,levels,cash,calendar,base,_,_,_,frames,_⟩:=sale
  intro m K late before b i S nn input t depth a
  let f:AheadT (hol G) chair.L.V CC CC (Q i) CC:=(frames i).some
  have start:f.p.f.arch.V.anchor ≤ m:=by rw [f.p.tap,base];exact late
  have hclock:1 ≤ zz L m:=by
    simpa only [f.p.depths,calendar] using f.p.f.arch.V.depth m start
  have pos:0 ≤ (B i).buy (zz L m):=zero_le_one.trans (Credit.purchase _ hclock)
  have wray (a b:Alma (Q i).F):‖(Wray L O (Q i).ans (Q i).path K m)⁻¹ a b‖ ≤ (B i).buy (zz L m):=by
    have s:=(bound i f.p.f.arch f.stamps m m K K start le_rfl before before a b).main
    simpa only [Realm.cash,f.p.lands,f.p.modes,f.p.depths,levels,cash,calendar] using s
  let M:=(Fintype.card (Alma (Q i).F):ℝ)*(B i).buy (zz L m)*S
  have nm:0 ≤ M := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) pos) nn
  have allocated (r:ℕ)(hr:r ≤ e)(a:Alma (Q i).F):
      ‖coeff r (PermuteLens L O (Q i) K m (b i) a)‖ ≤ M:=
    measured L O (Q i) K m (b i) r S _ pos (input r hr) wray a
  have pr:=paid i f.p.f m K start before (PermuteLens L O (Q i) K m (b i)) M nm allocated t depth a
  simpa only [received,f.p.lands,f.p.modes,f.p.depths,levels,cash,calendar] using pr

end YM.Integration.WilsonIndependentMatchedFreshPriceBook

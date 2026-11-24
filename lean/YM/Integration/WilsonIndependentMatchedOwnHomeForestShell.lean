import YM.Integration.WilsonIndependentMatchedOwnHomeKShell
import YM.Integration.WilsonMovingForkSharpOwnRoster
import YM.Integration.WilsonIndependentMatchedOwnHomeFixedPower
import YM.Integration.WilsonIndependentMatchedOwnHomeNearAxes

/-! The full K-born measured high shell in an incumbent or a fresh vacuum
at the grade-four moving test. The finite sharp witness supplies the raw
top row, including its old Gram return, at the very same appointments. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeForestShell
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Flooring
open WilsonIndependentMovingRosterAllFineSeats (Named Elected needed)
open WilsonSeparatedPrefixMovingPinnedPupil (Clear)
open WilsonIndependentSpoutMasterCoordinates (axis)
open WilsonSeparatedPrefixMovingJointSpectrum (transformed)
open WilsonMovingForkSharpExteriorRoof (amount)
open WilsonIndependentMatchedOwnHomeBornRaw (measured)
open WilsonIndependentMatchedOwnHomeKShell (rider cost Coins)
open WilsonMovingForkSharpBilledRaw (Issued)
open scoped BigOperators Topology Classical ContDiff
local notation "C" => Credit.leanC
variable {G:Gauge}{H:Hol G}{n e height seats:ℕ}

theorem original (M:Master H)(arms:Fin (n+1)→SealR G)(F:SealR G)(D e p ex:ℕ)(positive:0<p)
    (gain:2 ≤ F.h+ex)(near:∀s,Named M height seats (arms s))(far:Named M height seats F)
    (capacity:needed (F.h+capP arms) 0 p ≤ seats)(reserve:capP arms+F.h+ex ≤ seats):
    ∃(book:Coins)(P₁ P₂ P₃ P₄:Credit),∀{k u a:ℕ}{Z:Labels.Frame G 4}{T:SectionData Z}{admit:4<D}{v:Rails 4 k (u+a) e}
      (Y Y₀:CutsP H T admit v C C C C)(m:ℕ)(α:Wilt arms)(X:Herit arms)
      (C₀ C₁ C₂ first shape chron middle ledger pay thermal U₁ U₂ fund folds:Credit)
      (Φ:Rarity D)(ψ χ:Rarity F.D)(hΦ:ContDiff ℝ ∞ Φ.ψ.val)(hψ:ContDiff ℝ ∞ ψ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val),
      ∀a₀:(s:Fin (n+1))→Alma (arms s).F,Y.vesselsC=Y₀.vesselsC → Y.m=Y₀.m → Y.ceilC=Y₀.ceilC →
      Y.fuel=WilsonMovingForkSharpNearIncome.charge arms X e*Y₀.fuel →
      Elected M Y.vesselsC height seats → AheadT H Y.vesselsC C C F C →
      Issued Y m arms F α X C₀ C₁ C₂ first shape chron middle ledger pay thermal U₁ U₂ fund folds Φ ψ χ hΦ hψ hχ →
      Y.ceilC=m → Y.m ≤ m → ∀(older K:ℕ),Y.vesselsC.anchor ≤ older → older ≤ Y.m → m ≤ K → K ≤ Y.N →
      ∀(j:Alma F.F)(r nearGap farGap DF:ℝ)(B:Fin (n+1)→ℝ),
      Clear Y.vesselsC arms F α ψ older Y.m Y.ceilC m r nearGap farGap DF B →
      ∀(y gap out A L bound:ℝ)(o:CellR)(w:Fin 0→YForest G),Amplitude Φ A → ClearDay Φ χ gap → 0<gap →
      Φ.radius+|y|+1 ≤ out → χ.radius+|y|+1 ≤ out → 1 ≤ L → L/paceT Y.ax.S m Y.m ≤ bound →
      ∀(J:ℕ)(g:ℝ),J ≤ e → |g| ≤ 1 →
      let Δ:=paceT Y.ax.S m Y.m
      let ρ:=L/Δ
      let Z:=rider Y.vesselsC F Y.N Y.m m j
      let axisCost:=amount Y₀ m arms F (WilsonMovingForkSharpNearIncome.center arms a₀) C₀ C₁ C₂ first shape chron middle ledger pay thermal U₁ U₂ fund folds 0
        Φ χ hΦ hχ (transformed ψ hψ) older r nearGap farGap DF B y gap out A L bound (axis F j)
      let receipts:=((Fintype.card (Alma F.F):ℝ)^2*(e+1))*
        P₁.buy (Compar Y.ax.S Y.vesselsC.y Y.m m)*P₂.buy (Y.vesselsC.y m)*WilsonMovingForkSharpNearIncome.charge arms X e*|axisCost|
      let stipend:=((Fintype.card (Alma F.F):ℝ)^2*(e+1))*P₃.buy (Compar Y.ax.S Y.vesselsC.y Y.m m)*P₄.buy (Y.vesselsC.y m)
      let bill:=WilsonIndependentMatchedOwnHomeFixedPower.rent book H Y.vesselsC arms F X j ψ Φ y A older Y.m Y.ceilC m K p ex r nearGap farGap DF B ρ receipts stipend
      ‖measured Y.vesselsC arms F α ψ X Z Φ y o Y.m m Y.ceilC older K Y.N e g ρ w-
        measured Y.vesselsC arms F α ψ X Z Φ y o Y.m m Y.ceilC older K Y.N J g ρ w‖ ≤
        (Finset.Ico (J+1) (e+1)).card*|g|^(J+1)*((e+1)*book.clock.buy (Compar Y.ax.S Y.vesselsC.y older m)*bill):=by
  obtain ⟨P₁,P₂,tops⟩:=WilsonMovingForkSharpOwnRoster.original H F e
  obtain ⟨P₃,P₄,cancel⟩:=WilsonIndependentMatchedOwnHomeFixedPower.original (d:=D) (n:=n) H F e C
  obtain ⟨book,earned⟩:=WilsonIndependentMatchedOwnHomeKShell.original (d:=D) M arms F e p ex positive gain near far capacity reserve C
  refine ⟨book,P₁,P₂,P₃,P₄,?_⟩
  intro k u a Z T admit v Y Y₀ m α X C₀ C₁ C₂ first shape chron middle ledger pay thermal U₁ U₂ fund folds
    Φ ψ χ hΦ hψ hχ coord realm start endAt posted stock forward funded born interval older K live old cut top j r nearGap farGap DF B clear
    y gap out A L bound o w amp sep pos nearBox farBox outer bracket J g jlo small Δ ρ basis axisCost receipts stipend bill
  obtain ⟨_,quote,_⟩:=tops Y Y₀ m arms α X C₀ C₁ C₂ first shape chron middle ledger pay thermal U₁ U₂ fund folds Φ ψ χ hΦ hψ hχ
    coord realm start endAt posted forward funded born interval (cut.trans top) older live old j r nearGap farGap DF B clear y gap out A L bound o w amp sep pos nearBox farBox outer bracket
  have charge (l:ℕ)(ok:l ≤ e):‖ρ^4*WilsonSeparatedPrefixMovingPinnedRaw.raw Y.vesselsC arms F α ψ X basis Φ y o Y.m m Y.ceilC older Y.N l 0 w‖ ≤ Δ^F.h*receipts:=
    (quote l ok).trans_eq (by dsimp only [receipts,axisCost,Δ];ring)
  have firstStep:=earned Y.vesselsC stock forward older Y.m Y.ceilC m K Y.N live old (born ▸ interval) born.le cut top
    α ψ X j r nearGap farGap DF B Φ y A o w clear amp J g ρ (Δ^F.h*receipts) jlo small charge
  have lastStep:=cancel Y.vesselsC forward book arms X j ψ Φ y A older Y.m Y.ceilC m K Y.N p ex (live.trans old) interval
    (cut.trans top) r nearGap farGap DF B ρ receipts
  have warm:1 ≤ Compar Y.ax.S Y.vesselsC.y older m:=(Y.vesselsC.depth older live).trans (compar_tier live (old.trans interval))
  have clockNonneg:0 ≤ book.clock.buy (Compar Y.ax.S Y.vesselsC.y older m):=zero_le_one.trans (book.clock.purchase warm)
  exact firstStep.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left lastStep (mul_nonneg (by positivity) clockNonneg)) (by positivity))

end YM.Integration.WilsonIndependentMatchedOwnHomeForestShell
end

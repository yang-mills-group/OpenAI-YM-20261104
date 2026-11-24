import YM.Integration.FundedMarkedCoverRows
import YM.WilsonCoeffUV.Emit.RentedCapture

/-! The independent occupied upper history uses the original Wilson sources
localSection/sound/valuation. Its separated connected operator is reserved on
the funded existence run before the cutoffs and insertion fields are named. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorSeparatedPurchase
open Function Filter Lattice RG RG.Supply Wilson Precision Next.Foundations PowerSeries
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open WilsonLimitConstruction
open scoped Classical BigOperators Topology
variable {G:Gauge}

def Extra : FundedCompanySelection.Prediction G := FundedMarkedCoverRows.prices (fun _ _=>1)

theorem prepaid : FundedPredictionSupply.AllPrices (@Extra G) :=
  FundedMarkedCoverRows.purchase (fun _ _=>1)

def fee (T:SealR G) (X:Verse T.F) (e:ℕ):ℝ := 1+∑a:Alma T.F,∑i∈Finset.range (e+1),‖coeff i (X a)‖

theorem fee_pos (T:SealR G) (X:Verse T.F) (e:ℕ):0<fee T X e:=by unfold fee;positivity

theorem funded (T:SealR G) (X:Verse T.F) (e:ℕ) (z:ℝ) (warm:1≤z):
    sprouted T X e (fee T X e*Credit.leanC.buy z):=by
  intro i hi a
  have row:=Finset.single_le_sum (s:=Finset.range (e+1)) (f:=fun i=>‖coeff i (X a)‖) (fun _ _=>norm_nonneg _) (Finset.mem_range.mpr (by omega) : i∈Finset.range (e+1))
  have total:=Finset.single_le_sum (s:=Finset.univ) (f:=fun a:Alma T.F=>∑i∈Finset.range (e+1),‖coeff i (X a)‖)
    (fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _) (Finset.mem_univ a)
  have booked:‖coeff i (X a)‖≤fee T X e:=by unfold fee;linarith [row,total]
  exact booked.trans (le_mul_of_one_le_right (fee_pos T X e).le (Credit.purchase _ warm))

abbrev decks {v:ℕ} (k D:Fin v→ℕ) (hk:∀i,k i<D i) :=
  counter (hol G) (primes G) k D hk

def Upper {v e m:ℕ} (k D:Fin v→ℕ) (hk:∀i,k i<D i) (Q:Realm G (e+1) Credit.leanC) (early:Q.anchor≤ m):Prop:=
  let T:=decks (G:=G) k D hk
  ∀ (N:ℕ),m≤N → ∀ (X:(s:Fin v)→ Verse (T s).F) (z ρ:ℝ),Q.y m≤z →
    hgate (hol G) T Credit.leanC Credit.leanC Credit.leanC Credit.leanC Credit.leanC e z ≤ρ →
    ∀ (b:ℕ) (lo:m≤b), b≤N → ∀ (Y:Fin v→ Cover) (S:Finset (Fin v)),1<S.card →
      cleared Q.draws.S m b ρ Y S → ∀ i≤e,∀r:ℕ,
        Wig Bank.terrain Y (Q.mint b (early.trans lo)).σ
          ((∏ t∈S,fee (T t) (X t) e)*Real.exp (-penaltyB Credit.leanC z ρ (snowP Q.draws.S m b))) S
            ((Gears Q.draws Q.paid k k N N b (coatA Q.draws Q.paid N m T X) Y S).2 i r)

theorem original (R:Run G) (simple:G.Simple) (paid:Extra R.kit)
    (v:ℕ) (k D:Fin v→ℕ) (hk:∀i,k i<D i) (e:ℕ) : ∀ᶠ m:ℕ in atTop,
    ∃ (Q:Realm G (e+1) Credit.leanC) (here:Q.anchor≤ m),
    Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧ Q.y=zz R.family.path.levels ∧ Q.anchor=m ∧
      Upper k D hk Q here :=by
  filter_upwards [FundedMarkedCoverRows.realm R simple (fun _ _=>1) paid v k D hk e v e] with m live
  obtain ⟨Q,levels,ratio,clock,start,cl,_,⟨p⟩,_⟩:=live
  have here:Q.anchor≤ m:=start.le
  refine ⟨Q,here,levels,ratio,clock,start,?_⟩
  let T:=decks (G:=G) k D hk
  intro N above X z ρ warm large b lo hi Y S mixed clear i ei r
  exact ScaleS.crossing X (fun t=>fee (T t) (X t) e) p Credit.leanC
    (fun _=>fee_pos _ _ _) here above warm large (fun _=>funded _ _ _ _ ((Q.depth m here).trans warm))
    cl Y S mixed lo hi clear ei r

end YM.Integration.WilsonConditionalTaylorSeparatedPurchase
end


import YM.Integration.WilsonIndependentCollarVaryingRestoration
import YM.Integration.WilsonOriginalCensusWholePeriod

/-! A physical-period opening for all genuine binder patterns at once, with
a separately issued roster and wallet allowed on each canonical seed. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarWholeStation
open Filter Function Finset Lattice RG Wilson Marker Multi QuadraticLocal QuadraticLocal.Earn PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel.Mark (mass)
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm Next.Foundations
open WilsonIndependentCollarOriginalDose (axisFee)
open WilsonThermometerDeclaredSeeds WilsonReceivedCanonicalVerseBasis WilsonReceivedCanonicalVerseRegister
open WilsonIndependentCollarOrbitalBasisPayment (Choices)
open WilsonIndependentCollarPaidWindingPanel (signed earned)
open WilsonOriginalSparseFiledOpening (near)
open WilsonReceivedDepositedOrbitalNamedWage (wages)
open WilsonOriginalMixedBlockRows (room)
open WilsonOriginalCensusRosterOpening (opening)
open scoped Classical BigOperators

variable {G:Gauge}{n q:ℕ}{I:Type}[Fintype I][DecidableEq I]{D:Fin n→ℕ}

def ranks (I:Type)[Fintype I](k:Fin n→ℕ)(q:ℕ):ℕ:=Fintype.card I*mass k Finset.univ+q

theorem original (R:Run G)(κ:(v:Fin n)→Knob (D v))(pt:Fin n→Chamber)(simple:G.Simple)(k:Fin n→ℕ)
    (quiet:WilsonReceivedCloseFundedHeat.Quiet R)(salary:ℕ→Gear G→ℝ)(bought:FundedMarkedCoverRows.prices salary R.kit)
    (tests:Fin n→ℝ)(cap:∀v,0≤tests v)(A:ℕ):
    let L:=R.family.path.levels
    ∃C:ℝ,0≤C ∧ ∀ᶠ m:ℕ in atTop,∀K i:ℕ,m ≤ i → i < K →
      L.S.scale K-L.S.scale m≤(A:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))) →
      ∀(Q:Realm G (q+1) Credit.leanC),Q.anchor ≤ i → Q.draws=L → Q.paid=R.metals.O →
      ∀(target:(Stock.census (Fin n)).Mode)(M:Fin n→ℝ)(diameter power pole E:ℕ)(external:ℝ),
      let H:=R.alloy.B.a.clock.hatBeta (i+1)
      0<H → ∃δ:ℝ,0<δ ∧
      δ=(H^(near power pole E))⁻¹/(1+max 0 (earned R k A m C M target.val (Fintype.card I)))/
          (((ranks I k q:ℝ)+1)*max 1 external) ∧
      ∀ᶠ per:ℕ in atTop,opening (I:=I) R κ pt k tests i K q per (ranks I k q) diameter δ ∧
      ∀ (N:ℕ),K≤N → ∀(v:(j:Fin n)→R.family.label (k j)),(∀j∈target.val,axisFee R k v j≤M j) →
      let A₀:=Choices R k target.val
      ∀(side:A₀→Side)(P:(a:A₀)→Passport (side a) (Fin n))(B:(a:A₀)→I→Binder (P a) (Stock.census (Fin n)))
        (x:A₀→Affinity.Wallet (room (Fin n)))(extra high low:A₀→ℂ),(∀a,‖extra a‖≤external) →
        (∀a,‖high a-low a‖ ≤ (∑s:Finset I,‖wages (B a) (x a) target s‖)*(((ranks I k q:ℕ)+1:ℕ)*δ)) →
        (∑a:A₀,‖signed R k N per K m v target.val a*(extra a*(high a-low a))‖)≤(H^(near power pole E))⁻¹:=by
  intro L
  obtain ⟨C,non,cash⟩:=WilsonIndependentCollarVaryingRestoration.original R simple k A (Fintype.card I)
  obtain ⟨floor,opened⟩:=eventually_atTop.1 (WilsonOriginalCensusRosterOpening.original (I:=I) (e:=q) (k:=k)
    R κ pt simple quiet salary bought tests cap)
  refine ⟨C,non,?_⟩
  filter_upwards [cash,eventually_ge_atTop floor] with m offer late
  intro K i lower upper span Q anchor draw book target M diameter power pole E external H hot
  obtain ⟨ε,pos,exactε,give⟩:=offer K i (lower.trans upper.le) span target.val M power pole E hot
  let count:ℝ:=(ranks I k q:ℝ)+1
  let gross:=max (1:ℝ) external
  let δ:=ε/(count*gross)
  have hc:0<count:=by dsimp only [count];positivity
  have hg:0<gross:=zero_lt_one.trans_le (le_max_left _ _)
  have price:0<δ:=div_pos pos (mul_pos hc hg)
  have invert:(count*gross)*δ=ε:=by rw [mul_comm];exact div_mul_cancel₀ _ (mul_pos hc hg).ne'
  refine ⟨δ,price,by dsimp only [δ,count,gross];rw [exactε],?_⟩
  filter_upwards [opened i (late.trans lower) K upper Q anchor draw book (ranks I k q) diameter δ price] with per issued
  refine ⟨issued,?_⟩
  intro N top v money A₀ side P B x extra high low cost hears
  let roof:ℝ:=2^(Fintype.card I)
  have quote(a:A₀):‖extra a*(high a-low a)‖≤ε*roof:=by
    have bill:=hears a
    simp only [Nat.cast_add,Nat.cast_one] at bill
    have bill':‖high a-low a‖≤roof*(count*δ):=bill.trans (mul_le_mul_of_nonneg_right
      (WilsonIndependentCollarOrbitalUnweighted.disk (B a) (x a) target) (mul_nonneg hc.le price.le))
    rw [norm_mul]
    calc
      _ ≤ gross*(roof*(count*δ)):=mul_le_mul ((cost a).trans (le_max_right _ _)) bill'
        (norm_nonneg _) hg.le
      _ = ((count*gross)*δ)*roof:=by ring
      _ = ε*roof:=by rw [invert]
  have sum:=give N per top (by omega) v money (fun a=>extra a*(high a-low a)) (fun _=>0)
    (fun a=>by simpa using quote a)
  simpa using sum

end YM.Integration.WilsonIndependentCollarWholeStation
end

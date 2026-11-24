import YM.Integration.WilsonIndependentCollarLowerMass

/-! The named dated lower bank and its actual finite-mode / directional
salary for the genuine physical period opening and all later cutoffs. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarDatedLowerWallet
open Finset Function Lattice RG Wilson Precision PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Blue WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Cadenza QuadraticLocal Multi Marker
open WilsonReceivedFixedDigitHistory FundedMarkedPathSelection WilsonReceivedCanonicalVerseBasis
open WilsonThermometerDeclaredSeeds WilsonOlderFreshConnectedAppointment WilsonOlderFreshConnectedRobe
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonOriginalCensusDatedMaterial (Material words)
open WilsonIndependentCollarDatedPrior (inlet onLevels)
open FullQLocal Work.F08
open WilsonIndependentCollarDatedMaterial (filed)
open WilsonOriginalMixedBlockRows (room)
open WilsonOriginalCensusDatedHeldTariff (salary Rates periodTariff)
open WilsonIndependentCollarLowerMass (copies)
open Filter
open scoped Classical BigOperators Topology
variable {G:Gauge}{I:Type}{n q j N K:ℕ}{D k:Fin n→ℕ}{n':Side}
  {P:Earn.Passport n' (Fin n)}(R:Run G)(V:Realm G (q+1) Credit.leanC)
  (B:I→Earn.Binder P (Stock.census (Fin n)))(hj:V.anchor ≤ j+1)
  (cells:Digits V.draws (Fin n))(κ:(l:Fin n)→Knob (D l))(pt:Fin n→Chamber)(seed:(l:Fin n)→Choice R k l)
  (top:K≤N)(up:j+2≤K){A δ σ:ℝ}(paid:Paid R V hj D k δ σ)(apos:0≤A)(width:0<σ)
  (wallet:Uniform V (itinerary V.draws V.paid k N cells (K-(j+2)) (j+2) (start R k κ pt seed))
    (j+2) (by omega) A)(c:I→Fin n)(pin:∀l,c l∈(B l).mode.val)(deep:∀l,0 < mass k (B l).mode.val)
  (y:Fin n → Cover)(t:Case D)(closed:Cloze D k V Credit.leanC)(tickets:Insure n (mass k univ) V Credit.leanC)


local notation "H" => filed R V B hj cells κ pt seed top up paid apos width wallet c pin deep y t closed tickets
variable [Fintype I]

theorem charge (x:Affinity.Wallet (room (Fin n)))(s:(Stock.census (Fin n)).Mode):
    salary (H) x s=(copies B s:ℝ)*(‖∏v∈s.val,(x v).val‖*‖touch t s.val‖):=
  WilsonIndependentCollarLowerMass.charge (H) x s t fun _=>rfl

theorem one (x:Affinity.Wallet (room (Fin n)))(s:(Stock.census (Fin n)).Mode)
    (appointed:Injective fun z=>(B z).mode):
    salary (H) x s≤∏v∈s.val,‖(x v).val‖*‖t v‖:=by
  calc
    _≤((1:ℕ):ℝ)*(∏v∈s.val,‖(x v).val‖*‖t v‖):=
      WilsonIndependentCollarLowerMass.original (H) x s t (fun _=>rfl) 1
        (WilsonIndependentCollarLowerMass.unique s appointed)
    _=_:=by rw [Nat.cast_one,one_mul]

theorem original (R:Run G)(k D:Fin n→ℕ)(κ:(v:Fin n)→Knob (D v))(pt:Fin n→Chamber)
    (j K q:ℕ)(rates:Rates R k κ pt j K q)(s:(Stock.census (Fin n)).Mode)(a:Fin (q+1))
    (cap:ℕ)(wage:Fin n→ℝ){ε:ℝ}(positive:0<ε):
    ∀ᶠ per:ℕ in atTop,∀n₀:Side,(R.family.side j per).val ∣ n₀.val→
      ∀(N e:ℕ)(σ:ℝ)(side:Side)(P:Earn.Passport side (Fin n))(Z:Type)[Fintype Z]
        (rows:Z→Earn.Binder P (Stock.census (Fin n)))(L:Material R N j e k σ rows)
        (x:Affinity.Wallet (room (Fin n)))(t:Case L.tests),
        (∀z,L.source z=t) → copies rows s≤cap →
        (∀v∈s.val,‖(x v).val‖*‖t v‖≤wage v) →
        2*(salary L x s*periodTariff G (mass k s.val+a.val) n₀ (rates.width s.val a) (rates.fare s.val a))≤ε:=by
  filter_upwards [WilsonOriginalCensusDatedPeriodOpening.original R k κ pt rates s.val a
    (cap*(∏v∈s.val,wage v)) positive] with per opened
  intro board multiple N e σ side port Z _ rows L x t same tally fees
  apply opened board multiple (salary L x s) (WilsonOriginalCensusDatedPeriodOpening.nonneg L x s)
  exact (WilsonIndependentCollarLowerMass.original L x s t same cap tally).trans
    (mul_le_mul_of_nonneg_left (prod_le_prod (fun _ _=>mul_nonneg (norm_nonneg _) (norm_nonneg _)) fees)
      (Nat.cast_nonneg _))

end YM.Integration.WilsonIndependentCollarDatedLowerWallet
end

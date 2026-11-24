import YM.Integration.WilsonOlderFreshGraphTariff

/-! A single dated copy of the named Roll, with its original atoms retained.
It can be submitted to several physical binders sharing its source wallet. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshGraphSlate
open Function Filter Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink
open scoped Classical BigOperators Topology
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
structure Copy (G:Gauge)(d Q:ℕ)(σ:ℝ) where
  roll : Fin (Q+1)→Poetry.Roll G Unit
  fare : Fin (Q+1)→ℝ
  paid : ∀j,(roll j).Faith {()} () (j.val+d+2) (2*σ) (fare j)
  legal : ∀j,(roll j).honest
  positive : 0<d

namespace Copy
variable {G:Gauge}{n:Side}{d Q:ℕ}{σ:ℝ}(T:Copy G d Q σ)
abbrev Roster:=Name T.roll
instance : Countable T.Roster:=WilsonOlderFreshGraphArmada.countable T.roll T.fare σ T.paid
variable {P:Earn.Passport n Unit}{H:Marker.Census Unit}(S:Earn.Binder P H) (A:Unit→Set ℂ)
def rows : T.Roster→Earn.Row P H G (Affinity.Wallet A):=
  WilsonOlderFreshGraphVote.material S T.roll T.fare σ T.paid T.legal T.positive (value A)
def cost : ℝ:=gross S T.fare σ
theorem assays:Earn.Tableau (fun _=>(⊥:Submodule ℝ ℂ)) A (T.rows S A):=
  WilsonOlderFreshGraphArmada.tests S T.roll T.fare σ T.paid T.legal T.positive A

theorem earnings (σ0:0≤σ) (cap:∀t,‖value A t‖≤1)
    (w b:ℝ) (gain:0<w) (b0:0<b) (fee:w*T.cost S≤b)
    {ord seats shelf:ℕ}(ordQ:Q ≤ ord)(positive:1 ≤ seats)(ds:d ≤ shelf):
    Scene.Armada (T.rows S A) (fun _=>w) (fun _=>d) σ b ord seats shelf:=
  WilsonOlderFreshGraphWallet.at_price S T.roll T.fare σ T.paid T.legal T.positive A σ0
    cap w b gain b0 fee ordQ positive ds

theorem voted (cap:∀t,‖value A t‖≤1)
    {ord seats stage vac shelf:ℕ} (positive:1 ≤ seats)
    (launch:ord+1 ≤ stage) (budget:ord+d ≤ Burn.horizon vac+2)(ordQ:Q ≤ shelf)(ds:d ≤ shelf):
    Cruise.Voter (T.rows S A) σ ord seats stage vac shelf:=
  WilsonOlderFreshGraphVote.voter S T.roll T.fare σ T.paid T.legal T.positive (value A)
    cap positive launch budget ordQ ds

theorem group (t:Affinity.Wallet A) (g:ℝ) (U:Config G n) (z:T.Roster):
    (T.rows S A z).nominal g t U=value A t*(g^((z.1.val:ℤ)-((T.roll z.1).leg z.2.1).r)
       *((T.roll z.1).leg z.2.1).atom.unmasked U S.center:ℝ):=
  WilsonOlderFreshGraphMount.literal S ((T.roll z.1).leg z.2.1) z.1 d T.positive
    ((T.paid z.1).pinned z.2.1) (T.legal z.1 z.2.1) z.2.2 σ (value A) t g U
end Copy
end YM.Integration.WilsonOlderFreshGraphSlate
end

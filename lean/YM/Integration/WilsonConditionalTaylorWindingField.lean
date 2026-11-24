import YM.Integration.WilsonConditionalTaylorWindingSource
import YM.Integration.WilsonConditionalTaylorWindingPrior

/-! The genuine upper winding bill spent on the old marked trajectory. Its
finite component is the original torus logarithm at the original cover
coupling, and its spatial test and incoming field are specified explicitly. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWindingField
open Filter Function Lattice RG Wilson Next.Foundations PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Shard WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding ActualRunAdmissionScales WilsonConditionalTaylorSeparatedPurchase
open WilsonConditionalTaylorWindingSource WilsonConditionalTaylorWindingPrior
open scoped Classical BigOperators Topology
variable {G:Gauge} {n e:ℕ}

def Bill (R:Run G) (Q:Realm G (e+1) Credit.leanC) (m t:ℕ) (h:Q.anchor≤t)
    (J:Finset (Fin n)) (o:Fin n) (k D:Fin n→ℕ) (hk:∀i,k i<D i)
    (i r d c q degree:ℕ) (s:Gear G→ℝ):Prop:=
  let T:=decks (G:=G) k D hk
  ∀N per:ℕ, t<N → ∀(X:(a:Fin n)→ Verse (T a).F)(ρ:ℝ)
    (offset:(Fin n→ Cover)→Fin n→ Site (loose Q.draws t).L),
    let z:=sourceLoad Q m T X
    hgate (hol G) T Credit.leanC Credit.leanC Credit.leanC Credit.leanC Credit.leanC e z ≤ρ →
    let A:=(charge T e).buy (z+snowP Q.draws.S m (t+1))
    let g:=Pert.Asymptotics.regulatorRun R.family N per (t+1)
    let side:=R.family.side t per
    let prior:=kept Q m t N ρ k k (coatA Q.draws Q.paid N m T X)
    let K:=fun v=>prior (chartIn (loose Q.draws t) v (offset v))
    let x:=fun y=>PeriodicMarkedWinding.roots side y o
    let F:=fun y=>((logO Q.draws Q.paid t N (K (x y)) k J).2 i r)
    let P:=fun y=>coilH Q.draws Q.paid t N side (K (x y)) k (ratioHigh Q.draws Q.paid N t) J i r
    let σ:=s (Q.mint t h).gear
    ∃B:ℝ,B*g^(-(c:ℝ)) ≤ g^q*A^J.card ∧
      B≤(admittedCost R.family.path.levels t)^degree*(Real.exp (-(σ/512)*(side.val:ℝ))*A^J.card) ∧
      PostMark J o r (RootedPeriodicMarkedWinding.row side J o (fun y=>Carp.plume (F y) side-P y))
        (σ/32/2/2/2) B d

theorem spend (R:Run G) (Q:Realm G (e+1) Credit.leanC) (m t:ℕ) (here:Q.anchor≤ m) (mt:m≤t)
    (J Z:Finset (Fin n)) (o:Fin n) (k D:Fin n→ℕ) (hk:∀i,k i<D i)
    (i r d c q degree:ℕ) (s:Gear G→ℝ) (cl:Cloze D k Q Credit.leanC)
    (wallet:Tribe Q (hol G) Credit.leanC Credit.leanC (decks (G:=G) k D hk))
    (receipt:FundedMarkedWindingWindow.ReceiptOn R J Z o D k e i r d c q degree (fun I=>I.past) s t Q (here.trans mt)):
    Bill R Q m t (here.trans mt) J o k D hk i r d c q degree s:=by
  let T:=decks (G:=G) k D hk
  unfold Bill
  dsimp only
  intro N per hi X ρ offset gate
  let z:=sourceLoad Q m T X
  let A:=(charge T e).buy (z+snowP Q.draws.S m (t+1))
  let prior:=kept Q m t N ρ k k (coatA Q.draws Q.paid N m T X)
  let K:=fun v=>prior (chartIn (loose Q.draws t) v (offset v))
  have start:=earned Q m N here (mt.trans hi.le) T X wallet
  have regular (v:Fin n→ Cover):=
    WilsonConditionalTaylorWindingPrior.paid start cl gate mt hi (chartIn (loose Q.draws t) v (offset v)) Z
  have enough:1≤A:=(charge T e).purchase ((Q.depth _ here).trans (start.yell.trans (le_add_of_nonneg_right
    (sub_nonneg.mpr (PathCost.scales Q.draws.S (show m≤t+1 by omega))))))
  exact receipt N per hi K offset A (zero_le_one.trans enough) regular

theorem original (R:Run G) (simple:G.Simple) (paid:WilsonConditionalTaylorWindingDeposit.Extra R.kit)
    (period:RG05Preconstruction.ReadoutPurchase R.b) (n:ℕ) (J Z:Finset (Fin n)) (inside:J⊆Z) (o:Fin n) (root:o∈J)
    (k D:Fin n→ℕ) (hk:∀i,k i<D i) (e i r d:ℕ) (hi:i≤e):
    ∃(s:Gear G→ℝ)(degree:ℕ),(∀I,0<s I) ∧ ∀c q:ℕ,∀ᶠ m:ℕ in atTop,
    ∃(Q:Realm G (e+1) Credit.leanC) (here:Q.anchor≤ m),Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧
      Q.y=zz R.family.path.levels ∧ Q.anchor=m ∧
      ∀t,∀mt:m≤t,Bill R Q m t (here.trans mt) J o k D hk i r d c q degree s:=by
  obtain ⟨s,a,pos,paid⟩:=WilsonConditionalTaylorWindingDeposit.original R simple paid period n J Z inside o root k D hk e i r d hi
  refine ⟨s,a,pos,?_⟩
  intro c q
  filter_upwards [paid c q] with m bought
  obtain ⟨Q,here,levels,ratio,date,birth,cl,_,⟨wallet⟩,all⟩:=bought
  exact ⟨Q,here,levels,ratio,date,birth,fun t mt=>spend R Q m t here mt J Z o k D hk i r d c q a s cl wallet (all t mt)⟩

end YM.Integration.WilsonConditionalTaylorWindingField
end


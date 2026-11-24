import YM.Integration.WilsonConditionalTaylorSeparatedPurchase

/-! Cost of the actual close interval in the independent connected Wilson
course. The true cutoff, integrated center and marked locations survive in
AutumnDay. The numerical load is bought from the mesh and the finite inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorCapture
open Filter Lattice RG Wilson Next.Foundations PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Embroider WilsonConditionalTaylorSeparatedPurchase
open scoped Classical BigOperators Topology
variable {G:Gauge}

def weight {e:ℕ} (Q:Realm G e Credit.leanC) (b m:ℕ) :=
  Q.y b+(Q.draws.S.scale m-Q.draws.S.scale b)+((m-b:ℕ):ℝ)

def quote {a:ℕ} (T:Fin (a+1)→SealR G) (e B:ℕ) : Credit :=
  (invoke (hol G) T e Credit.leanC Credit.leanC Credit.leanC Credit.leanC Credit.leanC B).choose

def Short {a e b:ℕ} (k D:Fin (a+1)→ℕ) (hk:∀i,k i<D i) (Q:Realm G (e+1) Credit.leanC) (here:Q.anchor≤b):Prop:=
  let T:=decks (G:=G) k D hk
  ∀ m N,b≤ m → m≤N → ∀ (X:Herit T) (F:Wilt T) (ρ:ℝ) (Y:Fin (a+1)→ℝ) (B:ℕ),
    let z:=weight Q b m
    hgate (hol G) T Credit.leanC Credit.leanC Credit.leanC Credit.leanC Credit.leanC e z ≤ρ →
    Shipfit Q.draws.S T F m b ρ z Y B → ∀i≤e,∀r d:ℕ,
      Cork Bank.terrain 0 (Vσ Q b here)
        ((∏t,fee (T t) (X t) e)*(Real.exp ((quote T e B).buy z)*(∏t,Y t))) ((AutumnDay Q.draws Q.paid F X m b N d).2 i r)

theorem captured (R:Run G) (simple:G.Simple) (paid:Extra R.kit)
    (a:ℕ) (k D:Fin (a+1)→ℕ) (hk:∀i,k i<D i) (e:ℕ):
    ∀ᶠ b:ℕ in atTop, ∃ (Q:Realm G (e+1) Credit.leanC) (here:Q.anchor≤b),
    Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧ Q.y=zz R.family.path.levels ∧ Q.anchor=b ∧ Short k D hk Q here:=by
  filter_upwards [FundedMarkedCoverRows.realm R simple (fun _ _=>1) paid (a+1) k D hk e (a+1) e] with b hold
  obtain ⟨Q,levels,ratio,calendar,start,closed,_,⟨p⟩,_⟩:=hold
  let T:=decks (G:=G) k D hk
  have here:Q.anchor≤b:=start.le
  refine ⟨Q,here,levels,ratio,calendar,start,?_⟩
  intro m N onset fine X F ρ Y B
  let z:=weight Q b m
  intro entered ample cite i he r d
  have budget:PadRank Q b m z:=PadRank.frugal Q here onset
  have warm:1≤z:=(Q.depth b here).trans (budget.year b le_rfl onset)
  exact ScaleS.capture_exp X F p (fun t=>fee (T t) (X t) e) (fun _=>fee_pos _ _ _) Credit.leanC
    onset fine here ample closed budget cite (fun _=>funded _ _ _ _ warm) he r d

end YM.Integration.WilsonConditionalTaylorCapture
end


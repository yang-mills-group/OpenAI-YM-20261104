import YM.Integration.WilsonReceivedCloseFoldedOrdinary

/-! Signed linear combinations of ordinary Wilson moments on a common filed post, including
the complete product minus all of its declared counterterm alternatives. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseFoldedSlate
open Filter Finset Multi Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra Source
open FullQLocal FullQLocal.RenderedStep Multi Exterior Comparison.RG02.Cumulants
open scoped BigOperators

variable {G : Gauge} (R : Run G) {m b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))

local notation "read" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "P" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y
local notation "g" => regulatorRun R.family N per
local notation "move" i:max => R.family.path.levels.clock.op i per


local notation "J₀" => Stock.census V
local notation "width" fund:max expo:max => fund*((g b)⁻¹)^expo
local notation "pow₀" a:max d:max q:max => q+d*a+1+a
local notation "Pupil" i:max mi:max L:max =>
  Oak.student (n:=per) (i:=i) R hk D Q π Γ books mi (L).op (L).lesson ahead actors (L).model order (L).voter
local notation "teacher" i:max mi:max L:max x:max => Air.craft (Pupil i mi L)
  (fun s=>((Pupil i mi L) s).paint x) grades (π i) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
local notation "bank" i:max L:max x:max => Air.craft (L).model (fun s=>((L).model s).paint x)
  grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
local notation "Covered" => ∀i:ℕ,i ≤ b → Wallet actors → Stationary.Link G (R.family.side i per) → ℕ → Poly J₀
local notation "Walk" start:max i:max mi:max ib:max L:max =>
  WilsonReceivedCloseHistory.Trail (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    mb source start i mi (read i ib) L


theorem combine {ι:Type*} [DecidableEq ι] (rows:Finset ι) (c u v:ι→ℂ) (δ:ℝ)
    (estimate:∀s ∈ rows,‖u s-v s‖ ≤ δ) :
    ‖(∑s ∈ rows,c s*u s)-(∑s ∈ rows,c s*v s)‖ ≤ (∑s ∈ rows,‖c s‖)*δ := by
  rw [←Finset.sum_sub_distrib,Finset.sum_mul]
  calc
    _ ≤ ∑s ∈ rows,‖c s*u s-c s*v s‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro s hs
      rw [←mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left (estimate s hs) (norm_nonneg _)

def Signed (start:P b mb source) (top:b<N) (K:Covered) (span:ℕ) (H cap:ℝ)
    (active:Finset V) (a d q:ℕ) (U ε:ℝ) : Prop :=
  ∀i (ib:i ≤ b)(mi:m ≤ i),∃ L:P i mi (read i ib), Walk start i mi ib L ∧
    (∀s:(J₀).Mode,s.val ⊆ active → (Poly.toll L.w s)⁻¹ ≤ (width U d)^s.val.card) ∧
    ∀ (x:Wallet actors) (F:Forest (move i).ratio) (tag:(move i).Choices)
      (A:Stationary.Link G (R.family.side i per)) (z:ℝ),
      let B:=R.family.path.levels.budget i
      let angle:=Stationary.arm G (R.family.side i per) 1 A
      |z| ≤ |H| *(Real.log (R.family.path.levels.clock.hatBeta i))^span*((B.B:ℝ)^2*B.threshold)/(g (i+1)) → 
      (∀e,‖Exterior.collect G angle e‖ ≤ cap* |z|) → 
      let U₀:=Integral.sample (g (i+1)) angle
      flags (Ψ i).p.threshold U₀=∅ → 
      let Y:=(((Ψ i).eval U₀:ℂ)⁻¹) • LocalComparison.actualPush R.family N per i ((read i ib) x) U₀
      let W:=Bulk.Fk ((RunFormalChain.fromRun R).step N i per (ib.trans_lt top)) F tag (bank i L x) angle order
      let folded:=WilsonCoveredOrdinaryPolynomial.evaluated order (K i ib x A) (g (i+1):ℂ)
      Y.part (J₀).quiet=1 ∧ ∀ (rows:Finset (J₀).Mode)
          (_:∀s ∈ rows,s.val ⊆ active ∧ s.val.card ≤ a) (c:(J₀).Mode→ℂ),
        let cost:=∑s ∈ rows,‖c s‖
        let actual:=∑s ∈ rows,c s*Y.part s
        let finite:=∑s ∈ rows,c s*(Order.value (g (i+1):ℂ) (Order.ratio W)).part s
        let independent:=∑s ∈ rows,c s*folded s
        ‖actual-independent‖ ≤ cost*(ε*(g b)^q) ∧
        ‖finite-independent‖ ≤ cost*((ε/2)*(g b)^q) ∧
        ∀lag,lag ≤ order → let grade:=Order.observe J₀ order (Order.logMarked W) lag
          ‖(∑s ∈ rows,c s*((Poly.toll L.w s:ℂ)*grade.part s)) -
            (∑s ∈ rows,c s*((Poly.toll L.w s:ℂ)*(K i ib x A lag).part s))‖ ≤
            cost*((((3:ℝ)⁻¹^(pow₀ a d q))/((order:ℝ)+1))*(g (i+1))^(pow₀ a d q))

theorem original (start:P b mb source) (top:b<N) (K:Covered) (span:ℕ) (H cap:ℝ) (active:Finset V)
    (a d q:ℕ) (U ε:ℝ) (heard:WilsonReceivedCloseFoldedOrdinary.Heard R hk D Q π Γ Ψ books ahead actors pieces grades order
      shelf seats mb source start top K span H cap active a d q U ε) :
    Signed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source
      start top K span H cap active a d q U ε := by
  intro i ib mi
  rcases heard i ib mi with ⟨L,trail,sold,paid⟩
  refine ⟨L,trail,sold,?_⟩
  intro x F tag A z B angle hz inside U₀ clear Y W folded
  rcases paid x F tag A z hz inside clear with ⟨quiet,errors⟩
  refine ⟨quiet,?_⟩
  intro rows included c cost actual finite independent
  have gates:=fun s hs=>errors s (included s hs).1 (included s hs).2
  refine ⟨combine rows c (fun s=>Y.part s) folded _ (fun s hs=>(gates s hs).1),
    combine rows c (fun s=>(Order.value (g (i+1):ℂ) (Order.ratio W)).part s) folded _ (fun s hs=>(gates s hs).2.1),?_⟩
  intro lag hl grade
  apply combine rows c
  intro s hs
  rw [←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Poly.worth L.salary.positive s).le]
  exact (gates s hs).2.2 lag hl

end YM.Integration.WilsonReceivedCloseFoldedSlate

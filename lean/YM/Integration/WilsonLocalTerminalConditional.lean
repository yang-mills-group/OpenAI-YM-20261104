import YM.Integration.WilsonLocalPlaquetteReporting
import YM.Integration.WilsonLocalConditionalFactors
import YM.Integration.WilsonLocalHaarOrder

/-! At the true ultraviolet incoming date the signed local expansion of the
full normalized Haar/Wilson conditional keeps its measured transition kernel
at both angular configurations and the same held coarse field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalTerminalConditional
open Function Finset Set Lattice RG Tree Wilson RG16 Precision PertExtension PertExtension.Series Push.BetaTransport
open PhysicalNext.Repeat.Legato WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots
open WilsonLocalPlaquetteForest WilsonLocalPlaquetteField WilsonLocalPlaquetteAction
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side} {S:StepData c f}

def estimate (P:ChartRatio G) (p:ℕ) (δ H W β:ℝ) (ρ K:Config G f→ℝ)
    (T:Forest S.ratio) (B:Finset T.Free) (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El)
    (X Y:↥(moving T B)→G.Color) : Prop :=
  let E:=moving T B
  let g:=(Real.sqrt β)⁻¹
  let w:=background T B v
  let origins:=support T E
  let x:=extend T E X 0
  let y:=extend T E Y 0
  let U (Z:↥E→G.Color):=restored T B v (fun i=>G.lieExp (g•Z i))
  (∀i:↥E,g*‖X i‖≤δ ∧ g*‖Y i‖≤δ)→
  |Real.log ((Chart.jacobian P (g•X)*ρ (U X))/(Chart.jacobian P (g•Y)*ρ (U Y)))-
    Real.log (K (U X)/K (U Y))-
    (∑i:↥E,(WilsonLocalHaarOrder.polynomial P p g (X i)-WilsonLocalHaarOrder.polynomial P p g (Y i)))+
    β*booked (p+2) origins (filled T E v w) 1 (extend T E w 1) x y g|≤
    H*g^(p+1)*(∑i:↥E,(‖X i‖^(p+1)+‖Y i‖^(p+1)))+W*g^(p+1)*load (p+3) origins x y

theorem price {j k w a b h z:ℝ} (haar:|j-a|≤h) (wilson:|w+b|≤z) :
    |(j+k+w)-k-a+b|≤h+z := by
  calc
    _=|(j-a)+(w+b)| := by congr 1;ring
    _≤|j-a|+|w+b| := abs_add_le _ _
    _≤h+z := add_le_add haar wilson

theorem original (P:ChartRatio G) (hp:LocalRatio P) (p:ℕ) :
    ∃δ H W:ℝ,0<δ ∧ δ≤1/2 ∧ 0≤H ∧ 0≤W ∧ ∀(R:Run G) (m per:ℕ) (V:Config G (R.family.side m per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free)
    (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El) (X Y:↥(moving T B)→G.Color),
    let n:=m+1
    let S:=R.family.path.levels.clock.op m per
    let β:=(R.family.path.rep n per n).beta
    estimate P p δ H W β (actualConditionalDensity R.family n per m V) (fun U=>S.density β U V) T B v X Y := by
  obtain ⟨δ,H,hδ,hH,haar⟩:=WilsonLocalHaarOrder.original P hp p
  obtain ⟨W,hW,wilson⟩:=WilsonLocalPlaquetteReporting.received G p
  refine ⟨min δ (1/2),H,W,lt_min hδ (by norm_num),min_le_right ..,hH,hW,?_⟩
  intro R m per V T B v X Y
  dsimp only [estimate];intro room
  let C:=R.family
  let E:=moving T B
  let n:=m+1
  let β:=(C.path.rep n per n).beta
  let g:=(Real.sqrt β)⁻¹
  let U (Z:↥E→G.Color):=restored T B v (fun i=>G.lieExp (g•Z i))
  have positive : 0<β := Overlay.beta_positive R.makes.wilson (show n≤n from le_rfl)
  have hf:=haar (↥E) X Y g (inv_pos.mpr (Real.sqrt_pos.mpr positive))
    (fun i=>⟨(room i).1.trans (min_le_left ..),(room i).2.trans (min_le_left ..)⟩)
  have small : ∀i:↥E,g*‖X i‖<1 ∧ g*‖Y i‖<1 := by
    have cut : min δ (1/2)<1 := (min_le_right _ _).trans_lt (by norm_num)
    exact fun i=>⟨(room i).1.trans_lt cut,(room i).2.trans_lt cut⟩
  have spending:=wilson _ _ _ T B v X Y β positive small
  have source : (C.path.rep n per n).eval=bare β := (R.makes.wilson.starts n per).2
  have law:=WilsonLocalConditionalFactors.original C R.makes n per m (Nat.lt_succ_self m) V
    (U X) (U Y) _ _ hf.1 hf.2.1
  dsimp only at law
  rw [source] at law
  change |Real.log ((Chart.jacobian P (g•X)*actualConditionalDensity C n per m V (U X))/
    (Chart.jacobian P (g•Y)*actualConditionalDensity C n per m V (U Y)))-_-_+_|≤_
  rw [law];exact price hf.2.2 spending

end YM.Integration.WilsonLocalTerminalConditional

import YM.MergeProof.Tray
import YM.LocalLTE.Pond.Spores
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Eco
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Ninety

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {X : Targets s K} {D : Rolls s} {Θ : Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ} {P : Teller G}

open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe
open LocalLTE.Fan Pastel Marlin Animals
variable (R : Register D p u l)(f:ℕ→ℕ→ℕ)(ψ:ℕ→ℕ→ℝ)
def ContractK (j i:ℕ)(x:ℝ):Prop:=
    let p':= s.profile i; let B:=radiusB x; let L:=D.L j; let a:=betaF G x L; let μ:=R.μ j i
    (∀ c k:ℝ, 0 ≤ c → 0 ≤ k → k ≤ Real.exp (ballCost (f j i))*a^ (-(1/8):ℝ) → c ≤ Real.exp (-(X j i).mark L μ x) → ∃ κ, Payments.Rates B (stems μ L G x) c k κ) ∧
    ∀ V:BudgetPoint,V.threshold=Pressure.temp x→V.B=B→Time.Same p' V→∀ α:ℝ,|α|≤UVNext.CouplingReset.alphaBound D j→∀ F:ℝ,0≤F→F≤ YM.Merge.Spicy.opens G V p'.clip p'.width p'.paths α (Time.credit G p'* δE x)+Real.exp (ballCost 2:ℝ)*(ψ j i*a^(chip 0)) →∃ κ,Payments.Rates B (straw μ L G x) (stems μ L G x) F κ
-- Merchandise requires the contract at every admitted pair of stages.

def Merchandise (V:Delays Θ):Prop := ∀ j i:ℕ,StepStages j i→∀ x:ℝ,V.betaEntry j≤ x→ ContractK R f ψ j i x
lemma dealsK (V:Delays Θ): ∃ W:Delays Θ,DelayLe V W ∧ ∀ Y:Delays Θ, DelayLe W Y →Merchandise R f ψ Y:=by
    have h (j i:ℕ)(hi:StepStages j i):∀ᶠ x:ℝ in atTop,ContractK R f ψ j i x:=by
       let μ:= R.μ j i; let L:=D.L j; let H x:=betaF G x L
       have hp:0<μ:= (R.consumes _ _ hi).2.1
       let Z x:= (H x)^(-(1/4):ℝ)+Real.exp (ballCost 2:ℝ)*(ψ j i*(H x)^(chip 0)); have hZ:Rate G L (-(1/4)) Z:= Rate.add Rate.power (((Rate.power (G:=G) (L:=L) (a:=chip 0)).mul_left _|>.mul_left _).weaken (by norm_num [Pastel.chip]))
       filter_upwards [mingle (G:=G) L _ (show 0<μ/4 by positivity) (he:=zero_lt_one) (by norm_num : -(1/8:ℝ)<0) (Rate.power.mul_left (Real.exp (ballCost (f j i)))), mingle (G:=G) L Z (show 0<μ/8 by positivity) zero_lt_two (by norm_num : -(1/4:ℝ)<0) hZ,offerSp L (s.profile i) (UVNext.CouplingReset.alphaBound D j)] with x hz hv hB
       refine ⟨fun c k hu hk h hh=> hz _ _ hu hk h (by rwa [one_mul,← syrup (μ:=μ) L (X j i)]),?_⟩
       intro V hK hf hR α hα F h hF
       have hs : stems μ L G x= 2*lauge L (μ/8) x 1 G:=by unfold stems lauge; ring_nf
       have hC:0≤ stems μ L G x:=by unfold stems lauge; positivity
       obtain ⟨p,hp⟩:= hv _ F hC h (hF.trans (add_le_add_left (hB _ hK hf hR α hα) _)) hs.le
       exact ⟨p,show Payments.Rates _ (straw μ L G x) _ _ _ from by rw [show straw μ L G x=2*lauge L (μ/8) x (1/2) G from by unfold straw lauge; ring_nf]; exact hp⟩
    obtain ⟨x,-,hx,H⟩:= collect_upper V.betaEntry _ fun j=> eventually_transitions j _ _ (fun i hi=> h j i hi)
    exact ⟨{V with betaEntry:=x},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun Y hy j i hi x hx=>H j x ((hy.beta j).trans hx) i hi⟩
end YM.PhysicalNext.Repeat.Mallow

import YM.RG01Estimate.Shilling
import YM.RG01Estimate.Stamped
/-!
 # Constant checks around wrap/small enrollment. `Barrier` arbitrary slow j- budget for spare
 pre-L, bought on ANY additional Grantable real Run. ETS enables EVEN if advancing j/m from p.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Chart
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Laplace Pressure ConnectedActivityE6 Coat Evoc Push Deck
open Censor Censor.Toft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G : Gauge} (hG:G.Simple) {M:Metals G} {D:Rolls M.p}{A:Alloy M D}(R:Factor A)

-- support compression checks. Below ANY epoch ratio exponent e>0 of C.Height choice
-- to keep requested smaller η; use stage-dependent e to attain subpower automatically.
structure Barrier (A:Alloy M D) (e:ℕ→ℕ→ℝ) : Prop where
    stocks (m:ℕ): Toft.stock G (A.B.a.budget m) * Real.exp (((A.B.a.budget m).supportExponent+1)*81) ≤ A.B.a.clock.hatBeta m
    cover (m:ℕ): ((A.B.a.budget m).B:ℝ) ≤ A.B.a.clock.hatBeta m
    base (m:ℕ): let a := A.B.a; Time.base G (a.params m) ≤ a.clock.hatBeta m ^ (e (a.clock.J (m+1)) (a.clock.J m))

def taxi (e:ℕ→ℕ→ℝ) : Goal G where predicts {_M} {_D} {A} _ := Barrier A e -- variable matching pattern issue
lemma relation {d:BudgetPoint}{T:RG.Stage} (h:Time.Same T d): Toft.stock G d * Real.exp ((d.supportExponent+1)*81)= Toft.stock G (Time.probe T) * Real.exp ((T.supportExponent+1)*81):=by
   unfold Toft.stock turnFee pairBill; dsimp only [Time.probe]; rw [h.1,h.2.1,h.2.2]

lemma gates (e:ℕ→ℕ→ℝ)(h:∀ i j,StepStages j i→0< e j i): Funds (G:=G) (taxi e):= by
    intro s K R A hc F U b hS
    refine ⟨s.floorL,fun l _ D w P Υ φ S θ p Px V hy=>?_⟩
    let a i:= s.profile i
    have hx(j i:ℕ)(hk:StepStages j i) :∀ᶠ t:ℝ in atTop, Toft.stock G (Time.probe (a i)) * Real.exp (((a i).supportExponent+1)*81) ≤ t ∧ (radiusB t:ℝ)≤t∧Time.base G (a i)≤ t ^ (e j i):= by
        have hz:= (tendsto_rpow_atTop (h i j hk)).eventually_ge_atTop (Time.base G (a i))
        filter_upwards [eventually_ge_atTop (Toft.stock G (Time.probe (a i)) * Real.exp (((a i).supportExponent+1)*81)),hz,(Work.E09.radiusB_small 1 zero_lt_one 1).bound zero_lt_one,eventually_gt_atTop 0] with t ht hz hh hT
        refine ⟨ht,?_,hz⟩; simpa only [pow_one,Real.rpow_one,Real.norm_of_nonneg (le_of_lt hT),Real.norm_of_nonneg (Nat.cast_nonneg _),one_mul] using hh
    obtain ⟨X,-,hv,hf⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ (hx j))
    refine ⟨{V with betaEntry:= X},⟨hv,le_rfl,le_rfl,le_rfl⟩, fun V' hZ T W X H=>?_⟩
    intro A J η E' Z J' K' b hK hY hm
    change Barrier _ _
    have ht m:=step_paid H.a m
    have hp m:= hf _ _ ((hZ.beta _).trans (H.valid.pays m)) _ (ht m)
    have hu m: a (H.a.clock.J m)=H.a.params m:= (params_eq H.valid m).symm
    refine ⟨fun m=> ?_,fun m=> (hp m).2.1,fun m=> ?_⟩
    · refine (relation (show Time.Same (H.a.params m) (H.a.budget m) from ⟨rfl,rfl,rfl⟩)).trans_le ?_
      rw [← hu]; exact (hp m).1
    intro a₀; change Time.base G (H.a.params m)≤_
    rw [← hu m]; exact (hp m).2.2
end YM.RG01Estimate.Chart

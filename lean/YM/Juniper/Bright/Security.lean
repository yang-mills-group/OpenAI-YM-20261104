import YM.Juniper.Bright.Victor
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Rent
/-!
 # New **pre-L** demand for same-literal valuation at any power on any $Θ schedule
 Later currencies not transferable between Q: each path working needs this SAME pledge.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Bright
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Pressure
open PhysicalNext PhysicalNext.Repeat
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Push.PriceCompiler ConnectedActivityE6
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge}
def PearlAt {P:Teller G}(Q : ConnectedActivityE6.Target G P)(L:Side): Prop:= ∀ (X:Q.Expense)(W μ:ℝ)(o:Target.Order G W),0<W→0<μ→X.wanting< -(3/8:ℝ)→
       ∀ (p:ℝ) (k n j:ℕ), (-(3/8:ℝ))*k<p → ∀ (χ: Push.SectorMeasure.Chi), ∀ᶠ B:ℝ in atTop, Valuable X L k n j χ B μ p o
variable {s:Sheet G} {K : MapPrices} (Q : Targets s K)
def floorPrice : ℕ →ℕ:= fromMax (fun i j=> (pearl (Q i j)).choose)
abbrev Rhinestone (D:Rolls s) := ∀ i j, StepStages i j→ PearlAt (Q i j) (D.L i)
lemma precious (D:Rolls s) (h:floorPrice Q ≤ fun i=> (D.L i).val) : Rhinestone Q D:=fun i j hi=> (pearl (Q i j)).choose_spec _ ((le_fromMax (fun i j=> (pearl (Q i j)).choose) hi).trans (h i))
end YM.Juniper.Bright

import YM.OPE.Compatible.Yolk.Turn
/-!
# Stage endpoint. Needed nchosen after fixed L, supplies with no history assumptions other than regular portfolio and affordability.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C s : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
def secure (D:Patch)(Q:YM.ConnectedActivityE6.Target G P)(o:ConnectedActivityE6.Target.Order G W)(L:Side)(μ x C:ℝ)(m:ℕ)(a δ e d b y:ℝ):=∀ {c f:Side}{S:StepData c f}{R:Rep G f}{T:Tube G S},∀ (H:Cash W x μ L Q o C T R), S.patch=D → Stamp T → HasSlots R.p R.activities → Cash.Renewed m a δ e H →
       ∀ (F:Forest S.ratio)(X:Coat T F), X.x=x → X.width=o.K → RG.flags (Pressure.temp x) X.V=∅ → ∀ g:LogField G c,X.V=represent g→‖g‖≤d → Sparta R S F X.V (P.top.supportExponent-Q.ε) (freight Q L μ x) (incomingK G L x) b y
lemma operates (D:Patch)(L:Side) (Q:YM.ConnectedActivityE6.Target G P)(o:ConnectedActivityE6.Target.Order G W) (C : ℝ)(m:ℕ) (h: D.Branches P.bind G)(hp:foam Q L) (he:0<Q.exp)(hμ:0<μ) (i j:ℕ): ∃ n:ℕ,∀ᶠ x in atTop,∀ (a δ e:ℝ), secure D Q o L μ x C m a δ e (skimX G L x*echoL G L x^i) (skimX G L x*echoL G L x^n) (Real.exp (-(echoL G L x)^j)):=by
   obtain ⟨k,hk⟩:= vault Q L j hμ; obtain ⟨n,hn⟩:= opine (C:=C) (μ:=μ) Q (o:=o) D L h i k
   refine ⟨n,?_⟩; filter_upwards [hk,hn,summer Q o L hp hμ D C,stretchY Q L hμ m he,(Work.E01.radiusB_tendsto.comp (Work.E09.betaF_growth G L)).eventually_ge_atTop (4*L.val+1)] with x hx hy he ha ht a δ e
   intro c f S R T H hS hT hV hY F X hH hm hJ g hG hN; subst x; subst D
   have hσ := H.laws.data.funds.length_eq
   obtain ⟨s,he⟩:=he
   have hZ:=terrain X H hm hT hY he ha (hy _ he) hp (Real.exp_pos _|>.le) hG hN hJ hV (by rw [H.laws.intake.sizes,hσ];exact ht)
   refine ⟨hZ.branch,hZ.charge,hZ.leaves,fun i=> (hZ.flare i).trans (mul_le_mul_of_nonneg_left hx hZ.branch.le)⟩
-- caller needs Stamp and Cash AFTER, allgood can always issue X via Tag.a window or F.emanance; requires existence Coat over any V. trivial
lemma courier (χ:Chi) (x A:ℝ) (F:Forest S.ratio) (V:Config G c):∃ X:Coat T F, X.V=V∧ X.x=x ∧ X.width=A:= by
   refine ⟨⟨{ costs:=∅, aisles:=∅, flags:=∅ },x,χ,A,V, Classical.arbitrary _,1⟩, rfl,rfl,rfl⟩
end YM.PhysicalNext.Repeat.Aroma

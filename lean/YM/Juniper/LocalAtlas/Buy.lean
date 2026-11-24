import YM.Juniper.LocalAtlas.Stadium
import YM.Juniper.Provider.Nursery
/-!
 # Shape boost for B arc
 Uses actual PRECUToff high orders J CAN ask order>Profile.J from service.
 δ book holds whole profile: only need eventually J across scales. EPS shrinks
 with j, on `moor i` aux stencil calls only; not claiming POLY Λ prices here.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.LocalAtlas
open Function Filter Lattice RG Wilson Pressure Tree Input Org
open Push Push.AbsoluteSums Precision Push.PriceCompiler
open ConnectedActivityE6 Coat
open PhysicalNext PhysicalNext.Repeat Pane Roof Roost Legato Lantern Sienna
open AnalyticBridge VerifiedReset Collection Quotes
open Next.Fluctuations SectorMeasure Further.PhysicalPeriodLimitF933 Mural Uniform RG.Shoot Supply
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X : Metals G} (D:Rolls X.p) {C : Targets X.p X.K} {E:Expenses C}
    {p : Return.Wages} {v:ℕ→ℝ}(R:PhysicalNext.Repeat.Register D E p v) {P:Protection D}

noncomputable def leew (j:ℕ):ℝ:= (j+1:ℝ)⁻¹
private lemma lease (j:ℕ):0< leew j:= by unfold leew; positivity
local notation "Y"=> Roof.invitation D C

def Element (χ:ℕ→ℕ→ℝ→ℝ)(j i n:ℕ) (t:ℝ): Prop :=
    let P₀:= X.p.profile j; let Q:= X.p.profile i; let L:=D.L j; let V:= ConnectedActivityE6.loopBill G (D.L j) t; let z:= betaF G t L; let u:=eaves G L t; let o':=furl G L t
    Real.exp 1 ≤ t ∧ 2*o'<u ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F:Forest S.ratio) (B B' : BudgetPoint) (k:S.Choices) (h : 4≤j), S.patch=(Mural.sheet X.p D h) → S.kernel = X.p.kernel →
     Quilt T F (χ j i t) → T.high=P₀.clip→ T.low=Q.clip → T.up.Bounds T.high P₀.width P₀.paths V → T.down.Bounds T.low Q.width Q.paths V →
    ∀ α ρ, |α| ≤ cloak D j → Critical F T.high T.up ρ → (∃ ρ', Critical F T.high T.up ρ'∧ ClassicalMatch F T.high T.low T.up T.down ρ') → B'.threshold=Pressure.temp t →
    ∀ β a, Cash (p j i) t (R.μ j i) L (C j i) (R.o j i) a T (virgin T B β) →
     ∀ y : Positions (Uniform.Primary c G),flags B'.threshold (Boulevard.actual y)=∅→ ‖y‖+2*o' < u→
      0 < S.push β (virgin T B β).eval (Boulevard.actual y) ∧
       Estimate F T (C j i|>.table) k ρ n α (z^leew j)∧
       Blaze.Brush Q.order (3*z^(leaf n+leew j)) u⁻¹ (Token.harmony T B β α-arctic F T (C j i|>.table) k ρ n α β) y
lemma climate_w (χ:ℕ→ℕ→ℝ→ℝ)(j i n:ℕ)(h:StepStages j i) (hv:Bolt G (D.L j) (χ j i)) : ∀ᶠ t in atTop, Element D R χ j i n t:=by
   let K:= (X.p.profile i).order+n+1; have hp : n<K:=by unfold K; omega
   have ht : 2 ≤ K:= le_trans (le_trans (by decide : 2≤ 6) (X.p.profile i).order_ge) (by unfold K; omega)
   let P' := X.p.profile j; let T':= X.p.profile i; let L:= D.L j
   have hx:= (eventually_ge_atTop (Real.exp 1)).and (Sienna.contraction G (D.L j) (a:=2) zero_lt_one (belt G L) (by norm_num [Sienna.vow] : -1 < Sienna.vow))
   by_cases he:4≤j; swap
   · filter_upwards [hx] with t ht; refine ⟨ht.1,?_,fun _ _ _ _ _ _ _ _ h=>False.elim (he h)⟩; simpa only [Sienna.eaves,one_mul] using ht.2
   let Q:= Mural.sheet X.p D he; obtain ⟨M⟩:= Uniform.pre_order G P'.width P'.paths Q.J X.p.kernel (n:=K+1+2+3) (by omega)
   let E:= Classical.choice (Planned.JetPort.BareRates.offered G T'.width T'.paths (K+1+2)) -- namespace
   let F:= Classical.choice (Planned.JetPort.BareRates.offered G T'.width T'.paths (K+1+2+3)) -- namespace
   obtain ⟨Yc,hC,H⟩:= summit Q (C j i) (R.o j i) n K hp M (Classical.choice (Planned.JetPort.purchase (C j i|>.table) (C j i|>.table_exists) _)) E F P'.clip T'.clip ht hv (cloak D j) _ _ (R.consumes _ _ h).2.1 (lt_add_of_pos_right (leaf n) (lease j))
   filter_upwards [H,hC _ (lease j),hx] with t H' hC' hu
   refine ⟨hu.1,?_,fun c f S T F B B' k h hh hK hQ hp hh₀ hp' hT α ρ hα hρ hK' hr β b W y hw hx=>?_⟩
   · simpa only [Sienna.eaves,one_mul] using hu.2
   let X':= Greenbelt.prism T t Chi.canonical (R.o j i).K (Boulevard.actual y) F; rw [hr] at hw
   obtain ⟨hv,⟨hg,hΨ,hζ⟩,hU⟩:= H' c f S T F hh hK k B B' hr hQ hp hh₀ (hp ▸ hp') (hh₀ ▸ hT) ρ hρ hK' β b W X' rfl rfl hw.symm hw α hα y rfl hx
   have hc:= (le_abs_self _).trans hC'
   refine ⟨hv,⟨fun j hj=> (hg j hj).trans hc,fun j hj=> (hΨ j hj).trans hc,fun j hj=> (hζ j hj).trans hc⟩,hU.smaller (by unfold K; omega)⟩

abbrev Climate:= Element D R (Y)
lemma climate_events (j i n:ℕ)(h:StepStages j i) : ∀ᶠ t in atTop,Climate D R j i n t:= climate_w D R _ j i n h (Trio.circles G (D.L j) (C j i|>.halo))

def Confirm (U:Delays P) := ∀ j i, StepStages j i→∀ x,U.betaEntry j ≤ x → ∀ n≤j,Climate D R j i n x
lemma catalog (V:Delays P) : ∃ W:Delays P,DelayLe V W∧ Confirm D R W:= by
   have ht j i (h:StepStages j i) : ∀ᶠ x in atTop, ∀ n≤j,Climate D R j i n x:= (Set.finite_Iic j).eventually_all.mpr fun n _=> climate_events D R j i n h
   obtain ⟨f,-,hN,hP⟩:= collect_upper V.betaEntry _ (fun j=>eventually_transitions j _ _ (ht j)); exact ⟨{V with betaEntry:=f},⟨hN,le_rfl,le_rfl,le_rfl⟩,fun j i h t ht=> hP j t ht i h⟩
def proofBody (G:Gauge) : Legato.Booster G where
   asks S _ _ W:= Confirm _ S W
   mono h hv:= fun j i hi t he=> h j i hi t ((hv.beta j).trans he)
   buy S _ _ W:=catalog _ S W
-- Extended, retain Extras first
noncomputable def demand (E:Extras G): Extras G := { E with booster:= E.booster.and (proofBody G) }
lemma confirmed {hG:G.Simple}{N:Nursery G hG} (E:Extras G) (h:Stock (demand E) N): Confirm N.P N.X.shape N.A.delay := h.boosted.2
end YM.Juniper.LocalAtlas

import YM.LocalLTE.Motion.Mode
import YM.LocalLTE.Motion.Flit
/-! # Sharp itinerary frequency
All labels common, support ball of E_q leaves specified only at epochs whose radius G design. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.East
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Height LocalLTE.Fan Pastel -- namespace edit
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {T₀ : Patch} {ℓ k j n: ℕ} {K : Teller G} {s a W U V g C' y A M K₀ r β δ q b v σ t w Λ γ: ℝ} {m : ℕ}
variable {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} (H : Cash W s a L X o U T R) {I: Cash W s a L X o U T R'} {χ : Chi}
local notation "B" => radiusB s
open PhysicalNext.Repeat Roost
open YM.LocalLTE FrameBox Inset PriceCompiler
open LocalLTE.Fan Field Fan.Bakers Vine
variable {κ :ℝ}
-- on actual same epoch. Cane fixed R=base. δ tune.Numeral input scope.`Works` inside any H.
variable (f':ℕ→ℕ) (Q:H.fragrances) (hQ:East.lectures H j n f' Q) {I:Type} {φ : Filter I} (A:I→Rep G f) (G':∀ i,Cash W s a L X o U T (A i))
    (hS:Stamp T) (hw:Peers L s K X W o k j m n κ)
    (hc:∀ i,let H:=A i; H.path=R.path ∧ H.p=R.p∧ H.activities.reg=R.activities.reg ∧ H.activities.forced=R.activities.forced)
    (hE:∀ i:ℕ, f' i≤j→∀ V:Config G f, flags R.p.threshold V=∅ → Tendsto (fun x =>(A x).activities.E i V) φ (𝓝 (R.activities.E i V)) )
    (hA:Tendsto (fun x=> (A x).beta) φ (𝓝 R.beta))
local notation "ζ"=> (Inset.cone (-(1/2)) (betaF G s L))
local notation "Y"=> Fan.postponement L s o
-- convergence requires Packed pin and occupancy all x.Interpolation lemmas separately
variable (hK:∀ i, Coup.License j (A i) κ (betaF G s L) f' (L.val* Pressure.radiusB s))
include hE hA hc hQ
lemma chorus (r:Tree.Forest S.ratio)(V:Coat T r) (v:Vine.Disk G c)(i:Option (Fin Q.fst))(z:Air f G)(h:flags R.p.threshold (Vine.inputΛ V z v)=∅)(j':Veil c f)(hj:j'∈ East.docket H Q i) : Tendsto (fun x=> Fan.coming X.table (A x) V v z j') φ (𝓝 (Fan.coming X.table R V v z j')):= by
   have hh {p:ℕ} (D:PathData G→ℕ→ Atom G p) (k: Trans f)(c:I→ℝ){t:ℝ}(h':Tendsto c φ (𝓝 t)) : Tendsto (fun x=> Vine.atomΛ V (D (A x).path) k (c x) z v) φ (𝓝 (Vine.atomΛ V (D R.path) k t z v)):=by unfold Vine.atomΛ; simp_rw [fun x=> (hc x).1]; exact h'.mul_const _
   have he := hA.neg.mul_const Raw.orientation; rcases j' with l|l|l|l|l
   · exact (hE l (hQ.2 i l hj) _ h).neg
   · exact hh (·.cubic) l _ he -- t implicit is fixed section `t`!
   · exact hh (·.quartic) l _ he
   · exact hh (·.loop) l _ tendsto_const_nhds
   rcases l with l|l|l
   · exact he.mul_const _
   all_goals exact tendsto_const_nhds

omit hE hA hc
lemma parity {p:ℝ} (D: Cash W s a L X o U T R') (hp:∀ (R:Rep G f)(D:Cash W s a L X o U T R)(A:D.fragrances), East.lectures D j n f' A → Coup.License j R κ (betaF G s L) f' (L.val*Pressure.radiusB s) → ∀ (i:Option (Fin A.fst)) (F:Forest S.ratio)(Y':Coat T F), Y'.x=s→ Y'.width=o.K → let C:=East.docket D A i; let F:=Fan.Field.pin C D
           ∀ (u₀:Fan.Bakers.LevelsΛ C m),∀ y: Blaze.Vine.Disk G c, ‖y‖< ζ →∀ w∈ Fan.cabinet F (Fan.postponement L s o), Brush k p 1 (fun y=>Fan.Bakers.songP Y' R C X.table F y w u₀) y)
    (h:R'.path=R.path)(h₂:R'.p=R.p)(ht:R'.activities.reg=R.activities.reg)(hx:R'.activities.forced=R.activities.forced)(hL:Coup.License j R' κ (betaF G s L) f' (L.val*Pressure.radiusB s)) (i:Option (Fin Q.fst)) (F:Forest S.ratio)(Y':Coat T F)(he:Y'.x=s)(hY:Y'.width=o.K) : let C:=East.docket H Q i; let V:=Fan.Field.pin C H
           ∀ (u₀:Fan.Bakers.LevelsΛ C m),∀ y: Blaze.Vine.Disk G c, ‖y‖< ζ →∀ w∈ Fan.cabinet V (Fan.postponement L s o), Brush k p 1 (fun y=>Fan.Bakers.songP Y' R' C X.table V y w u₀) y := by
    obtain ⟨u,c,⟨S₀,v,e1,k1⟩,m,b,t⟩:=R; obtain ⟨r,C,⟨S₁,V,e2,k2⟩,M,b₁,T₁⟩:= R'; have hQ':= ((East.literal_cal H (X':=D) (Match.staple h.symm ht.symm hx.symm) rfl 0 j n h.symm ht.symm hx.symm f').1 Q).mp hQ;
    cases h; cases h₂; cases ht; cases hx; exact hp _ D Q hQ' hL i F Y' he hY
include hE hA hc
variable [φ.IsCountablyGenerated]
include G' hK hw hS
-- seats. transport support.c.A.Flag priors.Fork. Need Plans λ history. Cost Book.
lemma sunrise_b (r:Tree.Forest S.ratio)(V:Coat T r)(hr:V.x=s)(hX:V.width=o.K)(i:Option (Fin Q.fst))(D' : Fan.Bakers.LevelsΛ (East.docket H Q i) m): ∀ᶠ y: Vine.Disk G c in 𝓝 0,
     let F:=Field.pin (East.docket H Q i) H
     Tendsto (fun x=>Fan.Bakers.curlP V (A x) (East.docket H Q i) X.table Y F y D') φ (𝓝 (Fan.Bakers.curlP V R (East.docket H Q i) X.table Y F y D')):=by
    obtain ⟨hz,⟨d,hd⟩,p,hp⟩:= hw; let D:= docket H Q i; let F:=Field.pin D H
    let J y (R:Rep G f) (z:Body (↥F)) := Fan.Bakers.songP V R D X.table F y z D'
    have hY(x:I)(y:Disk G c)(hv: ‖y‖ <ζ) (z:Body (↥F))(h:z∈Fan.cabinet F Y) : ‖J y (A x) z‖ ≤ p:=by
       -- deploy actor at (A x). Note A records p equal. Need adaptation Magazine.B.F.f.Struct. lemma by cases
       obtain ⟨h₀,h₁,H₀,hX'⟩:=hc x; exact (East.parity H f' Q hQ (G' x) (fun R H A h v i F U hX hx=> hp c f S T R H.laws.data.funds _ _ H A h.1 i f' h.2 v F U hX hx) h₀ h₁ H₀ hX' (hK x) i r V hr hX D' y hv z h).bound
    have he:= Fan.Bakers.brightening V H hr hX hS (hp:=fun z h=> hd c f S T R H.laws.data.funds _ _ H r V hr hX z h) (hv:=hz)
    filter_upwards [he,Metric.ball_mem_nhds (0:Disk G c) hz] with x hx ht; dsimp only
    let v':=mem_ball_zero_iff.mp ht
    let S':= Fan.cabinet F Y; let μ:= (Fan.pool F V 0).restrict S'
    have hz (i:I):AEStronglyMeasurable (J x (A i)) μ:= (Fan.Bakers.commerce _ D F x (G' i) hr hX D').aestronglyMeasurable
    have h:∀ᵐ z : Body (↥F) ∂μ, z∈S':= ae_restrict_mem (Fan.alive F Y)
    refine tendsto_integral_filter_of_dominated_convergence (fun _=>p) (Eventually.of_forall hz) (Eventually.of_forall (fun y=> ?_)) (integrable_const _) ?_ -- Name and argument order
    · exact h.mono fun i hi=> hY y x (mem_ball_zero_iff.mp ht) i hi
    filter_upwards [h] with z hz
    have he:∀ j,|Pond.spill F z j| ≤ |Y|:= by
        have hV:0 ≤ Y:= by unfold Fan.postponement; have he:= Delay.monitor_pos G L s; have hv:=o.rare; positivity
        intro j; exact (Fan.fur F hz hV j).trans (le_abs_self _)
    have hP: flags R.p.threshold (inputΛ V (Pond.spill F z) x)=∅:=by
       apply Finset.not_nonempty_iff_eq_empty.mp; rintro ⟨x,h⟩; obtain ⟨k,-,hk⟩:= (flags_spec ..).mp h; exact (hx _ he k).not_gt hk -- check .not_gt
    unfold Fan.Bakers.songP; apply Tendsto.const_mul; unfold lilies; exact tendsto_finsetProd _ fun k _=> by unfold ask; exact Tendsto.const_mul _ ((chorus H f' Q hQ A hc hE hA r V x i _ hP k.val k.2).pow _)
end YM.PhysicalNext.Repeat.East

import YM.LocalLTE.Motion.Half
/-! Aux burning per star. Gold & Ruby over admitted readers. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Urns
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open YM.LocalLTE.Inset ClockB
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} {C:Targets X.p X.K} {Z:Expenses C} {F : ℕ→ℕ→Postage} {S:Time.Scouts (F:=F)} {p : Return.Wages} {s: Set ℝ} {v:ℕ→ℝ} {R:Register D Z p v} {c f:Side} {κ q η l e w : ℝ} {p' : ℕ} (W:Wind p' η) {m n j k N :ℕ} (hm:m<N)
    (hk:Reliable G κ q) {d:ℕ→ℕ→ℝ}
    (hV:Roof.WorksIn R A.post A.delay S) (hX:Spoke D R W A.post κ d A.delay)
    (h:Rich R (1/16) A.delay)
    (hP: Tenement R A.delay)
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall LocalLTE.Fan Pastel -- order
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "A₀" => A.B.a.S.side m n
local notation "B" => (A.B.a.budget m)
local notation "b" => Trio.resize W.ℓ (Rain.lint C A m)
local notation "z" => Trio.base b (radiusB x₀)
local notation "D₀" => Meadow.studioN W.ℓ (Rain.lint C A m) (radiusB x₀)
local notation "Jp" => A.B.a.clock.J (m+1)
local notation "Ip" => A.B.a.clock.J m
local notation "L" => D.L Jp
local notation "g" => gold G L x₀
local notation "γ" => A.B.kin.alpha N m
local notation "t" => X.p.profile Ip
local notation "s₀" => ClockB.lanternPay G L t W.q x₀
local notation "χ" => Chi.canonical
local notation "C₀" => yside (C:=C) (m:=m) (A:=A) W
local notation "P₀" => scene (C:=C) (m:=m) (A:=A) W
local notation "T" => Pane.orchestra A N
variable {β:ℝ} (X': Expose (A:=A) (R:=R) W β N m) (M:Maps (A:=A) (C:=C) W m N) (ht:AsDivisors A.B.a.S)
   (hC:(C (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).table=X.O)
   (hq: X'.Yields W k)
local notation "P'" => fronts (m:=m) (A:=A) (C:=C) W
open LocalLTE.FrameBox.Grove
variable {d':ℝ}
-- use Hart estimates at all x: true but parameter v changes β. M not.
section
open LocalLTE.Inset LocalLTE.Frame Token Shellac
lemma chorusAt (i:Stars) (j:ℝ)(V':Config G (C₀ i))(v:ℝ) (hv:v≠0) : ContinuousAt (fun ν=> M.reader W κ j ν i V') v:=by
    let E:=Positions (Uniform.Primary (yside (m:=m) (A:=A) (C:=C) W i) G); let D':= wick G L j x₀
    let Ψ :=LocalLTE.Inset.joint (M.tree i) (Pane.orchestra A N (P₀ i)) (C Jp Ip).table (M.station i) D' (M.notes i)
    let f:(ℝ×ℝ)→ E → ℝ:= fun v x=>
        YM.LocalLTE.stem (p'+1) Ψ (v.1,x) + v.2* LocalLTE.stem (p'+3) (Shellac.cedar (M.tree i) (Pane.orchestra A N (P₀ i)) (M.station i) (M.notes i)) x + LocalLTE.stem (p'+1) (shed (M.tree i) (Pane.orchestra A N (P₀ i)) (C Jp Ip).table (M.station i) γ (M.notes i)) x
    have h:Continuous (fun x:(ℝ×ℝ) × E=>f x.1 x.2):= ((((LocalLTE.stem_contDiff (m:=0) _ _).continuous.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).add ((continuous_snd.comp continuous_fst).mul ((LocalLTE.stem_contDiff (m:=0) _ _).continuous.comp continuous_snd))).add ((LocalLTE.stem_contDiff (m:=0) _ _).continuous.comp continuous_snd))
    let x:=LocalLTE.Frame.convertLinks Chi.canonical κ 1 V'
    have he:Continuous fun v:ℝ×ℝ=> LocalLTE.Frame.placed Chi.canonical κ (f v) V':=by
       rw [← continuousOn_univ]; let K (v) (i:G.El):= f v (LocalLTE.Frame.adj i x); change ContinuousOn (fun Ψ=>∫ u:G.El,K Ψ u ∂G.probHaar) _
       apply continuousOn_integral_of_compact_support (k:= Set.univ) isCompact_univ _ (fun i hi j hj=>False.elim (hj trivial)) -- edit
       exact (h.comp (show Continuous fun y:(ℝ×ℝ)× G.El=> (y.1,LocalLTE.Frame.adj y.2 x) from continuous_fst.prodMk ((LocalLTE.Frame.adj_el _).comp continuous_snd))).continuousOn
    change ContinuousAt ((fun v:ℝ×ℝ=> LocalLTE.Frame.placed Chi.canonical κ (f v) V') ∘ fun x:ℝ=> (x,x⁻¹^2)) v
    apply ContinuousAt.comp he.continuousAt; exact (continuousAt_id.prodMk ((continuousAt_id.inv₀ hv).pow 2))
lemma pointRead (i : Site (A.B.a.S.side m n))(η :ℝ)(h:η≠0)(j:ℝ)(X': Config G (A.B.a.S.side m n)) : ContinuousAt (fun ν=> Urns.inkO (κ:=κ) W M j i ν X') η :=by
    unfold inkO LocalLTE.Patch.mural; simp_rw [Pi.neg_apply,Finset.sum_apply,Pi.smul_apply,Function.comp_apply]
    unfold Boulevard.stillA; refine Tendsto.neg (tendsto_finsetSum _ fun «b» _=>?_); exact Tendsto.const_mul _ ((chorusAt W M _ j _ η h).tendsto.sub (chorusAt W M _ j _ η h).tendsto)
end
variable {u':ℕ}{Θ:ℝ}
include X'
lemma motU (i: Site (A.B.a.S.side m n)) (j:ℕ)(he: Straps D C W κ d' x₀ Jp Ip u' j Θ)(ht₁:m<N)(x:Directions G (A.B.a.S.side m n))(hx: ‖x‖< YM.LocalLTE.Inset.cone clr (betaF G x₀ (D.L Jp))): Brush (Urns.due j (X.p.profile Ip).order) (Urns.trimSum Θ) 1 ((inkO W M d' i (κ:=κ) (gStep β)) ∘ soloV) x:=by
    let V':= M.reader W κ d' (gStep β); let n':= due j (X.p.profile Ip).order
    unfold inkO LocalLTE.Patch.mural
    have hg s : Brush n' Θ 1 ((Boulevard.stillA (V' s)) ∘ Slide.shape (Trio.pad (P') s) i ∘ soloV) x:=by
       let Z:= LocalLTE.FrameBox.Hall.lumen (G:=G) (Trio.pad (P') s) i
       have hp:‖Z‖≤1:= Hall.focus ..; have ht:‖Z x‖ ≤ ‖x‖ := (Z.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hp)
       have hh:= Brush.reading Z (Urns.angled W X' M d' he s (Z x) (ht.trans_lt hx) ht₁) hp; rw [one_mul] at hh
       apply hh.shimmy; filter_upwards with y; exact congr_arg (Boulevard.stillA (V' s)) (Hall.sweep (Trio.pad (P') s) i y|>.symm)
    apply (Brush.spree Finset.univ _ _ zero_le_one (fun s _=> (hg s).smul (Slide.ray s))).opposite.shimmy; filter_upwards with y; simp only [Function.comp_apply,Pi.neg_apply,Finset.sum_apply,Pi.smul_apply]; rfl
end YM.PhysicalNext.Repeat.Urns

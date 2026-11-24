import YM.Contacts.Poetry.Stamp
import YM.Contacts.Terrain.Cardinal
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Rest
/-! Adapted from Song/{Embassy,Litho}. Exact energy criterion BEFORE mask harmonization. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Poetry
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo Terrain Refrain
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i : ℝ} {k j n ℓ : ℕ}
variable (p : BudgetPoint) (H : Cash W s μ L Q o α T R) (χ : Chi)
abbrev arena (β γ:ℝ): Magazine H → Config G c→ℝ := Sum.elim (Song.sequence H (runway H) χ) (sounding T.down T.low β γ)
abbrev gallery (β γ:ℝ) : Collection.Source G c := ⟨choir (arena H χ β γ) ∘ pennant H, fuse H (runway H) χ ∘ Refrain.badge H⟩
-- use Marquee only. API (No post at Reset yet)

section toll
variable (N : Captain H j C' d v Y A b r B q k χ) (O : Tree.Forest S.ratio) (hp : p.threshold=Pressure.temp s) (hP : p.order ≤ j)
    (hB : p.B=radiusB s) {σ C Λ : ℝ} (hx : T.down.Bounds T.low σ C Λ) (h : Cash.Renewed n a δ e H)
include N h hp hP hx
lemma aroma (γ α' : ℝ) (V : Config G c) : ((Beam.marquee H p).read (gallery H χ (R.beta+α') γ)).additive p V=((Beam.marquee H p).read (gallery H χ R.beta γ)).additive p V+ (-α')*(billOf p T.down.cubic V+billOf p T.down.quartic V) := by
  let A₀:= Beam.marquee H p
  let C₀:=Real.log (H.homesteadPool χ V)+γ*Collection.receipt T.down T.low p V
  have ht (β:ℝ) : (A₀.read (gallery H χ β γ)).additive p V= -(Real.log (H.homesteadPool χ V)) + (-(γ*Collection.receipt T.down T.low p V+(β*(billOf p T.down.cubic V+billOf p T.down.quartic V)+billOf p T.down.loop V))) := by
    refine ((pennant H).hasSum_iff.mpr (voices (Beam.contents H p) (arena H χ β γ) p V _ ?_)).tsum_eq; intro t
    let u := Seat.view t V
    have he : HasSum (fun i=> masked p.threshold (scaleT p H i).support (arena H χ β γ i) u) (-(Real.log (H.homesteadPool χ u))+ (-(γ*Collection.receipt T.down T.low p u+(β*(billOf p T.down.cubic u+billOf p T.down.quartic u)+billOf p T.down.loop u)))) := HasSum.sum (summon p H (runway H) χ N hp hP h u) (literalScore T.down T.low p u β γ hx)
    unfold u at he; simp_rw [Beam.patch]; rw [harmony χ h V t, Seat.view, Collection.receipt, layer_spread,bill_spread p _ hx.width hx.three, bill_spread p _ hx.width hx.four,bill_spread p _ hx.width hx.two] at he; exact he
  rw [ht,ht]; ring
omit N hp hP h hx
lemma highReceipt (V:Config G c) (A:PathData G) (c₀ : Clip) {σ C Λ:ℝ} (hx:A.Bounds c₀ σ C Λ) (b:ℝ) : layer (upperFade A p b 0) V= (-b)*(billOf p A.cubic V+billOf p A.quartic V) := by
  rw [show upperFade (n:=c) A p b 0=_ from funext (fun d=> funext fun U=> high_fade_eq b 0 U d),layer_scale,add_zero]; apply congr_arg
  have ht (W: Config G c) : (∑' i,summit A p i 0 W) = PathData.atomSeries A.cubic p W 0 + PathData.atomSeries A.quartic p W 0:= by
    have he:=summit_sum hx p W 0; exact (he.comp_injective Sum.inl_injective).tsum_sum (he.comp_injective Sum.inr_injective)
  have he i (Z:ℕ→Atom G i) (_h: SumBudget (fun k=> (Z k).budget σ) C) : billOf p Z V = VerifiedReset.factor * ∑ x: Seat c, PathData.atomSeries Z p (x.view V) 0:= by
    unfold billOf; rw [← Equiv.sum_comp (splay c) (fun x=> PathData.atomSeries Z p (Seat.view x V) 0),Fintype.sum_prod_type]; simp_rw [PathData.atomSeries,plumes]; rfl
  rw [layer]; simp_rw [ht]; rw [Finset.sum_add_distrib,mul_add,he _ A.cubic hx.three, he _ A.quartic hx.four]
-- Remove include H etc
include N hp hP h hx
lemma monopoly (γ:ℝ) (hv: Geo.Width p T.low σ)(hc: WilsonStartup.Decent T.low p) (V: Config G c):
    earlyValue (Beam.marquee H p) T.down T.low p (gallery H χ (R.beta+γ) γ) (R.beta+γ) (weighty H χ O) 0 V * Real.exp (layer (fun d:Low=> d.loan T.down T.low 0 p γ 0) V) = S.push R.beta R.eval V := by
  let τ:=weighty H χ O; let L:= Beam.marquee H p; let T':= T.down; let Z:= gallery H χ (R.beta+γ) γ; let v:= gallery H χ R.beta γ; let F:= Real.exp (layer (fun d:Low=> d.loan T' T.low 0 p γ 0) V)
  rw [← Song.forward p H (runway H) χ γ N O hp hP hx h V,← Beam.travels H p]
  have he: (L.read Z).gas p V=(L.read v).gas p V:= rfl
  have hk: (L.read Z).additive p V=(L.read v).additive p V+ layer (upperFade T.down p γ 0) V:= by rw [highReceipt p V T.down T.low hx γ]; exact aroma p H χ N hp hP hx h γ γ V -- edit
  unfold earlyValue Rep.eval Rep.exponent; dsimp only [Collection.frozen]; rw [neg_zero,zero_mul,Real.exp_zero,mul_one]
  rw [mul_right_comm (Real.exp _) ((Beam.marquee H p|>.read _).gas p V) (Real.exp _),mul_right_comm (Real.exp _) ((Beam.marquee H p|>.read _).gas p V) (Real.exp (-γ*_)), ← Real.exp_add, ← Real.exp_add]
  apply congr_arg₂ _ ?_ he; apply congr_arg Real.exp
  change τ* _ - _ - (L.read Z).additive p V+_ = τ* _ - _ - (L.read v).additive p V+_
  rw [hk, BetaTransport.channels_split V (R.beta+γ),BetaTransport.channels_split V R.beta]
  have hx := path_split hx hv hc γ 0 V; simp only [add_zero,zero_mul] at hx; have he:layer (fade T.down T.low p 0) V=0:= by
    unfold layer; have he i x:fade (n:=c) T.down T.low p 0 i x=0:= by unfold fade masked Low.fresh; simp
    simp_rw [he]; simp
  rw [he,zero_add] at hx; unfold Collection.receipt; linarith
include hB
-- shifted payload regular & K inheritance without epoch.
lemma desert (ha: preExponent p ≤ a) (ht:Armada Q L μ a s i B j k) (hn:p.power ≤ ℓ)(hd:WilsonStartup.Decent T.low p) (hw:preExponent p/p.B ≤ σ/2) (β γ:ℝ) : Collection.Local (Beam.marquee H p) p (gallery H χ β γ) (turnFee p*((collars G i s j ℓ*(salary Q L μ B s j k*(1-1/2)⁻¹))+Song.octaveNeed G p T.low σ C Λ β γ)) (Cash.armK Q L μ s 0 n) := by
  have he z: p.Regular (Beam.dashboard H z).support (Song.sequence H (runway H) χ z) ∧ p.supBounds (Beam.dashboard H z).site (Beam.dashboard H z).support (Song.sequence H (runway H) χ z) (N.markΦ z ℓ) := by
    have hk:= N.gloryBudget z p hp hP
    rw [Beam.see,Song.sequence,Terrain.stale]; refine ⟨CouplingShape.reg_scale _ hk.2.1,?_⟩
    have hb:=CouplingShape.sup_scale (-1) (hk.2.2 ℓ hn (Beam.dashboard H z).site (show _∈ perf H z from (by rw [← Beam.see]; exact (Beam.dashboard H z).anchor)))
    rw [abs_neg,abs_one,one_mul] at hb; exact hb
  have hr x : SumBudget (fun z=> if (Beam.dashboard H z).site=x then N.markΦ z ℓ*Real.exp (preExponent p*coverNumber p.B (Beam.dashboard H z).support) else 0) (collars G i s j ℓ*(salary Q L μ B s j k*(1-1/2)⁻¹)):= by
    have hv:= ht.applies N ℓ 0 x -- simp
    simp only [Nat.zero_le,↓reduceIte,pow_zero,mul_one] at hv
    refine budget_mono hv ?_ ?_
    · intro i; split; exact mul_nonneg (he i|>.2.1) (Real.exp_pos _).le; exact le_rfl
    intro z; split
    next hx => rw [Beam.see,hB,if_pos (show x∈Captain.reachability (H:=H) z from hx ▸ (show (Beam.dashboard H z).site∈perf H z from Beam.see H z ▸ (Beam.dashboard H z).anchor))]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))) (he z|>.2.1)
    exact hv.1 z
  obtain ⟨f,hf,hF⟩:= Song.stanzaReady (n:=c) T.down T.low p β γ hx hd hw
  have he':Meadow.Budget p (Beam.contents H p) (arena H χ β γ) (_ + octaveNeed G p T.low σ C Λ β γ):= ⟨Sum.elim (fun z=> N.markΦ z ℓ) f,fun i=> Cost.sum (hr i) (hf i),Sum.rec he hF⟩
  obtain ⟨s,h',hS⟩:= Meadow.soared p _ he'; exact ⟨fun i=> (hS i).1, Refrain.qualified p H (runway H) χ _ _ hp, fun s t=> Beam.moves .., ⟨_,fun i=> (hS i).2,h'⟩,chargesOut p H (runway H) χ h hB (show p.supportExponent+1 ≤ a by unfold preExponent at ha; linarith)⟩
end toll
end YM.PhysicalNext.Repeat.Poetry

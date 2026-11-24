import YM.OPE.Compatible.Zephyr.Stump
/-! # Conditional characteristic.S.Lap -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset
open Next.Rank.Thirst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : Rep G f}
    {p : BudgetPoint} {m n: ℕ} {W a r t σ E Λ μ x κ C w ε D b B: ℝ} {Ñ:ChartRatio G}
variable {F:Forest S.ratio} {I J:Seats F}{X Y Z:Support f}{q:Support c}
-- rename R explicit or from statement
abbrev Rails (R:Rep G f)(V:Config G c)(k:S.Choices)(I J:Seats F)(B:ℝ)(x:World F J G)(f':World F I G→ℝ) := let g:= Arbor V R k I J B x; (∫ p, g p * f' p ∂ hail G I) / (∫ p,g p ∂hail G I)
variable (R: Rep G f)(V:Config G c)
lemma furthers (U: World F J G)(H:I⊆J)(k:S.Choices)(ht:a≤B)(hz:0≤ B)(hf:4*B≤ R.p.threshold)(hp:dazed H a B U)(Z:FoldsGrip F I X)(hk:m≤R.p.B)(h:R.Lawful σ C Λ E w)(hc:WilsonStartup.Decent R.clip R.p)(hy:Geo.Width R.p R.clip σ)(hm:S.patch.Branches S.kernel G) (hx:Envelope (RockV R m I))(hT:∀ U, ‖RockV R m I U‖≤ μ)(hB:2*μ≤1/2):
    let g:= Arbor V R k I J B U
    Envelope g ∧ ∀ (p:World F I G→ℝ)(b:ℝ), Envelope p→ (∀ i, ‖p i‖≤ b)→ ‖report I J R V m k B p U - Rails R V k I J B U p‖ ≤ 4*(2*μ)*b:=by
         intro v; have hZ : Measurable (fun p:World F I G=> F.drape (Wind I p (ald I J U))):= F.continuous_drape.measurable.comp ((threadT G I).symm.measurable.comp (measurable_id.prodMk measurable_const)); let g:=ballotY I R V m k B U; let q(p:World F I G):= RockV R m I (F.drape (Wind I p (ald I J U))); have hn : Envelope g:= Env.along (coin_vote I hm h V m k B) (g:=fun p:World F I G=>(U,p)) (measurable_const.prodMk measurable_id);
         have hM(p):g p=v p*Real.exp (q p):=olympia U R H V k ht hz hf hp Z hk h hc hy p -- arg order
         have he : Envelope v:=by
             have hQ : Envelope q := Env.along hx hZ; have hA : v=g*(fun p=>Real.exp (-q p)) :=funext fun i=>by simp only [Pi.mul_apply,hM, mul_assoc,Real.exp_neg,mul_inv_cancel₀ (Real.exp_pos _).ne',mul_one]
             rw [hA]; exact hn.mul hQ.neg.exp
         have hr(i):0 ≤ v i:=by unfold v Arbor; split; exact Real.exp_nonneg _; exact le_rfl
         refine ⟨he,fun p x hv hX=>mutiny (he.integrable _) (hn.integrable _) ((he.mul hv).integrable _) ((hn.mul hv).integrable _) hr (mul_nonneg (by norm_num) ((norm_nonneg _).trans (hT 1))) hB ?_ ((norm_nonneg _).trans (hX 1)) hX⟩; intro i; have ht' : ‖q i‖≤μ:=hT _; change ‖g i-v i‖≤_; rw [hM i,show v i*_-_=v i*(Real.exp (q i)-1) by ring,norm_mul,Real.norm_of_nonneg (hr i)]; exact mul_le_mul_of_nonneg_left (tied (by linarith) ht') (hr i)
end YM.PhysicalNext.Repeat.Aroma

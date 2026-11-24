import YM.LocalLTE.Roost.Lawn
/-! Rate0 geometry & received masks in polynomial probe far off b. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Vine
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Frond Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
variable {v z r W s y η γ B : ℝ} {j n m : ℕ}
local notation "E"=> Disk G c
local notation "E₀"=> ZipP G c f
def sideways : E→L[ℝ] E₀:= (ContinuousLinearMap.snd ℝ ℝ (Directions G c)).prod 0
lemma sidefix (p:E) : pass (f:=f) p=sideways p:=rfl
lemma norm_side : ‖@sideways G c f‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y=> by rw [one_mul]; change max ‖Prod.snd y‖ ‖(0:Directions G f)‖≤ ‖y‖; exact max_le (le_max_right ..) (by rw [norm_zero]; exact norm_nonneg _)
lemma tally (x:E): ‖(pass x:E₀)‖≤‖x‖:=by rw [sidefix]; exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_of_le_one_left (norm_nonneg _) norm_side)
-- normalized twig angular receipts
lemma pruned (X:Coat T F)(p: Air f G) {V:ℝ}{x:E}(hf: Brush j V 1 (switchΛ X p) x)(hv:‖x‖≤ 1) : Brush j (1+V+(1+V)) 1 (twig X p) x:=by
  have hp : Brush j 1 1 (fun y:E=> y.snd) x:= linearB (ContinuousLinearMap.snd ℝ ℝ (Directions G c)) ((le_max_right ..).trans hv) (by rw [one_mul]; exact ContinuousLinearMap.norm_snd_le ..) zero_le_one
  let Z:Directions G f→ₗ[ℝ] Directions G f:= {
    toFun := X.blank.lens
    map_add' := fun q y => by funext i; by_cases he:X.blank.Hot i <;> simp [Coat.lens, he]
    map_smul' := fun b q=> by funext i; by_cases he:X.blank.Hot i <;> simp [Coat.lens,he] }
  have hv : ‖Z.toContinuousLinearMap‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=> by
    rw [one_mul]; refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun i=>?_); change ‖X.blank.lens x i‖≤_; unfold Coat.lens; split
    · exact norm_le_pi_norm x _
    rw [norm_zero]; exact norm_nonneg _
  have he:= hf.report _ hv; rw [one_mul] at he; exact (hp.climb (le_add_of_nonneg_right he.nonneg) le_rfl).pair (he.climb (le_add_of_nonneg_left zero_le_one) le_rfl)
lemma calmed (X:Coat T F)(p: Air f G) {V:ℝ}{x:E}(hf:‖switchΛ X p x‖≤ V): ‖twig X p x‖≤ ‖x‖+V:= by
  change max _ ‖X.blank.lens _‖ ≤ _; have hv:0≤V:=(norm_nonneg _).trans hf
  apply max_le ((le_max_right ..).trans (le_add_of_nonneg_right hv)); refine (le_trans ?_ (le_add_of_nonneg_left (norm_nonneg x))); apply (pi_norm_le_iff_of_nonneg hv).2; intro i; unfold Coat.lens; split
  · exact (norm_le_pi_norm _ _).trans hf
  rwa [norm_zero]
lemma price_mode (A: E→E₀) (X:E₀→ Config G f) {x:E}(hx:Brush j v 1 A x)(h:Mode X (A x) j s) : Mode (X∘ A) x j ((1+j.factorial*((royalty G)*(1+s)^j))*((1+v)*1)) :=by
  refine ⟨(by have hp:=hx.nonneg; have hy:=royalty_ge G; have he:=h.pos; positivity),fun i=> thicken (hx.pine (h.atLink i).trim)⟩
lemma thistles {P:Teller G}(L : Side)(D: Patch)(hd: D.Branches P.bind G) {p d : ℝ→ℝ}(Q:YM.ConnectedActivityE6.Target G P)(W:ℝ)(o:Target.Order G W) (j:ℕ)(hj:1≤j){v:ℝ}(h : -(1/2:ℝ) ≤ v)(hW:v<0) (hp:Rate G L v p)(hk: Rate G L 0 d)(he:∀ᶠ x in atTop,0≤p x) : ∃ A C R:ℝ→ℝ, Rate G L v A ∧ Rate G L 0 C ∧ Rate G L 0 R ∧ ∀ᶠ t in atTop, ∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D → ∀ μ α:ℝ, Target.GrantBodies W t μ L Q o α T → ∀ (F: Forest S.ratio) (X : Coat T F), X.x=t → X.width=o.K →∀ z: Air f G,(∀ i, |z i| ≤ |d t|)→∀ x: Disk G c,‖x‖≤p t →
    ‖twig X z x‖ ≤ |A t| ∧ Brush j (|C t|) 1 (twig X z) x ∧ Mode (inputΛ X z) x j (|R t|):= by
  obtain ⟨A,C,hA,hC,H⟩:= glideGrowth L D hd Q W o j hj h hW hp hk he
  obtain ⟨e,c,hr,hv,hy,hF⟩:= Frond.dressed P D hd j
  have hf := hp.add (hA.compare (v:=fun x=>|A x|) (Eventually.of_forall fun x=>(abs_abs _).le))
  let S₀ t:= 1+|C t|; let R t:= S₀ t+S₀ t; have hx: Rate G L 0 S₀:= (Rate.const _).add (hC.compare (Eventually.of_forall fun x=>(abs_abs _).le))
  let u t:= (1+j.factorial*((royalty G)*(1+c)^j))*((1+R t)*1)
  refine ⟨_,R,u,hf,hx.add hx,((((Rate.const 1).add (hx.add hx)).mul_right 1).mul_left _),?_⟩
  filter_upwards [H,hf.below hW e hr,hp.below hW 1 zero_lt_one] with t hx ht h hh f S T hS b μ H' F X hX hK z hy' x hv
  obtain ⟨hA,hV⟩:=hx _ _ S T hS _ _ H' F X hX hK z hy' x hv
  have hs:= ((calmed X z hA).trans (add_le_add hv le_rfl)).trans (le_abs_self _)
  have hm:= pruned X z hV (hv.trans ((le_abs_self _).trans h)); refine ⟨hs,hm.climb (le_abs_self _) le_rfl,?_⟩
  have he:=(hF _ _ S T H'.funds.funds hS (twig X z x) (hs.trans ht) X.k).2.1
  exact later (price_mode _ _ hm he) (le_abs_self (u t))
end YM.ConnectedActivityE6.Blaze.Vine

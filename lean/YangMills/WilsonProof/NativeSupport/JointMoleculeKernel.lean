import YangMills.WilsonProof.NativeSupport.JointPhysicalPush

/-! Reindex the measured original sectors by the very same countable molecules,
including the true chart overhead and every predictor choice. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointTicket
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations
open SectorMeasure Oriented Work.E03 Mask Contract Work.F03 Presented LabelSum Sector Footprint
open Packets SliceRows Control Window Pulse Coat Matter ProbabilityTheory Poll Pond
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus JointCoat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
    {F : Forest S.ratio} {R : Rep G f} {W μ C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}
variable (M : Team R) (X : Coat T F) (J : Finset (Bond c)) (h : Bond c→ℝ→ℝ)

def tithe (k : Finset ℕ) (W a : ℝ) (Ñ : ChartRatio G) (m : ℕ) (p : Molecule S) :=
  ∫ v,raw (W:=W) M X k p a Ñ m J h v ∂((F.order G).prod X.dice)

def fare (A : Stores S) (l : S.Choices) (p : Molecule S) :=
  let Y := (Matter.preps X A).taggedL l
  Y.tribute R Q.table * hike M (Matter.own p) J h Y p W o.a Q.table Q.halo

variable (H : Cash W X.x μ L Q o C T R) (hk : X.width=o.K)
variable (hm : ∀ b∈J,Measurable (h b)) (unit : ∀ b∈J,∀ e∈Set.Icc 0 (linkCap S),‖h b e‖≤1)
include H hk hm unit

theorem yoke (k : Finset ℕ) (p : Molecule S) :
    ‖hike M k J h X p W o.a Q.table Q.halo‖≤Team.crowns H.text M.weight (M.signs S) p := by
  unfold hike
  by_cases ha : X.approve k R
  · rw [if_pos ha]
    exact (norm_integral_le_integral_norm _).trans (raw_price M X H hk ha.1 k p J h hm unit).2
  rw [if_neg ha,norm_zero]
  unfold Team.crowns
  split
  · exact mul_nonneg M.profit (prod_nonneg fun i _=>H.positive i)
  exact le_rfl

theorem brew (j : Stores S) (k : S.Choices):
    let Y := (preps X j).taggedL k
    HasSum (fun i : Finset ℕ × ListsAt c f => fare (o:=o) (Q:=Q) M X J h j k (crew S Q.halo X.B (j,i)))
      (∫ i, (Y.χ.distribute j Y.x W (F.drape i) k X.V * (taggedKernel S R.beta k (F.drape i) X.V * M.cicada (F.drape i))) *
        JointPhysical.sample S k J h (F.drape i) X.V ∂F.order G):=by
  intro Y; let V:= Layout.rolls j Q.halo X.B
  let a(u:Finset ℕ × ListsAt c f):= crew S Q.halo X.B (j,u)
  let g (u):=fare (o:=o) (Q:=Q) M X J h j k (a u)
  have hu (i):g i=Y.tribute R Q.table * hike M i.1 J h Y (issue V i.1 i.2) W o.a Q.table Q.halo:=by
    have hv : Matter.own (a i)=i.1:= congr_arg (fun i : Packed S=> i.2.1) (deposit (j,i))
    unfold g fare; dsimp only; rw [hv]; rfl
  have hf: Summable H.text:= Summable.sum _ (hasSum_fintype _).summable (budgets_arr H)
  have hp: Summable g:= by
    apply Summable.of_norm_bounded (g:=fun t=> ‖Y.tribute R Q.table‖ * Team.crowns H.text M.weight (M.signs S) (a t))
    · apply Summable.mul_left; apply (Team.crowns_has _ _ hf H.positive).comp_injective
      intro t u (h:a t=a u); apply congr_arg (f:=fun i: Packed S=> i.2) (show ( (j,t) : Packed S)=(j,u) from ((deposit _).symm.trans ((congr_arg obtainBack h).trans (deposit _)))) -- exact
    intro i; rw [hu,norm_mul]; exact mul_le_mul_of_nonneg_left (yoke M Y J h H hk hm unit _ _) (norm_nonneg _)
  change HasSum g _; convert! hp.hasSum using 1; rw [hp.tsum_prod]; simp_rw [hu, (troops M Y H hk _ J h V (Layout.enlists j Q.halo X.B) hm unit).tsum_eq]; exact ((world M Y H J h hm unit).tsum_eq).symm
omit H hk hm unit in
def bourbon (W a:ℝ)(Ñ:ChartRatio G) (l : ℕ) (p : Molecule S):=
    let Y:= preps X (roster p)
    if Y.approve (Matter.own p) R∧ Layout (roster p) l X.B p.toLeft then likely (fun k=> tithe M (Y.taggedL k) J h (Matter.own p) W a Ñ l p) else 0
theorem success : HasSum (fun i:Molecule S=> overhead X R Q.table * bourbon M X J h W o.a Q.table Q.halo i) (JointPhysical.push S J h R.beta M.cicada X.V):=by
  let V:= crew S Q.halo X.B
  let f i:= overhead X R Q.table * bourbon M X J h W o.a Q.table Q.halo i; change HasSum f _; have hv: Injective V:=LeftInverse.injective (show LeftInverse obtainBack V from deposit)
  apply (hv.hasSum_iff (f:=f) ?_).1
  · rw [posted M X H J h hm unit]; apply Raw.finite_start; intro Y
    refine (hasSum_sum (s:=univ) (fun i _=> brew M X J h H hk hm unit Y i)).congr_fun ?_
    intro t; let u:= V (Y,t); let Z:= preps X Y; let p:= overhead X R Q.table; let b:ℝ:= Fintype.card S.Choices
    have hx: roster u=Y:= congr_arg Prod.fst (deposit (Y,t))
    have ht:Layout Y Q.halo X.B u.toLeft:= by rw [show u.toLeft=Layout.rolls Y Q.halo X.B from toLeft_disjSum ..]; exact Layout.enlists ..
    change overhead _ _ _ * bourbon M X J h W o.a Q.table Q.halo u = ∑ i:S.Choices,fare (o:=o) (Q:=Q) M X J h Y i u
    unfold bourbon; rw [hx]; dsimp only; split
    next active =>
      have hv i : (Z.taggedL i).tribute R Q.table=b⁻¹*p:=by rw [← show overhead _ R Q.table=p from visitsM X Y i Q.table R]; unfold b overhead tribute; ring
      have hp i: fare (o:=o) (Q:=Q) M X J h Y i u= (b⁻¹*p)*tithe M (Z.taggedL i) J h (Matter.own u) W o.a Q.table Q.halo u:=by
        unfold fare hike tithe; dsimp only; rw [show ((preps X Y).taggedL i).tribute _ _= _ from hv i, if_pos (show (Z.taggedL i).approve _ _ from active.1)]
      simp_rw [hp,← Finset.mul_sum]; unfold likely b p Z; ring
    next h=>
      rw [mul_zero]; symm; refine Finset.sum_eq_zero fun k _=> ?_; unfold fare hike; dsimp only; rw [if_neg (show ¬ (Z.taggedL k).approve (Matter.own u) R from fun hl=>h ⟨hl,ht⟩),mul_zero]
  intro i hi; unfold f bourbon; dsimp only; rw [if_neg (fun h=> hi ⟨_, recovery h.2⟩), mul_zero]

end YM.Integration.InletSusceptibility.JointTicket

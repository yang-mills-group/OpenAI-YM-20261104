import YM.Gaps1020.Local.Pushed
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open March Next.Foundations YM.GapsLocal.ExpShares
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k M : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g ρ ℓ : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {z : Air f G} {V:E→ Config G c}{x:E}

variable {H : Cash W s μ L Q o C T R}

open PhysicalNext.Repeat.Lotus

open YM.RG01.Survive
-- Include the implicit empty-ticket variant so retaining a nil source still
-- uses the forward Cash and charged Choice Ω. Difference vs A's vacuum
-- filter: no early rejection of CLUSTERS by estimates on head count/travel.
-- Only leaf cut & length, OR order above M. Caption literal integral law
-- exported from B2 applied to this same µ. Core admits **all** post/aux
-- Embrasures (Ports without W-collisions) on one Factor.
open Merge Palette PhysicalNext.Repeat.Daisy
open Push.AbsoluteSums.Mixed Push.AbsoluteSums.Reserves Gas Ursell Captain
open AnalyticBridge VerifiedReset Collection Extra.Iteration Quotes Song Match Geo

local notation "u0" => (Empty.elim : Empty → Leaf R)
local notation "T'" => Tickets (Palette.sign u0 S)
local notation "σ" => (0:Empty→ℝ)

def seatZ (p:H.fragrances) (M:ℕ)(χ:Chi)(A:ℕ→Prop): Config G c→ℝ:=
    ∑ i ∈ (univ : Finset (Requests u0 p (M:=M))).filter (fun i=> A (aggregateGrade u0 p i)), quantity u0 σ χ p i
lemma z_split (p:H.fragrances)(M:ℕ)(A:ℕ→Prop): seatZ p M χ (fun _=>True)=seatZ p M χ A + seatZ p M χ (fun i=> ¬ A i):=by unfold seatZ; simp only [Finset.filter_true]; rw [Finset.sum_filter_add_sum_filter_not]
private lemma no (t:T'): t.val=∅:= eq_empty_iff_forall_notMem.mpr fun i => Empty.elim i
private lemma emptyTeam (t:T')(p:H.ThinP)(V:Config G c): preserved H χ p (Palette.team u0 t) V = leaflet H χ V p:=by
   let U:= Palette.team u0 t; have hp:U.own=∅:=by unfold U Palette.team; simp [no];
   have hh: U.signs S=∅:=by unfold Team.signs; rw [hp, Finset.image_empty]
   have he (F:Forest S.ratio) (X:Coat T F)(v): teamWeight p.val R U (emptyTeamData U p.val) Q.table W o.a Q.halo X v=Polar.floating X o.a R W Q.table v (own p.val) Q.halo p.val:=by rw [lit]; unfold seats others; rw [hh,if_pos (empty_subset _),sdiff_empty]; unfold Team.paidU; rw [hp]; simp
   let G' i:= prism T s χ o.K V (Greenbelt.allot i); let f(i:Greenbelt.Reserve S):= fringe (G' i) W o.a p.val R Q.table Q.halo
   by_cases hx: awake H p U; swap
   · rw [preserved,writtenBy,if_neg hx]; unfold leaflet; letI : Nonempty (Forest S.ratio):= Tree.select S.ratio S.patch.odd_side; have h(i:Greenbelt.Reserve S)(Z:Site c→ G.El) : shelter ((G' i).rinse Z) W o.a p.val R Q.table Q.halo=0:=if_neg (fun h=>hx ⟨h.1,h.2,hh.symm ▸ empty_subset _⟩)
     have he {t:Fintype (Greenbelt.Reserve S)} : 0 = @likely (Greenbelt.Reserve S) t f:=by unfold likely f fringe; simp_rw [h]; simp
     exact he
   rw [preserved,writtenBy, if_pos hx]; unfold leaflet
   have h (f g:Greenbelt.Reserve S→ℝ)(x y:Fintype (Greenbelt.Reserve S))(h:f=g): @likely _ x f=@likely _ y g:=by rw [h,Subsingleton.elim x y]
   apply h; funext i; unfold fringe teamWeightFringe shelter teamWeightShelter seating bars teamWeightSeat teamWeightBars
   simp_rw [show ∀ (F:Forest S.ratio) (X:Coat T F)(v),teamWeight p.val R (team u0 t) (emptyTeamData (team u0 t) p.val) Q.table W o.a Q.halo X v=_ from he]
lemma s_revenue (p:H.fragrances)(M:ℕ): (fun V=>stream H χ V p) = seatZ p M χ (fun _=>True) := by -- notation may parse fun
   let m := univ (α:=T'); let f (i:S.Choices):=i -- remove
   have h(p:H.ThinP)(U:Config G c): ∑ i: Sections (S:=S) u0 (M:=M), rung u0 σ χ p i U=leaflet H χ U p:=by
      let t₀:T':= Tickets.none _; rw [Fintype.sum_prod_type, sum_eq_single t₀];
      · simp only [rung,scalarWeight,no,prod_empty,one_mul]; rw [recoversMix]; exact emptyTeam t₀ p U
      · intro i _ hi; exact (hi (Subtype.ext ((no i).trans (no t₀).symm))).elim
      simp
   funext U
   unfold stream Gas.term seatZ; rw [Finset.sum_apply]; simp only [Finset.filter_true]; simp_rw [quantity]; rw [← Finset.mul_sum]; have hh:= Fintype.prod_sum (f:=fun i (u:Sections (S:=S) u0 (M:=M))=> rung u0 σ χ (p.2 i) u U); simp_rw [h] at hh; rw [← show _=(∑ i:Requests u0 p (M:=M),∏ j: Option (Fin p.fst),rung u0 σ χ (p.2 j) (i j) U) from hh]; ring

variable (N:Captain H j C' d v Y A b r B q k χ)
local notation "Z" => horizonRadius G L s
lemma waiver : Thermal.BuysMix u0 H σ:=by
   constructor; exact fun i=> Empty.elim i
   intro i a k ht
   simp only [show Thermal.together u0 (c:=c) σ a=a from funext fun i=> by simp [Thermal.together,Tickets.extra]]
   refine ⟨ht.packetBound,ht.holds, ht.extra,fun p=> budget_loosen (ht.pays p) ?_⟩
   exact le_add_of_nonneg_right (show 0 ≤ ribbon Q L s from mul_nonneg (arable H).le (Real.exp_pos _).le)

def zPrice (p:H.fragrances) (M:ℕ)(P: BudgetPoint)(ρ:ℝ)(A:ℕ→Prop):=
    ∑ i ∈ (univ : Finset (Requests u0 p (M:=M))).filter (fun i=> A (aggregateGrade u0 p i)), sidecost p j P*cen N u0 σ p ρ M i
lemma zp_nonneg (p:H.fragrances)(D:BudgetPoint) (P:ℕ→Prop)(he:0 ≤ ρ): 0 ≤ zPrice N p M D ρ P:= sum_nonneg fun i _=> mul_nonneg (sidecost0 ..) (cen0 N u0 σ p waiver M i he)

-- u budget orientation after μ-promotion companion includes empty.
open Trees
variable (sP:ℕ→Prop)(M:ℕ)(Γ:Target.Expense Q)(P':BudgetPoint)(hs:P'.B=radiusB s)
    (hF:WarnBudget (ρ^(M+1)) N.conduit)(hρ:2 ≤ρ)(hB:Bikes Q L μ s Γ.earn (Height.asset Γ) B j k)(hd:degreePrice (radiusB s) (ρ*(swing Q L μ 1 s 0).rootHit) Q.δ≤1/2)(ht: degreePrice (radiusB s) (Shared.value Q L μ s B ρ k j M) (Height.asset Γ)≤1/2)
-- replicate amortized Proof on actual scalar without using real support allocator to ℂ and back
include hρ
lemma zCheap (p:H.fragrances)(i:ℕ) (h':∀ j,sP j→ i≤ j) : zPrice N p M P' ρ sP ≤ sidecost p j P' * ((ρ^i)⁻¹ * clusters H.seam (fun p=>2^j * combined N u0 σ M ρ (ρ^(M+1)) p) p.2):=by
   have he:= bookedCosts N u0 σ p waiver hρ M; have hk:0<ρ:=by linarith
   unfold zPrice; rw [← mul_sum]; apply mul_le_mul_of_nonneg_left _ (sidecost0 ..); rw [mul_comm,← div_eq_mul_inv, le_div_iff₀ (by positivity), sum_mul];
   refine (Finset.sum_le_sum (fun i hi=> ?_)).trans ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>?_)).trans he)
   · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show 1≤ρ by linarith) (h' _ (mem_filter.mp hi).2)) (cen0 N u0 σ p waiver M i hk.le)
   exact mul_nonneg (cen0 N u0 σ p waiver M _ hk.le) (by positivity)
local notation "η0" => Height.asset Γ

include hs hF hB hd ht
lemma zCash (i:ℕ)(h':∀ j,sP j→ i≤ j) (a:ℝ)(hb:a≤Γ.earn) : Ac.Hit (reachability (H:=H)) P'.B (fun z=> zPrice N z M P' ρ sP) a ((ρ^i)⁻¹ * (collars G η0 s j P'.power*(Shared.value Q L μ s B ρ k j M*(1-1/2:ℝ)⁻¹))) :=by
    intro x
    have hR:0<ρ:=by linarith
    let E':= reachability (H:=H); let c₀ i:= combined N u0 σ M ρ (ρ^(M+1)) i; let g' z:= clusters H.seam (fun i=>2^j*c₀ i) (z:H.fragrances).2; let a':=(ρ^i)⁻¹
    have hy:= readyLog N u0 σ ρ M hF (by linarith) Γ hB hd ht waiver
    have hz:=Ursell.log_hit_tail _ _ _ H.testS hy (add_nonneg hB.posts hB.allow.le) 0 x
    simp only [pow_zero,mul_one,Nat.zero_le,true_and] at hz
    have he0:0 < η0 := Height.asset_pos Γ
    have hp:(0:ℝ) ≤ a':=by unfold a'; positivity
    have ht':0 ≤ shiftG s:=by unfold shiftG; positivity
    have hα:0≤ collars G η0 s j P'.power:=by unfold collars Reserves.polyPrice; positivity
    have hw := budget_scale hp (budget_scale hα hz)
    refine budget_mono hw (fun z=>?_) (fun z=>?_)
    · dsimp only; split
      next h'=> exact mul_nonneg (zp_nonneg N z P' sP hR.le) (Real.exp_pos _).le
      next=>rfl
    dsimp only; split
    next ha=>
      have he:= zCheap N sP M P' hρ z i h' -- order check
      let Y:ℝ:= coverNumber P'.B (E' z); have hY:0≤Y:=Nat.cast_nonneg _
      rw [if_pos (show x∈ unionOf H.smallAt z.2 from ha), ← hs]; apply (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le).trans
      have hu:0 ≤ g' z:= clusters_nonneg _ (fun i=> hy.2.2.2.2.1 i) _
      change (sidecost z j P') * (a'*g' z) * Real.exp (a*Y) ≤ a'*(collars G η0 s j P'.power * (g' z * Real.exp ((Γ.earn+η0)*Y)))
      have hc:sidecost z j P'≤ collars G η0 s j P'.power* Real.exp (η0*Y):=by unfold sidecost; rw [mul_pow]; exact (mul_le_mul_of_nonneg_left (polynomial_cost he0 hY _) (pow_nonneg ht' _)).trans_eq (mul_assoc ..).symm
      apply le_trans (mul_le_mul (mul_le_mul_of_nonneg_right hc (mul_nonneg hp hu)) (Real.exp_monotone (mul_le_mul_of_nonneg_right hb hY)) (Real.exp_pos _).le (mul_nonneg (mul_nonneg hα (Real.exp_pos _).le) (mul_nonneg hp hu))) (le_of_eq ?_); rw [add_mul, Real.exp_add]; ring
    next h'=> exact hw.1 z

omit hs hρ hF hB hd ht
variable {D:RG.Stage}
omit N
/-- Stronger vacuum than A in γ-space. Works at any `Couture` purchase with `MarkerBudget`. Keeps positive cuts on leaf exponent grade including repeats and independent log projection path. `P'` is the actual support point before scalar extraction. -/
lemma hostPaid (N: Captain H D.order C' d v Y A b r B q k χ)(hp:P'.threshold=Pressure.temp s)(hr:P'.B=radiusB s)(he:P'.order≤ D.order)(hP:P'.power=D.power)(h:MixReceipt Γ D M N)
   (ha aP)(ha':(aP:ℝ)≤ Γ.earn)(hf:∀ i,sP i → ha ≤ i): let y p:= zPrice N p M P' Z sP; Ac.Hit (reachability (H:=H)) P'.B y aP ((Z^ha)⁻¹) ∧ ∀ i (o: Site c), o∈reachability i→ P'.Regular (reachability i) (seatZ i M χ sP) ∧ P'.supBounds o (reachability i) (seatZ i M χ sP) (y i):=by
   intro f
   have hx:= h.large; have hv : Sailor G P'.threshold q D.order:= ⟨fun i v hv=>N.weigh.stroke i v (hv.trans (hp.symm ▸ N.talent))⟩
   have hp0(p:H.fragrances) (o:Site c)(ho:o∈reachability p) t:= cents N u0 σ p waiver h.shared h.turns h.large h.chargeFits P' hp he hr hv o ho M t; let E' := Height.asset Γ
   exact ⟨fun i=> budget_loosen (zCash N sP M Γ P' hr h.Warn h.large h.book h.meet h.funds ha hf aP ha' i) (mul_le_of_le_one_right (by positivity) (hP.symm ▸ h.expCredit)), fun i o ho=> ⟨Meadow.regularA _ fun j _=> (hp0 i o ho j).1,Trio.sup_S (p:=fun j=> sidecost i D.order P' * cen N u0 σ i Z M j) P' _ _ _ _ (fun j _=> (hp0 i o ho j).1) (fun j _=> (hp0 i o ho j).2)⟩⟩
end YM.ConnectedActivityE6.Blaze.Thermal1020.Shared

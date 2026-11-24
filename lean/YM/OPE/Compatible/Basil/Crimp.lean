import YM.OPE.Compatible.Basil.Crowd
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Gnomon
/-! # Tie weighted debts to vertex prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma.Leaf
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Itinerary Gas Ursell Trees Animals Corona Daisy
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (X:Coat T F) (H:Cash W X.x μ L Q o C T R)(hk:X.width=o.K)
variable (M:Leaf S R)
def helm : Wing→Lotus.Wing
 | .logKey i=>.logKey i
 | .gasKey i=>.gasKey i
def tin_ : Lotus.Leaf R:=⟨helm M.turn,fun _=>0,fun _ _ _ _=>rfl,fun _ h=> (h rfl).elim,(by have h:= M.blank; cases he:M.turn; simp only [he] at h;exact h;exact trivial), M.weight,fun _=>by rw [norm_zero];exact M.profit,fun _ _=>rfl,measurable_const⟩
lemma colorCue : M.tin_.crest=M.crest ∧ M.tin_.turn.badge S=M.turn.badge S:= by cases he:M.turn<;> simp [tin_,helm, Lotus.Leaf.crest,Leaf.crest,he, Lotus.Wing.support,Lotus.Wing.badge,Wing.support,Wing.badge]
-- X infer
section stake
variable (hf:foam Q L) (hR:R.p.B≤2*radiusB X.x) {c₀:ℝ} {wy:ConnectedActivityE6.Alphabet c f →ℝ} (hp:(swing Q L μ R.beta X.x c₀).Buy S.patch.L Q.halo (radiusB X.x))
local notation "Costs"=> Mixed.costs S Q.halo (radiusB X.x) (steamP S (Q.costs L μ R.beta X.x c₀)) wy
include H hf hR hp
lemma pedestal {n:ℕ} -- edit
 (b : Molecule S→ℝ) (hv:0≤ b)(c':ℝ)(hc:0≤c') (H' : Accounts S Q.halo (radiusB X.x) (Q.costs L μ R.beta X.x c₀) H.birth wy (ConnectedActivityE6.lengths T R) (steamP S (Q.costs L μ R.beta X.x c₀)))
 (h : ∀ p,b p≠0→H.ticketsP 0 n 0 p ∧ M.turn.badge S∈p∧ (∃ j∈ M.crest.image S.ratio.parent,j∈ H.unionP p) ∧ b p ≤ c'* (M.weight*∏ i∈p.erase (M.turn.badge S), Costs i))
 (y : Site c)(hy:∀ p,b p≠0→ y∈H.unionP p) : SumBudget (fun p:H.ThinP=> b p.val * Real.exp (Q.exp * coverNumber (radiusB X.x) (H.unionP p.val))) (c'*(jewelDebt M.tin_ Q L X.x)*(swing Q L μ R.beta X.x c₀).ceiling 0 0 n 0):=by
   let m:=radiusB X.x; have he (i):0≤Costs i:=by
     rcases i with i|i
     · unfold Mixed.costs; dsimp only [Sum.elim]; split
       next h=> exact (H'.packetBound _ h).1
       rfl
     exact H'.holds _
   let s:= M.tin_; let r:=jewelDebt s Q L X.x
   have hd := (dew s H).2
   have hh:=premium_hit s H c₀ wy he hf hR hp H' 0 0 n y
   have hc' :=budget_scale (mul_nonneg hc hd.1) (budget_pull (fun p:H.ThinP=>p.val) Subtype.val_injective hh)
   refine budget_mono hc' (fun i=>mul_nonneg (hv _) (Real.exp_pos _).le) fun i=> ?_
   by_cases hz:b i.val=0
   · rw [hz,zero_mul]; exact hc'.1 i
   obtain ⟨hV,hA,-,hℓ⟩:= h i.val hz
   change _ ≤ (c'*r)*(if y∈H.unionP i.val then _ else 0)
   rw [if_pos (hy _ hz),persona, M.colorCue.2,if_pos ⟨hV,hA⟩,pow_zero,mul_one, ← mul_prod_erase _ _ hA,← mul_assoc _ _ (Real.exp _)] -- s delta unfolding
   have hN : needle s H c₀ wy (M.turn.badge S)= jewel s Q L X.x:= by rw [← M.colorCue.2]; exact nose _ _ _ _
   let a:=(M.turn.badge S); let v:= Costs
   refine (mul_le_mul_of_nonneg_right hℓ (Real.exp_pos _).le).trans_eq (congr_arg (fun x:ℝ=> x*Real.exp _) ?_); rw [hN]; have ht : M.weight=r * jewel s Q L X.x:=hd.2
   change c'*(M.weight * ∏ j∈i.val.erase a, v j)=_; rw [ht]
   have hE : (∏ j∈i.val.erase a, needle s H c₀ wy j)=∏ j∈i.val.erase a, v j:=prod_congr rfl fun j hj=> sleeve s H _ _ _ (M.colorCue.2.symm ▸ (show j≠a from ne_of_mem_erase hj))
   rw [hE]; ring
end stake
variable (hf:foam Q L) (hR:R.p.B≤2*radiusB X.x) (hp:(swing Q L μ R.beta X.x C).Buy S.patch.L Q.halo (radiusB X.x))
include hf hR hp hk
lemma y_pays (n:ℕ):
 SumBudget (fun p:H.ThinP=> if n ≤ Cash.numP p.val then ‖M.umi H X p‖ * Real.exp (Q.exp * coverNumber (radiusB X.x) (H.smallAt p)) else 0)
      (jewelDebt M.tin_ Q L X.x * (swing Q L μ R.beta X.x C).ceiling 0 0 n 0):=by
   let f p:= M.bloom X W o.a Q.table Q.halo p; let b p:= if n ≤ Cash.numP p then ‖f p‖ else 0
   have h i (hi:b i≠0):f i≠0 ∧ n≤ Cash.numP i:=by
     unfold b at hi; split at hi
     next h=> exact ⟨fun ht=>hi (by rw [ht,norm_zero]),h⟩
     next h=> exact False.elim (hi rfl)
   obtain ⟨j,hj⟩ : (M.crest.image S.ratio.parent).Nonempty:= by
     apply Finset.Nonempty.image; unfold Leaf.crest;cases M.turn
     · exact ⟨_,(R.activities.reg _).anchor⟩
     exact ((R.activities.forced _).inventory_ne).mono (R.activities.forced _).inventory_sup
   have he i (hi:b i≠0): j∈ H.unionP i := (bloom_active X H M (h i hi).1).2.2.2.1
     (halo_subset _ _ (Finset.image_subset_image (show M.crest⊆ RG.inspected M.crest from Finset.subset_union_left) hj))
   have hh := pedestal (n:=n) X H M hf hR hp b (fun i=>by unfold b; split; exact norm_nonneg _; rfl) 1 zero_le_one H.armed (?_) j he
   · rw [one_mul] at hh;convert hh using 1
     funext i; unfold b; split;rfl;rw [zero_mul]
   intro p hx; obtain ⟨hy,hF⟩:= h p hx; obtain ⟨hs,-,hA,Hj,-,ht⟩:=bloom_active X H M hy; refine ⟨⟨hs,Nat.zero_le _,hF,H.positive_volume p⟩, hA, ⟨j,hj,he p hx⟩,?_⟩
   let Y := planted X p; let K:= M.steep Y (own p) W o.a Q.table Q.halo p; let v:= M.weight*∏ i∈p.erase (M.turn.badge S), H.text i
   have h' q: ‖M.tithe (Y.taggedL q) (own p) W o.a Q.table Q.halo p‖ ≤ v:=(norm_integral_le_integral_norm _).trans (by have hf:= (M.tip (Y.taggedL q) (own p) H hk (planted_valid ..) p).2.2;rw [if_pos hA] at hf; exact hf)
   unfold b f bloom; rw [if_pos hF, if_pos (by unfold f bloom at hy; split at hy; assumption;exact (hy rfl).elim),one_mul]
   change ‖K‖ ≤ v; let c:=(Fintype.card S.Choices:ℝ); have hc : 0<c:=by unfold c; positivity
   unfold K steep likely; rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
   apply le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum (s:=univ) fun i _=> h' i)) (inv_nonneg.mpr hc.le))
   rw [sum_const,nsmul_eq_mul, card_univ, inv_mul_cancel_left₀ hc.ne']
end YM.PhysicalNext.Repeat.Aroma.Leaf

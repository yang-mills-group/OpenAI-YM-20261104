import YM.OPE.Compatible.Basil.String
/-! # Rare U under allgood W, viewed with ANY tree vertical chart. -/
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
variable (X:Coat T F) (H:Cash W X.x μ L Q o C T R)(hk:X.width=o.K) (M:Leaf S R)
def Flick (_H:Cash W x μ L Q o C T R)(X:Coat T F)(M:Leaf S R)(p:Molecule S)(z:ℝ) := ∃ A:Set (Air f G),MeasurableSet A∧
   X.dice.real A ≤ z^2 ∧ ∀ (r : F.Slice G)(y : Air f G), M.into X W o.a Q.table (own p) Q.halo p (r,y)≠0 → y∈ A
-- include H in def usage yes
include hk
lemma tide {s z:ℝ}(hh:0≤s) (ha:X.manifest)(hz : M.turn.badge S∈p) (hx:Flick H X M p z)(hw:∀ q:Finset (WarningAt c f),X.dice.real (X.catastrophe o.ξ R.beta q)≤(s^2)^q.card) (he:0≤z) :
    ‖M.tithe X (own p) W o.a Q.table Q.halo p‖ ≤ z * (M.weight * ∏ i∈p.erase (M.turn.badge S), hCost H s i) := by
     obtain ⟨A,h₀,h₁,h₂⟩:=hx; let q:=p.erase (M.turn.badge S); let B:= X.catastrophe o.ξ R.beta (blaze q); let v:= M.weight* ∏ i∈q,H.fair i
     let D:=(F.order G).prod X.dice; let G'(i:F.Slice G × Air f G) := (A ∩ B).indicator (fun _=>v) i.2; let u:= M.into X W o.a Q.table (own p) Q.halo p
     have hV:0≤v:=mul_nonneg M.profit (Finset.prod_nonneg fun i _=>H.fair_price i); have hB:MeasurableSet B:=Poll.sounded ..; have hM:Integrable G' D:=((integrable_const _ (μ:=X.dice)).indicator (h₀.inter hB)).comp_snd _
     have hf i: ‖u i‖≤G' i:=by
        rcases i with ⟨r,y⟩; by_cases hv : u (r,y)=0
        · rw [hv,norm_zero]; unfold G'; by_cases he:y∈ A∩ B
          · rw [Set.indicator_of_mem he]; exact hV
          rw [Set.indicator_of_notMem he]
        have hi:=h₂ r y hv
        let I:= (X.wrapY r); let hp:= M.paidU I o.a (I.liftA R.beta y); let Y:= X.body R Q.table W o.a (own p) Q.halo q
        have heq:u (r,y)= hp * Y (r,y):=by unfold u into premium; rw [if_pos hz]; rfl
        rw [heq] at hv ⊢
        have hh:=H.lease X rfl hk ha (own p) q r y (right_ne_zero_of_mul hv)
        unfold G'; rw [Set.indicator_of_mem (show y∈ A∩B from ⟨hi,hh⟩), norm_mul]; exact mul_le_mul (M.coin ..) (H.every X rfl hk ha _ q r y) (norm_nonneg _) M.profit
     let a:=(blaze q).card; let l:= s^a
     have hv : X.dice.real (A∩ B) ≤ z*l:=by
        have hx := measureReal_mono (μ:=X.dice) (Set.inter_subset_left (s:=A) (t:=B))
        have hb := measureReal_mono (μ:=X.dice) (Set.inter_subset_right (s:=A) (t:=B))
        have he₁: X.dice.real B ≤ l^2:= (hw (blaze q)).trans_eq (by unfold l a; rw [← pow_mul,← pow_mul,mul_comm])
        have ht:0≤l:=pow_nonneg hh _
        rcases le_total z l with hs|hs
        · exact ((hx.trans h₁)).trans (by rw [pow_two];gcongr)
        exact ((hb.trans he₁)).trans (by rw [pow_two];gcongr)
     change ‖∫ v,u v ∂D‖ ≤ _
     apply (norm_integral_le_integral_norm _).trans; apply (integral_mono (M.tip X _ H hk ha p|>.2.1|>.norm) hM hf).trans; rw [integral_prod _ hM]
     have hj(r:F.Slice G): (∫ y,G' (r,y) ∂X.dice)=X.dice.real (A∩B)*v:= integral_indicator_const v (h₀.inter hB)
     simp_rw [hj]; rw [integral_const]; simp only [probReal_univ,one_smul]
     apply (mul_le_mul_of_nonneg_right hv hV).trans_eq; change _= z*(M.weight*∏i∈q,hCost H s i)
     rw [soundP]; unfold v l a; ring
lemma blink {s z:ℝ}(ha:0≤s)(he:0≤z)(hp:(arcs Q L μ R.beta X.x C).Buy S.patch.L Q.halo X.B)(hh : castCash H M s)
 (hx : ∀ i:Molecule S,Cash.numP i=0→ M.bloom X W o.a Q.table Q.halo i≠0 → ∀ q:S.Choices,
    let Y:= (planted X i).taggedL q; Flick H Y M i z ∧ ∀ A:Finset (WarningAt c f),Y.dice.real (Y.catastrophe o.ξ R.beta A)≤(s^2)^A.card):
    SumBudget (fun p:H.ThinP=>if Cash.numP p.val=0 then ‖M.umi H X p‖*Real.exp (Q.exp*coverNumber X.B (H.smallAt p)) else 0)
        (z*jewelDebt M.tin_ Q L X.x*(arcs Q L μ R.beta X.x C).ceiling 0 0 0 0):=by
   obtain ⟨j,hj⟩ : (M.crest.image S.ratio.parent).Nonempty:= by
     apply Finset.Nonempty.image; unfold Leaf.crest;cases M.turn
     · exact ⟨_,(R.activities.reg _).anchor⟩
     exact ((R.activities.forced _).inventory_ne).mono (R.activities.forced _).inventory_sup
   let f p:= M.bloom X W o.a Q.table Q.halo p
   let b p:=if Cash.numP p=0 then ‖f p‖ else 0
   have h i (hi:b i≠0):f i≠0 ∧ Cash.numP i=0:=by
     unfold b at hi; split at hi
     next h=> exact ⟨fun ht=>hi (by rw [ht,norm_zero]),h⟩
     next h=> exact False.elim (hi rfl)
   have hT:=ring_cast (n:=0) H M hp b (fun i=>by unfold b; split; exact norm_nonneg _; rfl) z he hh (?_) j (fun i hi=> (bloom_active X H M (h i hi).1).2.2.2.1
     (halo_subset _ _ (Finset.image_subset_image (show M.crest⊆ RG.inspected M.crest from Finset.subset_union_left) hj)))
   · convert hT using 1; funext i; unfold b; split;rfl; rw [zero_mul]
   intro p hz; obtain ⟨hv,hF⟩:= h p hz; obtain ⟨hs,-,hA,Hj,-,ht⟩:=bloom_active X H M hv; refine ⟨(H.attends p).2 hs, hA,?_⟩
   let Y := planted X p; let K:= M.steep Y (own p) W o.a Q.table Q.halo p; let v:= z*(M.weight*∏ i∈p.erase (M.turn.badge S), hCost H s i)
   have h' q: ‖M.tithe (Y.taggedL q) (own p) W o.a Q.table Q.halo p‖ ≤ v:= tide (Y.taggedL q) H hk M ha (planted_valid ..) hA (hx p hF hv q).1 (hx p hF hv q).2 he
   unfold b f bloom; rw [if_pos hF, if_pos (by unfold f bloom at hv; split at hv; assumption;exact (hv rfl).elim)]
   change ‖K‖ ≤ v; let c:=(Fintype.card S.Choices:ℝ); have hc : 0<c:=by unfold c; positivity
   unfold K steep likely; rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
   apply le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum (s:=univ) fun i _=> h' i)) (inv_nonneg.mpr hc.le))
   rw [sum_const,nsmul_eq_mul, card_univ, inv_mul_cancel_left₀ hc.ne']
end YM.PhysicalNext.Repeat.Aroma.Leaf

import YM.OPE.Compatible.Basil.Crimp
/-!
 # Keep raw UX determinant exact. Strong on every small W.
-/
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
variable (X:Coat T F) (H:Cash W X.x μ L Q o C T R)(hk:X.width=o.K)(he : RG.flags (Pressure.temp X.x) X.V=∅) {j:ℕ}{δ b:ℝ}(hy:Cash.Renewed j a δ b H) (M: Leaf S R)
local notation "Φ"=> H.smallAt
local notation "F'"=> H.entries X
local notation "Ω" => Gas.total (blocked H.smallAt) F'
local notation "E'"=> Q.overture L μ X.x j
local notation "Q'"=> (1/2:ℝ)
include hk hy
lemma bill_vars : Ready Φ X.B (fun i=> ‖F' i‖) (a+b) E' δ Q':=by
   obtain ⟨hz,hF,hX,hl,hM,hT⟩:=hy.shift
   exact ⟨hz,hF,hX,hl,fun i=> norm_nonneg _,Push.AbsoluteSums.Labels.raise_prices _ _ (fun _=>norm_nonneg _) hT ((H.errorPaid X rfl hk j).1)⟩
lemma depthAt (i:H.ThinP) (ht:X.B+X.B+1= X.B*2+1)(hx:((X.B*2+1:ℕ):ℝ)^4*(E'*(1-Q')⁻¹)≤ Q.exp) :
    let z:= Gas.total (blocked Φ) (cut Φ (Φ i) F'); 0< Ω ∧ 0 ≤ z ∧ z ≤ Ω *Real.exp (Q.exp*coverNumber X.B (Φ i)):=by
     intro z; have hp:= bill_vars X H hk hy; have hb:= add_nonneg hy.full hy.post.le
     let c:= (E'*(1-Q')⁻¹); have hC:0≤ c:=mul_nonneg hp.1.le (inv_nonneg.mpr (by norm_num))
     obtain ⟨_,_,hG,hT⟩:= restores_log Φ (Φ i) X.B F' (fun i=> i.property.1) hb hp
     have ha: 0 < Ω := (Gas.price_log (blocked Φ) F' ⟨fun _=> Or.inl rfl,fun _ _=>blocked_back _⟩ Φ X.B (literal_test Φ fun i=> i.property.1) hb hp).2.2.2.1
     refine ⟨ha,(mul_nonneg ha.le (Real.exp_pos _).le).trans hG, hT.trans ?_⟩
     apply mul_le_mul_of_nonneg_left _ ha.le; apply Real.exp_monotone
     have hF : ((Φ i).card:ℝ) ≤ (coverNumber X.B (Φ i):ℝ) * ((X.B*2+1:ℕ):ℝ)^4:= by rw [←ht];exact_mod_cast Corona.pays (Φ i) _
     apply (mul_le_mul_of_nonneg_right hF hC).trans; rw [mul_assoc]; exact (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)).trans_eq (mul_comm ..)
include he
lemma custard (hx:((X.B*2+1:ℕ):ℝ)^4*(E'*(1-Q')⁻¹)≤ Q.exp)
    {A:ℝ}(hb:SumBudget (fun i:H.ThinP=>‖M.umi H X i‖*Real.exp (Q.exp*coverNumber X.B (Φ i))) A) :
    ‖S.push R.beta M.cicada X.V‖ ≤ S.push R.beta R.eval X.V*A:=by
    let g:= overhead X R Q.table; have hg:0<g:=overhead_pos X H
    let u:= M.umi H X
    have hy'(i:H.ThinP):= depthAt X H hk hy i (by omega) hx
    have hp := bill_vars X H hk hy; let q:= Q.exp; have he' :0≤q:=(mul_nonneg (by positivity) (mul_nonneg hp.1.le (by norm_num))).trans hx
    have hu : Summable u:=(hb.2.1.of_nonneg_of_le (g:=fun i=>‖u i‖) (fun i=> norm_nonneg _) (fun i=> le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (mul_nonneg he' (Nat.cast_nonneg _))))).of_norm
    have hf:Summable F':=by
       have ha:= Product.everyone_ne Φ X.B (show ∀ i,0≤ ‖F' i‖ from fun _=>norm_nonneg _) (fun i _=> i.property.1) hp.2.2.2.2.2
       exact (ha.2.1.of_nonneg_of_le (fun i=> norm_nonneg _) (fun i => le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (mul_nonneg (add_nonneg (add_nonneg hy.full hy.post.le) hp.2.1.le) (Nat.cast_nonneg _))))).of_norm
    rw [M.coupon X H hk he,← slogan X H hk he]
    rw [← (solvation Φ u F' hu hf (fun i=> i.property.1)).2.tsum_eq,norm_mul,Real.norm_of_nonneg hg.le, mul_assoc]; apply mul_le_mul_of_nonneg_left _ hg.le
    have hO:0≤Ω:= (Gas.price_log (blocked Φ) F' ⟨fun _=> Or.inl rfl,fun _ _=>blocked_back _⟩ Φ X.B (literal_test Φ fun i=> i.property.1) (add_nonneg hy.full hy.post.le) hp).2.2.2.1.le
    let f i:= u i*Gas.total (blocked Φ) (cut Φ (Φ i) F') -- annotate
    have hp : SumBudget (fun i:H.ThinP=> ‖f i‖) (Ω*A) :=budget_mono (budget_scale hO hb) (fun _=> norm_nonneg _) (fun i=>by obtain ⟨_,h,hT⟩:=hy' i; unfold f;rw [norm_mul,Real.norm_of_nonneg h]; apply (mul_le_mul_of_nonneg_left hT (norm_nonneg _)).trans_eq; exact mul_left_comm ..)
    exact (norm_tsum_le_tsum_norm hp.2.1).trans hp.2.2
lemma tastes (hx:((X.B*2+1:ℕ):ℝ)^4*(E'*(1-Q')⁻¹)≤ Q.exp) (hf:foam Q L) (hR:R.p.B≤2*radiusB X.x) (hp:(swing Q L μ R.beta X.x C).Buy S.patch.L Q.halo (radiusB X.x)) :
    ‖S.push R.beta M.cicada X.V‖ ≤ S.push R.beta R.eval X.V*(jewelDebt M.tin_ Q L X.x*(swing Q L μ R.beta X.x C).ceiling 0 0 0 0):=by
    apply M.custard X H hk he hy hx; simpa only [Nat.zero_le,↓reduceIte, Coat.B] using M.y_pays X H hk hf hR hp 0
end YM.PhysicalNext.Repeat.Aroma.Leaf

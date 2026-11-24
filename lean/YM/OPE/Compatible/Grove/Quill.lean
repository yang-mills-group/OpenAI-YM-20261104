import YM.OPE.Compatible.Grove.Uprise
/-! # Volume release - operative lifts in dense packets -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
variable {R:PathData G}{P :Clip}{A: CoverConfig G→ℝ}{q:Script (Shade G) r}{N:Side}
lemma readsPeriod (h:Earn r m A q D) (z:Site N)(v:deck (Shade G) N):
    let f:ℝ→ℝ:=fun t=> A (expandAt z (primU G (t • v)))
    ContDiff ℝ ∞ f ∧ WardBin.leading r f=value z q v :=by
       intro f; rw [show f= fun t:ℝ=>A (lotU (t • upl z v)) from funext fun t=>by unfold f primU; rw [expoS]; rfl]; exact h.fees _ ⟨‖v‖,norm_nonneg _,fun i=>(norm_le_pi_norm v _).trans_eq (by unfold poise;ring)⟩
abbrev avgF:ℝ:= (Fintype.card Signed:ℝ)⁻¹
def oathV (R:PathData G)(k:Clip):CoverConfig G→ℝ:= avgF • ∑ i,loftV R k i
def oathX (R:PathData G)(k:Clip)(r:ℕ):Script (Shade G) r:=avgF • ∑ i:Signed,loftX R k i r
lemma oath_earn (G:Gauge)(p:Clip)(s b:ℝ)(hs:0<s)(r m:ℕ): ∃ c:ℝ, ∀ R:PathData G,∀ U,R.Bounds p s b U→ Earn r m (oathV R p) (oathX R p r) c:=by
   obtain ⟨c,H⟩:=repute G p s b hs r m; exact ⟨_,fun R U h=> earnScale (earnSet _ _ _ _ (fun i _=>H R U h i)) avgF⟩
def oathL (R:PathData G):CoverConfig G→ℝ:= avgF • ∑ i:Signed, exactAtoms R.loop i
def oathY (R:PathData G)(r:ℕ): Script (Shade G) r:=avgF • ∑ i:Signed,paymentAtoms R.loop i r
lemma oathLoop (G:Gauge)(s:ℝ)(hs:0<s)(r m:ℕ):∃ C:ℝ,∀ (p:Clip)(R:PathData G)(b U:ℝ),R.Bounds p s b U→ Earn r m (oathL R) (oathY R r) (C*U):=by
    obtain ⟨c,hc,H⟩:= emp ℕ G 2 r s m hs; refine ⟨‖avgF‖*(Fintype.card Signed:ℝ)*c,fun p R b U h=>?_⟩; apply pricerise (earnScale (earnSet _ _ _ _ (fun i _=> H i _ _ h.two)) avgF); rw [Finset.sum_const, nsmul_eq_mul, card_univ]; exact le_of_eq (by ring)
-- exact roots up over Tor. 
abbrev waterV (p: CoverConfig G→ℝ) (v:Config G N):= ∑ i:Site N,p (expandAt i v)
section
lemma pearls (A:ℕ→ Atom G n)(V:Config G N) (i:Signed)(hs:0<s) (h: SumBudget (fun j=>(A j).budget s) b): waterV (exactAtoms A i) V=uncut A (pull i 0 V):=by
    unfold waterV uncut; rw [← Equiv.sum_comp (i.actEquiv (R:=Per N)).toEquiv]; refine sum_congr rfl fun p _=>?_ ; unfold Atom.unmasked RG.Slot.atSite; simp only [expandAt_pull]; rw [exactAtoms, gears _ _ _ hs h]; simp only [affine,add_zero];rfl
lemma waistJob (V:Config G N)(x:Signed)(h:R.Bounds P s b U): ∑ i:Site N, (∑ p:PlaqAxes,waistV R P x p) (expandAt i V)= Precision.quadratic P R (pull x 0 V):=by
   unfold Precision.quadratic; rw [Fintype.sum_prod_type,← Equiv.sum_comp (x.actEquiv (R:=Per N)).toEquiv]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_apply]; refine Finset.sum_congr rfl fun p _=> ?_; let W:=pull x 0 V; let y:Site N:=x.act i
   unfold waistV; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul, Finset.sum_apply]; change P.direct*facePrice G p x (expandAt y V)+_ * (∑ j,rhythm (duetU R p x j) _ _)= _ -- duplicate
   rw [priceValue,duet_power h, ← show expandAt i W=pull x 0 (expandAt y V) by unfold W; rw [expandAt_pull]; simp only [affine,add_zero];rfl]; erw [← (show expandAt i W=pull x 0 (expandAt (x.actEquiv.toEquiv i) V) by unfold W; rw [expandAt_pull]; simp only [affine,add_zero];rfl)]
   change P.direct*_+1/2* ‖voyageAt R p (expandAt i W)‖^2=P.direct*_+ ‖R.ell W (i,p)‖^2 /2; rw [show R.ell W (i,p)=voyageAt R p (expandAt i W) from rfl]
   rw [show faceValue (expandAt i W) (0,p)=faceValue W (i,p) from (travel_at ..).trans (by simp [faceValue])]; ring
lemma oath_main (V: Config G N)(h:R.Bounds P s b U): waterV (oathV R P) V= mainTerm P R V:=by
   unfold waterV oathV mainTerm Patch.average; simp only [Pi.smul_apply,smul_eq_mul,Finset.sum_apply,← Finset.mul_sum]; rw [sum_comm]; apply congr_arg; apply Finset.sum_congr rfl; intro i _; change ∑ j: Site N,(loftV R P i (expandAt j V))=_
   rw [show (∑ j: Site N,loftV R P i (expandAt j V))= (∑ j: Site N,(∑ p,waistV R P i p) (expandAt j V))+waterV (exactAtoms R.cubic i) V+waterV (exactAtoms R.quartic i) V from by
      unfold waterV; simp only [← sum_add_distrib]; rfl, waistJob _ _ h,pearls _ V _ h.width h.three,pearls _ V _ h.width h.four]
lemma oath_trail (V: Config G N)(h:R.Bounds P s b U): waterV (oathL R) V=Precision.loop R V:=by unfold waterV oathL Precision.loop Patch.average; simp only [Pi.smul_apply,smul_eq_mul,Finset.sum_apply, ← Finset.mul_sum]; rw [sum_comm]; apply congr_arg;exact sum_congr rfl (fun i _=> pearls _ V i h.width h.two)
end
-- pinned
structure Prom (p:Script (Shade G) r)(Y: ∀ c:Side,Config G c→ℝ)(m:ℕ)(U:ℝ):Prop where
   stone :soot m p U
   fixed : p.Idem
   Fire (c:Side)(v:deck (Shade G) c): WardBin.leading r (fun t:ℝ=> Y c (primU G (t • v)))= narrate c p v
lemma Prom.yield (h:Earn r m A q U) : Prom (silt q) (fun _=>waterV A) m (U*((r+1:ℕ):ℝ)^m) :=by
    refine ⟨silt_cost h.credit,⟨rooted _,fun i=>by rw [silt_symm i (safeEarn h),h.tandem i]⟩,fun n v=>?_⟩; unfold waterV narrate; rw [← silt_read (safeEarn h),WardBin.lead_sum _ _ (fun i _=> (readsPeriod h i v).1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]; exact sum_congr rfl fun i _=> (readsPeriod h i v).2
end Script
end YM.OPE.Flume

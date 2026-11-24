import YM.RG12.Burst.Whales
/-! A scaled Ore criterion. Adaptation of Rhyme/Rising on combined penalty (proof required, the output here has different magnitude & no theta hypothesis per facet). -/
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March
namespace Charity.RG12
variable (M:Leaf R) (H:Cash W x μ L Q o C T R)
    {s Y A b B C' v d q u r:ℝ}{j n:ℕ}{χ:Chi} (N: Captain H j q d v Y A b r B C' n χ)
local notation "d0" => jewelDebt M Q L x
local notation "za'" => za M H (n:=n)
variable {t Y₁ g z c₁ v₁ b₁ κ' e:ℝ}
variable (h: Herd H N.conduit A B n)
open Repeat.Height -- scope
local notation "sf" => grow G L x
local notation "wo" => Q.mark L μ x
local notation "m11" => mail11 (S:=S) (L:=L) (x:=x) M
variable (p:Clusters H.ThinP)(hg':1≤ grow G L x)
include hg' h
def red1 (i:H.fragrances):ℝ:= clusters H.seam (Zoe1 M H N) i.2
local notation "de" => ((m11) * (d0))
lemma tariff11 : let X:=H.bookFoot (.inr p); ∀ V,Healthy (Pressure.temp x) X V→ Ore V (matin M H p χ) v (de*red1 M H N p) j:=by
  intro Z; let f(p:H.ThinP) V := leaflet H χ V p; let g (p:H.ThinP)V:=libs M H χ V p
  have hx i:= N.collective i
  have he (i:H.ThinP):= debtor M H (p:=i.val) h i.2.2
  have ht i : H.smallAt (p.2 i)⊆ Z:=subset_biUnion_of_mem (H.smallAt ∘ p.2) (mem_univ _)
  intro V hV E _ _ _ U y hy hu
  let c:ℝ:= coefficient H.seam p.2/↑(p.1+1).factorial; let A(i:H.ThinP):=momentS H N i +2*(sip M H N i/m11)
  let K i t:= (∏ b∈univ.erase i,f (p.2 b) (U t))*g (p.2 i) (U t)
  have hg i : Healthy (Pressure.temp x) (H.smallAt (p.2 i)) V:=Finset.disjoint_of_subset_left (ht i) hV
  have hA i:Brush j (A (p.2 i)) 1 (f (p.2 i) ∘ U) y:= (((hx (p.2 i) V).2 (hg i)) E U y hy hu).climb (le_add_of_nonneg_right (mul_nonneg zero_le_two (div_nonneg (rise M H N (p.2 i)) (zero_lt_one.trans_le (mintN M (S:=S) hg')).le))) le_rfl
  have hJ:= mintN M (S:=S) hg'; have hK11:=zero_lt_one.trans_le hJ; have hQ1 := (dew M H).2.1; have hQ' := mul_nonneg hK11.le hQ1
  have hi(t':H.ThinP):0 ≤ A t':= add_nonneg (right H N _) (mul_nonneg zero_le_two (div_nonneg (rise M H N _) hK11.le))
  have hM i:Brush j (de*A (p.2 i)) 1 (g (p.2 i) ∘ U) y:= ((he (p.2 i)).2.2.2.2 V (hg i) E U y hy hu).climb (by
    change d0*sip M H N (p.2 i) ≤ de * _; have hf:=le_mul_of_one_le_left (div_nonneg (rise M H N (p.2 i)) hK11.le) (show (1:ℝ)≤2 by norm_num); let h:= hf.trans (le_add_of_nonneg_left (right H N (p.2 i)))
    have hl:=mul_le_mul_of_nonneg_left h hQ'; rw [mul_comm (m11),mul_assoc,mul_div_cancel₀ _ hK11.ne'] at hl; rw [mul_comm (m11)]; exact hl) le_rfl
  let a':=∏ i,A (p.2 i); let l:ℕ:= p.1+1
  have hK(i): Brush j ((a'*de)*(1+(l:ℝ))^j) 1 (K i) y:=by
    apply (((Brush.all_prod (univ.erase i) (fun i=> f (p.2 i) ∘ U) _ _ (fun i _=> hA i)).paints (hM i)).trim).climb _ le_rfl
    have hp : (univ.erase i).card=p.1:=by rw [card_erase_of_mem (mem_univ _),card_univ,Fintype.card_option,Fintype.card_fin]; omega
    simp only [sum_const, nsmul_eq_mul, hp,mul_one]; apply le_of_eq; unfold a' l; rw [← Finset.mul_prod_erase _ _ (mem_univ i)]; push_cast; ring
  apply ((Brush.spree _ K _ zero_le_one (fun i (_:i∈univ)=> hK i)).smul c).climb _ le_rfl; rw [sum_const,nsmul_eq_mul]
  have hc : (l:ℝ) * (1+(l:ℝ))^j≤ (2^(j+2):ℝ)^l:=by
    have hj : 1+(l:ℝ)≤ 2^l:= by rw [add_comm]; exact_mod_cast Nat.lt_two_pow_self (n:=l)
    calc
      (l:ℝ)*_ ≤ 2^(2*l)*((2^l:ℝ)^j) := by gcongr; exact (le_add_of_nonneg_left zero_le_one).trans (hj.trans (pow_le_pow_right₀ (by norm_num) (by omega))) -- issue
      _ = _:=by simp_rw [← pow_mul, ← pow_add]; ring_nf
  simp only [card_univ,Fintype.card_option,Fintype.card_fin]
  unfold red1 clusters; conv_rhs=> arg 2; arg 1; arg 2; change ∏ i, 2^(j+2)*A (p.2 i); rw [prod_mul_distrib,Finset.prod_const,card_univ,Fintype.card_option,Fintype.card_fin]
  calc
    _ = (‖c‖*(a'*de))*((l:ℝ)*(1+(l:ℝ))^j) := by unfold l; push_cast; ring
    _ ≤ (‖c‖*(a'*de))*(2^(j+2))^l := mul_le_mul_of_nonneg_left hc (mul_nonneg (norm_nonneg _) (mul_nonneg (Finset.prod_nonneg fun _ _=>hi _) hQ'))
    _ = _ := by unfold c l a'; rw [Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : 0<((p.1+1).factorial:ℝ))]; ring
omit h in
lemma redN (p:H.fragrances): 0 ≤ red1 M H N p:= by
  apply clusters_nonneg; intro i
  apply mul_nonneg (by positivity); exact add_nonneg (right H N _) (mul_nonneg zero_le_two (div_nonneg (rise M H N _) (zero_le_one.trans (mintN M (S:=S) hg'))))
def rib11 (y:Site c)(i:ℕ)(p:H.fragrances):= if speaks M H p then de*red1 M H N p*potY M H y i (j:=j) p else 0
omit h in
lemma ribN (y:Site c)(p:H.fragrances){i:ℕ}:0 ≤ rib11 M H N y i p:=by
  unfold rib11; split; apply mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans (mintN M (S:=S) hg')) (dew M H|>.2.1)) (redN M H N hg' p)); unfold potY flareC March.shiftG; positivity
  exact le_rfl
lemma allergen11 (U : BudgetPoint){y:Site c}(hy:y∈M.crest.image S.ratio.parent)(hU':U.threshold=Pressure.temp x)(hf:U.order≤j)(p:H.fragrances):U.supBounds y (locus M H y p) (matin M H p χ) (rib11 M H N y U.power p):=by
    by_cases hx:speaks M H p; swap; · unfold rib11; simpa only [if_neg hx] using! aliveY M H N h U hy hU' hf p
    unfold rib11 potY locus; rw [if_pos hx,if_pos hx]; let Y:= H.bookFoot (.inr p); let l:ℝ:=de*red1 M H N p; let q :ℝ:=coverNumber (radiusB x) Y; let t:= shiftG x * (1+q)
    obtain ⟨hX,hY,hF,_⟩:=heeds M H N h p
    have hL V (hh:Healthy U.threshold Y V):Ore V (matin M H p χ) v l j:= tariff11 M H N h p hg' V (hU' ▸ hh)
    have hhU:Sailor G U.threshold C' j:= ⟨fun c _ hb=> N.weigh.stroke c _ (hb.trans (hU'.trans_le N.talent))⟩
    have hN:0 ≤l:= mul_nonneg (mul_nonneg (zero_le_one.trans (mintN M (S:=S) hg')) (dew M H|>.2.1)) (redN M H N hg' p)
    have hs:1≤ shiftG x:=by unfold shiftG; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]
    have hi:1≤t:=one_le_mul_of_one_le_of_one_le hs (le_add_of_nonneg_right (Nat.cast_nonneg _))
    refine ⟨mul_nonneg hN (pow_nonneg (zero_le_one.trans hi) _),fun V ht l hl ha=>?_⟩
    apply (costsD hX hhU N.income y _ N.near (hL V ht) (Y:=t) ?_ hi l (hl.trans hf) ha).trans_eq; · exact mul_comm ..
    intro i he; have hh:=seatY M H y hy p; unfold locus at hh; rw [if_pos hx] at hh; have hf : (separation i y:ℝ) ≤ q*(4*(radiusB x:ℝ)+2)+2*(radiusB x:ℝ) := by unfold q; exact_mod_cast Lattice.Corona.extent Y (radiusB x) he hh
    unfold t shiftG; nlinarith [Nat.cast_nonneg (α:=ℝ) (radiusB x), show 0≤ q from Nat.cast_nonneg _]
end YM.PhysicalNext.Repeat.Daisy.Charity.RG12

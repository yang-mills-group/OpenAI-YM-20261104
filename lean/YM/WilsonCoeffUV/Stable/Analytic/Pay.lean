import YM.WilsonCoeffUV.Stable.AllHeights
import YM.WilsonCoeffUV.Horizon.Restore
/-!
# Uniform estimates on formal stable-state source propagation, exponential side

Use one true-width atom majorant for each (order,rank), same width after an arbitrary number
of blockings in the same stage, and overlap across stages. In unchanged order and rank the mean
of the slice differs from the careful predictor by a gradient at post cost multiplying only lower
coupling orders by Ward. Testing the latter predictor on a projected-null input is available at
pre cost. We need the secondary (projection of that answer) bound using only CHEAPER components
of the input, not with a factor involving the output rank kernel cost; otherwise multiplication by
Peaks in the full stable projection could destroy the pre-cost. All algebra in coupling series.
Not a statement on analytic IN g. No physical mask in these norms.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.StableStrip
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Shard Mer.Scopes
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{ι U V: Type*}{r h D l j i e k a m b u N M c:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B x δ:ℝ}

def coefficientCash (F:Frame G h) (s:ℝ)(p:0<s)(D:ℕ): ℝ:= ∑ i∈Finset.range (h+1),(paid_echo F s p i D).choose
lemma billCash_sum (F:Frame G h)(s:ℝ)(p:0<s)(D:ℕ): 0≤coefficientCash F s p D:= Finset.sum_nonneg fun i _=> (paid_echo F s p i D).choose_spec.1
lemma earlierCash (v:Alma F)(g:0<s){Y:Single G D}(ha:0≤ A)(p:∀ l< i,∀ k< valence F v,Twig 0 s A (Y l k)) : ‖ptax F Y i v‖≤ coefficientCash F s g D*A:=by
    let B (r:ℕ):=(paid_echo F s g r D).choose
    have hz k:0≤ B k:= (paid_echo F s g k D).choose_spec.1
    apply le_trans _ (b:=(∑ k∈ Finset.range (valence F v),B k)*A) (mul_le_mul_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg (t:=Finset.range (h+1)) (Finset.range_mono ((valence_cap ..).trans h.le_succ)) (fun i _ _=>hz i)) ha)
    unfold ptax; rw [Finset.sum_mul]; apply (norm_sum_le ..).trans; refine Finset.sum_le_sum fun k hk=>?_; have hv:=Finset.mem_range.mp hk; split; · exact (paid_echo F s g k D).choose_spec.2 v _ A (p _ (by omega) _ hv)
    rw [norm_zero]; exact mul_nonneg (hz _) ha
lemma atValence (p:0<s){Y:ChamberTen G (Vote D) r}(q:Twig 0 s A Y)(i:Alma F)(hk:r≤h): ‖echoS F Y i‖≤coefficientCash F s p D*A:=by
    apply ((paid_echo F s p r D).choose_spec.2 i Y A q).trans; exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=>(paid_echo F s p i D).choose_spec.1) (Finset.mem_range.mpr (by omega))) q.1

lemma earlierRows (e k h r D d:ℕ)(G:Gauge) : ∃ c:ℕ,∀ I:Cloister G h,∃ C:ℝ,0≤ C∧∀ P:Tand I.lamp e r D,∀ i j,lowerGrade i j e r→j≤d → Twig 0 I.lamp.exitS (C*P.x^c) (Orchard (inkPin I) P.P.P h k P.Y i j):=by
   classical
   let S:= ((Finset.range (e+1))×ˢ(Finset.range (d+1))).filter (fun i=> lowerGrade i.1 i.2 e r)
   let R (x:ℕ×ℕ)(I:Cloister G h)(c:ℕ)(C:ℝ):= ∀ P:Tand I.lamp e r D,Twig 0 I.lamp.exitS (C*P.x^c) (Orchard (inkPin I) P.P.P h k P.Y x.1 x.2)
   have HH (i:ℕ×ℕ) (hi:i∈S) : ∃ b':ℕ,∀ I:Cloister G h,∃ C,0≤ C ∧ R i I b' C:=by
       obtain ⟨v,hv⟩:= Fabric.higher (G:=G) ((Finset.mem_filter.mp hi).2) k D; refine ⟨v,fun I=>?_⟩
       obtain ⟨C,hC,t⟩:=hv I.lamp; let g:= gradeH (inkPin I).patch h k; have hg:0≤g:= grade_nn ..
       refine ⟨g*C,mul_nonneg hg hC,fun P=>?_⟩
       have he:= Cork.μ (t P).wax g; rw [abs_of_nonneg hg] at he; exact he.cost (le_of_eq (mul_assoc ..).symm)
   obtain ⟨c,H⟩:= gazette _ S R HH (fun i _ I d e a b g p q h P=> (h P).cost (mul_le_mul q (pow_le_pow_right₀ P.P.rich g) (pow_nonneg (zero_le_one.trans P.P.rich) _) (p.trans q)))
   refine ⟨c,fun i=>?_⟩; obtain ⟨C,h,p⟩:= H i; refine ⟨C,h,fun P x y t v=> p (x,y) ?_ P⟩; apply Finset.mem_filter.mpr; exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (show _ from by unfold lowerGrade at t; simp only; omega),Finset.mem_range.mpr (show y<d+1 from by omega)⟩,t⟩

lemma unShelved (F:Frame G h)(H:Hol G)(p:h<D)(e k r:ℕ): ∃ d:ℕ,∀ I:Cloister G h,∃ C:ℝ,0≤ C∧∀ (P:Tand I.lamp e r D)(_:Courant I P.P.P)(X:ℝ), I.lamp.dues r→ Stakes P.Y→ (∀ i:Alma F,valence F i=r→ glean F P.Y e i=0) → Twig 0 I.lamp.input X (P.Y e r) →
   let B:=I.lamp; let Z:=Orchard (inkPin I) P.P.P h k P.Y; let W:= C*P.x^d
   Twig 0 B.exitS ((velo H F p B r)/(inkPin I).patch.L.val * X + W) (Z e r) ∧ Clean 0 e r F W Z:=by
   obtain ⟨d,H'⟩:= Fabric.resinH (G:=G) (e:=e) r k D; obtain ⟨w,t⟩:=earlierRows e k h r D h G
   refine ⟨d+w+1,fun I=>?_⟩; let s:=I.lamp.exitS; have hs:0<s:=I.lamp.positive
   obtain ⟨A,hA,f⟩:= H' I.lamp; obtain ⟨T,hT,H0⟩:= tower_gain F H I p e r; obtain ⟨X,hX,F'⟩:= paid_echo F s hs r D
   let g:=gradeH (inkPin I).patch h k; have hg:0≤g:=grade_nn ..; let R:=g*A; have hR:0≤R:=mul_nonneg hg hA
   obtain ⟨C,hC,m⟩:=t I; let Y:=coefficientCash F s hs D; have hY:0 ≤ Y:=billCash_sum ..
   let L:=T+R+X*R+(Y*C+Y*C); have hL : T+R ≤ L:=by unfold L; nlinarith
   let k':=d+w+1
   have hL':0≤L:= (add_nonneg hT hR).trans hL
   refine ⟨L,hL',?_⟩; intro P u x tV z hE h₀ B Z G
   have he:1≤ P.x:=P.P.rich; have hb:0≤P.x:=zero_le_one.trans he
   obtain ⟨p0,p1⟩:= H0 P.P.P u P.Y P.x x tV hb z (fun i v r=> (P.rent i r (Or.inl v)).wax) (fun i v=>by rw [hE i v,norm_zero]; exact hb) ((P.P.Υ.mono (B.outlet.trans B.path.holds.le)).oneP) h₀
   let V:= g • (carnival (inkPin I) P.P.P k P.Y e r+veering (inkPin I) P.P.P k P.Y e r)
   let E:= hall (inkPin I).patch h P.P.P.Q (P.Y e r)
   have ha:Z e r= E+V:=by unfold Z Orchard; rw [Pi.smul_apply,Pi.smul_apply,helmet_bows,smul_add]; unfold hall E; rw [hall,smul_smul,gradeBB]
   let J:=P.x^k'
   have hc:Twig 0 B.exitS (R*J) V:=by
       have hx:= Cork.μ (f P).wax g; rw [abs_of_nonneg hg] at hx; refine hx.cost ?_
       change g*(A*P.x^d)≤ _; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ he (show d≤k' from by omega)) hR
   have hz: C*P.x^w ≤ C*J:= mul_le_mul_of_nonneg_left (pow_le_pow_right₀ he (show w≤k' from by omega)) hC
   have hr: T*P.x≤ T*J:= mul_le_mul_of_nonneg_left ((by rw [pow_one]:P.x ≤ P.x^1).trans (pow_le_pow_right₀ he (show 1≤k' from by omega))) hT
   have hj:0≤J:=pow_nonneg hb _
   refine ⟨ha.symm ▸ (Cork.add (P:=E) (Q:=V) p0 hc).cost ?_, mul_nonneg hL' hj,?_⟩
   · rw [add_assoc]; apply add_le_add_right; change T*P.x+R*J≤_; exact (add_le_add_left hr (R*J)).trans (le_trans (le_of_eq (add_mul ..).symm) (mul_le_mul_of_nonneg_right hL hj))
   intro i j p; let x:=valence F j; have hVal:x≤h:= valence_cap ..
   rw [tail_glint]; apply (norm_add_le ..).trans
   have hh : ‖ptax F Z i j‖≤ Y*C*J:=by rw [mul_assoc Y]; exact earlierCash j hs (mul_nonneg hC hj) (fun q h u p'=> (m P q u (Or.inl (by omega)) (p'.le.trans hVal)).cost hz)
   by_cases i0 : lowerGrade i x e r
   · refine (add_le_add hh (atValence hs ((m P i _ i0 hVal).cost hz) j hVal)).trans ?_; change Y*C*J+Y*(C*J)≤_; rw [←mul_assoc Y,←add_mul]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hj
   unfold x lowerGrade at i0; have hv':i=e:=by omega
   have hp: valence F j=r:=by omega
   subst i
   apply (add_le_add hh (b:=_) (d:=T*J+X*(R*J)) ?_).trans ?_
   · rw [hp,ha,echo_add j p0 hc hs hs]; apply (norm_add_le ..).trans (add_le_add ((p1.tell j (weigh_cap ..) hp).trans hr) (F' j V _ hc))
   change Y*C*J+(T*J+X*(R*J))≤ L*J; rw [← mul_assoc X]; simp_rw [←add_mul]; exact mul_le_mul_of_nonneg_right (by unfold L; nlinarith) hj
end YM.WilsonCoeffUV.StableStrip

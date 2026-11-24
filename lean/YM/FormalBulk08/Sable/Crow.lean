import YM.FormalBulk08.Sable.Joule
import YM.FormalBulk08.Palm.Sister
/-! Polygonal invariant projection. Payable on Schedule age not hypotheses H. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sable
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Grail Work.F03 Work.F05 Work.F08
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels Dawn Palm
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I:Type}{G:Gauge}{d m D l e r u :ℕ}{σ η A B C:ℝ}
lemma muses (o:Loc G 1)(F:Frame G d)(b:Cover)(D q m l e:ℕ)(hq:q≤d+1)(v:Seasons)(r: Fin m→ℕ)(H:Hol G)(hr:∀ i,0<r i)(hv:(∑ i,r i)+upper v<q)(hp:(d+1)*(d+1)≤u)(A:Fin m→ℝ)(hA:∀ i,0≤A i) : ∃ C:ℝ,0≤C∧∀ Y: Anthem D G,Clef o Y l→∀ B,Steps F o u q e m Y B → ∀ p:(i:Fin m)→Prism G.Color (r i),(∀ i,‖p i‖≤ A i) → ‖tariffs (fun i=>billPr G _ b (p i)) (Y (cone D v) e m)‖≤ C*B:= by
    let U i:=billPr G (r i) b;let P i:=Prism G.Color (r i); let c' (i:Fin m):=Module.finBasis ℝ (P i); let I(i:Fin m):= Fin (Module.finrank ℝ (P i))
    let Z i (a:I i):=eastern (charted (c' i a)) b; have hb i j:Z i j∈rangeLt (Axis→G.Color) (r i):= band_shift (read_poly _) _
    choose! C hC HC using fun w:(i:Fin m)→I i=>stitchK o F e q m hq v D l (fun i=> Z i (w i)) r hr hv (fun i=>hb _ _) H hp
    let k i (a:I i):=LinearMap.toContinuousLinearMap ((c' i).coord a); let c i j:= ‖k i j‖*A i; let M (w:(i:Fin m)→I i):=∏ i,c i (w i); have hM w:0≤M w:=Finset.prod_nonneg (fun i _=>mul_nonneg (norm_nonneg (k i (w i))) (hA _))
    refine ⟨∑ i,M i*C i,Finset.sum_nonneg (fun i _=>mul_nonneg (hM i) (hC i)),fun Y hY B hB p hp=>?_⟩; let t:=Y (cone D v) e m; obtain ⟨W,s,hs,hw⟩:=rum Y o hY (cone D v) e m
    let T i j:=assigns (Z i j); let D i j:= k i j (p i) • T i j
    rw [show (fun i : Fin m=> billPr _ _ _ (p i))=fun i=> ∑ j:I i,D i j from ?h, dial D ?hy hs t hw,Finset.sum_mul];apply (norm_sum_le ..).trans; refine Finset.sum_le_sum fun i _=>?_
    · have he : tariffs (fun j=> D j (i j)) t= (∏ j:Fin m,k j (i j) (p j))* tariffs (fun j=>T j (i j)) t:= by unfold tariffs;rw [←tsum_mul_left]; refine tsum_congr fun u=>?_ ; unfold D; simp only [Pi.smul_apply,smul_eq_mul,Finset.prod_mul_distrib];rw [mul_left_comm]
      rw [he,_root_.norm_mul,norm_prod, mul_assoc];exact mul_le_mul (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=> ((k j (i j)).le_opNorm (p j)).trans (mul_le_mul_of_nonneg_left (hp j) (norm_nonneg (k j (i j)))))) (HC i Y hY _ hB) (norm_nonneg _) (hM i)
    case h=> funext i; nth_rw 1 [← (c' i).sum_repr (p i)]; rw [map_sum]; apply Finset.sum_congr rfl; intro j _; rw [map_smul];rfl
    case hy=> exact fun i j=>shoulder (Submodule.smul_mem (rangeLt (Axis→G.Color) (r i)) (k i j (p i)) (hb i j))
lemma memoir (o:Loc G 1)(F:Frame G d)(n l e D q:ℕ)(r:Fin n→ℕ)(hr:∀ i,0<r i)(X: Fin n→ Snap G d)(hw:∀ i,throughSlot (X i) (r i))(v: Seasons)(hv:(∑ i,r i)+upper v < q)
      (hp:d<D)(hq:q≤d+1)(U : Side)(j t:ℕ)(hd:d≤j)(hj:4≤j)(ht:4≤t)(H:Hol G)(K:KernelChoices)(hs:(d+1)*(d+1)≤u):
    ∃ C:ℝ,0≤C∧∀ P:Flight j t,P.L=U→∀ x:Site P.L,∀ hL:2≤P.L.val,∀ Y:Anthem D G,Clef o Y l→∀ B:ℝ, Steps F o u q e n Y B →∀ η A:ℝ,0<η → (linesOf P K.penalty).strip η A → 0≤A →
     ‖slate (upmost P.L x (chair P G K) (Y (throughW x D hL (cone D v)) e n)) d n X‖≤ C*B:= by
    let U0 i:=Place.sampled (X i); choose f hf hz using fun i=> analyze (U0 i) (steady_bl _ _ (hw i))
    choose C hC HC using fun i:Fin n=> deliver (E:=G.Color) K.penalty K.penalty_pos hj ht (r i) (show r i ≤ j from (Finset.single_le_sum (f:=r) (fun i _=> Nat.zero_le _) (Finset.mem_univ _)).trans (by omega))
    let a i:= C i* pile (f i); have ha i:0≤a i:=mul_nonneg (zero_le_one.trans (hC i)) (pile_pos _); let s:=Finset.univ.filter (fun i:Spring D=>upper i.val≤ upper v)
    choose! c hc Hc using fun (x:Site U)(i:↥s)=> muses o F (lift x) D q n l e hq i.val.val r H hr (show (∑ j,r j)+upper i.val.val< q from (Nat.add_le_add_left (Finset.mem_filter.mp i.property).2 _).trans_lt hv) hs a ha
    let Y(x:Site U):=∑ i,c x i; have hY x:0≤Y x:= Finset.sum_nonneg (fun _ _=> hc x _); let E:=∑ x:Site U,Y x; have hE:0≤E:=Finset.sum_nonneg fun i _=>hY i
    let D0:= ((upper v+1:ℕ):ℝ)*Fintype.card (Spring D); refine ⟨D0*(‖cone D v‖*E),mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (mul_nonneg (norm_nonneg _) hE),fun P hs' x hL Z HZ B hB η A hη h' hA=>?_⟩
    choose g hg using fun i=>HC i P (f i); let L i:=assigns (eastern (charted (g i)) (lift x)); let z:=throughW x D hL (cone D v)
    obtain ⟨B',s0,hB',ha'⟩:= rum Z o HZ z e n
    let η':=min η s0; have ht:0 < η':=lt_min hη hB'; have he: η' ≤ P.L.val * s0:= le_trans (min_le_right ..) (zesp hB'.le);have h':=(show (linesOf P K.penalty).strip η' A from strip_mono h' (min_le_left ..) le_rfl)
    let b:=upmost P.L x (chair P G K) (Z z e n); change ‖slate b d n X‖≤ _; rw [severance b (pearl_agate (merit (chair P G K)) (jetty_agate _ (HZ.fare.2.1 z e n))) (upheave _ x (grown_budget G _ hA h') hA he ht.le ha') ht]; let W0 i:= charted (g i)
    rw [show tariffs (fun i=> assigns (Place.sampled (X i))) b = tariffs L (Z z e n) from occurs _ ha' hB'.le x ht he _ h' hA U0 r (fun i=>steady_bl _ _ (hw i)) W0 (fun i=>?R)]
    swap; · rw [← hz]; exact (hg i).rolled
    let V (p: Studio D):= tariffs L (Z p e n); have hV:IsLinearMap ℝ V:=peer_role o L HZ (fun i=>shoulder (band_shift (read_poly (g i)) _)); let M:Studio D→ₗ[ℝ]ℝ:=⟨⟨V,hV.1⟩,hV.2⟩
    have hz' i (hi: i∈s): ‖M (cone D i.val)‖≤ E*B:= by
        let x': Site U:= hs' ▸ x; have he' : lift x'=lift x:= by subst U; rfl
        let k:↥s:=⟨i,hi⟩; have hU:= Hc x' k Z HZ B hB g (fun i=>reel_norm (hg i) (zero_le_one.trans (hC i))); rw [he'] at hU
        exact hU.trans (mul_le_mul_of_nonneg_right (show c x' k≤E from (Finset.single_le_sum (f:= c x') (fun j _=>hc x' j) (Finset.mem_univ _)).trans (show Y x' ≤ E from Finset.single_le_sum (f:=Y) (fun i _=> hY i) (Finset.mem_univ _))) hB.1)
    rw [mul_assoc D0,mul_assoc ‖cone D v‖ E]; exact slips v x hL (by omega) M (E*B) (mul_nonneg hE hB.1) (fun i hi=>hz' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩))
lemma credulous (o:Loc G 1)(F:Frame G d)(l n q e D:ℕ)(hp:d<D)(hq:q≤d+1)(i:Letter F)(hz: slots F i=n)(hx:Pose.weight F i<q)(U:Side)(j t:ℕ)(hd:d≤j)(hj:4≤j)(ht:4≤t)(H:Hol G)(K:KernelChoices)(hs:(d+1)*(d+1)≤u):
    ∃ C:ℝ,0≤C∧∀ P:Flight j t,P.L=U→∀ x:Site P.L,∀ hL:2≤P.L.val,∀ Y:Anthem D G,Clef o Y l→∀ B:ℝ,Steps F o u q e n Y B →∀ η A:ℝ,0<η → (linesOf P K.penalty).strip η A → 0≤A →
     ‖pearlJ F (upmost P.L x (chair P G K) (Y (throughW x D hL (inside F i D)) e n)) (mint F i)‖≤C*B:= by
    let s: Finset (Fin n→WardBin.Board G d):= Finset.univ.filter (fun v=>WardBin.depth v=Pose.label F i)
    choose! C hC HC using fun x:↥s=> memoir o F n l e D q (fun i=> generation (WardBin.key (x.val i))) (fun i=>chip_gen _) _ (fun i=>chip_kind (x.val i)) (pet F i).val (show WardBin.depth x.val+upper (pet F i).val < q from (congr_arg (·+upper (pet F i).val) (show WardBin.depth x.val=Pose.label F i from (Finset.mem_filter.mp x.property).2)).trans_lt hx) hp hq U j t hd hj ht H K hs
    let c:=∑ i,C i; have hc:0≤c:= Finset.sum_nonneg (fun _ _=> hC _); obtain ⟨a,ha,H⟩:=pocket_book F (Pose.label F i) n (mint F i)
    refine ⟨a*c,mul_nonneg ha hc,fun P h x hL Y hY B hB η A hη hP hA=>?_⟩; unfold pearlJ;rw [show (F.grades (mint F i)).2=n from hz,mul_assoc];apply H _ _ (mul_nonneg hc hB.1); intro v hv; let k:↥s:=⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩; exact (HC k P h x hL Y hY _ hB _ _ hη hP hA).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=C) (fun i _=>hC i) (Finset.mem_univ _)) hB.1)
lemma endorse (o:Loc G 1)(F:Frame G d)(l n q e D:ℕ)(hp:d<D)(hq:q≤d+1)(i:Letter F)(hz: slots F i=n)(hx:Pose.weight F i<q)(U:Side)(j t:ℕ)(hd:d≤j)(hj:4≤ j)(ht:4≤t)(H:Hol G)(K:KernelChoices)(hs:(d+1)*(d+1)≤u):
    ∃ C:ℝ,0≤C∧∀ P:Flight j t,P.L=U→∀ hL:2≤P.L.val,∀ Y:Anthem D G,Clef o Y l→∀ B:ℝ, Steps F o u q e n Y B →∀ η A:ℝ,0<η → (linesOf P K.penalty).strip η A → 0≤A →
     ‖pearlJ F (towerV (chair P G K) Y d e n hL (inside F i D)) (mint F i)‖≤ C*B:= by
     obtain ⟨C,hC,H⟩:= credulous o F l n q e D hp hq i hz hx U j t hd hj ht H K hs; refine ⟨(U.val:ℝ)^d*C,by positivity,fun P he hL Y hY B hB η A hη hX hA=>?_⟩; obtain ⟨s,C',hs,-,h'⟩:= hY.fare.2.2 e n
     rw [(emerge o F (chair P G K) Y (strip_mono (grown_budget G _ hA hX) (min_le_left ..) le_rfl) (lt_min hη hs) hA _ _ _ _ _ (le_trans (min_le_right ..) (zesp hs.le)) (fun p=>⟨_,h' p⟩)).2,_root_.norm_mul]; refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum (fun x _=>H P he x hL Y hY _ hB _ _ hη hX hA))) (norm_nonneg _)).trans_eq ?_
     rw [Real.norm_eq_abs, income_by, he, ←mul_assoc]
end YM.FormalBulk08.Sable

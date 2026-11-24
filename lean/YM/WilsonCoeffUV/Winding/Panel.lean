import YM.WilsonCoeffUV.Winding.Elementary
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent
open scoped Topology BigOperators
variable {n L:Side}{ι U X α β V:Type*}{i j k r:ℕ}{s a A B t q :ℝ}
lemma spindle_size (L:Side)(x:Cover): size (L.val• x)=L.val*size x:=by unfold size; simp [Finset.mul_sum,Int.natAbs_mul]
lemma padLift (x y:Cloth (Co L α)): Bank.terrain.gap (panel L α x).1 (panel L α y).1≤ L.val * (Bank.terrain.gap x.1 y.1+8):=by
    let p:=L.val•x.1; let q:=L.val•y.1; let d:= Bank.terrain
    have he:d.gap p q=L.val*d.gap x.1 y.1:=by change size (L.val•y.1 - L.val•x.1) = _; rw [←smul_sub,spindle_size]; rfl
    have ht(z:Cloth (Co L α)):d.gap (L.val• z.1) (panel L α z).1≤4*L.val:=by change size (L.val•_ +lift z.2.1-L.val •_)≤_ ; rw [add_sub_cancel_left]; exact crowd _
    apply (d.tri _ p _).trans; apply le_trans (add_le_add (show d.gap (panel L α x).1 p ≤ 4*L.val from (d.swap ..).le.trans (ht x)) (d.tri _ q _))
    rw [he,mul_add]
    have hx:=ht y; change 4*L.val+(L.val*d.gap x.1 y.1+d.gap _ _ ) ≤ _
    unfold q; unfold d at *; omega
lemma guideScale {i j:ℕ}(p: j≤ L.val*(i+8))(v: (n*L).val≤4*j): n.val≤4*i+32:=by
    apply (Nat.mul_le_mul_right_iff (show L.val>0 from L.property)).mp
    calc
        _ ≤ 4*j:= v
        _ ≤ 4*(L.val*(i+8)):= Nat.mul_le_mul_left 4 p
        _ = _:= by ring
lemma cheer_mid (h:0<s){D:ℕ}(p:n.val≤ 4*D+32):Real.exp (-s*D) ≤ Real.exp (8*s)*catchW (s/8) n:=by
    unfold catchW; rw [← Real.exp_add,Real.exp_le_exp]; have ht : (n.val:ℝ)≤4*D+32:=by exact_mod_cast p
    nlinarith [mul_le_mul_of_nonneg_left ht h.le]
variable [NormedAddCommGroup V]
lemma tideCosts {Q:Ten V (Co (n*L) α) r}{F:Ten V (Cloth α) r}(s:ℝ)(p:0<s)(T:Amber (tor (n*L)) s A Q)(P:Amber Bank.terrain s A F)(v: Wound Q F (n*L) (slideC (n*L)) (soar Bank.terrain) s A):
    let B:= (A+A)*Real.exp (16*s)
    let T:= turnTen (panel L α).symm F
    let W:= turnTen (splitCo (ratioN L n) α) Q
    Wound W T n (slideC n) (soar Bank.terrain) (s/8) B∧ Amber Bank.terrain (s/8) B T∧ Amber (tor n) (s/8) B W:=by
   intro B F' Q'; let q:= Real.exp (8*s); have hq:1≤ q:= Real.one_le_exp (by positivity); have ha:=v.coal; have hl:1≤ (L.val:ℝ):=by exact_mod_cast L.property
   have hv : A*q≤ B:=by unfold B; rw [show Real.exp (16*s)=q*q from by unfold q; rw [←Real.exp_add]; congr 1; ring]; nlinarith [mul_nonneg ha (show q-1≥0 from by linarith)]
   have hu:A≤ B:=(le_mul_of_one_le_right ha hq).trans hv
   have hp:= gather_isle (ratioN L n) p.le (T.mono (div_le_self p.le hl)); have hP:= gather_coast (L:=L) p.le (P.mono (div_le_self p.le hl)); have he:s/8≤s:=by linarith
   refine ⟨⟨ha.trans hu,fun x w=>?_⟩,(hP.mono he).le hv,(hp.mono he).le hv⟩
   let y:= panel L α ∘ x; by_cases hz:4*soar Bank.terrain y < (n*L).val
   · rw [show Q' (slideC n x)=Q (slideC (n*L) y) from congr_arg Q (funext fun i=> (panel_wrap (ratioN L n) (x i)).symm)]
     apply (v.local_w y hz).trans; apply mul_le_mul hu ((catch_width he _).trans (Real.exp_monotone ?_)) (catch_hot ..) (ha.trans hu)
     apply mul_le_mul_of_nonpos_left _ (by linarith); exact_mod_cast (show n.val≤ (n*L).val from Nat.le_mul_of_pos_right _ L.property)
   have hh:n.val≤4*soar Bank.terrain x+32:= by
       apply guideScale (j:=soar Bank.terrain y) (L:=L) _ (Nat.le_of_not_gt hz); apply league_le; intro i j; exact (padLift _ _).trans (Nat.mul_le_mul_left L.val (Nat.add_le_add_right (leg_le Bank.terrain (Prod.fst∘ x) i j) 8))
   apply (norm_sub_le ..).trans; have H:= (cheer_mid p hh); have hX: 0≤ A*q:=mul_nonneg ha (zero_le_one.trans hq)
   have hU : ‖Q' (slideC n x)‖≤ (A*q)*(q*catchW (s/8) n):=by
       have hV:soar (tor n) (slideC n x)=soar Bank.terrain x:= exact_course (x:=Prod.fst ∘ x) w
       apply (hp.2 _).trans; rw [hV]; exact mul_le_mul_of_nonneg_left H hX
   apply le_trans (add_le_add hU ((hP.2 x).trans (mul_le_mul_of_nonneg_left H hX))); apply le_of_eq; unfold B; rw [show Real.exp (16*s)=q*q from by unfold q; rw [← Real.exp_add]; congr 1; ring]; ring
variable [NormedSpace ℝ V]
lemma Sight.panelCost {Q:Gen V (Co (n*L) α)}{F: Gen V (Cloth α)}(h:Sight (Q r) (F r) s A)(p:0<s): Sight (bend (splitCo (ratioN L n) α) Q r) (plants L F r) (s/8) (2*A*Real.exp (16*s)*Fintype.card (Site L)):=by
    let B:= Real.exp (16*s); let C:ℝ:= Fintype.card (Site L); let g:= ratioN L n; let e:= splitCo g α; have hh: 1≤ C:=by unfold C; exact_mod_cast (show 1≤Fintype.card (Site L) from Fintype.card_pos)
    have hc:0≤ C:=zero_le_one.trans hh
    obtain ⟨H,H',J'⟩:= tideCosts s p h.aim h.bound h.gall; have hv:= h.aim.1
    cases r with
    | succ r=>
        rw [plant_pt]; rw [pruce_down] at J' H
        refine Sight.more (A:=(A+A)*Real.exp (16*s)) ⟨by rw [pruce_down]; exact J',H',by rw [pruce_down]; exact H, stroller g h.strollT⟩ ?_
        rw [two_mul A]; exact le_mul_of_one_le_right J'.1 hh
    | zero=>
        rw [plant_coin, ← Nat.cast_smul_eq_nsmul (R:=ℝ)]; have he:2*A*Real.exp (16*s)*C=‖C‖*((A+A)*Real.exp (8*(2*s))):=by rw [Real.norm_eq_abs,abs_of_nonneg hc,show 8*(2*s)=16*s from by ring]; ring
        rw [show 8*(2*s)=16*s from by ring] at he; rw [he]
        have hx : pruce (bend e Q 0)=C • turnTen e (pruce (Q 0)):=by
            unfold pruce; simp only [↓reduceIte,within_bend,smul_smul]; have hz : (Fintype.card (Site (n*L)):ℝ)=(Fintype.card (Site L):ℝ)*Fintype.card (Site n):= by rw [Fintype.card_congr ((ratioN L n).splitSites), Fintype.card_prod,Nat.cast_mul,mul_comm]
            rw [hz,show C*_=(Fintype.card (Site n):ℝ)⁻¹ from ?_]; rfl
            have hc:(Fintype.card (Site L):ℝ)≠0:=by positivity
            unfold C; field_simp
        exact ⟨hx ▸ J'.smul _, H'.smul _, hx ▸ H.μ _,stroller g h.strollT⟩
end YM.WilsonCoeffUV.Winding

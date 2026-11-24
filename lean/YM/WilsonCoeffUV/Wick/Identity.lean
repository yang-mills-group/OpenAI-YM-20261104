import YM.WilsonCoeffUV.Wick.Lift
import YM.WilsonCoeffUV.Root.Gain.Deterministic
/-!
# From exponential horizontal ledgers to periodized-HARMONIC-free approximations

Leading projection proof will compute unchanged history on ordinary periods.
To identify the Wick limit, replace the actual positive-history propagating
series' order ZERO by margins with EXACT linear zero gradients also on constants.
General actual finite tori don't have the latter, so may not test with bare-G
on logs there. No claim that off-marks at higher orders separately transverse. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Carp
open Set Function Filter Lattice RG Laurent Exterior Bloch Metric Next.Free Precision Tree Soil
open Matrix FreeResolvent Blue Power Work.F08
open scoped Topology ContDiff BigOperators ComplexConjugate Classical
variable {U V P:Type*}{G:Gauge}{j k m N:ℕ}{n:Side} {s t A B C:ℝ} {w:Cover}
section
variable [NormedAddCommGroup V]
lemma reef (o:Cover)(x:dock Cover P j): tread (tor n) (wrap n o) (slideC n x)≤tread Bank.terrain o x := by
    have he y z: (tor n).gap (wrap n y) (wrap n z) ≤ Bank.terrain.gap y z := by unfold tor Bank.terrain; dsimp only; rw [← map_sub]; exact wrap_size ..
    have hh : stud (wrap n o) (slideC n x)=(wrap n) ∘ (stud o x):= comps_head o (wrap n)
    unfold tread; rw [hh]; exact league_le (tor n) _ (fun i j=>(he _ _).trans (leg_le Bank.terrain _ i j))
def peglet (F: Ten V (Cloth P) j)(n:Side)(x:dock (Site n) P j) : dock Cover P j→V:= (fun y=> if slideC n y=x then F y else 0)
def plume (F: Ten V (Cloth P) j)(n:Side): Ten V (Co n P) j:= fun x=> ∑' y, peglet F n x y
lemma plume_zero (n:Side): plume (0:Ten V (Cloth P) j) n=0:= funext fun x=> by unfold plume; simp [peglet]
variable [Fintype P]
lemma keg [CompleteSpace V]{F:Ten V (Cloth P) j}(h:Cork Bank.terrain w s A F)(ht:0<s): Summable fun y:dock Cover P j=> ‖F y‖:=by
   by_cases hz:j=0; · subst j; exact summable_of_hasFiniteSupport (Set.toFinite _)
   have hh:0< s/j:= by positivity
   refine (((train_pay (α:=P) hh w j).2.1.mul_left A).of_nonneg_of_le (fun _=> norm_nonneg _) (fun y=>?_))
   apply (h.2 y).trans (mul_le_mul_of_nonneg_left _ h.1)
   simpa only [sub_zero,neg_zero,zero_mul,Real.exp_zero,one_mul] using sail_cut (d:=Bank.terrain) (Nat.zero_le (tread Bank.terrain w y)) le_rfl ht (by omega) w y (fun i=> (show Bank.terrain.gap w (y i).1≤_ from leg_le Bank.terrain (stud w y) 0 i.succ))
lemma clothBound {F:Ten V (Cloth P) j} (h:Cork Bank.terrain w s A F)(he:0<t)(ht:t<s)(Q: dock (Site n) P j): SumBudget (fun y=> ‖peglet F n Q y‖) ((A * Real.exp (-t*tread (tor n) (wrap n w) Q))* tiePay P j (s-t)):=by
   by_cases hz:j=0
   · subst j
     have hh (x:dock Cover P 0):slideC n x=Q:= Subsingleton.elim ..
     simp only [peglet,hh,↓reduceIte,tiePay,pow_zero,mul_one]; refine ⟨fun y=>norm_nonneg _,summable_of_hasFiniteSupport (Set.toFinite _),?_⟩
     rw [tsum_fintype,Fintype.sum_unique]; apply (h.2 _).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) h.1); exact le_trans (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (hh _ ▸ reef w (default:dock Cover P 0))) (by linarith)) (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
   have hu:0<(s-t)/j:=div_pos (sub_pos.mpr ht) (by positivity)
   have hp:=tread (tor n) (wrap n w) Q
   have hv:= h.1
   apply budget_minor (cap_scale (train_pay hu w j) (show 0≤ A*Real.exp (-t*tread (tor n) (wrap n w) Q) by positivity)) (fun _=> norm_nonneg _)
   intro y; unfold peglet; split
   · rename_i hy; rw [←hy,mul_assoc]; exact (h.2 y).trans (mul_le_mul_of_nonneg_left (sail_cut (d:=Bank.terrain) (reef w y) he.le ht (by omega) w y (fun i=>leg_le Bank.terrain (stud w y) 0 i.succ)) hv)
   rw [norm_zero]; exact mul_nonneg (mul_nonneg hv (by positivity)) (sail_nn ..)
lemma caisson [CompleteSpace V]{F:Ten V (Cloth P) j}(h:Cork Bank.terrain w s A F)(ht:0<s) : Bends w (plume F) F:=by
    let u:=s/2; have hu:0<u:=by unfold u; positivity;
    have he:u<s:=by unfold u; linarith
    have hp:=keg h ht
    refine ⟨fun x=>?_,u,_,hu,Eventually.of_forall (fun n=> (show Cork (tor n) (wrap n w) u (A*tiePay P j (s-u)) (plume F n) from ?_))⟩
    swap
    · refine ⟨?_ ,fun y=> (norm_tsum_le_tsum_norm (clothBound h hu he y).2.1).trans ((clothBound h hu he y).2.2.trans_eq (by rw [mul_right_comm]))⟩
      exact mul_nonneg h.1 (by
        by_cases hx : j=0; · simp [hx,tiePay]
        exact pow_nonneg (boardPay_nn (div_pos (sub_pos.mpr he) (by positivity))) _)
    let Q y:= if y=x then F y else 0; have hQ : (∑' y,Q y)=F x:=by rw [tsum_eq_single x (fun i h=>if_neg h)]; simp only [if_true]
    have hx (y): Tendsto (fun n=> peglet F n (slideC n x) y) atTop (𝓝 (Q y)):=by
       refine tendsto_nhds_of_eventually_eq ?_; filter_upwards [slide_end w y,slide_end w x] with n hn hv; have hh : slideC n y=slideC n x ↔ y=x:= ⟨fun t=>by rw [t,hv] at hn; exact hn.symm, congr_arg _⟩
       simp only [peglet,hh]; rfl
    conv_rhs=>rw [← hQ]
    apply tendsto_tsum_of_dominated_convergence hp hx; apply Eventually.of_forall; intro n y; unfold peglet; split; rfl; rw [norm_zero]; exact norm_nonneg _
lemma creased [CompleteSpace V]{F: Ten V (Cloth P) j}(h:Cork Bank.terrain w s A F)(ht:0<s)(n:Side)(x): Summable (peglet F n x) := by exact ((clothBound h (half_pos ht) (half_lt_self ht) x).2.1).of_norm
omit [Fintype P] in
lemma rounding (n:Side)(v:Ten V (Cloth P) j)(p:Blue.Smooth v): Blue.Smooth (plume v n):=by
   intro q x; unfold plume
   conv_rhs=> rw [← Equiv.tsum_eq (q.arrowCongr (Equiv.refl (Cloth P))) (_)]
   apply tsum_congr; intro y
   have he : slideC n y=x ∘ q ↔ slideC n ((q.arrowCongr (Equiv.refl (Cloth P))) y)=x := ⟨fun h=>funext (fun i=> by change slideC n y (q.symm i)=x i; rw [h,Function.comp_apply,q.apply_symm_apply]),fun h=> funext (fun i=> by rw [Function.comp_apply,← h]; change _=foldUnder n (y (q.symm (q i)));rw [q.symm_apply_apply]; rfl)⟩
   simp only [peglet, he]; split; swap; rfl; exact (p q.symm y).symm
end
section real
variable {T:Ten ℝ (YForest G) (j+1)}(p:Cork Bank.terrain 0 s A T)(he:0<s)(h:∀ x i,windsL x i T=0)
include he p
lemma swellH (Y: Fin j→YForest G)(u:Edge Cover)(i:G.ColorIndex) : |T (Fin.cons (stone u i) Y)|≤ A*Real.exp (-s*size u.1):=by
    let y:Fin (j+1)→YForest G:=Fin.cons (stone u i) Y
    have hh: size u.1≤tread Bank.terrain 0 y:= by
       apply le_trans _ (leg_le Bank.terrain (stud 0 y) 0 (Fin.succ 0)); change _≤size (u.1-0); rw [sub_zero]
    exact (p.2 y).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonpos_left (by exact_mod_cast hh) (neg_nonpos.mpr he.le))) p.1)
lemma swayH (Y:Fin j→YForest G)(x i) (f:Cover→ℝ)(hf:broad f): Summable fun y=> f y * T (Fin.cons (stone (y,x) i) Y) := sweat_pay he (fun y=> swellH p he Y (y,x) i) hf
include h
lemma breezeSite (Y:Fin j→YForest G)(i:G.ColorIndex)(f:Cover→ℝ)(hf:broad f): ∑ u:Axis, ∑' y:Cover, nextV u f y * T (Fin.cons (stone (y,u) i) Y) =0:=by
   let F (u:Axis)(y:Cover):=T (Fin.cons (stone (y,u) i) Y)
   have hh u:Summable fun x=>f x * F u x:=swayH p he Y u i _ hf
   have ht u:Summable fun x:Cover=> f (x+step u)*F u x:=swayH p he Y u i _ (hf.around (step u))
   have hm u:Summable fun x=>f x*F u (x-step u):=by
      refine ((Equiv.subRight (step u)).summable_iff.mpr (ht u)).congr ?_; intro i; simp
   let Z (u:Axis)(y:Cover):= f y*(F u (y-step u)- F u y)
   have he u: Summable (Z u):=by simp only [Z,mul_sub]; exact (hm u).sub (hh u)
   have he' (u): (∑' y, Z u y)=∑' y:Cover,nextV u f y * F u y:=by unfold Z nextV; simp_rw [mul_sub,sub_mul]; rw [Summable.tsum_sub (hm u) (hh u),Summable.tsum_sub (ht u) (hh u),← (Equiv.addRight (step u)).tsum_eq (fun x:Cover=>f x*F u (x-step u))]; simp
   change (∑ u, ∑' y,nextV u f y * F u y)=0
   simp_rw [← he']; rw [← Summable.tsum_finsetSum (fun _ _=>he _)]
   trans tsum (fun _ : Cover=> (0:ℝ)); refine tsum_congr fun i'=>?_ ;
   · have hp := congr_fun (h i' i) Y; rw [windsL,Finset.sum_apply] at hp; simp only [Pi.sub_apply,prune, Finset.sum_sub_distrib,Pi.zero_apply] at hp
     unfold Z; rw [← Finset.mul_sum, Finset.sum_sub_distrib,sub_eq_zero.mpr (sub_eq_zero.mp hp).symm,mul_zero]
   rw [tsum_zero]
-- test all directions on FIRST leg and at fixed x other positions, scaled
omit h in
lemma round_bill (f:Co n (Hooks G) → ℝ)(Q:Fin j → Co n (Hooks G)) (hf:∀ Y, ∑' i:YForest G, f (foldUnder n i)*T (Fin.cons i Y)=0):
    ∑ i:Co n (Hooks G),f i*plume T n (Fin.cons i Q)=0:=by
  let Z (i:Co n (Hooks G))(x:dock Cover (Hooks G) (j+1)):= f i*peglet T n (Fin.cons i Q) x
  have ht i: Summable (Z i):= (creased p he n _).mul_left _
  unfold plume; simp_rw [←tsum_mul_left]; change ∑ i, ∑' y,Z i y=0; rw [← Summable.tsum_finsetSum (fun i _=> ht i)]
  let b:= (Equiv.prodComm (dock Cover (Hooks G) j) (Cloth (Hooks G))).trans (Fin.consEquiv (fun _:Fin (j+1)=> Cloth (Hooks G)))
  have hb(x:YForest G)(Y:Fin j→YForest G): (∑ i, Z i (Fin.cons x Y))= if slideC n Y=Q then f (foldUnder n x)*T (Fin.cons x Y) else 0:=by
     have hh i: slideC n (Fin.cons x Y)=Fin.cons i Q ↔ foldUnder n x=i ∧ slideC n Y=Q:=by
        refine ⟨fun z=>?_, fun ⟨e,p⟩=>?_⟩
        · exact ⟨congr_fun z 0,funext fun i=> congr_fun z i.succ⟩
        rw [← e,← p]; unfold slideC; rw [comps_head]
     split
     next H=> rw [Finset.sum_eq_single (foldUnder n x)]; · unfold Z peglet; rw [if_pos ((hh _).mpr ⟨rfl,H⟩)]
              · intro i _ hi; unfold Z peglet; rw [if_neg fun v=>hi ((hh _).mp v).1.symm,mul_zero]
              simp
     next H=> exact Finset.sum_eq_zero (fun i _=>by unfold Z peglet; rw [if_neg fun he=> H ((hh i).mp he).2,mul_zero])
  let W y := ∑ i:Co n (Hooks G),Z i y
  have H: Summable W:= summable_sum (fun i _=> ht i)
  have hx : Summable (W ∘ ⇑b):= b.summable_iff.mpr H
  rw [← b.tsum_eq W]; change tsum (W ∘ ⇑b)=_ ; rw [hx.tsum_prod]; trans tsum (fun _ : Fin j→YForest G=>(0:ℝ)); refine tsum_congr fun Y=>?_ ;
  · change (∑' i:YForest G,∑ a:Co n (Hooks G),Z a (Fin.cons i Y))=0; rw [tsum_congr (fun i=>hb i Y)]; split; exact hf _; exact tsum_zero
  rw [tsum_zero]
end real
section
variable {T:Ten ℝ (YForest G) (j+1)}(p:Cork Bank.terrain 0 s A T)(he:0<s)(h:∀ x i,windsL x i T=0)
include p he
lemma taps (u: Fin j → YForest G) (f: Co n (Hooks G) → ℝ) : Summable (fun i=> f (foldUnder n i)*T (Fin.cons i u)):=by
    have hv: Injective (fun i:YForest G=> (Fin.cons i u:Fin (j+1)→YForest G)):=fun _ _ h=> congr_fun h 0
    let W i:=T (Fin.cons i u); have he': Summable (fun i:YForest G=> ‖W i‖):= by exact ((keg p he).comp_injective (i:=fun i=> (Fin.cons i u:Fin (j+1)→YForest G)) hv)
    let v:= ∑ i:Co n (Hooks G), ‖f i‖; refine Summable.of_norm_bounded (he'.mul_left v) (fun i=>?_)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=fun k=>‖f k‖) (fun _ _=>norm_nonneg _) (Finset.mem_univ _)) (norm_nonneg _)
lemma tapsΩ (u: Fin j→YForest G) (f: Co n (Hooks G) → ℝ):
    ∑' i, f (foldUnder n i)*T (Fin.cons i u)= ∑ v: Hooks G, ∑' i:Cover, f (wrap n i,v)*T (Fin.cons (i,v) u):=by
   let Q:= fun i: YForest G=> f (foldUnder n i)* T (Fin.cons i u)
   let b:= Equiv.prodComm (Hooks G) Cover; have hp: Summable (Q ∘ b):= b.summable_iff.mpr (taps p he u f); rw [← b.tsum_eq Q]; change tsum (Q ∘ b)=_; rw [hp.tsum_prod,tsum_fintype]; rfl
include h
lemma lampStand (u: Fin j → Co n (Hooks G))(t:Hooks G): ∑ i: Site n,plume T n (Fin.cons (i,t) u)=0:=by
   let f (i:Co n (Hooks G)):ℝ:= if i.2=t then 1 else 0
   suffices H : ∀ x, ∑' i, f (foldUnder n i)*T (Fin.cons i x)=0 by simpa [f,Fintype.sum_prod_type,ite_mul] using round_bill p he f u H
   intro x
   rw [tapsΩ p he x f,Finset.sum_eq_single t]
   · simp only [f,if_true,one_mul]
     obtain ⟨a,k⟩:= t; obtain ⟨i,rfl⟩:=axisEquiv.surjective a
     have H:= breezeSite p he h x k (chalk i) (broad.chalk _)
     unfold nextV at H; simp_rw [chalk_inc, add_sub_cancel_left, ite_mul] at H
     rw [Finset.sum_eq_single i] at H; simpa [stone] using H
     · intro j hj hp; simp [hp]
     simp
   · intro j _ hp; simp [f,hp]
   simp
lemma lampStop (u: Fin j → Co n (Hooks G))(a:Slot G n 0): ∑ i: Woods G n, tensor G (d 0 n) i a * plume T n (Fin.cons i u)=0:=by
   obtain ⟨v,j,c⟩:=a; rw [vac_only j]
   apply round_bill p he
   intro x; set f:Cover→ℝ:= fun z=> if wrap n z=v then 1 else 0
   have hF y i: tensor G (d 0 n) (wrap n y,coord i,c) (v, Exterior.vac,c)= nextV i f y:=by
       unfold tensor; simp only [Matrix.of_apply]
       have ht:=d_sites (wrap n y) i (Pi.single (v, Exterior.vac) 1)
       unfold nextV
       simpa [f,Pi.single_apply] using ht
   have hf:broad f:= by
      refine ⟨0,1,zero_le_one,fun x=>?_ ⟩
      unfold f; split <;> simp
   rw [tapsΩ p he x (fun i=>tensor G (d 0 n) i (v,Exterior.vac,c))]; rw [Fintype.sum_prod_type,Finset.sum_comm,Finset.sum_eq_single c]
   · rw [← Equiv.sum_comp axisEquiv]; simp_rw [coord_map, hF]; exact breezeSite p he h x c f hf
   · intro j _ hj; simp [tensor,hj]
   simp
end
lemma curtainT (P:Gen ℝ (YForest G))(h:Pure P)(u:FiniteGen P)(p:∀ r,∃ s A,0<s ∧ Cork Bank.terrain 0 s A (P r))(v:∀ r x i,windsL x i (P (r+1))=0)(n:Side): NullTop (fun r=>plume (P r) n) :=by
   choose s a he hp using p; exact ⟨fun i=> rounding n _ (h i),⟨u.choose,fun i hi=>by change plume (P i) n= _; rw [u.choose_spec _ hi]; exact plume_zero _⟩, fun i Y a=> lampStop (hp _) (he _) (v _) Y a, fun i Y a=> lampStand (hp _) (he _) (v _) Y a⟩
end YM.WilsonCoeffUV.Bank.Carp

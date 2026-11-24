import YM.FVA2.O.Ward.Quad
/-! Odd generator ∆ and loop signs in the BV square. Using Heat.GroupX grouping. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Ward
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat
variable {R A P : Type} [AddCommGroup P] [CommRing R][Fintype A]{p:Sector A}
variable {K L:Flux A P R}{F H:Row A P R}{l r:Legs (Mode A P)}
lemma traceTier (hp:closed K p true)(hL:closed L p true)(h: Reverse K p)(w:Legs (Mode A P))(q:P)(hf:Symm (field p) F)(hh:Symm (field p) H)(hx:Pure (field p) false F) : trc L q (tree p K F H) w= - tree p K (trc L q F) H w + -(tree p K F (trc L q H) w) + pairedX p K L F H w q:= by
   unfold tree; simp_rw [at_trc,scatter_cons]
   let T:=allocate (field p) w (R:=R)
   let f a e l r:= attaches p K F H ((a,q)::(e,-q)::l) r+cross (p a) (degree (field p) ((e,-q)::l))*attaches p K F H ((e,-q)::l) ((a,q)::r)+ cross (p e) (degree (field p) l)*(attaches p K F H ((a,q)::l) ((e,-q)::r) + cross (p a) (degree (field p) l)*attaches p K F H l ((a,q)::(e,-q)::r))
   let B : Shared (Mode A P) R:= fun l r=>∑ a,∑ e,∑ i,∑ j,(hits p K L F H l r a e i j q+restL p K L F H l r a e i j q);
   change (∑ a,∑ e,L a e q • (T (f a e)))= - T _ + -T _ + T B;
   simp_rw [← map_smul,← map_sum, ← map_neg, ← map_add]; apply LinearMap.congr_arg; ext l r
   simp only [Finset.sum_apply,Pi.smul_apply,Pi.add_apply,Pi.neg_apply,f,B,smul_eq_mul, convertR h]; simp_rw [Finset.mul_sum,mul_add,Finset.sum_add_distrib]
   let A0 a e i j l r:= radius p K i j (L a e q • diffPair (a,q) (e,-q) F) H l r; let Ac a e i j l r := radius p K i j F (L a e q • diffPair (a,q) (e,-q) H) l r;
   have h1 j₁ j₂ (F H:Row A P R): radius p K j₁ j₂ (trc L q F) H l r=∑ a,∑ e,radius p K j₁ j₂ (L a e q • diffPair (a,q) (e,-q) F) H l r:=by
     simp_rw [trc, LinearMap.sum_apply, LinearMap.smul_apply, show ∀ i:Row A P R,radius p K j₁ j₂ i H l r=(rMap p K _ _ l r).flip H i from fun _=>rfl,map_sum] -- replace
   have h2 i j : radius p K i j F (trc L q H) l r =∑ a,∑ e,radius p K i j F (L a e q • diffPair (a,q) (e,-q) H) l r:= by
     simp only [trc,LinearMap.sum_apply,LinearMap.smul_apply]; simp_rw [show ∀ H: Row A P R,radius p K i j F H l r=rMap p K i j l r F H from fun _=>rfl,map_sum]
   unfold hits restL; simp_rw [Finset.mul_sum, Ward.left hp hL _ _ _ _ _ hf, Ward.right hp hL _ _ _ _ _ hh hx, h1,h2]; 
   conv_rhs => lhs; lhs; rw [summ_sum]
   conv_rhs => lhs; rhs; rw [summ_sum]
   simp_rw [Finset.sum_neg_distrib]; abel
variable [MeasurableSpace P]
-- specialization equal odd line to avoid anti-hits two different lines
lemma residue {K:Flux A P ℂ}{F H:Row A P ℂ}(hp:closed K p true)(hr: Reverse K p)
    (hf:Symm (field p) F)(hh:Symm (field p) H)(μ:Measure P)(h:Heat.Route K K p F H μ)(w:Legs (Mode A P)):
    (∫ q, pairedX p K K F H w q ∂μ)=0:= by
   rw [(hits_base μ h hr w).2]; change allocate _ w _ = _
   have he (l r:Legs (Mode A P)):
       (∑ i,∑ j,∑ k,∑ t,∫ q,hits p K K F H l r i j k t q ∂μ)=0:= by
      let x:= fun i j k t=> ∫ q,hits p K K F H l r i j k t q ∂μ
      have hz i j k t: x i j k t = - x k t i j := by
         change (∫ _, _ ∂μ)= -(∫ _, _ ∂μ); calc
          _ = ∫ q, - hits p K K F H l r k t i j (-net l - q) ∂μ := integral_congr_ae (Eventually.of_forall (fun q=> dance hp hp q i j k t hf hh))
          _ = _ := by rw [integral_neg,h.shift]
      change (∑ i,∑ j,∑ k,∑ t,x i j k t)=0; apply two_nsmul_eq_zero.mp; rw [two_nsmul]; apply eq_neg_iff_add_eq_zero.mp
      calc (∑ i,∑ j,∑ k,∑ t,x i j k t) = ∑ i,∑ j,∑ k,∑ t,- x k t i j := by exact sum_congr rfl fun i _=> sum_congr rfl fun j _=> sum_congr rfl fun k _=> sum_congr rfl fun t _=> hz i j k t
           _= _:= by simp_rw [ Finset.sum_neg_distrib ]; rw [summ_sum]
   simp_rw [he,mul_zero, ← show (0:Shared (Mode A P) ℂ)=(fun _ _=>0) from rfl, map_zero]
lemma bounce {K:Flux A P ℂ}{F H:Row A P ℂ}(hp:closed K p true)(hr: Reverse K p)
    (hf:Symm (field p) F)(hh:Symm (field p) H)(he:Pure (field p) false F)(μ:Measure P)
    (hx:Pass K F μ)(hy:Pass K H μ)(h:Heat.Route K K p F H μ):
    Ccy K (tree p K F H) μ + tree p K (Ccy K F μ) H + tree p K F (Ccy K H μ) = 0 := by
   ext w; obtain ⟨hf',ha⟩:= cycle_map μ (fun z=>tree p K z H) (sense_atLeft ..) w hx
   obtain ⟨hh',hb⟩:= cycle_map μ (tree p K F) (sense_atRight ..) w hy
   have ht:= (hits_base μ h hr w).1
   simp only [Pi.add_apply, Pi.zero_apply]
   rw [ha,hb]; unfold Ccy; simp_rw [traceTier hp hp hr _ _ hf hh he]; have h2:=integral_add (hf'.neg.add hh'.neg) ht; have h3:= integral_add hf'.neg hh'.neg; simp only [Pi.neg_apply,Pi.add_apply] at h2 h3
   rw [h2,h3, integral_neg, integral_neg, residue hp hr hf hh μ h]; abel
lemma t_bounce {K:Flux A P ℂ}{F H:Row A P ℂ}(hp:closed K p true)(hr: Reverse K p)
    (hf:Symm (field p) F)(hh:Symm (field p) H)(he:Pure (field p) false F)(μ:Measure P)
    (hx:Pass K F μ)(hy:Pass K H μ)(h:Heat.Route K K p F H μ): Pass K (tree p K F H) μ:= by
    intro w; simp_rw [traceTier hp hp hr _ _ hf hh he]; exact ((((cycle_map μ (fun z=>tree p K z H) (sense_atLeft ..) w hx).1).neg.add ((cycle_map μ (tree p K F) (sense_atRight ..) w hy).1).neg).add (hits_base μ h hr w).1)
-- ∆ alone
omit [MeasurableSpace P] in
lemma zeroPair {K:Flux A P ℂ}{F:Row A P ℂ}(hp:closed K p true)(hf:Symm (field p) F)(q u:P):
   trc K q (trc K u F) = -(trc K u (trc K q F)) := by
   classical
   have hu (v:P): slab K {v}=trc K v:= by simp [slab]
   have he:= loop_loop (hp.balanced {q}) (hp.balanced {u}) hf; simp_rw [← is_loop,hu] at he; simpa only [cross_true,neg_smul,one_smul] using he
lemma zeroCcy {K:Flux A P ℂ}{F:Row A P ℂ}(hp:closed K p true)(hf:Symm (field p) F)(μ:Measure P) [SigmaFinite μ] (hx: Pass K F μ)
    (hh: ∀ l, Integrable (fun x:P×P=>trc K x.1 (trc K x.2 F) l) (μ.prod μ)):
    Ccy K (Ccy K F μ) μ=0:= by
   ext w; have hb (u:P) := (cycle_map μ _ (sense_trc K u) w hx).2
   change (∫ t, _ ∂μ)=(0:ℂ); simp_rw [hb]; apply two_nsmul_eq_zero.mp; rw [two_nsmul]; apply eq_neg_iff_add_eq_zero.mp
   calc
    _ = ∫ x:P,∫ y:P,-trc K y (trc K x F) w ∂μ ∂μ := integral_congr_ae (Eventually.of_forall (fun x=>integral_congr_ae (Eventually.of_forall (fun y=> congr_fun (zeroPair hp hf x y) w ))))
    _ = _:= by simp_rw [ integral_neg ]; rw [← integral_integral_swap (hh w)]
end YM.FVA2.O.Ward

import YM.WilsonCoeffUV.Winding.Log
/-! # Log kernel transmission: Q step. -/
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Wheel Wheel.Mark Cosmos Mer Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent AnalyticNext.QuarticMatch.Sheets PowerSeries
open scoped Topology BigOperators
variable {n L:Side}{ι U X α β V:Type}{G:Gauge}{D k:ι→ℕ}{i i' j k' r e a l v:ℕ}{s A B C W t q :ℝ}
variable {J Z S X':Finset ι}{p:ι→Cover}{x:ι}[DecidableEq ι]
section
variable {P:(I:Arch G)→ (p:PackOne Z D k e I)→ Gen (Pen D X') (Co p.V.n I.dial)}{F:(I:Arch G) → PackOne Z D k e I→ Gen (Pen D X') (Cloth I.dial)}{Q: (I:Arch G) → (p:PackOne Z D k e I)→ Gen (Pen D (J\X')) (Co p.V.n I.dial)}{T: (I:Arch G)→PackOne Z D k e I→ Gen (Pen D (J\X')) (Cloth I.dial)}
lemma Bursted.claw (h:Bursted (F:=Arch.dial) (fun i p=>P i p (r+1)) (fun i p=>F i p (r+1)) X')(u:Bursted (F:=Arch.dial) (fun i p=>Q i p (l+1)) (fun i p=> T i p (l+1)) (J\X'))(v:X'⊆ J)(x:J.Nonempty)(hx:r+l=a): Bursted (F:=Arch.dial) (fun I p=>refuge (swivel (lakeL p.N v (P I p) (Q I p) a r l))) (fun I p=> ruins (swivel (lakeL p.M v (F I p) (T I p) a r l))) J:=by
   subst a; obtain ⟨d,H⟩:=h; obtain ⟨c,L⟩:= u; refine ⟨d+c,fun I=>?_⟩; obtain ⟨s,A,b,w,H⟩:=H I; obtain ⟨t,B,g,f,L⟩:=L I; let z:= min I.s (min s t); have hx:0<z:= lt_min I.h (lt_min b g); let u:=priceM I.dial 2 z; have hu:0≤u:=priceMP _ _ hx; have hv:=zero_le_one.trans I.book; have hp:z≤ min s t:= min_le_right ..; refine ⟨z/32,u*(sealM r l*3*I.mass*A*B),by positivity,by unfold sealM; positivity,fun q=>?_⟩; apply ((MarkC.cluster (v:=hx.le) (F:=F I q) (Q:=P I q) (Y:=T I q) (Z:=Q I q) (q.V.rateRamp.mono (min_le_left ..)) v ((H q).mono (hp.trans (min_le_left ..))) ((L q).mono (hp.trans (min_le_right ..)))).swings.camp x hx).more; unfold u; rw [pow_add]; conv_rhs=> rw [← Finset.card_sdiff_add_card_eq_card v];
   rw [pow_add]; exact le_of_eq (by ring)
end
lemma Bursted.clutch (b:X'⊆ J)(x:J.Nonempty)(h:∀ i≤a,∀ j≤ e,∀ r, Bursted (F:=Arch.dial) (fun (I: Arch G)(p:PackOne Z D k i' I)=>p.surfU X' i j r) (fun _ p=>p.surfC X' i j r) X')(g:∀ i ≤ a,∀ j≤ e,∀ r,Bursted (F:=Arch.dial) (fun (I:Arch G)(p:PackOne Z D k i' I)=>p.surfU (J\X') i j r) (fun _ p=>p.surfC (J\X') i j r) (J\X')): Bursted (F:=Arch.dial) (fun (I:Arch G)(p:PackOne Z D k i' I)=>sewsV p.N b (p.surfU X') (p.surfU (J\X')) a e r) (fun _ p=> Sewing p.M b (p.surfC X') (p.surfC (J\X')) a e r) J:=by
   unfold sewsV Sewing overture; simp_rw [Finset.sum_apply,←lakeReads]; apply Bursted.sum; intro i v; have he:=Finset.mem_antidiagonal.mp v; apply Bursted.sum; intro j z; have hu:=Finset.mem_antidiagonal.mp z; apply Bursted.sum; intro r v; exact (h i.1 (by omega) j.1 (by omega) (r.1+1)).claw (P:=fun _ p=>p.surfU X' i.1 j.1) (F:=fun _ p=>p.surfC X' i.1 j.1) (Q:=fun _ p=>p.surfU (J\X') i.2 j.2) (T:=fun _ p=>p.surfC (J\X') i.2 j.2) (g i.2 (by omega) j.2 (by omega) (r.2+1)) b x (Finset.mem_antidiagonal.mp v)
theorem woundStep (j i e r:ℕ)(h:i≤e)(J Z:Finset ι)(p:J⊆ Z): Bursted (F:=Arch.dial) (fun (I:Arch G)(p:PackOne Z D k e I)=>p.surfU J j i r) (fun _ p=>p.surfC J j i r) J:=by
   induction j using Nat.strong_induction_on generalizing i J r with
   | h j ih=>
       by_cases z:J=∅; · subst J; simp_rw [PackOne.zen,PackOne.zen']; exact Bursted.zero
       have hx:J.Nonempty:= Finset.nonempty_iff_ne_empty.mpr z; cases j with
       | zero=> exact Bursted.hatch G i r e h p hx
       | succ j=>
           have he i' (p:i' ≤ i) a (b:a≤ j) (K:Finset ι)(v:K⊆ Z)(r:ℕ):= ih a (by omega) i' r (p.trans h) K v
           let Q x p' y w r:= he y w x p' J p r
           have ht:= Bursted.stream (r:=r) Q h hx (M:=fun I v=> v.N) (T:=fun I v=> v.M) (fun I v=>v.V.rateRamp)
           have hp:= Bursted.stream (r:=r) Q h hx (M:=fun I v=>v.N.transpose) (T:=fun I v=>v.M.transpose) (fun I v=> v.V.rateRamp.spin)
           have hR:= (he i le_rfl j le_rfl J p (r+2)).soak (P:=fun _ p=>p.surfU J j i) (Q:=fun _ p=>p.surfC J j i) hx
           simp_rw [PackOne.more,PackOne.highest, Pi.smul_apply, Sat, SubC,Pi.add_apply,Finset.sum_apply]; apply Bursted.μ (a:=_); refine Bursted.plus ((hR.plus ht).plus hp) ?_
           apply Bursted.sum; intro K v; have hh:= Finset.mem_powerset.mp v; simp_rw [dif_pos hh]; exact Bursted.clutch hh hx (fun a x i z r=>he i z a x K (hh.trans p) r) (fun a x i z r=> he i z a x _ (Finset.sdiff_subset.trans p) r)

omit [DecidableEq ι] in
lemma MarkU.scoopT [NormedAddCommGroup V] {P:Ten V (Co n (α⊕β)) r}{F:Ten V (Cloth (α⊕β)) r}(h:MarkU p J P F s A): MarkU p J (scoop P) (scoop F) s A:= ⟨⟨h.access.1,fun x=>h.access.2 (pierR ∘ x)⟩,⟨h.bill.1,fun x=>h.bill.2 (pierR ∘ x)⟩, ⟨h.bill.1,fun x v=> h.gulf.local_w (pierR ∘ x) v⟩⟩
namespace PackOne
variable {I:Arch G}(p:PackOne Z D k e I)
abbrev sLane (J: Finset ι):= inHeat p.V.wheel p.V.shadow p.V.H (p.V.T p.V.n) I.R p.V.W' p.K J
abbrev primeJ (J: Finset ι)(i):=fade plug (finalZ (p.sLane J) (mass k J) i)
abbrev cabinJ (J: Finset ι)(i):=sluice (finalZ (p.surfC J) (mass k J) i)
lemma sealP : p.primeJ J i= sluice (∑ j∈ Finset.range (1+ mass k J+3*i), p.surfU J j i):=by unfold primeJ finalZ; rw [into_shade (ratioN I.P.L p.V.n), bend_sum]
end PackOne
lemma woundOptic (i e r:ℕ)(h:i≤e)(J Z: Finset ι)(p:J⊆ Z): Bursted (F:=fun _=>Hooks G) (fun (I:Arch G) (p:PackOne Z D k e I)=> p.primeJ J i r) (fun _ p=> p.cabinJ J i r) J:=by
   obtain ⟨d,H⟩:= Bursted.sum (Finset.range (1+mass k J+3*i)) (fun j _=> woundStep (G:=G) (D:=D) (k:=k) j i e r h J Z p)
   refine ⟨d,fun I=>?_⟩; obtain ⟨s,A,b,w,H⟩:= H I; refine ⟨s,A,b,w,fun p=>?_⟩; dsimp only; rw [p.sealP]; unfold PackOne.cabinJ; simp_rw [sluice, finalZ,Finset.sum_apply]; exact (H p).scoopT
-- reset D paid as external budget parameter, arbitrary. Already cost on both higher steps.
def rimJ (P:Cost)(i r:ℕ):ℝ:= ∑ j∈ Finset.range (i+1), ‖PowerSeries.coeff (i-j) (P^j*(P⁻¹)^r)‖
lemma cureOptic (e i r:ℕ)(h:i≤ e)(J Z: Finset ι)(v:J⊆ Z): ∃ d:ℕ,∀ I: Arch G,∃ A s:ℝ,0≤A∧0<s∧∀ p:PackOne Z D k e I, ∀ j≤ i, MarkU p.w J (p.primeJ J j r) (p.cabinJ J j r) s (A*p.V.coin^d*p.A^J.card):=by
    induction i with
    | zero=> obtain ⟨d,H⟩:=woundOptic (G:=G) (D:=D) (k:=k) 0 e r h J Z v; refine ⟨d,fun I=>?_⟩; obtain ⟨s,A,b,w,H⟩:=H I; exact ⟨A,s,w,b,fun p j i=> Nat.eq_zero_of_le_zero i ▸ H p⟩
    | succ i ih=>
       obtain ⟨d,H⟩:=ih (by omega); obtain ⟨c,V⟩:= woundOptic (G:=G) (D:=D) (k:=k) (i+1) e r h J Z v; refine ⟨d+c,fun I=>?_⟩; obtain ⟨A,s,b,x,H⟩:= H I; obtain ⟨t,B,y,u,V⟩:= V I; refine ⟨A+B,min s t,add_nonneg b u,lt_min x y,fun p j g=> ?_⟩; have ht:=p.V.paid; have he:=p.lih
       by_cases w:j ≤ i
       · apply ((H p j w).mono (min_le_left ..)).more; gcongr <;> first|omega | linarith
       have h:j=i+1:= by omega
       subst j; apply ((V p).mono (min_le_right s t)).more; gcongr <;> first|omega|linarith
theorem qLocal_mark (e i r:ℕ)(h:i≤e)(J Z:Finset ι)(v:J⊆ Z): ∃ d:ℕ,∀ I:Arch G,∃ A s:ℝ,0≤ A ∧ 0<s ∧∀ (p:PackOne Z D k e I)(B:Cost),
     MarkU p.w J (mist p.V.wheel p.V.shadow p.V.H (p.V.T p.V.n) I.R p.V.W' p.K B k J i r) (Blue.mix B (p.cabinJ J) i r) s (A* p.V.coin^d * p.A^J.card*rimJ B i r) :=by
   obtain ⟨d,H⟩:= cureOptic (G:=G) (D:=D) (k:=k) e i r h J Z v
   refine ⟨d,fun I=>?_⟩; obtain ⟨A,s,b,u,H⟩:= H I; refine ⟨A,s,b,u,fun P B=>?_⟩; change MarkU _ J (Blue.mix B (P.primeJ J) i r) (Blue.mix B _ i r) s _; rw [Blue.mix,Blue.mix,rimJ, mul_comm,Finset.sum_mul]; exact MarkU.sum (fun j p=> (H P _ (by have hp:j < i+1:= Finset.mem_range.mp p; omega)).μ _)
end YM.WilsonCoeffUV.Winding

import YM.OPE.Compatible.Channel.Currency
/-!
# Flight image to finite arrays. Cover version exact.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Set Lattice Laurent MeasureTheory RG Finset Next.Free Bloch Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier Work.F08 Matrix
open scoped Topology BigOperators Classical
variable {r n:ℕ} {I J T:Type*}[Fintype T][Fintype I] {L c f:Side} {g:Ratio c f}{A:Cross g.count T I}{η U:ℝ}
omit [Fintype T] in
private lemma allTape {f:Fin r→Cover×T→ℝ}(h:∀ i,Summable (f i)): HasSum (fun p:Page T r=> ∏ i,f i (p i)) (∏ i,∑' j,f i j):=by
   induction r with
   | zero=>
      letI:Unique (Page T 0):=inferInstance; letI:Fintype (Page T 0):= Fintype.ofFinite _
      convert! hasSum_fintype (fun p:Page T 0=> ∏ i,f i (p i)) using 1; simp
   | succ r ih=>
      let V(i:Page T r):= ∏ j,f j.succ (i j); let F(i:Page T (r+1)):= ∏ j,f j (i j)
      have hx:= ih (f:=fun i=> f i.succ) (fun i=> h _); let e:(Cover × T)× Page T r≃Page T (r+1):=Fin.consEquiv (fun _ : Fin (r+1) => (Cover × T))
      let c (i:(Cover × T)× Page T r):= f 0 i.1*V i.2; have hv : F ∘ e=c:= by ext1 i; unfold F c; rw [Function.comp_apply, Fin.prod_univ_succ]; simp [e, V]
      have he:Summable c:= ((h 0).norm.mul_norm hx.summable.norm).of_norm
      have hf: HasSum (F ∘ e) ((∑' i,f 0 i)*(∏ j:Fin r, ∑' i, f j.succ i)):=by rw [hv,← hx.tsum_eq,(h 0).tsum_mul_tsum hx.summable he]; exact he.hasSum
      rw [Fin.prod_univ_succ]; exact e.hasSum_iff.mp hf
namespace Script
open Page
private lemma origin_coord (g:Ratio c f)(i:Site c)(x:Cover): g.parent (g.embed i+wrap f x)=i+wrap c (cellar g.count x) ∧ g.residue (g.embed i+wrap f x)=wrap g.count x:= by
   constructor
   · rw [moves_parent,g.embed_parent,show g.residue (g.embed i)=0 from g.residue_embed i]; rfl
   rw [moves_residue,show g.residue (g.embed i)=0 from g.residue_embed i]; simp [arrives]
omit [Fintype T]
lemma sample_action (H:Whole A)(p:Cover×T) (w:deck I c) (x:Site c):
    HasSum (fun i:Cover×I=> linePay A p i * w (x+wrap c i.1,i.2)) ((installed g A *ᵥ w) (g.embed x+wrap f p.1,p.2)):=by
     let z0:= cellar g.count p.1; let d:= p.2
     have he (i:I): Summable fun y:Cover=>linePay A p (y,i):= by
        obtain ⟨η,U,h,hV⟩:=H; have ht:= one_price hV h p i 0; exact Sack.water ht (fun j:Cover=> poise_one 0 (j-z0))
     let f0 (y:Cover)(i:I):= linePay A p (y,i)*w (x+wrap c y,i)
     have hu i: Summable fun y=>f0 y i:= ((he i).norm.mul_right ‖w‖).of_norm_bounded (fun y=> by unfold f0; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm w _) (norm_nonneg _))
     have hh : Summable (uncurry f0):= by
         apply Summable.of_norm; let g (i:I×Cover):= ‖f0 i.2 i.1‖; have hs:Summable g:= (summable_prod_of_nonneg (f:=g) fun i=>norm_nonneg _).2 ⟨fun i=> (hu i).norm,(hasSum_fintype _).summable⟩; exact hs.prod_symm
     change HasSum (Function.uncurry f0) _
     refine hh.hasSum_iff.mpr ?_; symm
     rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,sum_comm,hh.tsum_prod]
     have hp:=origin_coord g x p.1
     rw [show (∑' i: Cover, ∑' j:I,uncurry f0 (i,j)) = ∑' j:I, ∑' i:Cover, f0 i j from hh.tsum_comm.symm, tsum_fintype]
     refine sum_congr rfl fun i _=> ?_
     simp_rw [installed_sift,hp.1,hp.2]; have ht := H.safe (wrap g.count p.1,d) i
     rw [sift_action ht.of_norm, ← (Equiv.addLeft z0).tsum_eq (fun y=> f0 y i)]; refine tsum_congr fun y=>?_ ; change A _ _ y * w _=A _ _ ((z0+y)-_) * w (x+wrap c (z0+y),i); rw [add_sub_cancel_left,map_add]; simp [add_assoc,z0,d]
lemma capstone (p:Page T r)(y:Cover)(H:Whole A)(w: Fin r→deck I c)(x:Site c):
    scribe x (call A y p) w = render (g.embed x+wrap f y) p (fun i=> installed g A *ᵥ w i):=by
       unfold scribe; simp only [call,render,← prod_mul_distrib]; let q:= slide y p
       let U i(s:Cover×I):= linePay A (q i) s*w i (x+wrap c s.1,s.2)
       have hh(i:Fin r):= sample_action H (q i) (w i) x
       have hs(i:Fin r): HasSum (U i) _:= hh i
       calc
          _ = (∏ i,∑' j:Cover×I,U i j):= (allTape (fun i=> (hs i).summable)).tsum_eq
          _ = _:= Finset.prod_congr rfl (fun i _=>by rw [(hs i).tsum_eq]; unfold q Page.slide; simp [add_assoc])
end Script
end YM.OPE.Flume

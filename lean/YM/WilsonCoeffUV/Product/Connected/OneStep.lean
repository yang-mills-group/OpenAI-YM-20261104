import YM.WilsonCoeffUV.Product.Connected.PriceDomains
/-!
# One-step polynomial cost across overlaps
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
variable {u:ℕ}{p:ProfileW}
section
variable [Fintype β]
lemma ribbonRent (Q:Fin i → ropes Cover α β)(P:Ten ℝ (Cloth α) i) (v:0<s)(hp:AngleSea p)(K:Fin i→ℝ)(t:∀ i,dragCup Bank.terrain s (K i) (Q i))(h:Rent p u P A): RentX p u (ribbon Q P) ((∏ i,K i*tender β s u)*A):=by
   let C i:= K i*tender β s u; let T:= ∏ i,C i; have hc i:0≤ C i:= mul_nonneg (t i).1 (tender_nn v β u); have ht:0≤ T:= Finset.prod_nonneg fun i _=> hc i
   have hv x: SumBudget (fun y=> quoteT p u y*‖ribbon Q P y x‖) (T*(quoteT p u x *‖P x‖)):=by
       let f i (y:Cloth β):= autumn 1 u (Bank.terrain.gap (x i).1 y.1)*‖Q i (x i) y‖; have he i: SumBudget (f i) (C i):= tender_finance _ v (t i).1 ((t i).2 _) zero_le_one le_rfl u
       have hu:= cap_scale (each_finance he) (mul_nonneg (zero_le_one.trans (quoteT_pos x p u)) (norm_nonneg (P x)))
       rw [mul_comm]; refine budget_minor hu (fun i=>mul_nonneg (zero_le_one.trans (quoteT_pos i ..)) (norm_nonneg _)) (fun i=>?_); exact (mul_le_mul_of_nonneg_right (quote_walk _ hp) (norm_nonneg (ribbon Q P i x))).trans_eq (by change _= (quoteT _ _ _* ‖P x‖)*∏ j,f j (i j); unfold ribbon f; rw [norm_smul,norm_prod,Finset.prod_mul_distrib]; ring)
   exact finance_flip (finance_glob hv (cap_scale h ht))
end
private def cass (_T: Type*)(k:ℕ): (dock Cover α k × dock Cover α 2)≃ dock Cover α (k+2) where
    toFun x:= Fin.cons (x.2 1) (Fin.cons (x.2 0) x.1)
    invFun x:= (Fin.tail (Fin.tail x),![Fin.tail x 0,x 0])
    left_inv := fun ⟨x,y⟩=> Prod.ext (by simp) (funext fun i=>by fin_cases i<;> simp)
    right_inv x:=by simp
lemma rimeX (G:ropes Cover α α)(P:Gen ℝ (Cloth α))(hs:0<s)(v:dragCup Bank.terrain s B G)(h:Rent p u (P (r+2)) A): RentX p u (rain G P r) (B*fareV r*A):=by
    let T:=cass (α:=α) Unit r; have hp x: Ridge p x.1 ≤ Ridge p (T x):= Ridge.cap (fun i=> Ridge.host p (T x) (Fin.succ (Fin.succ i)))
    have he:0≤ B*fareV r:=mul_nonneg v.1 (by unfold fareV; positivity)
    have hb:= cap_scale (Award.pivot (P:=P (r+2) ∘ T) h T rfl rfl) he
    refine budget_minor hb (fun i=>mul_nonneg (zero_le_one.trans (quoteT_pos i.1 ..)) (norm_nonneg _)) (fun i=>?_);
    rw [mul_left_comm (B*_)]; apply mul_le_mul (autumn_mono zero_le_one _ (hp i)) _ (norm_nonneg _) (zero_le_one.trans (quoteT_pos _ p u)); dsimp only; rw [rain_spell,norm_smul]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); simp_rw [norm_mul]; simp only [norm_div,norm_one,Real.norm_eq_abs,abs_of_nonneg (show 0≤(2:ℝ) by positivity),abs_of_nonneg (show 0≤ ((r+1:ℕ):ℝ) by positivity),abs_of_nonneg (show 0≤((r+2:ℕ):ℝ) by positivity)]
    have H (i j:Cloth α): |G i j|≤B:= Shard.herb_pt v hs.le i j
    refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (H _ _) (by norm_num :0≤(1/2:ℝ))) (by positivity)) (by positivity)) ?_; exact le_of_eq (by unfold fareV; ring)
def hewer (x:dock Cover α (i+j)) (y:dock Cover α 2) : dock Cover α (i+1):= Fin.cons (y 0) (x ∘ Fin.castAdd j)
def stepping (x:dock Cover α (i+j))(y:dock Cover α 2): dock Cover α (j+1):= Fin.cons (y 1) (x ∘ Fin.natAdd i)
def droplet (i j:ℕ)(α:Type*): ((dock Cover α (i+j)) × (dock Cover α 2)) ≃ ((dock Cover α (j+1)) × (dock Cover α (i+1))) where
   toFun x:= (stepping x.1 x.2,hewer x.1 x.2)
   invFun x:= (Fin.append (Fin.tail x.2) (Fin.tail x.1),![x.2 0,x.1 0])
   left_inv:= fun ⟨x,y⟩=> Prod.ext (funext (fun u=> Fin.addCases (fun _=>by simp [hewer,stepping]) (fun _=>by simp [hewer,stepping]) u)) (funext fun i=>by fin_cases i <;>simp [hewer,stepping])
   right_inv:= fun ⟨x,y⟩=>by
      dsimp [hewer,stepping]; congr <;>ext1 x <;>refine Fin.cases (by simp) (fun i=>by simp [Fin.tail]) x
lemma lip_up (x:dock Cover α (i+j))(y:dock Cover α 2)(w: AngleSea p):
    let a:=hewer x y; let b:=stepping x y; Ridge p x ≤ soar Bank.terrain a+Bank.terrain.gap (y 0).1 (y 1).1+Ridge p b:=by
      intro a b; refine Ridge.cap (fun l=> Fin.addCases (fun u=>?_) (fun u=>?_) l)
      · let x':=(a u.succ).1; apply (w x' (b 0).1).trans; rw [add_comm (p _) _]; apply add_le_add _ (Ridge.host p b 0); apply (Bank.terrain.tri _ (a 0).1 x').trans; rw [add_comm, Bank.terrain.swap (b 0).1]; exact Nat.add_le_add_right (leg_le Bank.terrain (Prod.fst ∘ a) 0 u.succ) _
      exact (Ridge.host p b (Fin.succ u)).trans (Nat.le_add_left ..)
lemma rill_norm (G:ropes Cover α α)(P Q: Gen ℝ (Cloth α))(x:dock Cover α (i+j))(y:dock Cover α 2):‖rill G P Q (i+j) i j x y‖=pegPrice i j*‖G (y 0) (y 1)‖*‖P (i+1) (hewer x y)‖ * ‖Q (j+1) (stepping x y)‖:=by rw [rill_spell,norm_smul]; simp_rw [norm_mul]; simp only [norm_div,norm_one,Real.norm_eq_abs,abs_of_nonneg (show 0≤(2:ℝ) by positivity), abs_of_nonneg (show 0≤((i+1:ℕ):ℝ) by positivity), abs_of_nonneg (show 0≤((j+1:ℕ):ℝ) by positivity)]; unfold pegPrice hewer stepping; ring
lemma torrid [Fintype α] (p': AngleSea p) (G:ropes Cover α α)(P Q:Gen ℝ (Cloth α))(h: Amber Bank.terrain s A (P (i+1)))(v:dragCup Bank.terrain s B G)(w:Rent p u (Q (j+1)) C)(hz:0<s)(ht:i+j=r): RentX p u (rill G P Q r i j) (pegPrice i j*(C*((B*tender α s u)*(A*piped α i s u)))):=by
    subst r; let f (x y:Cloth α):= autumn 1 u (Bank.terrain.gap x.1 y.1)*‖G x y‖; let g (v:dock Cover α (i+1)):= autumn 1 u (soar Bank.terrain v)*‖P _ v‖
    let H := B*tender α s u; have hh:0≤H:= mul_nonneg v.1 (tender_nn hz ..); let L:=A*piped α i s u; have hL:0≤L:=mul_nonneg h.1 (piped_nn i hz u)
    have hc:0 ≤ pegPrice i j:= by unfold pegPrice; positivity
    let M (x:dock Cover α (j+1))(y:dock Cover α (i+1)):= f (y 0) (x 0)*g y
    have he x: SumBudget (M x) (H*L):= by
       have hv (y:Cloth α): SumBudget (fun x=> f x y) H:=by
            unfold f; simp_rw [Bank.terrain.swap _ y.1]; exact tender_finance _ hz v.1 (fun x=> by rw [Bank.terrain.swap]; exact v.2 _ _) zero_le_one le_rfl _
       exact cap_walk _ _ (Fin.consEquiv (fun _:Fin (i+1)=>Cloth α)) (fun _=>rfl) (prod_cap (hv _) hL (fun x=>piped_cost hz zero_le_one le_rfl h x u))
    let T:= droplet i j α; have hp:= cap_scale (prod_cap w (mul_nonneg hh hL) he) hc
    refine budget_minor (cap_walk _ T.symm (f:=fun x=>pegPrice i j*((quoteT p u (T x).1*‖Q _ (T x).1‖)*M (T x).1 (T x).2)) (fun _=>by rw [T.apply_symm_apply]) hp) (fun i=>mul_nonneg (zero_le_one.trans (quoteT_pos i.1 ..)) (norm_nonneg _)) (fun x=>?_)
    let a:= hewer (i:=i) x.1 x.2; let b:=stepping (i:=i) x.1 x.2; let s:= soar Bank.terrain a; let t:= Bank.terrain.gap (a 0).1 (b 0).1
    have hw: quoteT p u x.1≤ autumn 1 u s*autumn 1 u t*quoteT p u b:= (autumn_mono zero_le_one u (lip_up x.1 x.2 p')).trans ((autumn_tax zero_le_one ..).trans (mul_le_mul_of_nonneg_right (autumn_tax zero_le_one ..) (zero_le_one.trans (quoteT_pos _ ..))))
    refine (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans_eq ?_; rw [rill_norm]; change _*(pegPrice i j*‖G (a 0) (b 0)‖ * ‖P _ a‖ * ‖Q _ b‖)= pegPrice i j * ((quoteT p u b *‖Q _ b‖)*((autumn 1 u t*‖G (a 0) (b 0)‖)*(autumn 1 u s*‖P _ a‖))); ring
end YM.WilsonCoeffUV.Mer

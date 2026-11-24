import YM.FormalBulk08.Grail.Oath

/-!
# Rooted sampled-prism operations for reading the transfers
- exact procedure: always FULL line at the same schedule + noise; neither
primitive nor perturbation/vacuum branch is changed. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Palm
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I J V : Type} {G:Gauge} {m l D n j t:ℕ}{σ η A B:ℝ}{a:Loc G 1}{L : Side}

lemma stipend_en {S : edgeL G→ℝ} (h:Stipend S) : Stipend (fun v=>‖S v‖):= by
    obtain ⟨A,l,h,H⟩:=h; refine ⟨A,l,h,fun i=>?_⟩; rw [Real.norm_of_nonneg (norm_nonneg _)]; exact H i
lemma tall_en {P:Reach I}{a:I}{T:Tile I m}(h:Knoxville P η a T A): Knoxville P η a (fun v=>‖T v‖) A:= by
    refine ⟨h.1, le_trans (le_of_eq ?_) h.2⟩; simp_rw [Real.enorm_eq_ofReal (norm_nonneg _), ofReal_norm] -- may fail
lemma row_en {S:Row I J}(h:S.strip η A) : (show Row I J from fun v t p=> ‖S v t p‖).strip η A:= by
    intro i j; specialize h i j; unfold Width at *; simp_rw [Real.norm_of_nonneg (norm_nonneg _)]; exact h

lemma tenspay (f:Fin m→V→ℝ)(h:∀ i,Summable (f i)) : Summable (fun v:chain V m=>∏ i,f i (v i)) := by
    let g : Tile V m:= fun v=> 1
    have hh:= lenses (fun _:Fin m=> ()) (fun i v (_:Unit)=> f i v) (fun i _=>h i) g (C:=1) (fun _=>by simp [g]); simp only [g,one_mul] at hh;exact hh
lemma ten_fold (f:Fin m→V→ℝ) (hf:∀ i,Summable (f i)) : (∑' v:chain V m,∏ i,f i (v i)) =∏ i, ∑' v:V,f i v:= by
    induction m with
    | zero=> simp only [Finset.univ_eq_empty,Finset.prod_empty]; rw [tsum_const];simp [chain]
    | succ m ih=> let e:= Fin.consEquiv (fun _:Fin (m+1)=>V); let F (v:chain V (m+1)):= ∏ i,f i (v i); have ht : Summable (F ∘ e) := (e.summable_iff).mpr (tenspay f hf)
                  change (∑' v,F v)= _; rw [← Equiv.tsum_eq e]; change (∑' i,(F∘e) i)=_; rw [ht.tsum_prod,Fin.prod_univ_succ,← ih (fun i=>f i.succ) (fun i=>hf _),←tsum_mul_right]; apply tsum_congr;intro v; rw [←tsum_mul_left]; refine tsum_congr fun i=>?_ ;change F (Fin.cons v i)=_;unfold F; rw [Fin.prod_univ_succ];rfl

lemma cargo (T:Tile (edgeL G) m) (h:Knoxville (fame _) σ (0,a) T A) (hs:0≤σ)(x:Site L)(hp:0<η)(ht: η ≤ L.val*σ)(S:Cross L (Loc G 1) (Loc G 1))(hu:S.strip η B)(hb:0≤B)(f: Fin m→edgeL G→ℝ)(hf:∀ i, Stipend (f i)) :
    Summable (uncurry (fun v w:chain (edgeL G) m=> carries (lift x) T w*(∏ i,merit S (w i) (v i)) * ∏ i,f i (v i))) := by
    let z:edgeL G:=(lift x,a); let K:= carries (lift x) T; let U:Tile (edgeL G) m:= fun w=>‖K w‖
    have hh : Knoxville (fame _) σ z U A:= tall_en (knight _ _ _ h)
    let F: Cross L (Loc G 1) (Loc G 1):= fun i j v=>‖S i j v‖
    have he:F.strip η B:= row_en hu; let D:= pearl (merit F) U;
    have hW := penn_prism (fun _:Fin m=>F) z a (fun _=>he) U hb hh ht hp.le
    have hZ : piz L z a=(0,a):= Prod.ext (show Stationary.rent L (lift x)=0 from (rent_raw _ (lift x) x (by simp)).2) rfl; rw [hZ] at hW
    let Q(v w:chain (edgeL G) m):= U w*∏ i,merit F (w i) (v i)
    let Z(v:chain (edgeL G) m):=∏ i,‖f i (v i)‖
    have hx : Summable (fun v=> D v*Z v):= ((pays_product (fun i v=>‖f i v‖) a hp (fun i=>stipend_en (hf i))).choose_spec.2 _ _ hW).1
    have hq v : Summable (Q v):= lenses _ _ (fun _ w=> center_row _ he hp.le hb w) U (C:=A) (fun w=> le_trans (le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (show 0≤σ*herb (fame _) z w from mul_nonneg hs (Nat.cast_nonneg _)))) (penn_chill w hh))
    let q(v w:chain (edgeL G) m):ℝ:= K w*(∏ i,merit S (w i) (v i))* ∏ i,f i (v i)
    have ha v w:‖q v w‖= Q v w*Z v:=by dsimp only [q]; rw [_root_.norm_mul,_root_.norm_mul,norm_prod,norm_prod]; rfl
    refine ((summable_prod_of_nonneg (f:=fun v:chain (edgeL G) m × chain (edgeL G) m=>‖q v.1 v.2‖) (fun _=> norm_nonneg _)).mpr ⟨fun v=>( (hq v).mul_right (Z v)).congr (fun w=>(ha v w).symm), hx.congr (fun v=>?_ )⟩).of_norm
    change _=(∑' w, ‖q v w‖); simp_rw [ha,tsum_mul_right];rfl
end YM.FormalBulk08.Palm

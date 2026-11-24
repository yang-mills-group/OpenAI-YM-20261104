import YM.FormalBulk08.Palm.Freight

/-!
Move an arbitrary polynomial probe on the FULL cover through the
analytic A0 rows. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Palm
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I J V : Type} {G:Gauge} {m l D n j t:ℕ}{σ η A B:ℝ}{a:Loc G 1}{L : Side}
lemma shirt (x:Cover): Stationary.rent L x=cellar L x := (rent_raw (cellar L x) x (wrap L x) (balance L x)).2

lemma rolls (S: Carrier.Lines L)(h:S.strip η A)(v:edgeL G)(f: Potential G)(hs:f∈rangeLt (Axis→G.Color) l)(hp:0<η) :
    let F(x:edgeL G):= merit (grown G S) v x*assigns f x
    Summable F ∧ (∑' i,F i)= applyLine S (verdict f) v.1 (Pose.bearing v) v.2.2:= by
    intro F
    let q:=cellar L v.1; let X:= Equiv.addLeft q; let W(j:Axis)(x:Cover):= member S v.1 (Pose.bearing v) j x • verdict f (q+x) j
    obtain ⟨B,hB,H⟩:= royalties l f hs; have ht j: Summable (W j):= Summable.of_norm (stream_income hp (h _ _) q l hB (fun z=> H z j)).2.1
    let V:= EuclideanSpace.proj (𝕜:=ℝ) (v.2.2)
    have he x j c: F (X x,axisEquiv j,c)= if v.2.2=c then V (W j x) else 0:= by
        change (if v.2.2=c then _ else (0:ℝ))* _= _; by_cases hz:v.2.2=c
        · subst c; rw [if_pos rfl, if_pos rfl]; change S (wrap L v.1,v.2.1) _ ((q+x)-Stationary.rent L v.1)* _= _; rw [shirt,show q+x-cellar L v.1=x from add_sub_cancel_left ..]; unfold W member; rw [map_smul]; rw [show coord (Pose.bearing v)=v.2.1 from axisEquiv.apply_symm_apply _,assigns,Pose.bearing,axisEquiv.symm_apply_apply]; rfl
        rw [if_neg hz,if_neg hz,zero_mul]
    have hh (p:Loc G 1) : Summable (fun w=> F (w,p)) := by
        apply (X.summable_iff).mp; rcases p with ⟨p,c⟩; obtain ⟨j,rfl⟩:=axisEquiv.surjective p; by_cases hx:v.2.2=c
        · exact (V.summable (ht j)).congr (fun x=>((he x j c).trans (if_pos hx)).symm)
        exact Summable.congr (summable_zero (α:=ℝ) (β:=Cover)) fun x=>((he x j c).trans (if_neg hx)).symm
    let T: Loc G 1 × Cover →ℝ:= fun p=> F p.swap; have hw: Summable T:=by
       apply Summable.of_norm; exact (summable_prod_of_nonneg (f:=fun i:Loc G 1×Cover=>‖T i‖) (fun _=>norm_nonneg _)).mpr ⟨fun v=>(hh v).norm, summable_of_ne_finset_zero (s:=Finset.univ) (by simp)⟩
    have hg: Summable F:= hw.prod_symm
    refine ⟨hg,?_⟩; rw [sum_strip hg]; rw [Fintype.sum_prod_type]
    change _= V (∑ j:Axis,∑' x,W j x); rw [map_sum]; symm; refine Fintype.sum_equiv axisEquiv _ _ fun i=>?_ ; rw [V.map_tsum (ht _), Finset.sum_eq_single v.2.2]; swap
    · intro b _ heq; rw [← Equiv.tsum_eq X (fun x:Cover=> F (x,axisEquiv i,b))]; simp_rw [he, if_neg (Ne.symm heq)]; rw [tsum_zero]
    swap; · simp
    rw [← Equiv.tsum_eq X (fun x:Cover=>F (x,axisEquiv i,v.2.2))]; exact tsum_congr fun b=> ((he b _ _).trans (if_pos rfl)).symm

def eastern (f: Place.Potential G)(v:Cover) := fun x:E4=> f (x+ Place.seat v)
lemma tariffs_shift (k:Cover)(T:Tile (edgeL G) m)(u:Fin m→ Place.Potential G): tariffs (fun i=> assigns (u i)) (Kemp.carries k T) = tariffs (fun i=> assigns (eastern (u i) k)) T:= by
    let X := Lotus.tint (I:=Loc G 1) k; let e:= Equiv.arrowCongr (Equiv.refl (Fin m)) X
    unfold tariffs; rw [← Equiv.tsum_eq e (fun j:chain (edgeL G) m=> Kemp.carries k T j * ∏ i, assigns (u i) (j i))]; apply tsum_congr; intro w; congr 1
    · apply congr_arg T; ext1 i; apply Prod.ext
      · change (w i).1+k+ -k=_;simp
      rfl
    apply Finset.prod_congr rfl; intro i _; unfold assigns; rw [show (e w i).1=(w i).1+k from rfl,show Place.seat ((w i).1+k) =Place.seat (w i).1+Place.seat k from ?h]; rfl
    case h=> ext i;simp
lemma occurs (T:Tile (edgeL G) m)(h:Knoxville (fame _) σ (0,a) T A)(hs:0≤σ)(x:Site L)(hp:0<η)(ht:η≤ L.val*σ)(S:Carrier.Lines L)(hu:S.strip η B)(hb:0≤B)(f:Fin m→ Place.Potential G)(n:Fin m→ℕ)(hf:∀ i,f i∈rangeLt _ (n i))(g : Fin m→Place.Potential G)(he:∀ i,applyLine S (verdict (f i))=verdict (g i)):
     tariffs (fun i=>assigns (f i)) (upmost L x (grown G S) T)= tariffs (fun i=> assigns (eastern (g i) (lift x))) T:= by
     let V:= Kemp.carries (lift x) T
     let u:= merit (grown G S); let F (v w:chain (edgeL G) m):= V w * (∏ i,u (w i) (v i)) * ∏ i,assigns (f i) (v i)
     have hx:Summable (uncurry F):= cargo T h hs x hp ht (grown G S) (grown_budget G _ hb hu) hb _ (fun i=> shoulder (hf i))
     rw [← tariffs_shift];unfold tariffs upmost pearl; simp_rw [←tsum_mul_right]
     change (∑' v,∑' w,F v w)=_; rw [← hx.tsum_comm];apply tsum_congr; intro w
     let Z(i)(v:edgeL G):= u (w i) v*assigns (f i) v
     have hZ i: Summable (Z i) := (rolls S hu (w i) (f i) (hf i) hp).1
     have hq i : assigns (g i) (w i)=∑' v,Z i v:= by
       have hh: (∑' v,Z i v)= _:= (rolls S hu (w i) (f i) (hf i) hp).2; rw [hh,he]; rfl
     simp_rw [hq]; rw [← ten_fold _ hZ,← tsum_mul_left]; exact tsum_congr fun j=>by unfold Z; rw [Finset.prod_mul_distrib]; exact mul_assoc ..
end YM.FormalBulk08.Palm

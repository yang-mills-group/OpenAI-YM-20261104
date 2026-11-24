import YM.FormalBulk08.Kemp.Mane

/-! Root fixed, not averaged across lifted images for mark. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05
open Lotus Shore Mesa Gorge City Cork Rift
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I J V: Type*} {r:ℕ} {m n : Side}{η θ A : ℝ}
variable (m : Side) (T : Tile (Biglot I) r)

/-- Include each lift (no difference-only wrap with augmentative center). -/
def sieve (v: chain (Tor m I) r): ℝ:= ∑' u:{u:chain (Biglot I) r// Lotus.drip m ∘ u=v}, T u.val
lemma sieve_i (v:chain (Tor m I) r): sieve m T v=∑' u, if Lotus.drip m ∘ u=v then T u else 0:= by
    unfold sieve; let p: Set (chain (Biglot I) r):= {w|Lotus.drip m ∘ w=v}; rw [← show (∑' u:p,T u.val)=(∑' u:{u:chain (Biglot I) r// Lotus.drip m ∘ u=v},T u.val) from tsum_congr fun _=>rfl, tsum_subtype p T]; apply tsum_congr; intro u; by_cases h:Lotus.drip m ∘ u=v; rw [Set.indicator_of_mem (show u∈p from h),if_pos h]; rw [Set.indicator_of_notMem (show u∉p from h),if_neg h]
lemma sieve_sand (h:Agate T): Agate (sieve m T):= by
    intro v s; rw [sieve_i,sieve_i]; let e : chain (Biglot I) r≃ chain (Biglot I) r:=Equiv.arrowCongr s.symm (Equiv.refl _); rw [←Equiv.tsum_eq e (fun u=> if Lotus.drip m ∘ u=v ∘ s then T u else 0)]; refine tsum_congr fun a=>?_; by_cases ha:Lotus.drip m ∘ a=v
    · rw [if_pos ha, if_pos]; exact h a s
      change (Lotus.drip m ∘ a) ∘ s=v ∘ s; rw [ha]
    rw [if_neg ha,if_neg]; exact fun hh=> ha (funext fun i=>by
       have he:= congr_fun hh (s.symm i)
       change (Lotus.drip m ∘ a) (s (s.symm i))= v (s (s.symm i)) at he; rwa [s.apply_symm_apply] at he)
@[simp] lemma sieve_zero (I:Type*): sieve m (0:Tile (Biglot I) r)=0:=funext fun _=>by simp [sieve]
lemma sieve_smul (a:ℝ): sieve m (a • T)=a • sieve m T:=funext fun _=>by simp [sieve,tsum_mul_left]
lemma sieve_sub_add {T S:Tile (Biglot I) r}(h:Summable T)(hs: Summable S):sieve m (T+S)=sieve m T+sieve m S ∧ sieve m (T-S)=sieve m T-sieve m S:= by
   constructor <;> (funext v;first| exact (h.subtype _).tsum_add (hs.subtype _)| exact (h.subtype _).tsum_sub (hs.subtype _))
lemma sieve_bill (o:Biglot I)(hs:0≤η)(h:Knoxville (fame _) η o T A): Knoxville (lake m I) η (Lotus.drip m o) (sieve m T) A:= by
    let R v (u:chain (Biglot I) r):= if Lotus.drip m ∘ u=v then T u else 0
    have ht : Allow (lake m I) η (Lotus.drip m o) R A := by
       refine ⟨h.1,?_⟩; rw [ENNReal.tsum_comm]; apply le_trans _ h.2;apply ENNReal.tsum_le_tsum; intro v; rw [tsum_eq_single (Lotus.drip m ∘ v)]; swap
       · intro u hu; unfold R; rw [if_neg (Ne.symm hu),enorm_zero,mul_zero]
       unfold R; rw [if_pos rfl]; apply mul_le_mul_left (shine_le _ hs _); have hp:=skirt_wide m (Fin.cons o v : chain (Biglot I) (r+1)); rwa [Fin.comp_cons] at hp
    have he : sieve m T=fun v=>∑' u,R v u:= funext fun i=>by rw [sieve_i]
    rw [he]; exact ht.bill
lemma sieve_kalm (T:Tile (Biglot I) r){o}(h:Knoxville (fame _) η o T A)(hs:0≤η): Kalm η o T (fun n=>sieve n T):= by
   refine ⟨fun v=>?_,A,.of_forall fun n=>sieve_bill n T o hs h⟩
   let f n (x:chain (Biglot I) r):=if Lotus.drip n ∘ x=Lotus.drip n ∘ v then T x else 0
   let y (x:chain (Biglot I) r):=if x=v then T x else 0
   have hx : ∑' x,y x=T v:= by rw [tsum_eq_single v (fun _ h=>if_neg h)];simp
   have hv : Tendsto (fun n=>∑' x,f n x) atTop (𝓝 (∑' x,y x)):= by
      refine tendsto_tsum_of_dominated_convergence (penn_total h hs) (fun a=> tendsto_const_nhds.congr' ?_) (.of_forall fun n x=>?_)
      · filter_upwards [eventually_all.mpr fun i=> same_drip (a i) (v i)] with n hn
        by_cases he : a=v
        · simp [f,y,he]
        have hh : Lotus.drip n ∘ a≠Lotus.drip n ∘ v:= fun ha=> he (funext fun i=> (hn i).mp (congr_fun ha i));simp only [y,f,hh,he,↓reduceIte,eq_self]
      unfold f; split <;> simp
   rw [hx] at hv; simp_rw [sieve_i];exact hv

lemma rinse (R:Ratio n m) : sieve n (jetty (Bank.scroll R.count I).symm T)=jetty (splitCo R I).symm (sieve m T):= by
    funext v; let e:=Bank.scroll R.count I; let f:= splitCo R I; rw [sieve_i]; change _= sieve m T (f.symm ∘ v); rw [sieve_i]; rw [←Equiv.tsum_eq (Equiv.arrowCongr (Equiv.refl _) e) _]; refine tsum_congr fun u=>?_
    rw [show ((Equiv.arrowCongr (Equiv.refl _) e) u)=e ∘ u from rfl]
    have hv : Lotus.drip n ∘ e ∘ u=v ↔ Lotus.drip m ∘ u=f.symm ∘ v := by
       constructor <;> intro h <;> funext i; · apply f.injective;rw [comp_apply,comp_apply,f.apply_symm_apply]; exact (Bank.scroll_pull _ R).symm.trans (congr_fun h i)
       exact (Bank.scroll_pull _ R).trans ((congr_arg f (congr_fun h i)).trans (f.apply_symm_apply _))
    by_cases hh: Lotus.drip n ∘ e ∘ u=v
    · rw [if_pos hh,if_pos (hv.1 hh)]; change T (e.symm ∘ e ∘ u)=_; exact congr_arg T (funext fun i=>e.symm_apply_apply ..)
    rw [if_neg hh,if_neg (hh ∘ hv.2)]
lemma rinse_bill (L:Side)(h : θ≤L.val*η)(he:0≤θ) (o : Biglot (Tor L I))(hx: Knoxville (fame _) η ((Bank.scroll L I).symm o) T A):
    Knoxville (fame _) θ o (jetty (Bank.scroll L I).symm T) (Real.exp (8*θ)*A) := by
    let U:= Bank.scroll L I; refine ⟨mul_nonneg (Real.exp_pos _).le hx.1,?_⟩
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]; refine le_trans ?_ (mul_le_mul_right hx.2 _); rw [← ENNReal.tsum_mul_left,← Equiv.tsum_eq (Equiv.arrowCongr (Equiv.refl _) U.symm) (fun v:chain (Biglot I) r=> ENNReal.ofReal (Real.exp (8*θ)) * (Gorge.shine η (wide (fame _) (Fin.cons ((Bank.scroll L I).symm o) v))*‖T v‖ₑ))]
    refine ENNReal.tsum_le_tsum fun v=>?_ ; have ht:=Bank.shift_wide L (Fin.cons o v : chain (Biglot (Tor L I)) (r+1)) h he; rw [Fin.comp_cons] at ht; exact (mul_le_mul_left ht _).trans_eq (mul_assoc ..)
end YM.FormalBulk08.Kemp

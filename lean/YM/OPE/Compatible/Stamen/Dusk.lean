import YM.OPE.Compatible.Stamen.Douse
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
-- area of focus. freezing by infinite root coefficient Delta
noncomputable def voice (a:Root I)(j m:ℕ): stave m (j+1) I →ₗ[ℝ] stave m j I where
       toFun p:= plant m (toque (seed m (j+1) I p) a) ‖p‖ (owns _ _ (humor p))
       map_add' p q:= seed_inj m _ _ (by rw[botany,map_add,map_add,botany,botany]; rfl)
       map_smul' c p:= seed_inj m _ _ (by rw[botany,map_smul,map_smul,botany];rfl)
noncomputable def Dragon (a:Root I)(k m:ℕ): End ℝ (Seat k m I):= LinearMap.pi (fun i=> ((i.val+1:ℕ):ℝ) • (voice a i.val m ∘ₗ (moduleAt m k (i.val+1) I).toLinearMap))
lemma dragN (p:Seat k m I)(j:ℕ)(a:Root I): lilies m k I (Dragon a k m p) j=((j+1:ℕ):ℝ) • toque (lilies m k I p (j+1)) a:=by
       by_cases h:j ≤ k
       · rw [soup,moduleAt,dif_pos h]; let i:= (⟨j,by omega⟩:Fin (k+1)); let v:= (moduleAt m k (j+1) I) p
         change seed m _ I (((j+1:ℕ):ℝ) • voice a j m v)=_; rw[map_smul]
         congr 1; exact botany m _ _ (owns _ _ (humor v))
       rw [(sproutV m k _).1 _ (by omega), (sproutV m k p).1 (j+1) (by omega),show toque 0 a= (0:Script I j) from rfl,smul_zero]
lemma quakeD (p:Script I (j+2))(h:p.sorted)(a b:Root I): toque (toque p a) b=toque (toque p b) a:=by
       ext1 x; let i:=Equiv.swap (0:Fin (j+2)) 1; rw [show toque (toque p a) b x= swing i p (Fin.cons b (Fin.cons a x)) from ?_]; exact congr_fun (h i) _
       refine congr_arg p ?_; funext t; refine Fin.cases ?_ (fun l=>Fin.cases ?_ (fun q=>?_) l) t <;> simp only [Function.comp_apply, Fin.cons_zero, Fin.cons_succ]
       · simp [i]
       · simp [i]
       unfold i; rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by exact Fin.succ_inj.not.mpr (Fin.succ_ne_zero _)),Fin.cons_succ,Fin.cons_succ]
lemma coreD (p:Script I (j+3))(h:p.sorted)(a:Root I)(A:RowB I): toque (pad A.val p) a= pad A.val (toque p a):=by
       ext1 x; change pad A.val p (Fin.cons a x)=_; rw [paia,paia]; apply tsum_congr; intro t; rw[duoW,duoW]; let T:=toque p t.1; change _* toque (toque T t.2) a x=_; rw [quakeD _ (touchS t.1 p h),show toque T a= _ from quakeD p h t.1 a]
lemma flareD (p:Script I (j+2))(c:ℝ)(A:RowB I): pad A.val (c • p)=c • pad A.val p:=by
       ext1 i; rw[paia,Pi.smul_apply,paia, smul_eq_mul, ← tsum_mul_left]; apply tsum_congr; intro a; rw [duoW,duoW]; change _*(c*_)=_; unfold toque; ring
lemma Lapid (p:Seat k m I)(a:Root I)(A:RowB I)(h:settled (m:=m) p): Dragon a k m (lapD A m k p)=lapD A m k (Dragon a k m p):=by
       apply lilies_inj I k m; funext j; rw [dragN,pulse_i,pulse_i,dragN,flareD]; let q:= lilies m k I p (j+3); have hp:toque (wind (j+1) • pad A.val q) a=wind (j+1) • pad A.val (toque q a):= congr_arg (fun z=> wind (j+1) • z) (coreD q (h _) a A)
       rw [hp, smul_smul, smul_smul]; apply congr_arg (· • _); unfold wind; push_cast; ring
lemma candleD (p:Seat k m I)(a:Root I)(A:RowB I)(c:ℝ)(h:settled (m:=m) p): Dragon a k m (boostS A c m k p)=boostS A c m k (Dragon a k m p):=by
       let f:= (lapD A m k).toLinearMap; have he(i:ℕ): Dragon a k m ((f^i) p)=(f^i) (Dragon a k m p) ∧settled (m:=m) ((f^i) p):=by
                  induction i with
                  | zero=> simpa
                  | succ i ih=> rw[pow_succ',End.mul_apply,End.mul_apply]; exact ⟨(Lapid _ _ A ih.2).trans (congr_arg f ih.1),tor_fit _ A ih.2⟩
       rw[boostS,Hflow,map_sum,Hflow]; exact Finset.sum_congr rfl fun i _=>by rw[map_smul,(he i).1]
lemma stoneD [Fintype I](p:Seat k m (Palette I))(a:Root (Palette I))(hp:p∈ empa I k m): Dragon a k m p∈ empa I k m:=by
       refine ⟨fun j=>?_,fun j=>?_⟩
       · rw[dragN]; intro i; exact congr_arg (fun v:Script (Palette I) j=> ((j+1:ℕ):ℝ) • v) (touchS a _ (hp.1 _) i)
       rw[dragN]; intro i n w s; rw [score_scaled,veilX _ ((sproutV m k p).2 _) (hp.2 _) a i n w s, mul_zero]
abbrev Deep (p:Seat k m I)(d:ℕ):Prop:=∀ i:ℕ,i < d→ lilies m k I p i=0
lemma dragDeep (p:Seat k m I)(a:Root I)(h:Deep (m:=m) p (j+1)):Deep (m:=m) (Dragon a k m p) j:=by intro i hi; rw [dragN,h _ (by omega), show toque 0 a=(0:Script I i) from rfl, smul_zero]
end YM.OPE.Silt.Phere

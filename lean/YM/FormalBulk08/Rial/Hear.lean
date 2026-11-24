import YM.FormalBulk08.Rial.Cure

/-! Projection commutes with turns in actual field colors and separate test
address. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Rial
open Filter Set Function Lattice Laurent Wilson Exterior Stationary
open Orb Reef Jets Lava Lotus Mesa Gorge Shore City Kemp Rift Wine Pose PowerSeries Wick
open Planned.PrimaryIntegral295 Place Carrier Film Labels Source Source.Drops Next.Foundations Dawn
open scoped Matrix Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {d l r k i D u: ℕ} (F:Frame G d)(s:Signed)(H: Hol G)
    {T Y: Anthem D G}{a:Loc G 1} (h: Son T Y l s)(hp: Clef a T l)(ht: Clef a Y l)

lemma scores (p:F.Coeff) (b:F.Index): F.act s.ortho p b=∑ i∈family F b,p i*(F.act s.ortho (copy F i) b):= by
   conv_lhs => rw [← Finset.univ_sum_single p]
   rw [_root_.map_sum,Finset.sum_apply,← Finset.sum_subset (Finset.subset_univ (family F b)) (fun i _ hi=> ?_)]; swap
   · have he : Pi.single i (p i)=p i • copy F i:=by ext v; by_cases h:v=i <;> simp [copy,h]
     rw [he,map_smul,Pi.smul_apply,exactGuard F s _ _ (by simpa [family] using hi),smul_zero]
   refine Finset.sum_congr rfl fun i _=> ?_; rw [show Pi.single i (p i)=p i • copy F i from (by ext v; by_cases h:v=i <;> simp [copy,h]),map_smul]; rfl
lemma real_scores (p:F.Coeff)(b:F.Index): (F.act s.ortho p b).re=∑ i∈family F b,(p i).re*(F.act s.ortho (copy F i) b).re := by
   rw [scores F, Complex.re_sum]; apply Finset.sum_congr rfl; intro i _; nth_rw 1 [← realTurn F s i b]; simp

include H hp h ht
lemma melody (x: Letter F)(e r): pearlJ F (T (inside F x D) e r) (mint F x)=∑ y∈mates F s x, coeff 0 (lariat F s x y)*pearlJ F (Y (inside F y D) e r) (mint F y):= by
   let p:= inside F x D; let Q:= froth s D p
   let a':=mint F x; let m:= Pose.slots F x; let n:=label F x
   let t:=slate (T p e r) d m; let S:=slate (Y Q e r) d m
   obtain ⟨w,B,hw,hb,hV⟩:=hp.fare.2.2 e r; obtain ⟨v,C,hC,hv,hU⟩:=ht.fare.2.2 e r
   have Ht (u:Fin m→Snap G d): t u=S (turnIn G d s∘u):= (wind_slate s H a (T p e r) (Y Q e r) (kport s h hp.fare ht.fare p e r) hw (hV p) hC (hU Q) u).symm
   have hz : F.coords (lent t n) = F.act s.ortho (F.coords (lent S n)):= by
       rw [Frame.act_coords, preserve s t S (monic_slate _ _ H hw (hV p) (perfumed T hp p _ _) d m) (monic_slate _ _ H hC (hU Q) (perfumed Y ht Q _ _) d m) (slotsFits F x) n (F.bound a') Ht]
   change (F.coords (lent t n) a').re= _; rw [hz,real_scores]; rw [show family F a'=family F (mint F x) from rfl,← swims F s x]; apply Finset.sum_congr rfl; intro y hy; have hp':Crew F s x y:=(Finset.mem_filter.mp hy).2
   let b : ℝ:= Dawn.tone (pet F x).val s
   have hk : Q=b • inside F y D:= by unfold Q inside p; rw [inside,breezy]; rw [hp'.1]; rfl
   have hy : (Y Q e r)= b • (Y (inside F y D) e r):= by rw [hk,ht.map_smul];rfl
   rw [lariat,if_pos hp',coeff_zero_C]
   have hm : (F.grades (mint F y)).2=m := congr_arg Prod.snd hp'.2
   have hq : (F.grades (mint F y)).1=n := congr_arg Prod.fst hp'.2
   change (Pose.pocket F S n _).re*_=(b* _)*_
   unfold S pearlJ; rw [hy,hm,hq,slate_scale (hU _) hC,stip]; simp [mul_comm,mul_left_comm,a',mul_assoc]
lemma hear_turn (x: Letter F): echo F T x=(lariat F s *ᵥ echo F Y) x := by
    have he (p: Letter F→Pence): (lariat F s *ᵥ p) x=∑ y∈mates F s x,lariat F s x y*p y:= by
       unfold Matrix.mulVec dotProduct; symm; apply Finset.sum_subset (Finset.subset_univ _); intro b _ hb; rw [lariat,if_neg (by simpa [mates] using hb),zero_mul]
    ext1 e; rw [echoline,he,map_sum]; let K:= Pose.slots F x
    let J(y: Letter F):=coeff 0 (lariat F s x y)
    have hm(y:Letter F):lariat F s x y=C (J y):= by unfold J lariat; split <;>simp
    let P (k:ℕ)(y:Letter F):=J y * if K-k ≤ e then pearlJ F (Y (inside F y D) (e-(K-k)) k) (mint F y) else 0
    refine Eq.trans (b:= ∑ k∈Finset.range (K+1),∑ y∈mates F s x,P k y) ?_ ?_; swap
    · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro y hy; have hv:= crew_rank F s ((Finset.mem_filter.mp hy).2); rw [hm y,coeff_C_mul,echoline,←hv.1,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; unfold P; by_cases ht':K-i≤e
    · simp_rw [if_pos (show Pose.slots F x-i≤e from ht'),if_pos ht'];exact melody F s H h hp ht ..
    simp only [K] at ht'; simp only [K, ht',↓reduceIte,mul_zero,Finset.sum_const_zero]
end YM.FormalBulk08.Rial

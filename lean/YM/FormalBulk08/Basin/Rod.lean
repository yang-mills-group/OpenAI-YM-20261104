import YM.FormalBulk08.Vale.Measure
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Basin
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Vale Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
variable (D : Reach V)(A B : V)
-- long link once, two roots.
lemma twoline (u:chain V m)(v:chain V n)(a b:V): let F:= herb D A (Fin.cons a u);let L:= herb D B (Fin.cons b v); let Z:= F+D.d a b+L
                   D.d A B ≤ Z ∧ herb D A (castle V m n (u,v))≤ Z := by
   intro F L Z
   let p:=wide D (Fin.cons B (Fin.cons b v : chain V (n+1))); have he : D.d A a≤ F:=reached D (Fin.cons A (Fin.cons a u)) 0 (Fin.succ 0)
   let H: chain V (n+2):= Fin.cons B (Fin.cons b v)
   have hQ i: D.d (H i) b ≤ L:= reached D H i (Fin.succ 0)
   have hv i:D.d (H i) A ≤ Z:= by have h1:=D.tri (H i) b A; obtain hu:=D.tri b a A;rw [D.turn b a,D.turn a A] at hu; have h:=hQ i; omega
   constructor
   · rw [D.turn]; exact hv 0
   refine known_wide _ _ _ fun i j=>?_ ;
   let T : chain V (m+1+1) := Fin.cons A (Fin.cons a u : chain V (m+1))
   have hg i j : D.d (T i) (H j) ≤ Z:= by
       have hM := D.tri (T i) a (H j); have hx:= D.tri a b (H j); rw [D.turn b (H j)] at hx; have hs:D.d (T i) a ≤ F:= reached D T i (Fin.succ 0); have hz:=hQ j; omega
   have hu : ∀ i: Fin (m+n+1), (∃ j,T j=(Fin.cons A (castle V m n (u,v)):chain V (m+n+1)) i) ∨ (∃ j,H j=(Fin.cons A (castle V m n (u,v)):chain V (m+n+1)) i):=by
       intro i; cases i using Fin.cases with
       | zero=> exact Or.inl ⟨0,rfl⟩
       | succ i=> cases i using Fin.addCases with
                  | left i=> exact Or.inl ⟨i.succ.succ,by simp [T,castle]⟩
                  | right i=>exact Or.inr ⟨i.succ.succ,by simp [H,castle]⟩
   obtain ⟨j',hj⟩|⟨j',hj⟩:= hu i <;> obtain ⟨i',hi⟩|⟨i',hi⟩:=hu j <;> rw [←hj,←hi]; exacts [(reached D T j' i').trans (show F ≤ Z by omega), hg j' i', (D.turn (H j') (T i')).trans_le (hg i' j'), (reached D H j' i').trans (show L ≤ Z by omega)]

lemma pi_charge {T:Tile V (m+1)}{p q:ℝ}{f:V→V→ℝ}{U:Tile V (n+1)}(hp:Knoxville D σ A T p)(hq: Knoxville D σ B U q)(h:Grate D σ f C)(hs:0≤σ) :
   Allow D (σ/2) A (weld f T U) (Real.exp ( - σ/2*D.d A B)*((1/2*(m+1)*(n+1))*p*q*C)) := by
    let E:ℝ:=Real.exp (-σ/2 * D.d A B); let K:ℝ:= 1/2*(m+1)*(n+1);have hE:0 < E:=Real.exp_pos _;have hK:0≤K:=by unfold K; positivity
    let s (a:V) (x:chain V m):= penon D A σ T (Fin.cons a x); let t (b:V)(y:chain V n):= penon D B σ U (Fin.cons b y)
    let W(a b:V):= Gorge.shine σ (D.d a b)*‖f a b‖ₑ
    have hv a b: W a b ≤ ENNReal.ofReal C:= (ENNReal.le_tsum (f:=W a) b).trans (h.2 _)
    have he (u:chain V m)(v:chain V n)(a b:V): Gorge.shine (σ/2) (herb D A (castle V m n (u,v)))*‖weld f T U (castle V m n (u,v)) (a,b)‖ₑ ≤ ENNReal.ofReal E* ENNReal.ofReal K*(s a u * W a b * t b v):= by
       obtain ⟨h,h'⟩:= twoline D A B u v a b; let d:= D.d A B;let X:=herb D A (castle V m n (u,v)); let P:= herb D A (Fin.cons a u);let Q:=herb D B (Fin.cons b v)
       have he:X+d ≤ 2*(P+D.d a b+Q):=by omega
       have ht : Gorge.shine (σ/2) X ≤ ENNReal.ofReal E* Gorge.shine σ (P+D.d a b+Q):= by
           unfold Gorge.shine; rw [←ENNReal.ofReal_mul hE.le]; refine ENNReal.ofReal_le_ofReal ?_; unfold E; rw [←Real.exp_add]; apply Real.exp_monotone; have hh : ((X+d:ℕ):ℝ)≤ 2 * ((P+D.d a b+Q:ℕ):ℝ):=by exact_mod_cast he -- Nat vs real* two
           push_cast at *; change _≤ -σ/2*(d:ℝ)+ σ*((P:ℝ)+ ↑(D.d a b)+ (Q:ℝ)); nlinarith only [hh,hs]
       refine le_trans (mul_le_mul_left ht _) (le_of_eq ?_)
       rw [show weld f T U (castle V m n (u,v)) (a,b)= K*f a b*(T (Fin.cons a u))*(U (Fin.cons b v)) from by unfold weld K halve clutch; simp [Lava.shed,castle,Function.comp_def]; ring, shine_add, shine_add, enorm_mul,enorm_mul,enorm_mul,←ofReal_norm K,Real.norm_eq_abs,abs_of_nonneg hK]; unfold s W t penon P Q; ac_rfl
    change 0≤E * _ ∧ (∑' x,∑' a, _ * ‖weld f T U x a‖ₑ)≤_
    refine ⟨mul_nonneg hE.le (mul_nonneg (mul_nonneg (mul_nonneg hK hp.1) hq.1) h.1),?_⟩
    rw [ENNReal.tsum_comm,ENNReal.tsum_prod'];apply le_trans (b:=∑' a:V,∑' b:V, ∑' u:chain V m, ∑' v:chain V n, ENNReal.ofReal E* ENNReal.ofReal K*(s a u * (ENNReal.ofReal C) * t b v))
    · refine ENNReal.tsum_le_tsum fun a=> ENNReal.tsum_le_tsum fun b=> ?_; rw [←Equiv.tsum_eq (castle V m n),ENNReal.tsum_prod']; refine ENNReal.tsum_le_tsum fun u=>ENNReal.tsum_le_tsum fun v=> (he u v a b).trans (by gcongr;exact hv a b)
    have hx : (∑' a,∑' x,s a x) ≤ ENNReal.ofReal p:= by rw [←ENNReal.tsum_prod, show (∑' c: V × chain V m, s c.1 c.2)=_ from Equiv.tsum_eq (Fin.consEquiv (fun _:Fin (m+1)=>V)) (penon D A σ T)]; exact hp.2
    have hY : (∑' b,∑' y,t b y) ≤ ENNReal.ofReal q:= by rw [←ENNReal.tsum_prod, show (∑' c: V × chain V n, t c.1 c.2)=_ from Equiv.tsum_eq (Fin.consEquiv (fun _:Fin (n+1)=>V)) (penon D B σ U)]; exact hq.2
    simp_rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_right]; rw [ENNReal.ofReal_mul hE.le,ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hK hp.1) hq.1), ENNReal.ofReal_mul (mul_nonneg hK hp.1),ENNReal.ofReal_mul hK]; refine le_trans (b:=ENNReal.ofReal E * ENNReal.ofReal K*((ENNReal.ofReal p)*(ENNReal.ofReal C)*(ENNReal.ofReal q))) ?_ (le_of_eq ?_)
    · simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
      gcongr
    ac_rfl
end YM.FormalBulk08.Basin

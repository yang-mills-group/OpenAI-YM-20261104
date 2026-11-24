import YM.OPE.Compatible.Harks.Reed
/-!
# layers of paid small initial/correction directions
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {E F M:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F] {r x b c t q:ℝ}
variable {a f:ℕ→ E}{g:ℕ→ F}{p:ℕ→ E→L[ℝ] E}
variable {d k:ℕ}{G:ℕ→Type}[∀ i,NormedAddCommGroup (G i)][∀ i,NormedSpace ℝ (G i)]
variable {μ:ℕ→ℝ}{T:Cuts d μ t x E G}
-- MinRate
lemma inLayer (h:t<r)(hp:∀ i,Grooved T (p i))(hp':Run p a 0)(hk:k≤d)(hx:∀ i:ℕ,i<k→ r < μ i)(hh: Hex r a b): a 0 ∈ T.flag k:=by
   induction k with
   | zero=> exact T.first _
   | succ i ih=> have he:= ih (by omega) (fun j hj=>hx j (by omega)); exact (T.next _ (by omega) _).mpr ⟨he,det (T.fast.trans h.le) (hx _ (by omega)) (Run.tap hp' hp (by omega) he) (Hex.invoke (T.Tap i) hh) ⟩
lemma dagger (p f:ℕ→ E)(x:ℕ→ E→L[ℝ] E) (g:ℕ→ E) (h:Run x (p-f) g): Run x p (fun i=> g i+f (i+1)-x i (f i)):=by intro i; have he:=h i; simp only [Pi.sub_apply,map_sub] at he; rw [show p (i+1)= (p (i+1)- f (i+1)) + f (i+1) by abel,he]; abel
lemma solk [∀ i,CompleteSpace (G i)](T:Cuts d μ t x E G)(hr:t<r)(hx:∀ i:ℕ,i<d→μ i≠r): ∀ i:ℕ,i ≤ d→ ∃ C:ℝ,0≤C ∧ ∀ p:ℕ→ E→L[ℝ] E,(∀ i,Grooved T (p i))→∀ f:ℕ→ E,∀ b:ℝ,Hex r f b→ (∀ j:ℕ,f j∈ T.flag i)→ ∃ v∈ T.flag i,Hex r (race p f v) (C*b):=by
   intro i hi; induction hi using Nat.decreasingInduction with
   | self =>
      refine ⟨1/(r-t),by apply div_nonneg zero_le_one (sub_nonneg.mpr hr.le),fun p hp f b hf he=>?_⟩; refine ⟨0,(T.flag _).zero_mem,?_⟩; have ht:= gait p f 0; have hx:= Run.herd ht hp (k:=d) le_rfl he (show (0:E)∈T.flag d from Submodule.zero_mem _); have hb:b/(r-t)=1/(r-t)*b:=by ring
      exact Run.gap hr _ T.fast hb.le hf ht (fun i=> (hp i).march _ (hx i)) (show ‖(0:E)‖≤1/(r-t)*b from hb ▸ (by rw [norm_zero]; exact div_nonneg hf.price (sub_nonneg.mpr hr.le)))
   | of_succ k hj H =>
     have he:k<d:=hj; let L:=T.lift k he; let A:=T.Tap k; obtain ⟨c,hc,H⟩:= H; let q:= ‖L‖ * ‖A‖ / |μ k-r|; have hq: 0≤ q:=by unfold q; positivity
     let B:= 1+ max 0 x*q+r*q; have he':0≤r:=T.fast.trans hr.le; refine ⟨q+c*B,by dsimp only [B]; positivity,fun p hp f b hf hh=>?_⟩
     let a:= fun i=>A (f i); have ht:= Hex.invoke A hf; obtain ⟨y,hG⟩:=scar (E:=G k) (hx k he|>.symm) ((T.tempo _ he).le) he' ht; let X:= race (flint (μ k)) a y; let z:= fun i=>L (X i); have hz:Hex r z (q*b):= (show Hex r z (‖L‖*((‖A‖*b)/|μ k-r|)) from Hex.invoke _ hG)|>.tips he' (le_of_eq (by unfold q; ring)); have hg(i): z i∈T.flag k ∧ A (z i)=X i:=T.rises ..
     let g:= fun i=> f i+p i (z i)-z (i+1); have hv(i): g i∈ T.flag (k+1):=by refine (T.next _ he _).2 ⟨(T.flag _).sub_mem ((T.flag _).add_mem (hh i) ((hp i).leaves k he.le _ (hg _).1)) (hg _).1, ?_⟩; unfold g; rw [map_sub,map_add,(hp i).tempo k he _ (hg _).1,(hg i).2,(hg (i+1)).2]; change a i + _ - (μ k • X i + a i)=0; abel
     obtain ⟨w,hW,hg'⟩:= H p hp g (B*b) ((show Hex r g _ from Hex.sub (hf.add (Hex.pays hz p (fun i=>(hp i).cap.trans (le_max_right ..)))) hz.forward).tips he' (le_of_eq (by unfold B; ring))) hv; let Y:=race p g w; have hx: Run p (z+Y) f:=by
          intro i; rw [Pi.add_apply,Pi.add_apply,map_add]; rw [show Y (i+1)=p i (Y i)+(f i+p i (z i)-z (i+1)) from gait p g w i]; abel
     refine ⟨(z+Y) 0,(T.flag k).add_mem (hg 0).1 ((T.next k he w).1 hW).1,?_⟩; rw [hx.isRace.symm]; exact (hz.add hg').tips he' (le_of_eq (by ring))
end YM.OPE.Hark

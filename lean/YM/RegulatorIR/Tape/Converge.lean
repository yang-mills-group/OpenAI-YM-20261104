import YM.RegulatorIR.Tape.Apply
import YM.RegulatorIR.Tape.Bag
import Mathlib.Analysis.Normed.Group.Tannery
/-!
# Tallies convergence and contact support. May be used on arbitrary infinite Jets with moment
bound. Here needed only in bulk Wick proof for period-class determination (no curve rates).
-/
noncomputable section
namespace YM.RegulatorIR.Tape
open Function Filter Set
open scoped NNReal ENNReal Topology BigOperators Classical
variable {ι α β γ : Type*} {f g : Tape α} {F G : ι→Tape α} {s : ℝ} {l : Filter ι} {w : Weight α} {V : Weight β} {A : ℝ≥0∞} {S : Set α}

abbrev Up (l : Filter ι)(w : Weight α)(F : ι→Tape α)(f : Tape α):= Tendsto (fun i=>tally w (F i -f)) l (𝓝 0)
lemma first_zero {x y:ι→ℝ≥0∞} (h : Tendsto x l (𝓝 0))(d : y≤x): Tendsto y l (𝓝 0):= tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _=>zero_le) d
lemma multiplyZero {x y:ι→ℝ≥0∞} (a :ℝ≥0∞)(hc:a<∞) (h : Tendsto x l (𝓝 0))(H:Tendsto y l (𝓝 a)): Tendsto (fun i=>x i*y i) l (𝓝 0):= by simpa only [zero_mul] using ENNReal.Tendsto.mul h (Or.inr hc.ne) H (by simp)
lemma Up.stays (f:Tape α) : Up l w (fun _=>f) f:=by simp_rw [Tape.Up,sub_self,tally_zero]; exact tendsto_const_nhds
lemma Up.added (h:Up l w F f)(hh:Up l w G g): Up l w (fun i=> F i+G i) (f+g) := first_zero (by simpa only [add_zero] using h.add hh) (fun i=>by rw [show F i + G i-(f+g)=F i-f+(G i-g) from by abel]; exact tally_add ..)
lemma Up.smult (h:Up l w F f)(s:ℝ): Up l w (fun i=>s • F i) (s • f) := by simp_rw [Tape.Up, ← smul_sub,tally_smul]; exact (by simpa only [mul_zero] using ENNReal.Tendsto.const_mul h (Or.inr (enorm_ne_top (x:=s))))
lemma Up.package (f : Tape α)(hf : Carried f w){F : ι→ℝ} (H : Tendsto F l (𝓝 s)): Up l w (fun i=>F i • f) (s • f) := by
 simp_rw [Tape.Up,← sub_smul,tally_smul]; refine multiplyZero (tally w f) hf ?_ tendsto_const_nhds; exact tendsto_iff_enorm_sub_tendsto_zero.mp H
lemma Up.sum (T : Finset γ){F : γ→ι→Tape α}{f : γ→Tape α} (h:∀ i∈T, Up l w (F i) (f i)): Up l w (fun i=>∑ v∈T,F v i) (∑ v∈T,f v):=by
 induction T using Finset.induction_on with
 | empty=> simpa only [Finset.sum_empty] using (by exact stays _ : Up _ _ (fun _=>(0:Tape α)) 0)
 | insert v t ht ih=> simp_rw [Finset.sum_insert ht]; exact added (h v (by simp)) (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))
lemma Up.bag (T : Multiset γ){F : γ→ι→Tape α}{f : γ→Tape α} (h:∀ i∈T, Up l w (F i) (f i)): Up l w (fun i=>YM.RegulatorIR.bag T (fun j=>F j i)) (YM.RegulatorIR.bag T f):=by
 induction T using Multiset.induction_on with
 | empty=> simpa only [bag_empty] using (by exact stays _ : Up _ _ (fun _=>(0:Tape α)) 0)
 | cons v t ih=> simp_rw [bag_cons]; exact added (h v (by simp)) (ih (fun i hi=>h i (by simp [hi])))
lemma Up.braid {G : ι→Tape β}{g : Tape β} (H : Up l w F f)(P : Up l V G g)(hx : Carried f w)(hy : Carried g V): Up l (loom w V) (fun i=> Tape.braid (F i) (G i)) (Tape.braid f g):= by
 let u:=fun i=> tally w (F i -f); let v:=fun i=> tally V (G i -g); let x:= tally w f; let y:= tally V g
 have hr : Tendsto (fun i=> u i*(v i+y)+v i*x) l (𝓝 0):= by simpa only [add_zero] using (multiplyZero y hy H (show Tendsto (fun i=> v i+y) _ (𝓝 _) from by simpa only [zero_add] using! (P.add_const y))).add (multiplyZero x hx P (y:=fun _=> x) tendsto_const_nhds) -- parameter
 refine first_zero hr (fun i=>?_); rw [show Tape.braid (F i) (G i)-Tape.braid f g=Tape.braid (F i-f) (G i) + Tape.braid f (G i-g) from funext fun z=>by simp only [Tape.braid,Pi.sub_apply,Pi.add_apply]; ring]; apply (tally_add ..).trans; simp_rw [tally_braid]; apply add_le_add
 · exact mul_le_mul_right (calc tally V (G i)=tally V (G i-g + g) := by rw [sub_add_cancel]
                              _ ≤ _:=tally_add .. ) _
 exact le_of_eq (mul_comm ..)
-- fixed or varying target path. Need uniform op bound and entrywise convergence in norm.
lemma dominated {F : ι→α→ℝ≥0∞}{f : α→ℝ≥0∞}(h : ∀ x,Tendsto (F · x) l (𝓝 0)) (B : ∀ i x, F i x ≤ f x) (hs:∑' x,f x<∞) : Tendsto (fun i=>∑' x,F i x) l (𝓝 0):=by
 have he i : ∑' x,F i x<∞:= (ENNReal.tsum_le_tsum (B i)).trans_lt hs
 let t x:= (f x).toReal; let y i x:= (F i x).toReal
 have hv:Summable t:= ENNReal.summable_toReal hs.ne
 have hy i : ENNReal.ofReal (∑' x,y i x)=∑' x,F i x := by unfold y; rw [← ENNReal.tsum_toReal_eq (fun x => ((ENNReal.le_tsum x).trans_lt (he i)).ne), ENNReal.ofReal_toReal (he i).ne]
 simp_rw [←hy]; refine Eq.mp (congrArg (fun x=> Tendsto _ _ (𝓝 x)) ENNReal.ofReal_zero) (ENNReal.tendsto_ofReal ?_)
 have ht x : Tendsto (fun i=> y i x) l (𝓝 0):=ENNReal.toReal_zero ▸ (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp (h x)
 simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence (f:=y) (g:=fun _=>0) hv ht (Eventually.of_forall (fun i x=> by rw [Real.norm_of_nonneg (by unfold y; positivity)]; exact ENNReal.toReal_mono ((ENNReal.le_tsum x).trans_lt hs).ne (B i x)))
lemma Up.shift (K : ι→ Rows α β)(k : Rows α β) (B : ∀ i, Meter S w V A (K i))(D: Meter S w V A k)
   (H : ∀ x∈S, Up l V (K · x) (k x)) (h:Lower V)(hT : A<∞) (hF : ∀ i,Within S (F i))(hX:∀ i,Carried (F i) w)(hf : Within S f)(hx:Carried f w)(hU:Up l w F f): Up l V (fun i=>Tape.mix (F i) (K i)) (Tape.mix f k) := by
 let U i x:= ‖f x‖ₑ * tally V (K i x-k x); let R i:=tally w (F i-f)*A
 have hπ i : tally V (mix f (K i)-mix f k) ≤ ∑' x,U i x:= by
   rw [show mix f (K i)-mix f k=mix f (K i-k) from funext (fun y=> by rw [Pi.sub_apply,mix,mix,mix]; simp_rw [Pi.sub_apply,mul_sub]; exact ((Meter.mix_summable h hf (B i) hT hx y).tsum_sub (D.mix_summable h hf hT hx y)).symm)]; exact tally_mix ..
 let t x:=(‖f x‖ₑ * w x)*(A+A); have hp : Tendsto (fun i=>∑' x,U i x) l (𝓝 0):= by
   apply dominated (f:=t)
   · intro x; by_cases he : f x=0;
     · simp only [U,he,enorm_zero,zero_mul]; exact tendsto_const_nhds
     unfold U; simpa only [mul_zero] using ENNReal.Tendsto.const_mul (H x (hf x he)) (Or.inr (enorm_ne_top (x:=f x)))
   · intro i x; unfold U t; by_cases he:f x=0
     · simp only [he,enorm_zero,zero_mul,le_refl]
     rw [mul_assoc,mul_add]; exact mul_le_mul_right ((tally_sub ..).trans (add_le_add (B i x (hf x he)) (D x (hf x he)))) _
   unfold t; rw [ENNReal.tsum_mul_right]; exact ENNReal.mul_lt_top hx (by finiteness)
 refine first_zero (x:=fun i=>R i+∑' x,U i x) (by simpa only [add_zero] using (multiplyZero A hT hU tendsto_const_nhds).add hp) (fun i=>?_); rw [show mix (F i) (K i)-mix f k=mix (F i-f) (K i)+(mix f (K i)-mix f k) from by rw [sub_mix (hF i) hf (B i) hT h (hX i) hx]; abel]; exact (tally_add ..).trans (add_le_add ((B i).mix_cost ((hF i).sub hf)) (hπ i))
lemma Up.mixture {K : Rows α β}(B : Meter S w V A K)(h:Lower V)(hT : A<∞)(hF : ∀ i,Within S (F i))(hX:∀ i,Carried (F i) w)(hf:Within S f)(hx:Carried f w)(H:Up l w F f): Up l V (fun i=>mix (F i) K) (mix f K):= Up.shift (fun _=>K) K (fun _=>B) B (fun _ _=>Up.stays _) h hT hF hX hf hx H
lemma Up.cash (H : Up l 1 F f)(x : α): Tendsto (fun i=> F i x) l (𝓝 (f x)):= tendsto_iff_enorm_sub_tendsto_zero.mpr (first_zero H (fun i=> by simpa only [Pi.one_apply,ENNReal.coe_one,mul_one,Pi.sub_apply] using Tape.point 1 (F i-f) x))
end YM.RegulatorIR.Tape

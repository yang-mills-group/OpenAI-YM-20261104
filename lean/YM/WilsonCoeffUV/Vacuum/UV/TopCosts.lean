import YM.WilsonCoeffUV.Vacuum.UV.Schedule
/-!
# Recurrence budget with both TOP contributions

Further polynomial losses exactly charged; costs before L on arc demand.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free Extension.UV.Linear PathCost
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{n N M e m i k r b j l:ℕ}{U V W T :Credit}
namespace Realm
variable (R:Realm G e U)
abbrev horizonC (N m:ℕ):= actionW R.draws R.paid N m

def Present (R:Realm G e U) (m i j N:ℕ)(h:R.anchor≤m)(V:Credit):= Amber terrain (R.mint m h).σ (R.cash V m) (R.horizonC N m i j)
def Same (R:Realm G e U) (m i j b N M:ℕ)(h:R.anchor≤m)(V:Credit):= PairA (R.mint m h).σ (R.cash V m) (R.tempC m b) (R.horizonC N m i j) (R.horizonC M m i j)
end Realm
open Realm
variable (G e U)
def Costs (V:Credit)(i j:ℕ):Prop:=∀ R:Realm G e U,∀ m (h:R.anchor≤m) N,m≤N  →  R.Present m i j N h V
def Traces (V:Credit)(i j:ℕ):Prop:=∀ R:Realm G e U,∀ m (h:R.anchor≤m) b N M,m≤b → b≤N → b≤ M →  R.Same m i j b N M h V
variable {G e U}
lemma Traces.more {k r:ℕ}(p: Traces G e U V k r)(h:∀ y:ℝ,1≤y  →  V.buy y ≤ W.buy y): Traces G e U W k r:= fun R m z b N M hb hp hx=> (p R m z b N M hb hp hx).up (h (R.y m) (R.depth m z)) (trail_pos ..).le
lemma Traces.commands (p:Traces G e U V i j): Costs G e U V i j:= fun R m h N he=> (p R m h N N N he le_rfl le_rfl).pose
lemma PairA.graded {X:Type*}{u v σ θ a:ℝ} {P Q: Ten ℝ (Cloth X) j}(h:PairA u a σ P Q)(hp:σ≤θ)(ht:v≤ u): PairA v a θ P Q:= ⟨h.pose.mono ht,h.vale.mono ht,(h.visit.mono ht).le (mul_le_mul_of_nonneg_left hp h.nn)⟩
lemma elderT (R: Realm G e U)(u:R.anchor≤m)(v:m<b){j0:ℕ}(p:b≤N)(q:b≤M)(hb:∀ i j,lowerGrade i j k j0  →  Traces G e U W i j) : (R.mint m u).runs k j0 (R.cash (doubling U) m*R.tempC m b) (R.cash (jump U W) m) N M:= by
    intro i j H
    have h : R.anchor≤m+1:=by omega
    have ht:= (hb i j H R (m+1) h b N M v p q)
    exact ((ht.up (R.shift_z W u) (trail_pos ..).le).graded (R.also_temp u) (R.crossing m u))
private lemma top (R:Realm G e U)(h:R.anchor≤N)(p:k≤e)(b:r+2≤ e+2): R.Present N k (r+2) N h U:=by
   let H:= R.mint N h
   have he := ore_buy G (r+2) k H.σ H.width
   unfold Realm.Present horizonC actionW; rw [story_top]; exact (show Amber terrain _ _ (lop (moon G) k (r+2)) from he.le ((R.taxes N h).stowage k _ p b))
lemma recurring (hk:k+1≤e)(hr:r≤ e)(hw: ∀ i j, lowerGrade i j (k+1) (r+2) →  Costs G e U W i j): ∃V:Credit, Costs G e U V (k+1) (r+2):=by
   let F:= jump U W
   let Z:=U.prodC (F.powC (carryD G k r)); let V:= U.plus Z
   refine ⟨V.behind,fun R m h N he=>?_⟩
   suffices H: ∀ i,i ≤ N → ∀ hv:R.anchor ≤ i, Amber terrain (R.mint i hv).σ (Credit.tower V Credit.liftA (R.y i)) (R.horizonC N i (k+1) (r+2)) by exact (H _ he h).le (Credit.donation _ _ Credit.lift_good _ (R.depth _ h))
   intro i hi
   induction hi using Nat.decreasingInduction with
   | self=>
       intro p; have hp:= R.depth N p
       exact (top R p hk (by omega)).le (le_trans (Credit.thickens _ hp) (Credit.raised V Credit.liftA _ Credit.lift_good hp))
   | of_succ i he' IH=>
       intro p
       let y:=R.y i; let z:=R.y (i+1); let C:= PathCost.arc R.draws.S i
       let H:=R.mint i p
       have hy:1≤ y:= R.depth _ p; have hh:= R.taxes i p; have hf:= R.crossing i p
       let B:= V.tower Credit.liftA z
       let x:= R.cash F i
       have he:1≤ x := F.purchase hy
       have hu:= toll_energy H R.hG R.green he' (hh.enough r hr) B x he (show ∀ i' j,lowerGrade i' j (k+1) (r+2) →  Amber terrain _ _ (R.horizonC N (i+1) i' j) from fun i' j w=> (((hw i' j w R _ (by omega) N he' : Amber ..)).le (R.shift_z _ p)).mono hf) ((IH (by omega)).mono hf)
       have hB:0 ≤ B:= (IH (by omega)).1
       apply hu.le
       have h₁: H.gear.gain r /(loose R.draws i).L.val ≤ Real.exp (-C/4):= (hh.gain _ hr).trans (Real.exp_le_exp.mpr (by have Q:0≤C:= arc_nn ..; linarith))
       have h₂ : carryF G k r H.gear * x^carryD G k r ≤ V.buy y:= by
           calc
            _ ≤ U.buy y*x^carryD G k r:=mul_le_mul_of_nonneg_right (hh.burst k _ hk hr) (pow_nonneg (by linarith) _)
            _ ≤ _:= le_trans (le_of_eq (show _= Z.buy y by rw [show Z=U.prodC (F.powC _) from rfl,Credit.products,Credit.power])) (Credit.thickened U hy)
       have hh:(H.gear.gain r*B / (loose R.draws i).L.val:ℝ)= H.gear.gain r/ (loose R.draws i).L.val * B:=by ring
       rw [hh]; exact (add_le_add (mul_le_mul_of_nonneg_right h₁ hB) h₂).trans (Credit.step_cap _ hy (R.depth (i+1) (by omega)) (R.age _ _ p (by omega)) (arch_pos ..))

lemma tally_trace (hk:k+1≤e)(hr:r≤ e)(hw:∀ i j,lowerGrade i j (k+1) (r+2) →  Traces G e U W i j) (hx: Costs G e U V (k+1) (r+2)) : ∃T: Credit,Traces G e U T (k+1) (r+2):=by
   let F:= jump U W
   let Z:= ((U.prodC (F.powC (carryD G k r))).prodC (Credit.unit.plus (jump U V))).prodC (doubling U)
   let S:=(V.plus V).plus Z
   refine ⟨V.plus S.behind,fun R m h b N M he hp hq=>?_⟩
   have hu:= R.depth m h
   refine ⟨(hx R m h N (by omega)).le (Credit.thickens _ hu),(hx R m h M (by omega)).le (Credit.thickens _ hu),?_⟩
   suffices H : ∀ i, i≤b → ∀ hv:R.anchor≤ i, Amber terrain (R.mint i hv).σ (Credit.tower S Credit.liftA (R.y i)*R.tempC i b) (R.horizonC N i (k+1) (r+2)-R.horizonC M i (k+1) (r+2)) by exact (H m he h).le (mul_le_mul_of_nonneg_right ((Credit.donation S Credit.liftA Credit.lift_good _ hu).trans (Credit.thickened _ hu)) (trail_pos ..).le)
   intro i hi
   induction hi using Nat.decreasingInduction with
   | self=>
      intro q; rw [Realm.tempC,trail_end,mul_one]
      have hz:= R.depth b q; refine ((hx R b q N hp : Amber ..).sub (hx R b q M hq)).le (le_trans ?_ (Credit.raised S Credit.liftA _ Credit.lift_good hz)); exact (Credit.fuel _ _ hz).trans (Credit.thickens _ hz)
   | of_succ i he' IH=>
      intro q
      let y:=R.y i; let z:=R.y (i+1); let C:= PathCost.arc R.draws.S i
      let H:= R.mint i q
      have hy:1≤ y:= R.depth _ q; have hz:= R.depth (i+1) (by omega)
      have ht:= R.taxes i q
      have hd:= R.crossing i q
      let x:= F.buy y
      have ha:1≤ x:= F.purchase hy
      let Q:= (jump U V).buy y
      let B:= Credit.tower S Credit.liftA z
      have hl:= R.dominates_both q he'
      let θ:= R.cash (doubling U) i*R.tempC i b
      have hQ t (ha:b≤t): Amber terrain H.past Q (R.horizonC t (i+1) (k+1) (r+2)):= ((hx R _ (by omega) _ (show i+1≤t from by omega) : Amber ..).le (R.shift_z _ q)).mono hd
      have hJ: Amber terrain H.past _ (R.horizonC N (i+1) (k+1) (r+2)-R.horizonC M (i+1) (k+1) (r+2)):= (IH (by omega)).mono hd
      apply (toll_range H R.hG R.green Q x (B*R.tempC (i+1) b) θ ha he' hp hq hl.1 hl.2 (ht.enough r hr) (elderT R q he' hp hq hw) (hQ _ hp) (hQ _ hq) hJ).le
      have h₁ : H.gear.gain r*(B*R.tempC (i+1) b) / (loose R.draws i).L.val ≤ Real.exp (-C/4)*B*R.tempC i b:= by
          rw [show H.gear.gain r*(B*R.tempC (i+1) b) / _= H.gear.gain r / (R.draws.S.block i).val*(B*R.tempC (i+1) b) from (show _= H.gear.gain r / (R.draws.S.block i).val*(B*R.tempC (i+1) b) from by change H.gear.gain r*_/(R.draws.S.block i).val=_; ring)]
          refine (mul_le_mul_of_nonneg_right (ht.gain r hr) hJ.1).trans_eq ?_
          rw [show R.tempC i b=Real.exp (-C/4)*R.tempC (i+1) b from one_leg .., show -PathCost.arc _ _/2= -C/4+ -C/4 by unfold C; ring,Real.exp_add]; ring
      have h₂ : carryF G k r H.gear*x^carryD G k r*(1+Q)*θ≤ S.buy y*R.tempC i b:= by
          have hv:= (jump U V).purchase hy
          have hf : 0≤ 1+Q := by unfold Q; linarith
          have hm:0≤ θ:=mul_nonneg (zero_le_one.trans ((doubling U).purchase hy)) (trail_pos ..).le
          let v:=U.buy y*x^carryD G k r
          calc
           _ ≤ (U.buy y*x^carryD G k r)*(1+Q)*θ:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (ht.burst _ _ hk hr) (pow_nonneg (by linarith) _)) hf) hm
           _ ≤ Z.buy y * R.tempC i b:= by
             unfold Z; rw [Credit.products,Credit.products,Credit.products,Credit.power]; unfold θ; rw [← mul_assoc];
             have hj:= Credit.fuel Credit.unit (jump U V) hy; rw [Credit.unit_cost] at hj; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj (mul_nonneg (zero_le_one.trans (U.purchase hy)) (pow_nonneg (zero_le_one.trans ha) _))) (zero_le_one.trans ((doubling U).purchase hy))) (trail_pos ..).le
           _ ≤ _:= mul_le_mul_of_nonneg_right (Credit.thickened _ hy) (trail_pos ..).le
      refine le_trans (add_le_add h₁ h₂) ?_
      rw [←add_mul]; exact mul_le_mul_of_nonneg_right (Credit.step_cap _ hy hz (R.age _ _ q (by omega)) (arch_pos ..)) (trail_pos ..).le
end YM.WilsonCoeffUV.Bank

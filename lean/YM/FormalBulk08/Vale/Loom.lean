import YM.FormalBulk08.Vale.Turns
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Vale
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
def GaugeWave (l:ℕ)(p:Waves V) : Prop :=∀ n e r,p n e r≠0 → r +2*n≤l+3*e
lemma ample {T S:Waves V} (h:GaugeWave i T)(hs:GaugeWave m S): GaugeWave (i+m) (doubled T S):= by
   intro n e r hx; by_contra hp; apply hx; unfold doubled; apply Finset.sum_eq_zero; intro a ha; apply Finset.sum_eq_zero; intro b hb; apply Finset.sum_eq_zero; intro c hc; have he:= Finset.HasAntidiagonal.mem_antidiagonal.mp c.property; simp only [Finset.HasAntidiagonal.mem_antidiagonal] at ha hb
   by_cases ht:T a.1 b.1 c.val.1=0
   · rw [ht,show clutch (0:Tile V _) (S a.2 b.2 c.val.2)=0 from funext fun i=>by simp [clutch],sand_nil,length_void]
   rw [show S a.2 b.2 c.val.2=0 from Classical.byContradiction (fun hx=> by apply hp; apply Classical.not_not.mp; have := h a.1 b.1 c.val.1 ht;have :=hs a.2 b.2 c.val.2 hx;omega), show clutch _ (0:Tile V _)=0 from funext (fun v=>by simp [clutch]),sand_nil,length_void]
lemma slender {V:Type*}: GaugeWave 0 (pebbleW V) := by
    intro n e r h; by_contra! hu; apply h; unfold pebbleW;funext v;by_cases ht:n=0
    · rw [if_pos ht]; exact if_neg (by omega)
    rw [if_neg ht];rfl
lemma hiked {P:I→ Waves V}{L: List I}{l:I→ℕ}(h:∀ i∈L,GaugeWave (l i) (P i)): GaugeWave (L.map l).sum (campfire P L):= by
   induction L with
   | nil=>exact slender
   | cons i l ih=>exact ample (h i List.mem_cons_self) (ih (fun i hx=>h _ (List.mem_cons_of_mem _ hx)))

lemma edema [Fintype V] (f:Pap V)(P:I→Pap V)(t:I→ℕ)(K:List I)(hp:∀ i∈K,Young (rancho (P i)) (t i))(q: V→V→ℝ)(hx: Fiery (rancho f))(h:∀ i j,q i j=q j i)(hu:coeff 0 f=0)(L:Pap V)(he:L=(K.map P).prod)(ht:Young (rancho L) (K.map t).sum):
    let U:=fun i=> flare q f (P i); let p:= (K.map U).prod; let A:= flare q f L; let B:= A-p; let M:= (K.map t).sum
    GaugeWave M (posting B) ∧
    posting B 0 =0 ∧
    ∀ s e r, posting B (s+1) e r=((s+1:ℕ):ℝ)⁻¹ • (stare q (posting B s e (r+1+1))+(2:ℝ) • brawl q (posting (coal q f)) (posting B) s e r+(2:ℝ) • collision q (fun i=>posting (U i)) K s e r):= by
   intro U p A B M
   have hR {Y:Pap V} {k:ℕ}(v:Young (rancho Y) k) : GaugeWave k (Lava.posting (flare q f Y)) := by rw [posting_dipper q f Y hu h,posting_swim q f hu]; exact fun n e r v'=> (youth_egg q v hx n e r v').2
   obtain ⟨hd,hP⟩:= crew_cause q f P K hu h L he
   have hQ : GaugeWave M (posting p):= by unfold p; rw [←campH];apply hiked; exact fun i hi=> hR (hp i hi)
   refine ⟨?_,?_,?_⟩
   · intro n e r hv; by_contra hg; apply hv
     have ht' : posting p n e r=0:= Classical.byContradiction (fun he=> hg (hQ n e r he));rw [show posting B= posting A-posting p from postSub A p, Pi.sub_apply,Pi.sub_apply,Pi.sub_apply, ht',sub_zero];exact Classical.byContradiction fun he => hg (hR ht n e r he)
   · funext e r; rw [Lava.posting,read_initial]; have he:early B=0:=hd; rw [he,_root_.map_zero,marble_zero];rfl
   intro s e r
   change shaft Polynomial.derivative' B=Wick.cinder q B+2*crossHeat q (coal q f) B+2*pile q U K at hP; have he:=congr_arg (fun z:Heat ℝ V=>readSlice z e s) hP; rw [read_diff] at he; simp_rw [two_mul,read_add,read_track] at he
   have hQ := congr_arg (marble r) he;clear he
   simp_rw [←canyon_eq, _root_.map_add,canyon_eq, marble_stare, read_cross, stone_crest] at hQ -- caution map_add includes LHS arithmetic index s+
   have hh : (((s+1:ℕ):ℝ) • Lava.posting B (s+1) e r)= marble r (readSlice B e (s+1)*(↑s+1:TypeR V)):= by simp only [←canyon_eq, Lava.posting,←canyon_eq, ←map_smul];congr 1; simp [MvPolynomial.smul_eq_C_mul,mul_comm]
   rw [← hh] at hQ; change ((s+1:ℕ):ℝ) • Lava.posting B (s+1) e r = (stare q (Lava.posting B s e (r+1+1))+ _) + (Lava.posting (pile q U K) s e r+Lava.posting (pile q U K) s e r) at hQ; simp_rw [pile_cast] at hQ; rw [two_smul ℝ, two_smul ℝ, ← show _ = stare q _+ _+ _ from hQ,inv_smul_smul₀ (by positivity : ((s+1:ℕ):ℝ)≠ 0)]
where postSub (p q:Heat ℝ V): posting (p-q)= posting p-posting q:=by funext i j r; simp only [Lava.posting, Pi.sub_apply,readSlice,map_sub, Polynomial.coeff_sub,←canyon_eq]
end YM.FormalBulk08.Vale

import YM.FormalBulk08.Dove.Card

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dove
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {I Z:Type}{G:Gauge}{K:KernelChoices}{E:ℕ}
-- spires g_{j+1}/g_j = bookH. backwards wake.
def spires (K:ℕ→Pence)(i:ℕ): ℕ→Pence
   | 0=> 1
   | j+1=> propel (bookH (K (i+j))) (spires K i j)
def slopes (K:ℕ→Pence)(j:ℕ): ℕ→Pence
   | 0=>1
   | i+1=> propel (nextU (K (j-(i+1)))) (slopes K j i)
-- one family centered at k. Expose where read.
def expanse (K:ℕ→Pence)(k i:ℕ):= if k≤ i then spires K k (i-k) else slopes K k (k-i)
lemma fill_expanse (K:ℕ→Pence)(i): expanse K i i=1:=by simp [expanse,spires]
lemma expanses_spires (K:ℕ→Pence)(i j)(h:i≤j): expanse K i j=spires K i (j-i):=if_pos h
lemma expanses_slopes (K:ℕ→Pence)(i j)(h:i≤j): expanse K j i=slopes K j (j-i):=by by_cases hx:i=j; simp [hx,fill_expanse,slopes]; exact if_neg (by omega)
lemma expanses_reverse (K:ℕ→Pence)(k i:ℕ): expanse K k i= propel (nextU (K i)) (expanse K k (i+1)) := by
    by_cases he:k≤ i
    · rw [expanses_spires _ _ i he, expanses_spires _ k (i+1) (by omega), show i+1-k=i-k+1 by omega,spires, show k+(i-k)=i by omega];exact (invited ..).1.symm
    rw [expanses_slopes _ i k (by omega), expanses_slopes _ (i+1) k (by omega), show k-i=k-(i+1)+1 by omega, slopes,show k-(k-(i+1)+1)=i by omega]
lemma expanses_link (K:ℕ→Pence)(k i:ℕ): expanse K k (i+1)= propel (bookH (K i)) (expanse K k i) := by rw [expanses_reverse K k i];exact (invited ..).2.symm

lemma Pact_lift {X Z:Type}{τ:Time X}{t:Time Z}{δ:X→ℝ}{g:Z→X}{D:Z→ℝ}(p:Soft t (fun i=> τ.day (g i))){f u : X→ℝ}(h:Pact τ δ f u)(e:∀ i, δ (g i)≤D i): Pact t D (fun i=> f (g i)) (fun i=>u (g i)) := by
    refine ⟨town_fold p h.left,town_fold p h.right,?_⟩; obtain ⟨C,c,h,E⟩:=h.blur; exact ⟨_,town_fold p c,fun i=>h (g i),fun i=>(E (g i)).trans (mul_le_mul_of_nonneg_left (e i) (h _))⟩
variable {ρ:ChartRatio G}{W: Lab G K I}
-- universal window: may take X to be a master search space all x. age valued at measurement point Z
namespace Lab
variable (u:Use W ρ E)(v:LocalRatio ρ)(a:hue G)(hs:G.Simple)
variable (T:Z→transferPoint W) -- don't use
-- Projection to arbitrary transferPoint
include v hs
lemma pesto (i:transferPoint W)(N)(he:i.b < N): Fresh (bandK ρ a W (fun _=>N) i.a i.b) ∧ Still (bandK ρ a W (fun _=>N) i.a i.b):= by
   let V:=W.V i.a; have ht:= genu V (W.wood i.a) (W.toEmpire.bill i.a) ρ a v hs (N:=N) (i:=i.b+1) he; exact sig_mat a _ (creed _ _ _ _ _ ht.toStory (V.clock.adm _) v) K.penalty_pos (V.clock.adm _)

omit v hs
-- any footing whose τ age carries the spread
structure Voyage (W:Lab G K I)(s:Z→ℕ) where
   bed:Z→Leaf W.scrolls
   summit:Z→ℕ
   top:Z→ℕ
   extra: ∀ i,summit i ≤ top i
   high:∀ i,(bed i).b+s i ≤ summit i
variable {s:Z→ℕ}(F:Voyage W s)
namespace Voyage
abbrev test (E:Voyage W s) (z:Z) (i:ℕ)(h:(E.bed z).b ≤ i)(e:i<(E.bed z).b + s z): transferPoint W:= ⟨⟨(E.bed z).a,i, (E.bed z).zone.trans h⟩,E.summit z,E.top z,e.trans_le (E.high _),E.extra _⟩
def Dend (z:Z):= ratioR (W.V (F.bed z).a).S (F.summit z) ((F.bed z).b + s z) targetPower
def ridge (i: Walk s): transferPoint W:= F.test i.z ((F.bed i.z).b+i.i) (Nat.le_add_right ..) (by have :=i.away;omega)
def slide (i: Walk s): transferPoint W:= F.test i.z ((F.bed i.z).b + s i.z - (i.i+1)) (by have :=i.away;omega) (by have :=i.away;omega)
abbrev spine (ρ:ChartRatio G)(a:hue G)(M: Z→ℕ)(x:Z):= bandK ρ a W (fun _=>M x) (F.bed x).a
lemma ratio_test (F:Voyage W s)(i:Z)(j:ℕ)(h:(F.bed i).b ≤ j)(e:j<(F.bed i).b+s i): spinR targetPower (F.test i j h e) ≤ Dend F i:= by
   let V:= (W.V (F.bed i).a).S; change ratioR V (F.summit i) _ _≤ ratioR V _ _ _; change ratioR V (F.summit i) (j+1) _≤ _; unfold ratioR;gcongr
   all_goals first|exact targetPower_pos.le|exact V.strictAnti.antitone e|exact V.a_pos _|exact (V.a_pos _).le|exact div_nonneg (V.a_pos _).le (V.a_pos _).le
variable (τ:Time Z)
-- window demands guaranteed e.g. by Y charges. only need coarse age + length in spread
include u
lemma runway (p:Soft τ (fun z=> (chron _).day (F.bed z)))(h: Soft τ (fun i=> sowing (W.V (F.bed i).a).S (F.bed i).b ((F.bed i).b+s i))):
   Soft τ (fun i=>(s i:ℝ))∧ Soft (tcash τ s) (fun i=>(purseP W).day (F.ridge i)) ∧ Soft (tcash τ s) (fun i=>(purseP W).day (F.slide i)) := by
    obtain ⟨B,b,A⟩:= u.liable.distance
    have hh (f:Walk s→ℕ)(hf:∀ i,(F.bed i.z).b≤f i)(h':∀ i,f i <(F.bed i.z).b+s i.z): Soft (tcash τ s) (fun i=>(purseP W).day (F.test i.z (f i) (hf i) (h' i))) := by
        refine (((soft_coin τ B).times (p.plus h)).reach (fun i:Walk s=> i.z)).below (fun i=>?_); rw [abs_of_nonneg ((purseP W).good _)];
        let n:= (F.bed i.z).b;let m:= n+s i.z; let x:=(F.bed i.z).a; let S:= W.scrolls.mesh x
        refine le_trans (A x (f i) n (F.bed i.z).zone (hf i)) ?_; have he: sowing S n (f i)≤sowing S n m:= by have hx:= sowing_plus S (i:=f i) (j:=m) (h' i).le; unfold sowing at *; linarith
        exact (mul_le_mul_of_nonneg_left (add_le_add_right he _) b).trans (le_abs_self _)
    have hr (i:Walk s):=(F.ridge i).wing
    refine ⟨?_, hh _ (fun i=>by have :=i.away;omega) (fun i=>by have :=i.away;omega), hh _ (fun i=>by have :=i.away;omega) (fun i=>by have :=i.away;omega)⟩ -- explicit
    refine (h.times (soft_coin τ (Real.log (2:ℝ))⁻¹)).below fun i=>?_ ; rw [Nat.abs_cast]; apply le_trans _ (le_abs_self _); rw [←div_eq_mul_inv]; exact (le_div_iff₀ (Real.log_pos (by norm_num))).mpr (sowing_green ..)
end Voyage
end Lab
end YM.FormalBulk08.Dove

import YM.FormalBulk08.Wine.Ink

/-! Canter to/from all alphabet grades, not horizontal assumption. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wine
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa Gorge City Cork
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {V I : Type} (H U : Pence)

def bill (e j r : ℕ) := coeff (e-j) (H^j*U^r)
def stamp (T:OrbitV V)(e r:ℕ):Tile V r := ∑ j∈Finset.range (e+1),bill H U e j r • T j r
lemma paid_nil (T:OrbitV V)(r)(h:Fresh H)(g:Fresh U): stamp H U T 0 r=T 0 r := by rw [stamp]; have hx:= (Fresh.mul (h.pow 0) (g.pow r));change bill H U 0 0 r=1 at hx;simp [hx]
variable [Fintype V]
lemma term_read (j r n:ℕ) (p:TypeR V) (h:j≤n) : MvPolynomial.homogeneousComponent r (coeff n (canter H U V (C p* X^j)))= bill H U n j r • MvPolynomial.homogeneousComponent r p:= by
   rw [← MvPolynomial.sum_homogeneousComponent p]; simp_rw [map_sum,Finset.sum_mul,map_sum,Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [tremble H U i j _ (MvPolynomial.homogeneousComponent_isHomogeneous ..), coeff_mul_X_pow',if_pos h,coeff_mul_C,worm,coeff_map];rw [←MvPolynomial.smul_eq_C_mul,map_smul]; rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.homogeneousComponent_isHomogeneous ..)]; split_ifs with hp
   · subst i;rfl
   simp
lemma stamp_book (p:Pap V): rancho (canter H U V p)=stamp H U (rancho p) := by
    ext e r v; refine congr_fun ?_ v; apply facade_unique (marble_agate _ _) (show Agate (stamp H U (rancho p) e r) from Agate.sums _ fun _ _=> (marble_agate _ _).smul _);rw [marble_grade,(steam H U (dict p e)).apex, map_sum,map_sum,map_sum, stamp,map_sum]; apply Finset.sum_congr rfl; intro j hj; rw [term_read H U j r e _ (Nat.le_of_lt_succ (Finset.mem_range.mp hj)),map_smul,rancho,marble_grade]
lemma motor_size {F: Rays V→ Rays I}(i:I)(j:ℕ):(coeff j (motor F i)).IsHomogeneous (j+1):= by rw [motor,after_one, Nat.add_comm]; apply paste_grade
omit [Fintype V] in
lemma morph {G : Gauge}{n: Side}{p t:Pap (wire G n)}(s x)(h:Rite p t s x)(hp:H*U=1): Rite (canter H U (wire G n) p) (canter H U (wire G n) t) s x:= by intro I inst a b k ha hb ht hY hz hh he; rw [←calming H U hp (motor a) motor_size, ← calming H U hp (motor b) motor_size,h I a b k ha hb ht hY hz hh he]
omit [Fintype V] in
lemma tale {G : Gauge}{S:Pot G}{M: Row (TypeFace 2) (TypeFace 2)}(h : Story S M)(hA:Still H)(hB:Still U)(ha:Fresh H)(hb:Fresh U)(hr:H*U=1): Story (stamp H U S) M:= by
   have hp: Vivid (stamp H U S):= by
       refine ⟨fun j r=> up_sums _ _ (fun i _=> ?_),fun j r=> Agate.sums _ (fun i _=> ?_),fun j r he=> ?_⟩
       · intro x v; simp only [Pi.smul_apply]; rw [h.civil i r x v]
       · exact (h.agate i r).smul _
       unfold stamp at he;by_contra! ht; refine he (Finset.sum_eq_zero ?_); intro i hi; rw [Finset.mem_range] at hi; by_cases hs : S i r=0
       · rw [hs,smul_zero]
       rw [bill, (hA.pow i|>.mul (hB.pow r)) _ (by have :=h.valence i r hs;omega), zero_smul]
   have hx{r:ℕ}{I:Type}{V : Finset I}{U:I→Tile (edgeL G) r}(hu:∀ i∈V,∃ s C:ℝ,0<s∧Bail (fame _) s (U i) C): ∃ s:ℝ,0<s ∧ ∀ i∈V,∃ C,Bail (fame _) s (U i) C:= by
        induction V using Finset.induction with
        | empty=> exact ⟨1,by simp,by simp⟩
        | @insert i V he ih=>
           obtain ⟨s,C,hs,hC⟩:=hu i (Finset.mem_insert_self ..); obtain ⟨z,hz,h⟩:=ih fun x h=> hu x (Finset.mem_insert_of_mem h)
           refine ⟨min s z,lt_min hs hz,fun j hj=>?_⟩
           rcases Finset.mem_insert.mp hj with rfl|hj; exact ⟨C,hC.shrink (min_le_left ..)⟩
           obtain ⟨K,hK⟩:=h j hj;exact ⟨K,hK.shrink (min_le_right ..)⟩
   have he j r (i:ℕ): ∃ s C:ℝ,0<s∧Bail (fame _) s (bill H U j i r • S i r) C:= by obtain ⟨s,C,hs,hC⟩:=h.fare i r; exact ⟨s,_,hs,hC.smul _⟩
   have heq n: stone (stamp H U S) n=canter H U _ (stone S n) := by
       symm; apply vine_eq hp n
       · intro j r i; rw [stamp_book]; simp_rw [stamp]; obtain ⟨s,hs,hC⟩:= hx (V:=Finset.range (j+1)) (fun v _=>he j r v)
         choose! C H using hC; rw [cum_sums _ _ _ _ H hs.le];apply Finset.sum_congr rfl;intro l _; rw [h.flower _ _ i]; exact cum_smul .. |>.symm
       intro j; have HJ e: rancho (stone S n) e 0=0:= (marble_eq_zero_iff _ _).mpr (by rw [sow_coeff,sow,map_sum];exact Finset.sum_eq_zero fun l _=> MvPolynomial.homogeneousComponent_of_mem (facade_grade _ _)|>.trans (if_neg (by omega)))
       change rancho (canter H U (wire G n) _) j 0=0; rw [stamp_book]; simp [stamp,HJ]
   refine {hp with
      ink:=?_
      fare:=fun j r=>?_
      civic:= fun n s x=> heq n ▸ morph H U s x (h.civic n s x) hr }
   · rw [paid_nil H U S 2 ha hb,h.ink]
   obtain ⟨s,hs,hC⟩:= hx (V:=Finset.range (j+1)) (fun v _=> he j r v)
   choose! C H using hC; exact ⟨s,_,hs,bail_many _ _ C H⟩
end YM.FormalBulk08.Wine

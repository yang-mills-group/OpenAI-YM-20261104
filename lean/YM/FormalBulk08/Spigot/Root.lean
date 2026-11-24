import YM.FormalBulk08.Spigot.Slope
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type*}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}

abbrev zoom (v:Cover)(i:Axis)(z:ℤ):Cover:= Function.update v i z
lemma neigh (v:Cover)(i:Axis)(z:ℤ): zoom v i (z+1)=zoom v i z+step i:= funext fun j=>by by_cases h:j=i <;> simp [zoom,h]
lemma studio_cost (v:Cover)(i:Axis)(z:ℤ)(h:z.natAbs ≤ (v i).natAbs):size (zoom v i z)≤size v:= Finset.sum_le_sum fun j _=>by by_cases he:j=i <;> simp [zoom,he,h]
lemma studio_amount (v:Cover)(i:Axis):(v i).natAbs≤size v:=Finset.single_le_sum (f:=fun i=>(v i).natAbs) (fun _ _=>Nat.zero_le _) (Finset.mem_univ _)
lemma zoom_lock (v:Cover)(i k:Axis)(z:ℤ)(h:i≠k): zoom (v+step i) k z=zoom v k z+step i:= funext fun j=>by by_cases he:j=k <;> simp [he,zoom,Ne.symm h]

-- integrate on ℤ use succ and pred; transmit over signs
private def accr (f:ℤ→ℝ)(p:ℕ):ℝ:= ∑ i∈Finset.range p,f (i:ℤ)
private def debit (f:ℤ→ℝ)(p:ℕ):ℝ:= ∑ i∈Finset.range p,f (-(i:ℤ)-1)
def streamline (f:ℤ→ℝ)(x:ℤ):ℝ:=if 0≤x then accr f x.natAbs else -debit f x.natAbs
lemma stream_up (f:ℤ→ℝ)(p:ℕ): streamline f p=∑ i∈Finset.range p,f (i:ℤ):= by simp [streamline,accr]
lemma stream_down (f:ℤ→ℝ)(p:ℕ): streamline f (-(p:ℤ))= -∑ i∈Finset.range p,f (-(i:ℤ)-1):= by
    cases p with
    | zero=>simp [streamline,accr]
    | succ p=> rw [streamline,if_neg (by omega)]; congr!
lemma stream_credit (f:ℤ→ℝ)(p:ℤ): streamline f (p+1)=streamline f p+f p:= by
    cases p with
    | ofNat p=> exact (show streamline f ((p+1:ℕ):ℤ) = _ from (stream_up ..).trans ((Finset.sum_range_succ ..).trans (by rw [←stream_up]; rfl)))
    | negSucc p=>
      rw [show Int.negSucc p= -((p+1:ℕ):ℤ) by omega,show -((p+1:ℕ):ℤ)+1= -(p:ℤ) by omega,stream_down,stream_down,Finset.sum_range_succ]; rw [show -(p:ℤ)-1= -((p+1:ℕ):ℤ) by omega]; ring
lemma stream_scale (f:ℤ→ℝ)(b:ℝ)(p:ℤ): streamline (fun i=>b * f i) p=b*streamline f p:= by unfold streamline accr debit; split <;> simp [Finset.mul_sum]
lemma stream_defray (f:ℤ→ℝ)(p:ℤ)(h:∀ i,|f i|≤B): |streamline f p|≤ p.natAbs*B:= by
    have he:0≤B:= (abs_nonneg (f 0)).trans (h _)
    unfold streamline accr debit; split; swap;· rw [abs_neg]; exact (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (fun i _=> h _)).trans_eq (by simp))
    exact (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (fun i _=> h _)).trans_eq (by simp))
lemma stream_telescope (f:ℤ→ℝ)(p:ℤ): f p=f 0+streamline (fun i=>f (i+1)-f i) p:= by
    let g i:= f (i+1)-f i
    have hx:f 0=f 0+streamline g 0:= by simp [streamline,accr]
    have he z : f (z+1) = f 0+streamline g (z+1) ↔ f z=f 0+streamline g z:= by rw [stream_credit]; dsimp only [g]; constructor <;> intro h <;> linarith
    by_cases h:0≤p
    · have hz (n:ℕ): f n=f 0+streamline g n:= by
        induction n with
        | zero=> exact hx
        | succ n ih=> rw [Nat.cast_add,Nat.cast_one]; exact (he _).mpr ih
      exact_mod_cast (show f p=f 0+streamline g p from (show (p.natAbs:ℤ)=p by omega) ▸ hz p.natAbs)
    have hz (n:ℕ): f (-n:ℤ)=f 0+streamline g (-n:ℤ):= by
        induction n with
        | zero=>simpa only [Nat.cast_zero,neg_zero] using hx
        | succ n ih=> apply (he _).mp; rw [show -((n+1:ℕ):ℤ)+1=-(n:ℤ) by omega]; exact ih
    exact (show -(p.natAbs:ℤ)=p by omega) ▸ hz p.natAbs
abbrev Pillow:=Edge Cover→ℝ
def beadCurl (U:Pillow)(x:Cover)(i j:Axis):ℝ := U (x,i)+U (x+step i,j)-U (x+step j,i)-U (x,j)
def curlP (p:Face ℤ)(U:Pillow):=beadCurl U p.1 p.2.val.1 p.2.val.2
lemma weave (i j:Axis)(h:i≠j):∃ (a:PlaqAxes)(z:ℝ),|z|=1∧ ∀ U x,z*curlP (x,a) U= beadCurl U x i j:= by
    rcases lt_or_gt_of_ne h with h|h
    · exact ⟨⟨(i,j),h⟩,1,by norm_num,fun _ _=> by rw [one_mul]; rfl⟩
    refine ⟨⟨(j,i),h⟩,-1,by norm_num,fun U x=>?_⟩; change (-1)*beadCurl U x j i= _; unfold beadCurl;ring
end YM.FormalBulk08.Spigot

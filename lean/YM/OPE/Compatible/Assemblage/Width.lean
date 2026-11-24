import YM.OPE.Compatible.Assemblage.Reserve
import YM.Work.I01
/-!
# Recovery and group width at δ radius

Polynomial log budget cannot use the B² mixing threshold for charging
intermediate *grouping* covers. And the group pays for a line not a
ball. These are the torus estimates (adapted lower bound from Work.I01,
using real gap spacing factors adjustable independently vs account, to
state later uniform sched price). Apply at every pre-capture level;
once failing the recovery criterion at next output regroup there with
(linear) upper price.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace YM.Lattice.Corona
open Relation
variable {ι : Type*} {n : Side} {b l : ℕ}
-- charge in line units
lemma linear_lane (h:0<b) (x y:Site n) (hp:separation x y≤ l*b) : coverNumber b ({x,y}:Support n) ≤ 81*(l+1):=by
    induction l generalizing y with
    | zero=> refine (MergeProof.Ribbons.ManyCopies.pairCover h x y 0 hp).trans (by decide)
    | succ l ih=>
      let z:= line x y (l*b)
      have he : separation x z≤ l*b:= (show separation (line x y 0) z ≤ l*b-0 from line_dist _ _ _ _ (Nat.zero_le _))|>.trans_eq (Nat.sub_zero _) |> (fun he=> line_home x y ▸ he)
      have ht : separation z y ≤ 1*b:=by
         have hf:= line_dist x y (l*b) ((l+1)*b) (by rw [Nat.add_mul];omega)
         rw [line_end x y hp] at hf; rw [Nat.add_mul] at hf; unfold z; omega
      let P:Support n:={x,z}; let Q:Support n:={z,y}
      refine (cover_mono (show ({x,y}:Support n) ⊆ P∪Q from (by simp [P,Q])) b).trans ((meets_sum (x:=z) (by simp [P]) (by simp [Q]) b).trans ((add_le_add (ih z he) (MergeProof.Ribbons.ManyCopies.pairCover h z y 1 ht)).trans ?_))
      simp only [Nat.mul_add]; norm_num
lemma clearance_units (o : ι→Site n)(F : Finset ι)(H:Support n)(h : 0<b)
    (hsep : ∀ i∈ F,∀ j∈F,i≠j→ (l+3)*b≤ separation (o i) (o j))(hcard:2≤F.card)(hsub:F.image o⊆ H): (l+1)*F.card ≤64*coverNumber b H:=by
  obtain ⟨D, hD, hprice⟩ := coverNumber_realized b H
  obtain ⟨N,hN,R,hstep,hvisits⟩:= ring_path _ (halo_ship b hD.2)
  have hpick (i:ι)(hi:i ∈ F): ∃ k,k ≤ N ∧ separation (R k) (o i)≤ b:=by
    obtain ⟨c,hc,hdist⟩:=halo_spec.mp (hD.1 (hsub (Finset.mem_image_of_mem o hi)))
    obtain ⟨k,hk,he⟩:= hvisits c hc; exact ⟨k,hk,he.symm ▸ hdist⟩
  choose! t ht hnear using hpick
  let gap:=(l+1)*b; have hpos: 0<gap:=Nat.mul_pos (by omega) h
  have apart (i:ι)(hi:i∈F)(j:ι)(hj:j∈F)(hne:i≠j)(hij:t i≤t j): t i+gap ≤ t j:=by
    have hspan := path_span hstep (t i) (t j) hij (ht j hj)
    have h1:= separation_triangle (o i) (R (t i)) (o j); have h2:= separation_triangle (R (t i)) (R (t j)) (o j); rw [separation_comm (o i) (R (t i))] at h1; have := hnear i hi; have := hnear j hj; have hp:= hsep i hi j hj hne; rw [Nat.add_mul] at hp; dsimp [gap]; rw [Nat.add_mul]; omega
  let bucket:=fun i=>t i/gap
  have later (i:ι)(hi:i∈F)(j:ι)(hj:j∈F)(hne:i≠j)(hij:t i ≤ t j):bucket i< bucket j:=by
    have h:=Nat.div_le_div_right (c:=gap) (apart i hi j hj hne hij); rw [Nat.add_div_right (t i) hpos] at h; exact h
  have hpack:F.card≤N/gap+1:=by
    let I:= Finset.range (N/gap+1); refine (Finset.card_le_card_of_injOn (s:=F) (t:=I) bucket ?_ ?_).trans_eq (Finset.card_range _)
    · intro i hi; exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (c:=gap) (ht i hi)))
    intro i hi j hj heq; by_contra hne; rcases le_total (t i) (t j) with hij|hji; exact (later i hi j hj hne hij).ne heq; exact (later j hj i hi (Ne.symm hne) hji).ne heq.symm
  have hm := (Nat.le_div_iff_mul_le hpos).mp (show F.card-1 ≤ N/gap by omega)
  rw [← hprice]; apply Nat.le_of_mul_le_mul_right (c:=b) _ h -- arguments inspect
  calc
    _ = F.card * gap:=by unfold gap; ring
    _ ≤ 2*(F.card-1)*gap:= Nat.mul_le_mul_right _ (by omega)
    _ = 2*((F.card-1)*gap):= by ring
    _ ≤ 2*N:= Nat.mul_le_mul_left _ hm
    _ ≤ 2*(D.card*((b+b+1)+(b+b+1))):= Nat.mul_le_mul_left _ hN
    _ ≤ 2*(D.card*(32*b)):= Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    _ = _ := by ring
end YM.Lattice.Corona
namespace YM.MergeProof.Ribbons.ManyCopies.Guard
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V:Type}[Fintype V][DecidableEq V]{n:Side}{B:Census V}{x:V→Site n}
    (χ:Guard B){A A':V→ℝ}{b l:ℕ}
def Border (b l:ℕ)(o:V→Site n):Prop:= ∀ i:B.Mode,χ.safe i →∀ j∈i.val,∀ k∈i.val, j≠k→ (l+3)*b≤ separation (o j) (o k)
omit [Fintype V] in
lemma lanes (h:Border χ b l x)(hw:∀ i,0<A i)(hw':∀ i,0<A' i)(he:∀ i, A' i ≤ A i*Real.exp ((l:ℝ)/64))(ht:0 < b) : χ.Gates x b A A' 1:=by
    intro i hq hp s hs; have hf:= Corona.clearance_units x i.val s ht (h i hp) hq hs
    unfold Poly.toll; refine (Finset.prod_le_prod (fun i _=> hw' i|>.le) (fun i _=>he i)).trans ?_; rw [Finset.prod_mul_distrib,prod_const]; refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun i _=>hw i|>.le); rw [← Real.exp_nat_mul]
    have hh : (l:ℝ)*i.val.card ≤64*(coverNumber b s:ℝ):=by exact_mod_cast ((Nat.mul_le_mul_right i.val.card (Nat.le_succ l)).trans hf)
    exact Real.exp_monotone (by linarith)
end YM.MergeProof.Ribbons.ManyCopies.Guard

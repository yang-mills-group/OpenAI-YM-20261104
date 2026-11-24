import YM.MergeProof.Paddle
import YM.Corona.Halo
/-! Cost near a delayed leap. `square` decoupling gap would lose!
Use packing at a prescribed, often much smaller aperture (`m~ log beta`).
Adapted Work.I01. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent.Leap
open Function Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Menu
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {n:Side}{V:Type}[Fintype V][DecidableEq V]{m B:ℕ}
omit [Fintype V] in
lemma fits {o:V→Site n}{F:Finset V}(hB:8 ≤ m)(hm:0<B)(hsep:∀ i∈F,∀ j∈F,i≠j→ B*m ≤ separation (o i) (o j))(hcard:2≤F.card){H:Finset (Site n)}(hsub:F.image o⊆ H) : m*F.card ≤64*coverNumber B H:=by
  classical
  obtain ⟨D, hD, hprice⟩ := coverNumber_realized B H
  obtain ⟨N, hN, R, hstep, hvisits⟩ :=
    Corona.ring_path _ (Corona.halo_ship B hD.2)
  -- Pick a time for each marker in F, within B of it.
  have hpick (i : V) (hi : i ∈ F) :
      ∃ k, k ≤ N ∧ separation (R k) (o i) ≤ B := by
    obtain ⟨c, hc, hdist⟩ :=
      halo_spec.mp (hD.1 (hsub (Finset.mem_image_of_mem o hi)))
    obtain ⟨k, hk, he⟩ := hvisits c hc
    exact ⟨k, hk, he.symm ▸ hdist⟩
  choose! t ht hnear using hpick
  let gap := (B*m) - 2*B
  have hsq : 8*B ≤ B*m := by nlinarith only [Nat.mul_le_mul_left B hB]
  have hpos : 0 < gap := by dsimp [gap]; omega
  -- A gap in distance forces a gap in time, paying two radii.
  have apart (i : V) (hi : i ∈ F) (j : V) (hj : j ∈ F) (hne : i ≠ j)
      (hij : t i ≤ t j) : t i + gap ≤ t j := by
    have hspan := Corona.path_span hstep (t i) (t j) hij (ht j hj)
    have h1 := separation_triangle (o i) (R (t i)) (o j)
    have h2 := separation_triangle (R (t i)) (R (t j)) (o j)
    rw [separation_comm (o i) (R (t i))] at h1
    have := hnear i hi
    have := hnear j hj
    have := hsep i hi j hj hne
    dsimp [gap]
    omega
  let bucket := fun i => t i / gap
  have later (i : V) (hi : i ∈ F) (j : V) (hj : j ∈ F) (hne : i ≠ j)
      (hij : t i ≤ t j) : bucket i < bucket j := by
    have h := Nat.div_le_div_right (c := gap) (apart i hi j hj hne hij)
    rw [Nat.add_div_right (t i) hpos] at h
    exact h
  -- At most one marker per bucket, including the bucket containing N.
  have hpack : F.card ≤ N/gap + 1 := by
    let I := Finset.range (N/gap + 1)
    calc
      F.card ≤ I.card := by
        apply Finset.card_le_card_of_injOn bucket
        · intro i hi
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (c := gap) (ht i hi)))
        · intro i hi j hj heq
          by_contra hne
          rcases le_total (t i) (t j) with hij | hji
          · exact (later i hi j hj hne hij).ne heq
          exact (later j hj i hi (Ne.symm hne) hji).ne heq.symm
      _ = N/gap + 1 := Finset.card_range _
  have hm : (F.card-1)*gap ≤ N := (Nat.le_div_iff_mul_le hpos).mp (by omega)
  rw [← hprice]
  apply Nat.le_of_mul_le_mul_left (c := B) _ (by omega)
  calc
    B * (m * F.card) = F.card * (B*m) := by ring
    _ ≤ (2*(F.card-1)) * (2*gap) :=
      Nat.mul_le_mul (by omega) (by dsimp [gap]; omega)
    _ = 4*((F.card-1)*gap) := by ring
    _ ≤ 4*N := Nat.mul_le_mul_left _ hm
    _ ≤ 4*(D.card*((B+B+1)+(B+B+1))) := Nat.mul_le_mul_left _ hN
    _ ≤ 4*(D.card*(16*B)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    _ = B*(64*D.card) := by ring


open Finset GridApprox.Nil Local Extra.Trajectories Source Extra.Multi
lemma palms {a v:V→ℝ}{C:Census V}(hv:∀ i,a i≤v i*mintK m)(hw:∀ i,0<a i)(he:∀ i,0 < v i)(hx:8 ≤ m)(hm:0<B){o:V→Site n}(h:∀ i j:V,i≠j→ B*m ≤ separation (o i) (o j)): Repegs o B v a (1/2) 1 C:=by
   intro i hi X hX
   have ht := fits hx hm (fun i _ j _ h' => h i j h') hi hX
   rw [one_mul]; unfold Poly.toll
   refine (Finset.prod_le_prod (fun i _=>hw i|>.le) (fun i _=>hv i)).trans ?_
   rw [Finset.prod_mul_distrib,prod_const]; apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun i _=> he i|>.le); unfold mintK; rw [← Real.exp_nat_mul]
   apply Real.exp_monotone; linarith only [show (m:ℝ)*i.val.card ≤64*coverNumber B X from by exact_mod_cast ht]
open Relation Corona
-- single connecting halo, linear (not filled box).
lemma skinny {x y:Site n}(he:separation x y ≤ B*m) : coverNumber B ({x,y}:Support n) ≤ m+1:=by
   let f i:= line x y (B*i); let D:= (range (m+1)).image f; have hk:f 0=x:=by simp [f];
   have hb:f m=y:=line_end _ _ he
   have hx : ∀ w:ℕ,w ≤ m →f w ∈ D := fun w hw=> mem_image_of_mem f (mem_range.mpr (by omega))
   apply le_trans _ ((show D.card ≤ _ from card_image_le).trans_eq (card_range _))
   refine list_cost _ ⟨fun i hi=> halo_subset _ _ ?_,ship_halo _ ?_⟩
   · obtain h|h:= mem_insert.mp hi; rw [h,←hk]; exact hx _ (by omega)
     rw [Finset.mem_singleton.mp h,←hb]; exact hx _ le_rfl
   have hy (i : ℕ)(h:i ≤ m): ReflTransGen (Touch D (B+B+1)) (f 0) (f i):= by
       apply line_path _ _ (fun j hj=> hx j (hj.trans h))
       intro j _; exact (line_dist x y (B*j) (B*(j+1)) (Nat.mul_le_mul_left B (by omega))).trans (by rw [mul_add,mul_one]; omega)
   intro i hi j hj; obtain ⟨w,hw,rfl⟩:= mem_image.mp hi; obtain ⟨v,hv,rfl⟩:= mem_image.mp hj; exact (Corona.sym (hy w (Nat.le_of_lt_succ (mem_range.mp hw)))).trans (hy v (Nat.le_of_lt_succ (mem_range.mp hv)))
end YM.MergeProof.Accent.Leap

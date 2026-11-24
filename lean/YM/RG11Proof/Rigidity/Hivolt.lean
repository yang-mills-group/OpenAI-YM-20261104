import YM.RG11Proof.Rigidity.Counterweight

/-!
# Select total primary top weights, at any number of points
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell Maxwell.Free palette Strip Crowd Function Filter Set
open scoped BigOperators Topology Classical

variable {G : Gauge} {P : Type*} [Fintype P] {S : Finset E4}

lemma told (W : Crowd G) (u v : Word G→ℝ) (h : ∀ t∈W,u t.2=v t.2) : W.asks u=W.asks v := by
  induction W with
  | nil=> rfl
  | cons a l ih=> rw [ask_one,ask_one,h a (List.mem_cons_self ..),ih (fun v hv=> h v (List.mem_cons_of_mem a hv))]

lemma tinted (W : Crowd G) (F : Word G → ℝ→ℝ) (h : ∀ t∈W,Continuous (F t.2)) :
    Continuous (fun x=> W.asks (fun w=> F w x)) := by
  induction W with
  | nil => exact continuous_const
  | cons a l ih => simp_rw [ask_one]; exact (continuous_const.mul (h _ (List.mem_cons_self ..))).add (ih (fun t ht=> h _ (List.mem_cons_of_mem a ht)))

def roll (N m : ℕ) (Θ:P→Stream) (p : Word G) : ℝ :=
    if cargo p=N ∧ List.length p=2*m then pairCost (dial Θ) p else 0

/-- The data of all spherical pair contractions survives on the associated
engineering graded part. `Θ` arbitrary by origin, not by particular leg of
the list. Positive weights expose this face without having to assume the
frame preserves *either* weight or Wick length here. -/
theorem privilege (c : G.ColorIndex) {W : Crowd G} (h : Blind S W) (N : ℕ) (hN : ∀ t∈W,cargo t.2 ≤ N)
    (Θ:P→Stream) (m : ℕ) : W.asks (roll N m Θ)=0 := by
  have hw (Θ:P→Stream) : W.asks (sensors Θ m)=0 := by
    rw [show sensors (G:=G) Θ m=_ from (show sensors (G:=G) Θ m=(fun p=>mill Θ m (fun l=> stitch l p)) from rfl),← sum_wheels]
    refine mill_funds _ _ (fun L=> ?_) m
    have hk:=cosmic c h (L.map fun i=>(Θ i,Θ i))
    simpa only [show (spool Θ : P → Spindle G)=(fun x=>(byColor conduit : Stream × Stream→Spindle G) (Θ x,Θ x)) from rfl,stainL,List.map_map,Function.comp_def] using hk
  let R (t : ℝ) (p : Word G) := t^(N-cargo p)*unpaid Θ t m p
  have H (t : ℝ) (ht : t≠0) : W.asks (R t)=0 := by
    have hp (p) (hq : cargo p ≤ N) : R t p=t^N*sensors (bank Θ t) m p := by
      unfold R; rw [← banksOut Θ t ht,← mul_assoc,← pow_add,Nat.sub_add_cancel hq]
    rw [told _ _ (fun u : Word G=> t^N*sensors (bank Θ t) m u) (fun u hu=>hp _ (hN u hu)),ask_mul,hw,mul_zero]
  have hp : NeBot (𝓝[≠] (0:ℝ)):=inferInstance
  have hx : W.asks (R 0)=0 := tendsto_nhds_unique
    ((((tinted W (fun p x=> R x p) (fun t _=> (continuous_id.pow _).mul (unpaid_cont Θ m t.2))).tendsto 0).mono_left nhdsWithin_le_nhds).congr' ((by filter_upwards [self_mem_nhdsWithin (s:=({(0:ℝ)}ᶜ : Set ℝ)) (a:=0)] with i hi; exact H i hi) : (fun t=> W.asks (R t)) =ᶠ[𝓝[≠] (0:ℝ)] fun t=> (0:ℝ))) tendsto_const_nhds
  have he (p) (hL : cargo p≤N) : R 0 p=payout m*roll N m Θ p := by
    unfold R roll; rw [receive]
    split_ifs with h₁ h₂ h₃
    all_goals simp_all <;> omega
  apply (mul_eq_zero.mp ?_).resolve_left (payout_pos m).ne'
  rw [← ask_mul,← told W _ _ (fun w hw=> he _ (hN w hw))]; exact hx

end YM.RG11.Rigidity

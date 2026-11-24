import YM.Contacts.Procession.Manor
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Sun
open Function Set Filter Pulse Pulse.Spine Origin Shuttle Finset
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon -- remove gala
open scoped Classical Topology BigOperators NNReal Matrix ContDiff
variable {α β ι:Type} {u B i k j r n t v d p:ℕ}
section
variable [Fintype α] (g:α→α→ℝ) {A V:House α}
lemma passenger {V F:House α} (h:∀ i ≤ k,V i=F i): walk g A V t k=walk g A F t k := by
    induction t using Nat.strongRecOn generalizing k with|_ s ih=>
      cases s with
      |zero=> rw [walk_start,walk_start]; apply h; rfl
      |succ s=>
       have he(i:ℕ)(hp:i ≤ s)(r:ℕ)(hr:r ≤ k): walk g A V i r=walk g A F i r:= ih i (by omega) (fun n hn=>h _ (hn.trans hr)); rw [walk_step,walk_step]; apply congr_arg; rw [indus,indus, fact g (gathering g A) (gathering g A) _ _ (fun _ _ _ _=> rfl) he, fact g _ _ (gathering g A) (gathering g A) he (fun _ _ _ _=> rfl), he s le_rfl k le_rfl]
lemma passenger_at (p:ℕ)(A:House α): walk g A (shiftA i V) v p= shiftA i (walk g A V v) p:= by -- V implicit
    induction v using Nat.strongRecOn generalizing p with|_ s ih=>
      cases s with
      | zero=>rw [walk_start,walk_start]
      | succ s=>
       let Z:=walk g A V; let Y:= walk g A (shiftA i V); let H:= paceA i Z
       rw [walk_step, respects g Y H (gathering g A) (fun j hj=> funext fun p=> ih j (by omega) p),indus]; unfold H; rw [pact,packed]; change _ • ((brillo g (shiftA _ _ _))+_+_)= _; unfold shiftA; split_ifs; · rw [walk_step]; rfl
       simp
lemma linear_canal (p:ℕ)(A:House α) : IsLinearMap ℝ (canal g p A):= by
    constructor; · intro x y; simpa only [one_smul] using canal_linear (p:=p) g (A:=A) x y 1
    intro a x; simpa only [Welcome.shuffle, add_zero] using canal_linear (p:=p) g (A:=A) x 0 a
lemma prefold (Y:House α) (p:ℕ)(hv:k≤p+t)(he:t ≤ i)(A:House α)(hf:Proper k Y)(hA:Snug A): canal g p A (shiftA t Y) i= canal g k A Y (i-t):= by unfold canal; simp_rw [passenger_at,shiftA,if_pos he]; apply Eq.symm (sum_subset (Finset.range_mono (by omega)) _); intro l _ hl; ext1 j; exact bounds_t g hA Y hf l (by rw [Finset.mem_range] at hl; omega)
-- unit-leaf superposition in response budgets
lemma lantern (p i:ℕ)(A V : House α)(hV:Proper p V)(hA: Snug A):
    canal g p A V i = ∑ j∈Finset.range (i+1),∑ r∈Finset.range (p+j+1),canal g r A (leafS (V j r)) (i-j):= by
   let X(j r:ℕ):=leafS (V j r); let Y j:= Finset.range (p+j+1); let W:=Finset.range (i+1); let L(j r:ℕ):=shiftA j (X j r); let F:=∑ j∈W,∑ r∈Y j,L j r; have he b (hb:b≤ i):F b=V b:= by
      ext1 r; unfold F L X; simp_rw [Finset.sum_apply,shift_once]; rw [Finset.sum_eq_single b]
      · simp_rw [Pi.single_eq_same]
        by_cases hr: r≤p+b
        · rw [sum_eq_single r]; exact Pi.single_eq_same r _; intro c _ hh; exact Pi.single_eq_of_ne (Ne.symm hh) _; intros hx; exact (hx (mem_range.mpr (by omega))).elim -- hm orientation
        rw [hV.thin _ _ (by omega)]; exact sum_eq_zero fun i hi=> by have hu:=mem_range.mp hi; exact Pi.single_eq_of_ne (by omega:r≠i) _
      · intro j hj hy; refine sum_eq_zero fun i hi=>?_ ; rw [Pi.single_eq_of_ne (Ne.symm hy)]; rfl
      · intro hh; exact (hh (mem_range.mpr (by omega))).elim
   have ht : canal g p A V i = canal g p A F i := sum_congr rfl (fun j _=> (passenger g he).symm); rw [ht]; let f:= (linear_canal g p A).mk' (canal g p A); change f _ i= _; unfold F; simp_rw [map_sum,Finset.sum_apply]; refine sum_congr rfl (fun j hj=> sum_congr rfl (fun r hr=> ?_)); have hx:=mem_range.mp hj; have hv:=mem_range.mp hr; exact prefold g (X j r) p (by omega) (by omega) A (bornS _ (hV.sym _ _)) hA -- i−j, casts
end
end YM.Contacts.Procession.Sun

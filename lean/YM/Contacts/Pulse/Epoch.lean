import YM.Contacts.Pulse.Square
namespace YM.Pulse.Spine
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Extension.UV.Linear
open scoped Classical Topology BigOperators NNReal ENNReal
noncomputable section
variable {G:Gauge} {A:Levels G}{T: MapPrices}{M:Horizon A}
def rentCheque (T:MapPrices)(j:ℕ):ℝ≥0:= ⟨T.α j,(T.alpha_pos j).le⟩
def sight (T:MapPrices)(j:ℕ):ℝ≥0:= min (rentCheque T j) (rentCheque T (j+1)) / 3
lemma rent_pos (T:MapPrices)(j:ℕ): 0< rentCheque T j:= T.alpha_pos j
lemma sight_pos (T:MapPrices)(j:ℕ): 0<sight T j := div_pos (lt_min (rent_pos T _) (rent_pos T _)) (by positivity)
lemma shelf_span (T:MapPrices)(j:ℕ): (sight T j:ℝ)*3 ≤ T.α j ∧ (sight T j:ℝ)*3≤ T.α (j+1) := by simp only [sight,rentCheque,NNReal.coe_div,NNReal.coe_min,NNReal.coe_ofNat,NNReal.coe_mk]; rw [div_mul_cancel₀ _ (by norm_num : (3:ℝ)≠0)]; exact ⟨min_le_left .., min_le_right ..⟩
lemma released {m n:ℕ}(h:M.Suffices T)(hN:m≤n): Whole (M.H n m).metric := ⟨_,_,T.alpha_pos _,(h.rows n m hN).2.1⟩
lemma sturdy (T:MapPrices)(j:ℕ) : ∃ C:ℝ, 1≤C ∧ ∀ (A:Levels G) (M:Horizon A) (N N' m:ℕ), m ≤ N → m ≤ N' → A.clock.J m=j → M.Suffices T → Rooted (terrain (sight T j) (TypeFace 1)) (keconomic (M.H N m).metric (M.H N' m).metric) C := by
  obtain ⟨C,hC,h⟩:=delta_budget 1 (T.α j)
  let a:ℝ:= Fintype.card (TypeFace 2); let b:= a*(a*(C*T.Ω j)*C); let u:= Fintype.card (Breed 1 (TypeFace 1))
  let k:= (u:ℝ)*(b+b); refine ⟨max 1 k,le_max_left ..,fun A M N n m hN hn hu hm=> ?_⟩
  have hh (i:ℕ)(hi:m ≤ i): (krow (M.H i m).metric).strip (T.α j) b:= strip_compose (T.alpha_pos j).le (strip_compose (T.alpha_pos j).le (strip_trans h) (hu ▸ (hm.rows i m hi).2.1)) h
  have he : Row.strip (portfolio (M.H N m).metric (M.H n m).metric) (rentCheque T j) (b+b) := strip_minus (hh N hN) (hh n hn); refine (arrive_both he (Cost.nonneg (he (coord 0) (coord 1))) (le_trans ?_ (shelf_span T j).1)).weaken (fun _=> le_rfl) (le_max_right ..); linarith only [NNReal.coe_nonneg (sight T j)]
lemma pessimistic (h:0≤b)(C D:ℝ)(hC:0<C) : ∃ k:ℕ,∀ (L:Side), k≤L.val → b/(L.val:ℝ)≤ C ∧ (D:ℝ) /(L.val:ℝ) ≤ Real.exp (- (Real.log (L.val:ℝ))/2) := by
  obtain ⟨k,hk⟩:= exists_nat_gt (max (b/C) (D^2))
  refine ⟨k,fun L hL=> ?_⟩; have ht:= side_pos L; have hu : max (b/C) (D^2) < L.val:= hk.trans_le (by exact_mod_cast hL)
  constructor; · rw [div_le_iff₀ ht]; rw [mul_comm]; exact ((div_lt_iff₀ hC).1 (lt_of_le_of_lt (le_max_left ..) hu)).le
  refine le_of_pow_le_pow_left₀ two_ne_zero (Real.exp_pos _).le ?_
  rw [div_pow,← Real.exp_nat_mul]; push_cast; rw [show (2:ℝ)* (-Real.log L.val /2)= -Real.log L.val by ring, Real.exp_neg,Real.exp_log ht,div_le_iff₀ (pow_pos ht _)]; exact hu.le.trans' (le_max_right ..) |>.trans_eq (by field_simp)
-- entry t floor uniform both price times output suppress at immediate top
abbrev economy (A:Levels G)(M:Horizon A)(N N' m:ℕ):= keconomic (M.H N m).metric (M.H N' m).metric
def particolor (A:Levels G) (T:MapPrices) (u:ℕ→ℝ) := fun i => terrain (sight T (A.clock.J i)) (TypeFace 1)
def earn (S:Schedule)(m N:ℕ):= Real.exp (-(S.scale N-S.scale m)/2)
lemma earn_step (S:Schedule)(m N:ℕ): earn S m N=earn S (m+1) N * Real.exp (-Real.log (S.block m).val/2) := by unfold earn; rw [← Real.exp_add, S.scale_succ]; congr 1; ring
@[simp] lemma earn_same (S:Schedule)(m:ℕ): earn S m m=1:= by simp [earn]
structure Truce (T:MapPrices)(A:Levels G) : Prop where
  tariff M (N N' m : ℕ) : M.Suffices T → 5≤A.clock.J (m+1) → m<N → m<N' → Rooted (terrain (sight T (A.clock.J m)) (TypeFace 1)) (economy A M N N' m) (earn A.S m (min N N'))
lemma chosen_flags (G:Gauge)(T:MapPrices) : ∃ f:ℕ→ℕ,∀ A:Levels G,(∀ i,f (A.clock.J (i+1)) ≤ (A.S.block i).val) → Truce T A := by
  choose w hw hw' using sturdy (G:=G) T; let F j := sight T j; let d i := max 0 (T.Ω i)
  choose u hu hu' x hx h using fun i j => angled (σ:=F i) (η:=F j) (TypeFace 1) (TypeFace 1) 1 (sight_pos T _) (show 0≤d i from le_max_left ..)
  choose k hk using fun i j=> pessimistic (NNReal.coe_nonneg (F j)) (u i j) (w i*x i j) (NNReal.coe_pos.mpr (hu i j))
  refine ⟨fun i=> max (k i i) (k i (i-1)),fun A hA=>?_⟩
  let J:=A.clock.J; refine ⟨fun M N N' m hM hv hN hz=> ?_⟩
  have step (m:ℕ)(hm:m<min N N')(he: 5≤ J (m+1))(C:ℝ)(H:Rooted (terrain (F (J (m+1))) _) (economy A M N N' (m+1)) C):
      Rooted (terrain (F (J m)) _) (economy A M N N' m) (C*x (J (m+1)) (J m)/(A.S.block m).val):= by
    let j:=J (m+1); let v:=J m; have hy:v=j ∨ v=j-1:= by have hi:= A.fits.stepSlow m; have hv:= A.fits.mono (Nat.le_succ m); change j≤v+1 at hi; change v≤j at hv; omega
    let L:= A.S.block m; have hkx : k j v ≤ L.val:= hy.elim (fun h=>h.symm ▸ le_trans (le_max_left ..) (hA m)) (fun h=> h.symm ▸ le_trans (le_max_right ..) (hA m))
    let R: Fin (1+1)→voyage L:= ![(M.towers N m).A0,(M.towers N' m).A0]
    have H₁ : m<N:= lt_of_lt_of_le hm (min_le_left ..); have H₂:= lt_of_lt_of_le hm (min_le_right ..)
    have hs : (F v:ℝ) ≤ T.α j:= by
      change 5≤ j at he; apply le_trans (b:=(F v:ℝ)*3); · linarith only [NNReal.coe_nonneg (F v)]
      rcases hy with h|h; · rw [← h]; exact (shelf_span T _).1
      rw [show T.α j=T.α (v+1) from congr_arg T.α (show j=v+1 by omega)]; exact (shelf_span T v).2
    have hd (i:ℕ)(hi:m < i) (l:List Axis)(hl:l.length ≤3): Row.strip (advanceC L (M.towers i m).A0 l) (F v) (d j/(L.val:ℝ)^(1+l.length)):= strip_mono (( (hM.costs i m hi).2.2.2 l (hl.trans (show _ ≤ _ by change 3≤ j-2; change 5≤j at he; omega))).1) hs (by gcongr; exact le_max_right ..)
    have huP:= H.weaken (terrain_le (hu' j v)) le_rfl
    have hy₁ q : ((M.H N (m+1)).metric.acts q)ᵀ=(M.H N (m+1)).metric.acts q:= (hM.all N _ H₁ q).symmetric.1; have hy₂ q := (hM.all N _ H₁.le q).symmetric.1
    have hr:= steadfast (F:=(M.H N (m+1)).metric) (G:=(M.H N' (m+1)).metric) (M:=(M.H N m).metric) (K:=(M.H N' m).metric) (released hM H₁) (released hM H₂) (released hM H₁.le) (released hM H₂.le) (R:= (M.towers N m).A0) (R':=(M.towers N' m).A0) (side_diverges A.S m) (A.clock.op m) (fun _ => rfl) (fun q P Q hp hq=> by
      have hh1: (M.towers N m).A0=P:=eq_of_heq hp; have hh2:(M.towers N' m).A0=Q:=eq_of_heq hq; rw [←hh1,←hh2]; exact ⟨(hM.crossings N m q H₁).trial,(hM.crossings N' m q H₂).trial⟩) hy₁ hy₂ huP (hk j v L hkx).1 (hd N H₁ [] (by simp)) (hd N' H₂ [] (by simp)) (by unfold d; have hh:= side_pos L; positivity)
    have ht : install ∘ R = ![install (M.towers N m).A0,install (M.towers N' m).A0]:= funext fun i=> by fin_cases i<;>rfl
    rw [economy,hr,← ht]; refine h j v L (A.S.block_odd m) (hk j v L hkx).1 R (fun i=> ?_) C _ H (both_publish _) (vessel_age (released hM H₁) (released hM H₂) ((hM.all _ _ H₁ 1).starts.trans (hM.all _ _ H₂ 1).starts.symm)); fin_cases i
    · exact hd N H₁
    exact hd N' H₂
  suffices he : ∀ d (m:ℕ), min N N'= m + 1 + d → 5≤ J (m+1) → Rooted (terrain (F (J m)) _) (economy A M N N' m) (earn A.S m (min N N')) by exact he (min N N'-(m+1)) m (by omega) hv
  have hr m : w (J (m+1))*x (J (m+1)) (J m)/(A.S.block m).val ≤ Real.exp (-Real.log (A.S.block m).val/2):= by
    apply (hk _ _ _ ?_).2; have hi := hA m
    have hh:J m ≤ J (m+1):= A.fits.mono (by omega); have ht:J (m+1) ≤ J m +1:= A.fits.stepSlow m; have hz:J m=J (m+1) ∨ J m=J (m+1)-1:= by omega
    rcases hz with h|h
    · exact le_trans (congr_arg (k (J (m+1))) h).le ((le_max_left ..).trans hi)
    exact le_trans (congr_arg (k (J (m+1))) h).le ((le_max_right ..).trans hi)
  intro u
  induction u with
  | zero=> intro m hm hu; refine (step m (by omega) hu (w (J (m+1))) (hw' _ A M N N' _ (by omega) (by omega) rfl hM)).weaken (fun _=>le_rfl) ?_; rw [earn_step,hm,Nat.add_zero,earn_same,one_mul]; exact hr m
  | succ i ih=>
    intro m hm hu; have he:= ih (m+1) (by omega) (hu.trans (A.fits.mono <| Nat.le_succ _)); refine (step m (by omega) hu _ he).weaken (fun _=> le_rfl) ?_
    rw [earn_step A.S m (min N N'),mul_div_assoc]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply le_trans _ (hr _); gcongr; exact le_mul_of_one_le_left (hx ..) (hw _)
end
end YM.Pulse.Spine

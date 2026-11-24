import YM.FormalBulk08.Glide.Post

/-!
Real body with source root. Fling analog independent of rank0.
Preserve actual ζ width on both sides of the contractions, no
ambiguity about budget before coupling or choices of presentations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05
open Lotus Shore Mesa Gorge City Cork Rift
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {X V I : Type*} {m n : ℕ} {D : Reach V} {R : Reach I}{η θ A B C : ℝ}
def herb (D : Reach V)(x : V) (v : chain V n):= wide D (Fin.cons x v)
def penon (D: Reach V)(x:V)(η : ℝ)(T:Tile V n)(v:chain V n):=Gorge.shine η (herb D x v) * ‖T v‖ₑ
lemma cloth (u:chain V n)(a x:V):herb D a u≤herb D x u+D.d a x:= by
    have h i : D.d a (u i)≤ herb D x u+D.d a x:= (D.tri ..).trans ((add_le_add_right (show D.d x (u i)≤ _ from reached D (Fin.cons x u : chain V (n+1)) 0 i.succ) (D.d a x)).trans_eq (Nat.add_comm ..))
    refine known_wide D _ _ fun i j=>?_; cases i using Fin.cases <;> cases j using Fin.cases <;> simp only [Fin.cons_zero,Fin.cons_succ]
    · rw [D.self]; omega
    · exact h _
    · rw [D.turn]; exact h _
    rename_i i j; exact le_trans (b:=herb D x u) (reached D (Fin.cons x u) i.succ j.succ) (Nat.le_add_right ..)
lemma penn_bail {a:V}{T : Tile V n}(h:Knoxville D η a T C)(he:0≤η):Bail D η T C:= by
    refine ⟨h.1,fun i x=> le_trans (b:=∑' v:pack i x,penon D a η T v.val) ?_ ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (penon D a η T)).trans h.2)⟩
    exact ENNReal.tsum_le_tsum (fun v=> mul_le_mul_left (shine_le _ he (known_wide _ _ (herb D a v.val) (fun i j=> reached D (Fin.cons a v.val) i.succ j.succ))) _)
lemma penn_shrink {a:V}{T:Tile V n}(h:Knoxville D η a T C)(he:θ≤η): Knoxville D θ a T C:= ⟨h.1,(ENNReal.tsum_le_tsum fun _=>mul_le_mul_left (sheen_le η he _) _).trans h.2⟩
lemma penn_move {a x:V}{T : Tile V n}(h: Knoxville D η a T C)(he:0≤η): Knoxville D η x T (Real.exp (η*D.d x a)*C) := by
    refine ⟨mul_nonneg (Real.exp_pos _).le h.1,?_⟩
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]; refine le_trans ?_ (mul_le_mul_right h.2 _); rw [←ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro v
    have he := shine_le _ he (cloth (D:=D) v x a); rw [shine_add] at he; exact (mul_le_mul_left he _).trans_eq (by unfold Gorge.shine; ac_rfl)
lemma penn_same {a x:V}{T : Tile V n}(h: Knoxville D η a T C)(he:0≤η)(e:D.d x a=0): Knoxville D η x T C:= by simpa only [e,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] using (penn_move (x:=x) h he)
lemma penn_chill (u:chain V n) {a:V}{T : Tile V n}(h: Knoxville D η a T C): ‖T u‖*Real.exp (η*herb D a u) ≤ C:= by
   have he:= (ENNReal.le_tsum u).trans h.2
   change Gorge.shine η (herb D a u)* _≤_ at he;unfold Gorge.shine at he; rw [←ofReal_norm,←ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm] at he; exact (ENNReal.ofReal_le_ofReal_iff h.1).mp he
lemma penn_amount {a:V}{T : Tile V n}(h:Knoxville D η a T C): Summable (fun v=>Real.exp (η*herb D a v)*‖T v‖) ∧ (∑' v,Real.exp (η*herb D a v)*‖T v‖)≤C:= by
   refine from_evil h.1 (fun _=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) ?_; apply le_trans ?_ h.2; apply ENNReal.tsum_le_tsum; intro v; rw [ENNReal.ofReal_mul (Real.exp_pos _).le,ofReal_norm];rfl
lemma penn_total {a:V}{T : Tile V n}(h:Knoxville D η a T C)(hs:0≤η): Summable (fun v=>‖T v‖):= by simpa only [zero_mul,Real.exp_zero,one_mul] using (penn_amount (penn_shrink h hs)).1
lemma penn_neg {a:V}{T : Tile V n}(h:Knoxville D η a T C): Knoxville D η a (-T) C:=by simpa using h.smul (-1 : ℝ)
lemma penn_sub {a:V}{T S: Tile V n}(h:Knoxville D η a T B)(he:Knoxville D η a S C): Knoxville D η a (T-S) (B+C):= sub_eq_add_neg T S ▸ h.add (penn_neg he)

def Allow (D: Reach V)(η:ℝ) (o:V)(F:chain V m→X→ℝ) (C:ℝ):= 0 ≤ C ∧ (∑' v,∑' x,Gorge.shine η (herb D o v)*‖F v x‖ₑ) ≤ ENNReal.ofReal C
lemma Allow.bill {F:chain V m→X→ℝ}{o:V}(h:Allow D η o F C): Knoxville D η o (fun v=> ∑' x,F v x) C:= by
   refine ⟨h.1,(ENNReal.tsum_le_tsum fun (v : chain V m)=> ?_).trans h.2⟩; rw [ENNReal.tsum_mul_left]; exact mul_le_mul_right (enorm_tsum_le_tsum_enorm (f:=fun x : X=>F v x)) (Gorge.shine η (herb D o v))
lemma Allow.points {F:chain V m→X→ℝ}{o:V}(h:Allow D η o F C)(hs:0≤η) (v:chain V m): Summable fun x=> ‖F v x‖:= by
   apply tsum_enorm_ne_top_iff_summable_norm.mp; apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans ?_ ((ENNReal.le_tsum v).trans h.2)); exact ENNReal.tsum_le_tsum (fun _=>le_mul_of_one_le_left' (shine_plus _ hs _))
lemma quake {x:V}{y:I}(W:Solar D R η θ)(M:Fin m→V→ I→ℝ)(H : W.capsule x y=1)
    {F:Tile V m}(h: Knoxville D η x F C)(hp:∀ i,Hill W.capsule (M i) A B)(he:0≤A): Allow R θ y (fun v t=> F t*∏ i,M i (t i) (v i)) (W.fare*(C*A^m)) := by
    refine ⟨mul_nonneg W.good (mul_nonneg h.1 (pow_nonneg he _)),?_⟩; rw [ENNReal.tsum_comm,ENNReal.ofReal_mul W.good, ENNReal.ofReal_mul h.1, ENNReal.ofReal_pow he]
    let N i (a:I) (b:V):= W.capsule b a * ‖M i b a‖ₑ
    refine le_trans ?_ (mul_le_mul_right (mul_le_mul_left h.2 _) _)
    rw [←ENNReal.tsum_mul_right,←ENNReal.tsum_mul_left]; refine ENNReal.tsum_le_tsum fun v=>?_
    have hh : (∏ i:Fin m,∑' a, N i a (v i)) ≤ ENNReal.ofReal A ^ m:= by simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using Finset.prod_le_prod' (s:=Finset.univ) (f:=fun i=>∑' a,N i a (v i)) (fun i _=> (hp i).rows (v i))
    rw [←eun_tsum (fun i a=>N i a (v i))] at hh
    refine le_trans ?_ (mul_le_mul_right (mul_le_mul_right hh (penon D x η F v)) _)
    rw [←ENNReal.tsum_mul_left,←ENNReal.tsum_mul_left]; refine ENNReal.tsum_le_tsum fun t=>?_
    have hx:=W.carried (Fin.cons x v : chain V (m+1)) (Fin.cons y t); simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,H,one_mul] at hx; apply (mul_le_mul_left hx _).trans_eq
    have ht (s:Finset (Fin m)): ‖∏ i∈s,M i (v i) (t i)‖ₑ = ∏ i∈s, ‖M i (v i) (t i)‖ₑ := by induction s using Finset.induction <;> simp_all [enorm_mul]
    unfold penon N herb; change _ = _ *(_*(∏ i:Fin m, W.capsule (v i) (t i)*‖M i (v i) (t i)‖ₑ)); rw [enorm_mul,ht,Finset.prod_mul_distrib]; ring
-- specializes shore
variable {I J : Type}[Fintype I][Fintype J](M:Row I J)(z:Biglot I)(x: J)
lemma penn_pearl {T : Tile (Biglot I) n}(h:Knoxville (fame _) η z T A)(hs:0≤η)(hh:Row.strip M η C)(hp:0≤C) : Knoxville (fame _) η (z.1,x) (pearl (lands M) T) (1*(A*((Fintype.card J)*C)^n)):= by
    apply (quake (x:=z) (y:=(z.1,x)) (bridge I J η hs) (fun _:Fin n=> lands M) _ h (fun _=>grad_line M hh hp) (by positivity)).bill; simp [bridge,linkshine,Gorge.shine]
end YM.FormalBulk08.Kemp

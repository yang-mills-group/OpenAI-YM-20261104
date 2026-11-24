import YM.MS.Class.PairDetect
/-!
# $c A A$ jets determine rank three. First derive all antifield
 terms from the single $c^+cc$ symbol, and its invariant alternation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau.Detect.Mark
open Function Filter Set Finset Plane Koszul Real Momentum Wire
open scoped Topology ContDiff InnerProductSpace
open Complex (I)
variable {G: Gauge} {F : Law G} {h : ℤ}

abbrev LieColor (i j k: CI G) : ℝ := ⟪G.ad (eb G i) (eb G j), eb G k⟫_ℝ
abbrev token (F: Law G) (i j k:CI G):= F [S i 0,C j 0,C k 0]
abbrev ping (F: Law G) (i j k: CI G) (a b: Axis):= F [U a i 0,W b j 0,C k 0] -- keyword?
variable (X:Class F h)
include X
lemma af_constant (hh : h≤4) (w L : Legs (Lane4 G)) (hp : net w=0) (hL : net L=0) (he : fieldDim wfield w=4) (hg : w.map Prod.fst=L.map Prod.fst): F w=F L:= by
   let A : Lane4 G→Lane4 G:= fun q=> (q.1,(0: FourP))
   have hx : w.map A=L.map A:= by convert congr_arg (List.map (fun x=> (x,(0:FourP)))) hg using 1 <;> simp [A]
   have hz : fieldDim wfield L=4:= by unfold fieldDim; rw [← List.map_map,← hg,List.map_map]; exact he
   obtain hl|hl:= lt_or_eq_of_le hh
   · exact (X.tall _ hp (by omega)).trans (X.tall _ hL (by omega)).symm
   exact (X.graded.level _ (fun _=>hp) (by omega)).trans ((congr_arg F hx).trans (X.graded.level _ (fun _=>hL) (by omega)).symm)
lemma anti_constant (hh:h≤4) (i j k : CI G) (a b p q r) (H : p+(q+r)=(0: FourP)): F [U a i p,W b j q,C k r]=ping F i j k a b:=af_constant X hh _ _ (by simpa [U,W,C,qnote,net] using H) (by simp [U,W,C,qnote,net]) rfl rfl -- by rfl?
lemma token_constant (hh:h≤4) (i j k : CI G) (p q r) (H : p+(q+r)=(0: FourP)): F [S i p,C j q,C k r]=token F i j k:=af_constant X hh _ _ (by simpa [S,C,qnote,net] using H) (by simp [S,C,qnote,net]) rfl rfl
-- helpers precision spike etc
omit X in
lemma prec_at (a j k: Axis) : precision a j (spike k)= (if a=j∧a≠k then 1 else 0):= by
    have he : Momentum.sq (spike k)=1:= by unfold Momentum.sq; rw [Finset.sum_eq_single k (fun j _ hj=> by simp [hj]) (by simp)]; simp
    unfold precision delta; rw [he]; by_cases ha:a=k <;> by_cases hj:j=k <;> (subst_vars; simp_all <;> tauto)

lemma changes (hh:h≤4) i j k a b: ping F i j k a b= if a=b then token F i j k else 0:= by
   let q:=spike b
   have h0:= X.closed [U a i (-q), C j q,C k 0] (by simp [U,C,qnote,net]); rw [qAnti,qGhost] at h0; simp_rw [qGhost,q0, at_D] at h0
   simp_rw [token_constant X hh i j k (-q) q 0 (by simp), anti_constant X hh i j k a _ (-q) q 0 (by simp)] at h0
   set Y:=token F i j k
   have hv (i:Axis) (hn:i≠b) : q i=0:= spike_of_ne hn
   simp_rw [Pi.zero_apply,Complex.ofReal_zero, mul_zero, zero_mul,Finset.sum_const_zero, sub_zero] at h0
   rw [Finset.sum_eq_single b (fun j _ hj=> by rw [hv j hj, Complex.ofReal_zero,mul_zero, zero_mul]) (fun hh=> (hh (mem_univ _)).elim)] at h0
   rw [show q b=1 from spike_self b] at h0; split
   · subst a; simp [q] at h0; exact mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp h0).symm
   rename_i h1; simp [hv a h1] at h0; exact h0
lemma field_alt (hh:h≤4) i j k: token F i j k= - token F j i k:= by
    let p:=spike 0
    have Hv:= X.closed [W 1 i p,W 1 j (-p), C k 0] (by simp [W,C,qnote,net]); rw [qAA,qAA,qGhost] at Hv; simp_rw [q0,at_D] at Hv
    have he l : F [W 1 i p,U l j (-p), C k 0]= F [U l j (-p), W 1 i p,C k 0]:= by
       have hz:=X.swap [] (W 1 i p) (U l j (-p)) [C k 0] (by simp [W,U,C,net,qnote]); simpa [parity,Landau.p,cross] using hz
    simp_rw [he, Pi.zero_apply, Complex.ofReal_zero, mul_zero,zero_mul, Finset.sum_const_zero,sub_zero,add_zero,k_even] at Hv
    simp_rw [anti_constant X hh i j k _ 1 p (-p) 0 (by simp),anti_constant X hh j i k _ 1 (-p) p 0 (by simp),changes X hh] at Hv
    -- `simp` sums
    simp [p,prec_at,mul_ite] at Hv; linear_combination -Hv
lemma ghost_alt i j k: token F i j k= - token F i k j:= by
   have hp:= X.swap [S i 0] (C j 0) (C k 0) [] (by simp [S,C,net,qnote]); simpa [parity,Landau.p,cross,token] using hp
lemma lie_token (hh:h≤4) (K:G.Simple) : ∃ c:ℝ,(h=4 ∨ c=0) ∧ ∀ i j k :CI G, token F i j k=(LieColor i j k:ℂ)*(c:ℂ):= by
    rcases lt_or_eq_of_le hh with hl|hl
    · refine ⟨0,Or.inr rfl, fun i j k=>?_⟩; rw [Complex.ofReal_zero,mul_zero]; exact X.tall _ (by simp [S,C,qnote,net]) hl
    let p:=token F
    have hc i j k : p i j k=p j k i:= by dsimp only [p]; rw [field_alt X hh i j k,ghost_alt X j i k,neg_neg]
    obtain ⟨c,he⟩:= triple_value K p (fun g i j k=> X.solid.color _ (fun _=> by simp [S,C,qnote,net]: Course true [S i 0,C j 0,C k 0]) g) (field_alt X hh) hc
    refine ⟨c.re, Or.inl hl, fun i j k=> ?_⟩; obtain ⟨x,hx⟩:= evenStar (p i j k) (by
        have hz:= X.solid.real' [S i 0,C j 0,C k 0] (fun _=>by simp [S,C,qnote,net]); simpa only [invertMom,List.map_cons,List.map_nil,S,C,qnote,neg_zero] using hz)
    change p i j k= _; rw [hx]; specialize he i j k; rw [hx,← show LieColor i j k=inner ℝ _ _ from rfl] at he; apply Complex.ext
    · simpa using congr_arg Complex.re he
    simp

end YM.MS.Landau.Detect.Mark

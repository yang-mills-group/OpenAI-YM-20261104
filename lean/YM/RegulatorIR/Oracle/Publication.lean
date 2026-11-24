import YM.RegulatorIR.Oracle.Lading

/-! Extend uniform positivity on *large* tori only to spectral publication.
Use lifted rows commuting with period (never consume θ-restriction). -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry FreeResolvent Matrix
open scoped Topology ENNReal NNReal BigOperators Classical Matrix
variable {X Y A B C V J K :Type} {S T U:Side→Type}
variable (W:Quarry X A S) {p:Side} {σ α:ℝ}
section density
variable {n m : Side} {X Y:Type}
-- equal finite fibers of surjective AddMonoidHom. count by shifts.
private lemma traceY [Fintype X] [Fintype Y] [AddGroup X][AddGroup Y](f:X→+Y)(h:Surjective f) (a:Y→ℝ) : ∑ i:X,a (f i) = Fintype.card (Stalk f 0)* ∑ i:Y, a i := by
 let e: X≃ (i : Y) × (Stalk f i):= (Equiv.sigmaFiberEquiv f).symm
 have he : ∀ i:Y,Fintype.card (Stalk f i) = Fintype.card (Stalk f 0):=by
    intro i; obtain ⟨x,rfl⟩:=h i;apply Fintype.card_congr (Equiv.subtypeEquiv (Equiv.subRight x) (fun i=>?_)); simp only [Equiv.subRight_apply,map_sub];rw [sub_eq_zero]
 rw [← Equiv.sum_comp e.symm (fun i=>a (f i)),Finset.mul_sum]; simp_rw [Fintype.sum_sigma]; apply Finset.sum_congr rfl;intro i _;rw [Finset.sum_congr rfl (g:=fun _=>a i) (fun j _=>?_),Finset.sum_const, Finset.card_univ,nsmul_eq_mul, he]; exact congr_arg a j.property
lemma universal_gap {α:ℝ}{K:Row A A}[Fintype A]{N:ℕ} (h:Row.safe K)(H:∀ p:Side,N≤p.val → Gap (K.acts p) α) (n:Side): Gap (K.acts n) α:=by
 let a:Side:=⟨n.val*(N+1),Nat.mul_pos n.property (Nat.succ_pos _)⟩
 have hv:N ≤ a.val:= Nat.le_trans (by omega : N≤ N+1) (Nat.le_mul_of_pos_left (N+1) n.pos)
 obtain ⟨f,hf⟩:= Universal.modulo (m:=a) (n:=n) (dvd_mul_right ..); let s:= Universal.overlay (α:=A) f
 have hs : Surjective f:= fun i=> ⟨wrap a (Lattice.lift i),(hf _).trans (wrap_lift i)⟩
 let k:ℝ := Fintype.card (Stalk f 0); have hk:0<k:=Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr (by obtain ⟨x,h⟩:=hs 0;exact ⟨⟨x,h⟩⟩))
 have hp (v:Co n A→ℝ): ∑ i : Co a A,v (s i)= k*∑ i,v i:=by
    simp_rw [Fintype.sum_prod_type]; convert traceY f hs (fun i=> ∑ j:A,v (i,j)) using 2; all_goals first | rfl | (unfold k; congr! 2)
 constructor; intro i
 have ht:= (H a hv).lower (i ∘ s); rw [Universal.law K h f _ i] at ht; swap; exact fun i j=> by rw [map_add,hf]
 change α* ∑ j:Co a A,i (s j)*i (s j) ≤ ∑ j: Co a A,i (s j)* ( (K.acts n*ᵥ i) (s j)) at ht
 rw [hp (fun j=>i j*i j), hp (fun j=>i j*(K.acts n *ᵥ i) j),mul_left_comm] at ht;exact le_of_mul_le_mul_left ht hk
private lemma reindex [Fintype X][Fintype Y](e:X≃ Y)(A:Matrix Y Y ℝ) (h:Gap (A.submatrix e e) α): Gap A α:=by
 constructor;intro x
 have hp:= h.lower (x ∘ e); have hv : (A.submatrix e e) *ᵥ (x ∘ e) = (A *ᵥ x) ∘ e:= funext fun i=> e.sum_comp fun j=>A (e i) j*x j
 rw [hv] at hp
 convert hp using 1
 · congr 1;exact Eq.symm (e.sum_comp (fun j=>x j*x j))
 exact Eq.symm (e.sum_comp (fun i=> x i * (A *ᵥ x) i))
end density
lemma reindexed [Fintype X] [Fintype Y][Fintype A][Fintype B][Fintype C][Fintype V] (e:X≃ Y)(f:A≃B)(g:C≃V)(M:Matrix Y B ℝ)(P:Matrix B V ℝ): M.submatrix e f*P.submatrix f g= (M*P).submatrix e g:=by ext1 i j;exact f.sum_comp (fun q=>M (e i) q *P q (g j))
variable {W}
section front
variable [Fintype A] [DecidableEq A] [∀ n,Fintype (S n)][∀ n,DecidableEq (S n)]
def E_lower (c α:ℝ)(K:Layer X X) (W:Quarry X A S) := ∀ p:Side, c ≤ p.val → Gap (ledgerRow W W K p) α
variable (W)
omit [Fintype A] in
lemma membership [Fintype Y][DecidableEq Y] (T:Y ≃ A) : submatrix (1:Matrix A A ℝ) T T=1:=by ext1 i j;simp only [Matrix.submatrix_apply,Matrix.one_apply,Matrix.one_apply,T.injective.eq_iff]
lemma pricingX {K:Layer X X}(W:Quarry X A S) (h:Albedo W W K) (s:ℝ) {α c:ℝ}{C:ℝ≥0∞}(hC:C≠⊤)(H: chestE W W s K C)(hv: E_lower c α K W)(hp:0 < s)(hα:0 < α) {γ:ℝ}(hm : γ < FreeResolvent.margin A s C.toReal α) (hγ:0<γ):
 ∃ U:Layer X X, Albedo W W U ∧ chestE W W γ U (Fintype.card A * ENNReal.ofReal (inversePrice A s C.toReal α 0 γ)) ∧ lap K U=ID X ∧ lap U K=ID X:=by
 let R:= cargo W W K
 have hz: lading W W R=K:= unwind W W h; have hi:R.strip s C.toReal:=cargoW W W H hC
 obtain ⟨N,hN⟩:= exists_nat_ge c
 have he(n):Gap (R.acts n) α:= universal_gap (Row.rights s _ hi hp.le) (N:=N) (fun p hvp=>?_ ) n
 · obtain ⟨T,ht,Ht⟩:= FreeResolvent.strip_resolvent R (u:=0) le_rfl hα hp ENNReal.toReal_nonneg hi he hm
   let U:= lading W W T; have hc:= roots W W ht; have hs : Billed K:=H.billed hp.le hC
   have hb:Billed U:=hc.billed hγ.le (ENNReal.mul_ne_top (by finiteness) ENNReal.ofReal_ne_top); have hu:Albedo W W U:=ladingW W W T
   have hy (p:Side) : ledgerRow W W (lap K U) p=1 ∧ ledgerRow W W (lap U K) p=1:=by
      rw [Ledger.lap W W W p hs hb hu,Ledger.lap W W W p hb hs h]; rw [← hz]; unfold U;rw [ledger_lade,ledger_lade, Ht]; let A:= W.markedP p
      have hp:= FreeResolvent.resolve_left (he p) hα (u:=0) le_rfl; have h:=FreeResolvent.resolve_right (he p) hα (u:=0) le_rfl
      simp only [zero_smul,add_zero] at hp h
      rw [reindexed A A A,reindexed A A A,h,hp,membership A];simp
   exact ⟨U,hu,hc, solely W W (hs.lap hb) billed_id (h.lap hu) (Albedo.base _) (Eventually.of_forall fun i=>Eq.trans (hy _|>.1) (main_zero .. |>.symm)), solely W W (hb.lap hs) billed_id (hu.lap h) (Albedo.base _) (Eventually.of_forall fun i=> (hy _|>.2).trans (main_zero .. |>.symm))⟩
 apply reindex (W.markedP p) _
 rw [← ledger_lade, hz]; exact hv p (hN.trans (by exact_mod_cast hvp))
end front
end YM.RegulatorIR.Oracle

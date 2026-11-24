import YM.MS.Fiddle.Born
/-!
# Choosing a uniform oscillatory displacement
In lattice volume use the unfolded mesh and require one-coordinate distance in scaled period. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fiddle
open Function Set Filter Finset Metric Real MeasureTheory Momentum Tone Landau Osc Osc.Snap Lattice
open scoped Topology ContDiff
variable {I E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {S:Scale I}{K:Cost I E}{f:I→ QP× E→ℂ}{a b w:I→ℝ}{V:I→QP}{r M:ℝ}
lemma flare {u:QP}(h:0<r)(he:r≤‖u‖): ∃ x:QP,Tone.bill u x= -1∧ ‖x‖≤ π/r:= by
    have H:r>0:= h; obtain ⟨k,hk⟩ : ∃ i:Axis, r≤|u i|:= by by_contra! hx; exact he.not_gt ((pi_norm_lt_iff h).mpr hx);
    let Y:= u k; have hy:|Y| >0:= h.trans_le hk; have hv:Y≠0:=abs_pos.mp hy; let F:=π/Y; let X: QP:= Pi.single k F; have ht: pairing u X= π:= by simp [pairing,X,Pi.single_apply, mul_ite]; change Y*_=π; unfold F; field_simp
    refine ⟨ X,by rw [Tone.bill,ht,mul_comm]; exact Complex.exp_pi_mul_I,?_ ⟩; apply (pi_norm_le_iff_of_nonneg (div_nonneg pi_pos.le h.le)).mpr; intro i; unfold X; by_cases he:i=k; · subst i; simp [F,abs_of_nonneg Real.pi_pos.le,norm_eq_abs]; apply div_le_div_of_nonneg_left _ h hk; exact Real.pi_pos.le
    simp [he]; exact div_nonneg Real.pi_pos.le h.le
variable {μ:I→Measure QP} {d j:ℕ}
lemma lounge (p q x:QP): Tone.bill p (x-q)= (Tone.bill p q)⁻¹ * Tone.bill p x:= by rw [sub_eq_add_neg,rightadd, Tone.inverse,mul_comm]
abbrev quoteF (V:I→QP)(μ:I→Measure QP)(f:I→ QP× E→ℂ):= waveInt (fun i=> Tone.bill (V i)) μ f
-- continuous contour gain.P.P
lemma large (H:∀ i,0<w i)(he:∀ i, w i≤‖V i‖)(hr:∀ i,S.length i ≤ M*w i)(hL:M≥0)(hx:pole S f a) (j:ℕ): Bound S ( quoteF V (fun _=>planeF) f ) (fun i=> a i* fee S i*(S.length i/w i)^j):= by
   choose x hx' hX using fun i=> flare (H i) (he i); let B(i):QP:= x i; let P(i:E):Measure QP:=planeF; let U(i:I):= (Tone.bill (V i) (x i))⁻¹
   have hz(i:I): S.length i * ‖x i‖ ≤ π * M:= by
       obtain hv := hX i; have hs := S.pos i; refine ( mul_le_mul (hr i) hv (norm_nonneg _) (mul_nonneg hL ( H i|>.le)) ).trans_eq ?_; field_simp [(H i).ne']
   obtain hk:= rapid_pay ( E:=QP) (fun i=>sailor (V i)) (Tall S 5 (by omega)) hx (fun i=>lounge (V i) (x i)) hz (mul_nonneg Real.pi_pos.le hL) (fun i=> measurePreserving_add_left planeF (x i)) hX 1 zero_lt_one (V:=U) (by intro i; simp [ U,hx',show (1:ℂ)+1=2 by ring]) ( tom S (E:=E) 5 (by omega) ) j;
   apply hk.raise; refine ⟨ π^j,pow_pos Real.pi_pos j,0,fun i p hp=>?_⟩; rw [pow_zero,mul_one]; apply le_of_eq; dsimp only; rw [show S.length i*( π/w i )=π*( S.length i/w i ) by ring,mul_pow]; ring
-- for remote; if fraction = g-π maybe choose exact. Define allowing shifted by mesh via integer at distances. Need lemma no zeros and uniform cap compact.
def boundX (r:ℝ) (x:ℝ): Prop:= ∀ i:ℤ,r≤ |x+tier*i|
lemma escape (h:0< r)(hx:r≤ |M| ∧ |M|≤tier-r): 1≠bellZ M := by
   intro ht; obtain ⟨n,hn⟩:= Complex.exp_eq_one_iff.mp ht.symm; obtain he:= congr_arg Complex.im hn; simp at he; obtain ⟨h1,h2⟩:=hx; rcases lt_trichotomy n 0 with h4|h4|h4; ·
      have hu: (n:ℝ) ≤ -1:= by exact_mod_cast (show n ≤ -1 by omega); -- patch
      unfold tier at *; have H':=neg_le_of_abs_le h2; nlinarith [Real.pi_pos]
   · rw [h4] at he; simp only [Int.cast_zero,zero_mul] at he; simp [he] at h1; linarith
   unfold tier at *; have hu: 1≤(n:ℝ):=by exact_mod_cast h4;
   have H':=le_of_abs_le h2; nlinarith [Real.pi_pos]
lemma farBolt (h:0<r): ∃ C:ℝ,0<C∧∀ M:ℝ,r≤ |M|→ |M|≤tier-r → C ≤ ‖(1:ℂ)-bellZ M‖:= by
   let X:=Set.Icc ( - (tier-r)) (tier-r) ∩ {x:ℝ | r≤ |x|}; have hx (x:ℝ): x∈X ↔ r≤|x|∧ |x|≤tier-r:= by simp only [X,Set.mem_inter_iff,Set.mem_Icc,abs_le,Set.mem_setOf]; tauto
   rcases X.eq_empty_or_nonempty with ht|ht; exact ⟨1,zero_lt_one,fun i hi hv=> False.elim (Set.notMem_empty  i (ht ▸ ((hx i).mpr ⟨hi,hv⟩)))⟩
   obtain ⟨x,hp,hc⟩:= ( isCompact_Icc.inter_right ( isClosed_le continuous_const continuous_abs ) : IsCompact X )|>.exists_isMinOn ht (show ContinuousOn (fun p:ℝ=>‖(1:ℂ)-bellZ p‖) X from (( continuous_const.sub bellZ_p.continuous ).norm).continuousOn)
   exact ⟨_,norm_pos_iff.mpr ( sub_ne_zero.mpr (escape h ((hx x).mp hp))), fun i hi ht=> hc ((hx i).mpr ⟨hi,ht⟩)⟩
-- version requiring direct compact dist in component of net (periodic via H axes), after taking torus representative separate.L
lemma atom (i:Axis)(q:QP)(b:ℝ): pairing q (whole b (Lattice.step i))=q i * b:= by rw [show whole b (Lattice.step i)=b • Tone.embed (Lattice.step i) from rfl]; simp [pairing,apply_ite,Pi.smul_apply] -- `step` amb
lemma sharp (i:Axis)(b:ℝ): ‖whole b (Lattice.step i)‖ ≤ |b|:= by rw [show whole b (Lattice.step i)=b • Tone.embed (Lattice.step i) from rfl,norm_smul]; apply mul_le_of_le_one_right (by positivity); apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro a; rw [emb_step]; split <;> norm_num
lemma bill_absneg (p:ℝ): ‖(1:ℂ)-(bellZ p)⁻¹‖ = ‖(1:ℂ)-bellZ p‖ := by rw [show (bellZ p)⁻¹=star (bellZ p) from ?_,← star_one ℂ, ← star_sub,norm_star]; congr 2; simp; unfold bellZ; rw [ ← Complex.exp_neg ]; change _=(starRingEnd ℂ) (Complex.exp _); rw [← Complex.exp_conj]; congr 1; simp
lemma RemoteOsc (hr:0<r)(hp:∀ i, ∃ j:Axis, r≤ |V i j*b i| ∧ |V i j*b i| ≤ tier-r ) (hK:∀ i,S.length i*b i≤M)(hb:0≤M)(hv:∀ i,0<b i)(hf: pole S f a) (k:ℕ): Bound S ( quoteF V (fun i=>rail (b i)) f ) (fun i=> a i* fee S i*(S.length i*b i)^k):= by
   choose j hj hu using fun i=>hp i; let P (i:I):= whole (b i) (Lattice.step (j i)); have hL(i:I): ‖P i‖≤ b i:= by simpa only [P, abs_of_pos (hv i)] using sharp (j i) (b i)
   obtain ⟨C,hC,hx⟩:= farBolt hr;
   exact rapid_pay (fun i=>sailor (V i)) ( local_p hv hb hK ( show 5>4 by omega )) hf (fun i x=>lounge ( V i ) ( P i ) x ) (fun i=>( mul_le_mul_of_nonneg_left (hL i) (S.pos i).le).trans (hK i)) hb (fun i=> Snap.boom ( hv i ) _) hL C hC (fun i=>by rw [show Tone.bill (V i) ( P i )=bellZ ( V i ( j i )* b i ) from congr_arg bellZ (atom _ _ _) , bill_absneg]; exact hx _ (hj i) (hu i)) (spending hv hb hK (show 5>4 by omega)) k
end YM.MS.Fiddle

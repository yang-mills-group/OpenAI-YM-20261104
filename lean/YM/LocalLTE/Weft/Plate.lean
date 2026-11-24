import YM.LocalLTE.Weft.Germs
/-! Weft impulses and version band after variable evaluation. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Weft
open Filter Set Metric Function MeasureTheory Finset
open Tensor Analysis ConnectedActivityE6.Blaze
open scoped Topology BigOperators Classical ContDiff
variable {E F A G' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup A][NormedSpace ℝ A] [NormedAddCommGroup G'][NormedSpace ℝ G']
variable {k n m : ℕ} {C d v w :ℝ} {f:ℝ→E→ F}
namespace Hex
lemma applyX (L:E→ₗ[ℝ]F→ₗ[ℝ] A){s:ℝ→E}{u:ℝ→F}(h:Hex k s)(H:Hex m u): Hex (k+m) (fun i=> L (s i) (u i)):=by
   let U t:=∑ i,mark k i t • L (pick k s i) (u t)
   apply Hex.change (f:=U) ?_ (?_); swap
   · intro i hi; change _ = L (s i) (u i); rw [h.seen hi,map_sum,LinearMap.sum_apply]; simp_rw [map_smul, LinearMap.smul_apply]; rfl
   exact Hex.total Finset.univ fun j _=> Hex.wallet (f:=fun i=>L (pick k s j) (u i)) ((Hex.held (j:=j) (1:ℝ)).change (fun s hs=> show mark k j s*1=_ from mul_one _)) (H.alpha _)
lemma biv (L:E→L[ℝ]F→L[ℝ] A){s:ℝ→E}{u:ℝ→F}(h:Hex k s)(H:Hex m u) : Hex (k+m) (fun i=>L (s i) (u i)):=by
    let f:E →ₗ[ℝ] F →ₗ[ℝ] A:= {
       toFun x:= (L x).toLinearMap
       map_add' a b := LinearMap.ext (fun x=>by rw [map_add]; rfl)
       map_smul' a b:= LinearMap.ext fun x=>by rw [map_smul]; rfl }
    exact Hex.applyX f h H
lemma chord {Y:ℝ→T E F k}{x:ℝ→E}(h: Hex n Y)(hw:Hex m x): Hex (n+m*k) (fun s=> diagonal (Y s) (x s)):=by
    induction k generalizing F n with
    | zero=>
       let e: T E F 0 →ₗ[ℝ] F := (continuousMultilinearCurryFin0 ℝ E F).toLinearEquiv.toLinearMap
       rw [mul_zero,add_zero]; apply (h.alpha e).change; intro i hi; change e (Y i)=(Y i) _; rw [show e (Y i)=Y i (fun _=>0) from rfl]; exact congr_arg (Y i) (Subsingleton.elim ..)
    | succ i ih=>
       let E':= E →L[ℝ] F
       let G : T E F (i+1) →ₗ[ℝ] T E E' i := (continuousMultilinearCurryRightEquiv ℝ (fun _:Fin (i+1)=> E) F).toLinearEquiv.toLinearMap
       have hg:= ih (h.alpha G)
       let U:=(ContinuousLinearMap.id ℝ E'); have hh:= Hex.biv (s:=fun s=> diagonal (G (Y s)) (x s)) (h:=hg) U hw; rw [Nat.mul_succ, ← Nat.add_assoc]; apply hh.change
       intro s hs; unfold Tensor.diagonal; change ((Y s).curryRight (fun _=> x s)) (x s)=Y s (fun _=>x s); rw [ContinuousMultilinearMap.curryRight_apply]; congr 1; ext j; induction j using Fin.lastCases <;> simp
end Hex
namespace Arp
-- multidirectional CMLM estimate
lemma stemB {f:E→F} {x:E} (hf:Brush k C v f x) (i:ℕ) (L:T F A i): Brush k (‖L‖*C^i) ((i:ℝ)*v) (diagonal L ∘ f) x:= by
    induction i generalizing A with
    | zero =>
       have he: Tensor.diagonal L=(fun _=> L (fun _=>0)):=funext fun y=> congr_arg L (Subsingleton.elim ..)
       simp only [he,pow_zero,mul_one]; have hL : Brush k (‖L (fun _=>0)‖) (↑(0:ℕ)*v) ((fun _:F => L (fun _=>0)) ∘ f) x:= Brush.certified (by simp) _
       exact hL.climb (L.fin0_apply_norm.le) le_rfl
    | succ i ih=>
       let Q:= L.curryRight; have he:= ih Q; let R: (F →L[ℝ] A) →L[ℝ] F →L[ℝ] A:=ContinuousLinearMap.id ..
       apply ((he.twins hf R).climb ?_ ?_).shimmy
       · refine Eventually.of_forall fun y=>?_ ; change Tensor.diagonal L (f y)= Q (fun _=>f y) (f y); unfold Q; simp only [ContinuousMultilinearMap.curryRight_apply]; unfold Tensor.diagonal; congr 1; ext k; induction k using Fin.lastCases <;> simp
       · have hq:0≤ (‖Q‖*C^i*C):= mul_nonneg (mul_nonneg (ContinuousMultilinearMap.opNorm_nonneg Q) (pow_nonneg hf.nonneg _)) hf.nonneg
         refine le_trans (mul_le_of_le_one_left hq (ContinuousLinearMap.norm_id_le)) (le_of_eq ?_); unfold Q; rw [L.curryRight_norm]; ring
       push_cast; ring_nf; exact le_rfl
lemma streamH {J:E→L[ℝ] F}(q:F)(hz:‖q‖≤1) (he:‖J‖ ≤1) {g:ℝ→F→A} (p:ℕ) (h:Arp k m C g)(hn:n≤ m) : Arp (k+n) p ((n:ℝ)*(C*2^n*(1 + (n:ℝ))^p)) (fun s x=> stem n (g s) (s • q+J x)):=by
   let P(i:ℕ)(s:ℝ)(x:E):= diagonal (coeff (g s) i 0) (s • q+J x); let d:= n; let t:= C*2^n*(1 + (n:ℝ))^p
   have ht i (hi:i∈ range n): Arp (k+n) p t (P i):=by
      have hj:i<n:=Finset.mem_range.mp hi; let C' s:=coeff (g s) i 0
      have he':Hex k C':=h.coeffHex _ (hj.le.trans hn)
      refine ⟨Hex.invert fun x=>?_ ,fun s hs=>?_⟩
      · have hk: Hex 1 fun s:ℝ=> s • q:=by refine (Hex.held (k:=1) (⟨2,by decide⟩) q).change (fun i hi=> ?_); dsimp only; congr 1; change i^(2:ℕ)/i^1=i; rw [pow_one,pow_two,mul_div_cancel_right₀ _ (hi.1.ne')]
        exact (Hex.chord he' (hk.add (Hex.constant (J x)))).grow (by omega)
      let u (x:E):= q+J x; have hp:Brush p 1 1 J 0:= Brush.linearB J (by rw [map_zero,norm_zero]; linarith) (he.trans_eq (one_mul (1:ℝ)).symm) zero_le_one -- edit
      have h' : Brush p 2 1 u 0:= by rw [show (2:ℝ)=1+1 from (by norm_num)]; exact ((Brush.certified zero_le_one _).climb hz le_rfl|>.gathering hp)
      have hx := (Arp.stemB h' _ (s^i • C' s));
      refine (hx.trim.climb (?_) le_rfl).shimmy (Eventually.of_forall fun u=> (by unfold P; dsimp only; rw [map_smul,← smul_add, homogeneous]; rfl)) -- edit
      have hv:(i:ℝ) ≤ n:= Nat.cast_le.mpr hj.le
      have hu:1+(i:ℝ)*1 ≤ 1 + (n:ℝ):=by linarith
      exact mul_le_mul (mul_le_mul (h.postage _ (hj.le.trans hn) s hs) (pow_le_pow_right₀ (by norm_num) hj.le) (by positivity) h.nonneg) (pow_le_pow_left₀ (by positivity) hu _) (by positivity) (mul_nonneg h.nonneg (by positivity))
   have hx:= sumQ (range n) P (fun _=> t) ht; rw [sum_const,card_range,nsmul_eq_mul] at hx; refine Arp.adjust hx (fun s hs=> funext fun x=> ?_); unfold stem; rw [Finset.sum_apply]; rw [Finset.sum_apply]
end Arp
namespace Warp
lemma stencil {J:E→L[ℝ] F}(q:F)(hz:‖q‖≤1)(he:‖J‖≤1){g:ℝ→F→A}(p:ℕ)(h:Warp k m C g)(hn:n≤ m) : Arp (k+n) p ((n:ℝ)*(C*2^n*(1 + (n:ℝ))^p)) (fun s x=> stem n (g s) (s • q+J x)):=by
   obtain ⟨f,H,hp⟩:=h.hymn; refine (Arp.streamH q hz he p H hn).adjust (fun s hs=> funext fun x=>?_)
   have he: stem n (g s)=stem n (f s):=by unfold stem; apply sum_congr rfl; intro i _; rw [GermCoeff i (hp _ hs)]
   rw [he]
end Warp
end YM.LocalLTE.Weft

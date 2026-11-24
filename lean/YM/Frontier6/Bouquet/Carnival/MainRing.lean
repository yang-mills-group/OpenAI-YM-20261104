import YM.Frontier6.Bouquet.Carnival.Rhythm

/-! Uniform prices per term; may compare the rsums directly in absolute
 normal estimates. Delta for the common regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I J L Y: Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
variable (K:Final C F S){P:Ensemble}(d:Slot →ℕ)(v:(j:Slot)→ S.Field (d j))(i:P) (p:Part d i) (M:Pod→ℝ) (R: Air (S:=S) P I L Y)(B C':ℝ)(n:ℕ)
def stageP (s a r:ℝ)(x:Seats P)(H: Patron S P Y)(f:Full (fiber P)):Y:= uKernel K d v s a P x (moves K i H p x) (supplements i p s r f)
abbrev titled (s a r:ℝ)(x:I):Full (fiber P)→ Y := stageP K d v i p s a r (R.region x).center (R.sky x)
lemma stage_land (s a:ℝ)(z:Swing i p R B)(f:Full (fiber P)):
   let Φ:=landscape K i M p R B; launch K d v (Φ.region z) (Φ.sky z) s a (supplements i p s z.radius f)=titled K d v i p R s a z.radius z.here f:=by intro u; unfold launch; rw [show (u.region z).center = (R.region z.here).center from land_center ..]; rfl
section
variable {u n' b r: ℝ}{s a:ℝ}{x:I}{f:Full (fiber P)}
lemma titled_void (hf:supplements i p s r f=0): titled K d v i p R s a r x f=0:=by unfold titled stageP; rw [hf]; exact select_zero _ _ _ _ _ _
end
-- explicit entry commission
abbrev tariff (x:I)(u ε δ D: ℝ)(r:ℝ):ℝ:= Rhythm δ (r/(R.lengths x i))*(D*u*R.freight d x ε)
structure Announces (ε δ D:ℝ) : Prop where
   pos : 0≤D
   keep : ∀ x:I,∀ (f:Full (fiber P))(s a r U:ℝ),0<a → Length P M s → 0<r → r≤1 → R.suitable x C' s → Fellow P (R.lengths x) (R.region x) B f n U → ‖titled K d v i p R s a r x f‖≤ tariff d i R x U ε δ D r
   continuousUp : ∀ x:I,∀ (f:Full (fiber P))(s a b r U:ℝ),0<a→a≤b→ Length P M s→0<r→ r≤1→ R.suitable x C' s → Fellow P (R.lengths x) (R.region x) B f n U→ ‖titled K d v i p R s a r x f - titled K d v i p R s b r x f‖ ≤ tariff d i R x U ε δ D r*R.delta x b
section
variable {ε δ:ℝ}(he: R.Welkin M) (h:Dais K d P M)(hf:Air.Hosts K R)(hp:Seated K d v i n)(hB:1≤ B)(hC:1 ≤ C')(ht:0<δ)(hd:δ ≤1/4)(hh:2*δ≤ε)
include he h hf hp hB hC ht hd hh
lemma winnings : ∃ D:ℝ, Announces K d v i p M R B C' (n+toil i p n) ε δ D:=by
    let X:= landscape K i M p R B; let N:=n+toil i p n; obtain ⟨D,hD,H⟩:=teams K i M p R B C' he n hB hC
    obtain ⟨V,hV⟩:= hp h (land_welkin K i M p R B h he) (prize K i M p R B h he hf (zero_lt_one.trans_le hB)) (max B 2) (widened B C') δ (hB.trans (le_max_left ..)) (hC.trans (le_max_left ..)) ht
    let Z:=V*D*Zoom i d B; let Q(s r:ℝ)(f):=supplements i p s r f; have hP:=hV.pos; have hz:0 ≤ Z:= mul_nonneg (mul_nonneg hP hD) (le_trans zero_le_one (le_max_left ..));
    have hv(z: Swing i p R B)(s:ℝ)(f:Full (fiber P)): Flare i (Q s z.radius f) (X.lengths z i):=by rw [show X.lengths z i=z.radius from (congr_fun (techno K i M p R B z) i).trans (update_self ..)]; exact sprinkles i p z.pos
    have ha(x:I){U r:ℝ}(he':0 ≤ U)(hr:0<r):0 ≤ tariff d i R x U ε δ Z r:=mul_nonneg (rhythm_nn (div_pos hr (R.length_pos x i)).le) (mul_nonneg (mul_nonneg hz he') (R.freight_pos d he _ _).le)
    refine ⟨Z,hz,fun x f s a r U h' hl hr ht' H' hc=>?_,fun x f s a b r U h' hb hl hr ht' H' hc=>?_⟩
    · have hu:= hc.costs.nonneg; by_cases hj:supplements i p s r f=0; rw [titled_void K d v i p R hj,norm_zero]; exact ha x hu hr
      obtain ⟨z,hz',hv',h⟩:= accepted K i M p R B C' f x hB hl.pos hr ht' H' hc.local_ hj; subst x; subst r; rw [← stage_land K d v i p M R B s a z]; apply (hV.price z _ _ _ _ hl h' h (H z f s U hl H' hc) (hv z s f)).trans; let W:=z.radius/(R.lengths z.here i); change V*(D*U*Tempo i p W)*X.freight d z δ ≤ Rhythm δ W*(V*D*_*U* R.freight d z.here ε); calc
        _ = V*D*U*(Tempo i p W*X.freight d z δ):=by ring
        _ ≤ V*D*U*(Zoom i d B*Rhythm δ W*R.freight d z.here ε) := mul_le_mul_of_nonneg_left (moves_freight K i M p R B z he ht hh hd) (by positivity)
        _ = _ := by ring
    have hu:=hc.costs.nonneg; by_cases hj:supplements i p s r f=0; rw [titled_void K d v i p R hj,titled_void K d v i p R hj,sub_self,norm_zero]; exact mul_nonneg (ha x hu hr) (R.delta_pos _ (h'.trans_le hb)).le
    obtain ⟨z,hz',hv',h⟩:= accepted K i M p R B C' f x hB hl.pos hr ht' H' hc.local_ hj; subst x; subst r; rw [← stage_land K d v i p M R B s a z,← stage_land K d v i p M R B s b z]; apply (hV.discount z _ _ _ _ _ hl h' hb h (H z f s U hl H' hc) (hv z s f)).trans; let W:=z.radius/(R.lengths z.here i); change V*(D*U*Tempo i p W)*X.freight d z δ*X.delta z b≤ Rhythm δ W*(V*D*_*U* R.freight d z.here ε)*R.delta z.here b; calc
        _ = V*D*U*(Tempo i p W*X.freight d z δ* X.delta z b):=by ring
        _ ≤ V*D*U*(Zoom i d B*Rhythm δ W*R.freight d z.here ε* R.delta z.here b):= mul_le_mul_of_nonneg_left (moves_error K i M p R B z he ht hh hd (h'.trans_le hb)) (by positivity)
        _ = _ := by ring
end
-- rsums included
lemma ann_play (he: R.Welkin M) (h:Dais K d P M){x:I}{s a:ℝ}{f:Full (fiber P)}(hh:Length P M s)(hf:Fair f (R.region x).foot (R.region x).center):
    let c:= (R.region x).center; let H:= R.sky x; pollen K (prepared K (common a) d v s) (common a) i c (moves K i H p c) (demands i s p f)= ∑' j:ℕ, titled K d v i p R s a (Normal.pitch j) x f:=by
   let A:=common a; let T:=prepared K A d v s; let g:=demands i s p f; intro c H; let R':= shift i p (R.region x) M; let J:=moves K i H p c; change pollen K T A i c J g = _; have ht:= he.safe x; have hh':Fair g R'.foot c:= escort i p ht hh hf; have hx: c= R'.center:= (shifts ..).symm; apply Eq.trans (attends K i J c T A g ⟨R'.foot, unflag i p h ht (he.smooth _),hh'⟩ (fun z hz=>mem_closedBall_zero_iff.mpr ((pricesR i z (shift_cozy i p ht) g (hx ▸ hh') hz).trans (h.zenith _ (stage_in i.property))))) (_); simp only [titled,stageP,supplement,uKernel]; rfl -- check
end YM.Frontier6.Bouquet.Atelier

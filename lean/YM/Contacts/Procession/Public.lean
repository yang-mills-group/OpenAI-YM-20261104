import YM.Contacts.Procession.Praxis
/-! # One-mark projection at cover potential rank/timing. Keep coordinate economy phase-independent on shelves in this epoch. -/
noncomputable section
namespace YM.Contacts.Procession.Cartons
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open MeasureTheory Labels Source Drops Analysis Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Spine Origin
open Milling Milling.Steam Milling.Forge Milling.Garf Tensor MultiNext.SignedSource Pattern Shuttle Tide
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff Matrix.Norms.Frobenius
open Morning Mediator Next.Foundations
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 90000
set_option autoImplicit false
variable {G:Gauge}{X Y: Type}{m:Side}{F:Cohort G}{d k h u n:ℕ}(B: Labels.Frame G d)
-- read on entire Mark.App.No power prices assumed.
open Planned.PrimaryIntegral295 WardBin Push.Local
abbrev cotton (Q:Snap G d→ℝ) : Snap G d→ℂ:= Complex.ofRealCLM ∘ Q
namespace Shape
variable {B}{Q:Snap G d→ℝ}{q:B.Coeff}
lemma align (h:Shape B Q q)(J:Jet G)(hk:k ≤ d) : iteratedDeriv k (fun x=> Labels.read (scaleJet J x) (B.coords.symm q).val) 0= ((iteratedDeriv k (Q∘ glide J d) 0:ℝ):ℂ):= by
    let i:Fin (d+1):= ⟨k,Nat.lt_succ_of_le hk⟩; exact ((runProbe_eq B (J,i) q).symm.trans (h.read (J,i)))
lemma clarity (h:Shape B Q q): star q=q:= by
    let A:= B.coords.symm q; let H:=realBar A; have he:H=A:=jet_test_ext H A fun J k hk=>?_ ; · exact (show _=_ from (show _=q from funext fun i=> by rw [Pi.star_apply,← B.conj_basis q i, show realBar _=_ from he, B.coords.apply_symm_apply]))
    let L:= (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap; let X:= fun t=> Labels.read (scaleJet J t) A.val; rw [show (fun x=> Labels.read (scaleJet J x) H.val)= L ∘ X from funext (fun t=> conj_value A.val _ )]; have ht:iteratedDeriv k (L ∘ X) 0=L (iteratedDeriv k X 0):=(DFunLike.congr_fun (L.iteratedFDeriv_comp_left (read_smooth J A.val _ |>.contDiffAt) (n:=k) (i:=k) le_rfl) (fun _=>1)); rw [ht]; unfold X A; rw [h.align J hk]; change star _ = _; simp
private lemma roll (J:Jet G)(d:ℕ)(t:ℝ): glide J d t= engineered t (trunk d J):= by funext i; rw [engineered_at]; rfl
lemma badge (h:Shape B Q q)(H:ContDiffAt ℝ d Q 0)(J:Jet G)(hk:k≤ d): leading k (fun t=> Labels.read (scaleJet J t) (B.coords.symm q).val) = leading k (fun t=> cotton Q (engineered t (trunk d J))) := by
    unfold leading; rw [h.align J hk]; have he:ContDiffAt ℝ d (Q ∘ glide J d) 0:= ContDiffAt.comp _ (by rw [glide_zero]; exact H) ((glide_ever d J).contDiffAt.of_le le_top); apply congr_arg; rw [show (fun t=> _)=_ from (show (fun t=> cotton Q (engineered t (trunk d J)))=Complex.ofRealCLM ∘ (Q ∘ glide J d) from funext fun t=> congr_arg (cotton Q) (roll J d t).symm)]; exact (DFunLike.congr_fun (Complex.ofRealCLM.iteratedFDeriv_comp_left he (Nat.cast_le.mpr hk)) (fun _=>1)).symm
lemma reads_tile (h:Shape B Q q)(H:ContDiffAt ℝ d Q 0)(hk:k≤d)(ht:n≤ d) : (gradePart (k,n) (B.coords.symm q)).val= WardBin.tile (Tensor.coeff (cotton Q) n 0) k := by
    let A:= B.coords.symm q; let p(i:ℕ):= gradePart (k,i) A; let y(i:ℕ):= WardBin.tile (Tensor.coeff (cotton Q) i 0) k; let s:= Finset.range (d+1); have hx(i:ℕ): pureDegree (p i).val k i:= (Labels.pure_grade ..).1 (gradePart_mem ..); have hy(i:ℕ): pureDegree (y i) k i:= tile_grade ..; have hK: ContDiffAt ℝ d (cotton Q) 0:= Complex.ofRealCLM.contDiff.contDiffAt.comp _ H
    have hw : ∑ i∈s,(p i).val=∑ i∈s,y i:= eval_ext _ _ fun J=> by simp only [map_sum]; exact ( (Parts.scaled_label_leads A hk J).symm.trans ( (h.badge H J hk).trans (Parts.leading_snap_sum hK hk J)))
    have hh(f:ℕ→Pol G)(h:∀ i,pureDegree (f i) k i): piece (k,n) (∑ i∈s,f i)= f n:= by
        rw [map_sum, Finset.sum_eq_single n]; exact MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same (show MvPolynomial.IsWeightedHomogeneous bidegree (f n) (k,n) from h n);
        · intro i hi he; exact MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne (k,n) (show MvPolynomial.IsWeightedHomogeneous bidegree (f i) (k,i) from h i) (fun H=>he (congr_arg Prod.snd H).symm)
        exact fun he=> (he (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))).elim
    exact (hh (fun i=>(p i).val) hx).symm.trans ((congr_arg (piece (k,n)) hw).trans (hh y hy))
-- with cutoff h−|ξ|. enough for all pol directions
lemma antenna (h:Shape B Q q)(k:ℕ)(H:∀ i:B.Index,(B.grades i).1=k → q i=0) (i:ℕ): gradePart (k,i) (B.coords.symm q)=0 := by
    let V:= B.coords.symm q; rw [← B.basis.sum_repr (B.coords.symm q),map_sum]; refine sum_eq_zero fun a _=> ?_; rw [map_smul]; by_cases he:(k,i)=B.grades a; · rw [show B.basis.repr (B.coords.symm q) a=q a from (congr_fun (B.coords.apply_symm_apply q) a), H a (congr_arg Prod.fst he.symm),zero_smul]
    rw [gradePart_zero (B.basis a) _ _ he (B.pure a),smul_zero]
lemma detects (z:B.Index) (h: Shape B Q q) (H: ContDiffAt ℝ d Q 0) : (gradePart (B.grades z) (B.coords.symm q)).val= WardBin.tile (Tensor.coeff (cotton Q) (B.grades z).2 0) (B.grades z).1:= h.reads_tile H (B.bound _) (Film.second_fits ..)
end Shape
lemma silent_projection (hh:Tags F)(H:h≤ d)(hx: d ≤ n) (hq:d*(d+1)≤u)(hY:∀ i:B.Index,(B.grades i).1≤h → exhibit B (panel F d u n) i=0): Morning.unreads F d u n h:= by
   intro v i hi; rw [show (fun t=> _)=_ from (show (fun t=> panel F d u n (Weighted.scaled (fun j:Fin (d-1)=> j.val+2) (Mom.deck) t v))= panel F d u n ∘ glide (expand d v) d from funext (fun t=> congr_arg (panel F d u n) (Mom.deck_price v t)))]; let Q:=panel F d u n; let hK:= gauges B hh hx hq; let J:= expand d v; let Y:= B.coords.symm (exhibit B Q); let R:= fun t:ℝ=> Labels.read (scaleJet J t) Y.val; have he := Parts.scaled_label_leads Y (hi.trans H) J
   rw [Finset.sum_eq_zero (fun j a=> by rw [show gradePart (i,j) Y=0 from hK.antenna i (fun x hx=> hY x (hx ▸hi)) j]; simp)] at he
   unfold leading at he; have ht:= hK.align J (hi.trans H); change iteratedDeriv i R 0 = _ at ht; change (_:ℝ) • iteratedDeriv i R 0=0 at he; rw [ht] at he; exact Complex.ofReal_eq_zero.mp (or_iff_right (by positivity:_root_.Not ((i.factorial:ℝ)⁻¹=0))|>.mp (smul_eq_zero.mp he))
end YM.Contacts.Procession.Cartons

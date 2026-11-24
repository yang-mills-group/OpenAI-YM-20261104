import YM.FVA2.Neck
/-!
# Probe on Panel F. Scarce detectors. interpolation and loan identities for κ.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.FVA2.Panel
open Function Filter Set MeasureTheory Pert Pert.Position Maxwell Maxwell.Free Pert.RawLabels PositionX PositionX.Jet PositionX.Ribbon PositionX.Detector PositionX.Bend Elegant PayAll WorldJet Verne Strat ColorCode MS.Book MS.Book.Convolve PowerSeries Clock
open scoped Topology ContDiff Classical
variable {G:Gauge}{F:Labels.Frames G} {m n d e k:ℕ}
section shifts
variable (A B:Panel F){P Q: Strat F} (s t:ℝ)
-- sc power formula and coherent.
def swell := (A.slide s).flip (Λ F s)
lemma scl (T:Strat F) : swell (A.flip T) s= (swell A s).flip (Λ F (-s)*T*Λ F s):= by unfold swell; rw [ ← flip_slide, flip_mul, flip_mul, ← mul_assoc, ← mul_assoc, north,one_mul ]
-- hack: operator uses left? `Λ s*(Λ (-s)*T*Λ s)= T*Λ s`. OK
lemma swell_steps : (A.swell s).swell t=A.swell (s+t):= by unfold swell; rw [ ← flip_slide,flip_mul,Strat.east,slide_steps ]
lemma join_scl (v:Word ℝ)(h:light v): swell (A.join v) s=(swell A s).join v:= by unfold swell; rw [ ← join_slide, join_flip (A:=_) (φ:=v) (h:=h), resetR s h ]
lemma z1 : A.swell 0=A:= by unfold swell; rw [ slide0 ]; exact leading _
lemma static_heated (b:Buffer F d)(p: PayAll.reprK F d m) (v:Fin m→ E F d) (k:ℕ) : heated p (just b) k v=p k (frameC F b ∘ v):= by
    let S:= keynote ∘ p; let f:= delay S k; have hp:= appears_delay S k; have h := appears_market hp ( Act.static ( n:=k ) b ); have hz : (fun s=>market F ((fun _:ℝ=>b) s) ( f s ))= pulls (frameC F b) ∘ f:= rfl;
    let L:= lookie F ⟨m,v,0⟩; change L (predMarket ( just b ) S k)=_; rw [← heap (p k) (0:Test m) ]; exact congr_arg L ( h.same (hp.pull (frameC F b)) le_rfl ) -- supposed congr.L p k v; change defeq
lemma unfold_scl (x:Polyp m)(v:Fin m→ E F d) (k:ℕ) : (A.swell s).out d x k v= A.out d (shiftP s x) k (Δ F s d ∘ v):= by unfold swell flip slide; simp only []; rw [ Λwire,static_heated,frame_Øb]
-- lift title
lemma paid_scl (h:A.clearP): (A.swell s).clearP:= Panel.night _ _ ( skim A h s ) -- order
lemma grows_scl (T: Strat F)(h:T.pulse) : Strat.pulse (Λ F (-s)*T*Λ F s):= by
   intro d; unfold Stable; simp_rw [ pay, Λwire, voters ]; rw [ show T.wire d 0=0 from h d, (identity_t ( Jet.just _ 0 ) ).1 ]; unfold just; simp only [if_true ]; rw [ ← sequenced, neg_add_cancel ]; exact clear ..
end shifts
section detect
variable (A B: Panel F){P Q: Strat F}{φ v : Word ℝ} (D:(d:ℕ)→ Detector F d) {q:ℝ} (R:Booth q F)
def Fresh (A:Panel F): Prop:= A.clearP ∧ ∀ d,A.lives d 0=pureBank F d
def testable (A:Panel F) (D:(d:ℕ)→ Detector F d) {q:ℝ}(R:Booth q F) := metricT R (predMarket ((D 6).report (A.lives 6)) (A.lives 6))
def tangible := Genuine (A.testable D R)
lemma pure_ren (p:Bank F d)(v:Word (Bank F d))(hp:v 0=p)(h: light φ) : Jet.ren φ v 0=p:= by
    funext m t; ext1 w; let f:=lookie F (Pert.Position.Section.mk m w t); change ( f ∘ ren φ v ) 0= f p; rw [ ren_writes, Jet.ren_light h,comp_apply,hp ]
lemma Fresh.pre (h:A.Fresh)(H: light φ): (A.join φ).Fresh:= by refine ⟨ Panel.bright A φ h.1,fun d=>?_⟩; rw [total_book _ _ h.1]; exact pure_ren _ _ (h.2 d) H -- syntax
lemma Fresh.matrix (h:A.Fresh)(hp:P.pulse): (A.flip P).Fresh:= by
   refine ⟨ Panel.night A _ h.1,fun i=>?_ ⟩; rw [ turn_book _ _ h.1 ]; exact Verne.dawn _ _ (hp i) (h.2 i)
lemma money (h:A.Fresh)(hp:P.pulse) : A.testable D R=(A.flip P).testable D R:= by
   unfold testable; rw [ turn_book _ _ h.1 ]; obtain hm:= Verne.riseD (P.wire 6) (A.lives 6) ( D 6 ) (h.2 6) (hp 6);
   conv_lhs => rw [hm, ← together ]
lemma fieldYear (h:A.Fresh)(hp: light φ): (A.join φ).testable D R=ren φ (A.testable D R):= by
    unfold testable; rw [total_book _ _ h.1, Elegant.same (D 6) ( A.lives 6 ) hp (by rw [h.2 6]; exact lucid ( D 6 )), meter_ren _ _ _ hp ]
include D
lemma final_frame (h:A.Fresh)(hp:P.pulse)(hq:Q.pulse) (he:A.flip P=A.flip Q): P=Q:= by apply Strat.ext; intro d; apply learn _ _ ( A.lives d ) (D d) (h.2 d) (hp d) (hq d); rw [← turn_book _ P h.1, ← turn_book _ Q h.1,he ]
lemma recognized_t (h:A.Fresh)(hT:A.tangible D R)(hp:P.pulse)(hq:Q.pulse)(hv: light φ) (hh:light v) (hx: (A.join φ).flip P= (A.join v).flip Q): φ=v∧P=Q:= by
    have he' : ren φ (testable A D R)= ren v (testable A D R):= by rw [ ← fieldYear A D R h hv, money _ D R (Fresh.pre A h hv) hp, hx, ← money _ D R (Fresh.pre A h hh) hq, fieldYear A D R h hh ]; -- args order h binder.
    let u:= A.testable D R; let a:= inverse u; have he:Genuine u := hT; -- remove
    have hh': φ=v:= by apply Eq.symm; calc
       _ = ren (ren v u) a:= by rw [← asc hh (show Genuine u from hT).1, headback hT, head_ren hh]
       _ = ren (ren φ u) a:= congr_arg (fun c : Word ℝ=> ren c a ) he'.symm
       _ = _:= by rw [← asc hv (show Genuine u from hT).1, headback hT, head_ren hv]
    rw [ hh' ] at hx; exact ⟨ hh', final_frame _ D (Fresh.pre A h hh) hp hq hx ⟩
end detect
end YM.FVA2.Panel

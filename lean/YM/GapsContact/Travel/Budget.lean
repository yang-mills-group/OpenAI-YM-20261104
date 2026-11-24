import YM.GapsContact.Travel.Deck
import YM.MergeProof.South.Merman
import YM.MergeProof.North.Prax
/-! Root-cylinder costing, no longer superpolynomial. Variants of Block, Celery and Merman. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open GridApprox.Joint GridApprox
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V} {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay GapsContact.Dusk
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
variable (L:C.label d)(X:Extra.Histories.Music (C.labels.level d) C.path N p)
local notation "ζ!"=> ζ d
variable (h:Scrim C W u ψ φ δ ζ r D){b:C.label d}{Z:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)}{g:ℕ→ℝ} {Q:ℝ}
    (J:ℕ) (K:Stock.Tabs C.path.levels)
local notation "a"=> lens C N k p d L
local notation "U!"=> C.O N p ((s!).terminal b) 0
def endpointT (J m:ℕ):=Real.exp (Vac.treasury C.path.levels J+5)/paceFactor T m J
include H h K
set_option maxHeartbeats 800000 in
lemma afterquakes (hN:k<N)(hJ:C.ref d ≤ J) (hk:m ≤ k)(hw:0<w)(hX:Embrace (φ:=φ) (ζ:=ζ) (D:=D) (ψ:=ψ) C N k m p d L X Q w Z g b hN.le)(hL: Sung Y! T N p C.params W ℓ X) (hp:∀ i:ℕ,C.ref d ≤ i→∀ hi:i<N, Carol Y! T N p i (D N p i hi) (X.tone (i+1)) (X.tone i) (ψ i)) (hi:∀ b',profile (R N).activities ((X.tone N).plays b').forced=hook (R N).activities (R N).p.threshold (booster Y! (R N) 0 b'))
    (hV:Stock.Tabs.opens C.path.levels 1 J m) (n:ℕ) (hc:GridApprox.room C.path.levels J k n)(hh:Interior (GridApprox.window 0 n) (a)) (hG:G.Simple)(K':Shipper T r D) (h_X:Club T C.params Y! (ζ d) ψ J k N p (stair φ w m) D Z g hN.le) : (center C.S p (hV.1.trans (hk.trans hN.le)) 0).rootTest (C.beta N p) (backTo T N p hN.le a-U!) ≤ endpointT C J m/(w):=by
    have hK:= hJ.trans hV.1
    let t : J≤k:= hV.1.trans hk; let h':J≤N:= t.trans hN.le; let V':= (Site (C.side J p)); let X':=(center C.S p h' 0); let Z':= (center C.S p t 0); let B':= Stock.census V'
    let f := fun i=>Mix.camp C p J i; let ν (i:V'):=dye (X'.omega i) (X'.hand i)
    have hp':Migrating T m p N f:= ⟨fun j hj _=> funext fun i=> Work.I03.camp_step C p (hV.1.trans hj) i⟩
    have h₀:= Work.I03.answer G C 1 le_rfl K J m hV N (hk.trans hN.le) p h'
    have hA(s)(he:m ≤ s)(hw:s ≤ N): Edition.Spaced (C.path.levels.budget s|>.B) (f s):= fun i j hij=> by
       have ht:= h₀.2.2 s he hw i j hij; rw [mul_one] at ht; exact_mod_cast ht
    let U:=U!; let Tq:=a; let v (i:V') := stepUp (ν i) (f N i) (initial Y! T N p (-b) 0); let q (i:V'):= -X'.copy i U; let q'(i:V'):= stepUp (ν i) (f k i) (Tq); let s':=Stock.final V'
    let A:=birth B' (R N) q; let T':=couple (gust T N p N A k hN.le) (fun i=>Z'.copy i Tq)
    let G':=gust T N p k T' m hk
    have hEq(i:V') : (s!).terminal.symm (-((s!).terminal b))=-b:=by rw [map_neg,LinearEquiv.symm_apply_apply]
    have hz : v=q:=by
       funext i V; let g' := -((s!).terminal b); have he: initial Y! T N p (-b) 0= -U:= Eq.trans (show initial Y! T N p (-b) 0=C.O N p g' 0 from by unfold Family.O TransferData.cylinder; rw [hEq i]) ((C.linearO N p d 0).mk' _ |>.map_neg _)
       have hh' : f N i= X'.copyMap i 0:= (h₀.1 i).symm
       have ht:X'.copyMap i 0=X'.translateBy i:=by change (X'.omega i).act 0+_= _; simp
       unfold v stepUp; rw [he,hh',ht]; change scalar (ν i) (- U (pull _ _ V))= - X'.copy i U V
       dsimp only [ν]; simp_rw [calling]; change dot _ _= - dot _ _; unfold dot; split <;> simp <;> rfl
    have ht : q'=fun i=> Z'.copy i Tq:=by
       have hP:= Work.I03.answer G C 1 le_rfl K J m hV k hk p t; funext i V; have hh' : f k i= Z'.copyMap i 0:= (hP.1 i).symm
       have ht:Z'.copyMap i 0=Z'.translateBy i:=by change (Z'.omega i).act 0+_= _; simp
       unfold q' stepUp; rw [hh',ht]; change scalar (ν i) _= _; dsimp only [ν]; rw [calling]; rfl
    have hv : Continuous U:= C.continuousO ..
    have H' : Integrable A (prior G _):=by
       apply (Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)); refine hatCont C N p q ?_ (by rw [(H.wilson.starts ..).2]; exact bare_cont _) B'
       intro i; unfold q; refine Continuous.neg ?_; unfold Tiling.copy; by_cases hx:X'.hand i <;>simp only [hx, ↓reduceIte]; exact (hv.comp (continuous_pull ..)).star; exact hv.comp (continuous_pull ..)
    have hq':Integrable T' (prior G _):=comes T N p t hN.le U Tq H.wilson H' (Envelope.compactC hv) (cylinder_env hh)
    obtain ⟨Hq,Hv⟩:= embracing C N k m p d H f ν w L X h hN hK hk hw hX hL hp hi hp' (fun i=> (Extra.Multi.Occupancy.of_injective (Edition.injected _ _ (C.path.levels.budget m|>.B_pos) (hA m le_rfl (hk.trans hN.le))) i).trans (h.back m)) (show Drake B' _ (f m) from ⟨fun _ _ i _ j _=> hA m le_rfl (hk.trans hN.le) i j⟩) (show Drake B' _ (f k) from ⟨fun _ _ i _ j _=> hA k hk hN.le i j⟩) (show Integrable (birth B' (R N) v) _ from by rw [hz]; exact H') (show Integrable (couple (gust _ _ _ _ (birth B' (R N) v) k hN.le) q') _ from by rw [hz,ht]; exact hq')
    have hE :G' = gust T N p k (couple (gust T N p N (birth B' (R N) (fun i=>v i)) k hN.le) (fun i=>q' i)) m hk := by rw [hz,ht]
    let Qp:= paceFactor T m J*w
    let Y:= gust T N p k T' J t
    have hl: Integrable Y (prior G _):=gust_live T N p k T' hq' t
    obtain ⟨Hp,Hv⟩:=solos (M:=G') C N m p d J H w h f ν (hk.trans hN.le) hG K' hJ hV.1 (gust_live T N p k T' hq' hk) ⟨fun i hj _=>funext fun v=>Work.I03.camp_step C p hj v⟩ (fun i hi _=> (by rw [show f i=(C.S.toDepth hi p).embed from funext fun v=> (dif_pos hi)];exact Ratio.embed_injective _) ) (club_restrict C N k m p d J hk h_X) hw (show Served _ _ _ G' _ _ _ _ from (hE.symm ▸ Hq))
    have hζ:Y=gust T N p m G' J hV.1:= gust_cross hV.1 hk
    rw [← hζ] at Hp; have hw': 0<Qp:= mul_pos (pace_pos ..) hw
    have hS := spiker C N J p H s' (moment (C.beta N p) (Joint.cutoff T N p t hN.le U Tq s'.val)) (t.trans hN.le) (fun _=>hw') Hp Hv hl (conducts T N p t hN.le U Tq H.wilson H' (Envelope.compactC hv) hh hc s' J t)
    let c:=Vac.treasury (T).levels J+ (5:ℝ); let Xp:= Fintype.card V'
    let W':=moment (C.beta N p) (Joint.cutoff T N p t hN.le U Tq s'.val)
    unfold Tiling.rootTest; rw [endpointT,div_div]; refine Stock.spacer ‖W'‖ c Qp Xp (norm_nonneg _) hw' Fintype.card_pos ?_
    rw [show Poly.toll (fun _ : V'=>Qp) s'=Qp^Xp from by simp [Poly.toll,Xp,s',Stock.final], show (Fintype.card (Site (C.side J p)):ℝ)*Vac.treasury C.path.levels J+(Xp:ℝ)*(2+1+2*1)=Xp*c from by unfold c Xp V'; ring] at hS; exact hS
end YM.MergeProof.Accent
end
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay GapsContact.Dusk
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
local notation "ζ!"=> ζ d
section
open GridApprox
variable (h:Scrim C W u ψ φ δ ζ r D) (L:Stock.Tabs C.path.levels)
variable (J:ℕ) (hV : Stock.Tabs.opens C.path.levels 1 J m) {hk:m≤k}{hN:k<N}
local notation "o"=> fun i=> Mix.camp C p J i
local notation "V"=> Site (C.side J p)
local notation "Bt"=> Stock.census V
local notation "u'"=> hands C p J
local notation "α'"=> march (fun _ : V=> w) φ m k
local notation "h!"=> center C.S p (hV.1.trans (hk.trans hN.le)) 0
variable (f:Config G (C.side N p)→ℂ) (Q:Coefficient (C.labels.level d) (C.side k p)) {c t E:ℝ}
include H h L
local notation "xp"=> C.path.levels.params k
set_option maxHeartbeats 1000000 in
lemma prairie (hG:G.Simple)(K:Shipper T r D) (htJ:C.ref d ≤ J){hk:m ≤ k}(hN:k<N)(hR:GridApprox.room C.path.levels J k (lensScope C d))
   (hf : Continuous f)(E:ℝ)(hw:0 < w)(hp:0 < E)(X:Extra.Histories.Music (C.labels.level d) C.path N p)
   (hL:Sung Y! T N p C.params W ℓ X) (P:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p))(b:C.label d)(x:ℕ→ℝ)(Z:(F).Index→ ∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p))(e:(F).Index → C.label d)(g:(F).Index →ℕ→ℝ)
   (hK:Club T C.params Y! (ζ d) ψ J k N p (stair φ (2*w) m) D P x hN.le)
   (hU:(P k).exponentialEntry 0 Y! (R k)= Q.exponentialEntry 0 Y! (R k) + ((X.tone k).plays (-b)).exponentialEntry 0 Y! (R k))
   (hB:profile (R k).activities (P k).forced=profile (R k).activities Q.forced+profile (R k).activities ((X.tone k).plays (-b)).forced) (s:C.label d) (hs:b=∑ i,s i • e i)(hΨ:∀ i, Embrace (φ:=φ) (ζ:=ζ) (D:=D) (ψ:=ψ) C N k m p d (Size.axis F i) X 1 (8*E*w) (Z i) (g i) (e i) hN.le)
   (hγ:∀ i, Club T C.params Y! (ζ d) ψ J k N p (stair φ (8*E*w) m) D (Z i) (g i) hN.le)
   (hβ:(∑ i, ‖s i‖) ≤ 4*E)(hW:Interior (GridApprox.window 0 (lensScope C d)) (∑ i,(-s i) • lens C N k p d (Size.axis F i)))
    (hZ:Served (R k) (fun i=> radiant (alto T k d) (u' i) (o k i) (Q.exponentialEntry 0 Y! (R k))) (fun i=>sunny (R k) Q.forced (u' i) (o k i) (alto T k d)) (gust T N p N (birth (Bt) (R N) (fun i=> (center C.S p (hV.1.trans (hk.trans hN.le)) 0).copy i f)) k hN.le) (o k) (α') (C.path.levels.budget k).supportExponent 1) : (center C.S p (hV.1.trans (hk.trans hN.le)) 0).rootTest (C.beta N p) (backTo T N p hN.le (∑ i,(-s i) • lens C N k p d (Size.axis F i))-(-f)) ≤ endpointT C J m / w:=by
    have ht:= htJ.trans hV.1; let I:=Option (F).Index
    let q:= Size.axis F; let a':= 2*w; let v' := 8*E*w; have h':0 < v':=by unfold v'; positivity
    let W₀:= center C.S p (hV.1.trans (hk.trans hN.le)) 0; let b' i:=(s!).terminal (e i); let n:=lensScope C d; let y i:= lens C N k p d (q i); let ℓ':= ∑ i,(-s i) • y i; let r':= backTo T N p hN.le ℓ'
    let J' := hV.1.trans hk; let V':= -f; let S:= stakes C J m/w
    let w' (i:V):= -W₀.copy i V'; let K':=birth (Bt) (R N) w'
    let A:=gust T N p N K' k hN.le; let Y:= couple A (fun i=> (center C.S p J' 0).copy i ℓ')
    let U':= gust T N p k Y m hk
    have hi : Integrable K' (prior G _):=by
       apply (Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)); apply hatCont C N p w' _ (by rw [(H.wilson.starts ..).2]; exact bare_cont _) (Bt); intro i; rw [show w' i=W₀.copy i f from handneg C N p J _ _ i]
       unfold Tiling.copy; by_cases ht:W₀.hand i <;>simp only [ht, ↓reduceIte]; exact (hf.comp (continuous_pull ..)).star; exact hf.comp (continuous_pull ..)
    have hZ': Integrable Y (prior G _):=comes T N p J' hN.le V' ℓ' H.wilson hi (Envelope.compactC hf.neg) (cylinder_env hW)
    have hη:Migrating T m p k o:= ⟨fun j hj _=> funext fun i=> Work.I03.camp_step C p (hV.1.trans hj) i⟩
    have h₀:= Work.I03.answer G C 1 le_rfl L J m hV k hk p J'
    have hA: Edition.Spaced (C.path.levels.budget m|>.B) (o m):= fun i j hij=> by
       have ht:= h₀.2.2 m le_rfl hk i j hij; rw [mul_one] at ht; exact_mod_cast ht
    let D' (i:V) (j:I):=Option.elim j (1:ℂ) (fun l=>Motion.scalar (hands C p J i) (-s l)); let Z' (i:I):=Option.elim i P Z; let g' (i:I):=Option.elim i x g; let x' (i:I):=Option.elim i a' (fun _=>v')
    have hh: ∀ i:I,Club T C.params Y! (ζ d) ψ m k N p (stair φ (x' i) m) D (Z' i) (g' i) hN.le:=fun i=>by cases i;exact club_later C hV.1 hK;exact (hΨ _).descent
    have hy'(i:V): (∑ j,D' i j • liftF T Y! N p (u' i) (fun l=>o l i) (Z' j) k)= radiant (alto T k d) (u' i) (o k i) (Q.exponentialEntry 0 Y! (R k))+(center C.S p J' 0).copy i ℓ' ∧ (∑ j,D' i j • liftK T N p (u' i) (fun l=>o l i) (Z' j) k)=sunny (R k) Q.forced (u' i) (o k i) (alto T k d):=by
       rw [← handmove C k p J J']; exact plush C N k p d X Z' e (fun i=>s i) b q Q (u' i) (fun l=>Mix.camp C p J l i) (ht.trans hk) hN.le hL hs hU (fun i=> (hΨ i).exp) hB (fun i=>(hΨ i).tank)
    have hxx:∀ i,0<x' i:=(fun i=>by cases i; exact mul_pos (by norm_num) hw;exact h')
    have hpX(i): ∑ j,w*‖D' i j‖/x' j≤1:=by
       change ∑ j: Option (F).Index, w*_/_≤ _; rw [Fintype.sum_option]; simp only [x',D',Option.elim, norm_one,mul_one,norm_scalar,norm_neg]
       rw [show w/a'=(1:ℝ)/2 from by unfold a'; field_simp, ← Finset.sum_div,← Finset.mul_sum]; linarith only [(show w*(∑ i,‖s i‖)/v'≤ 1/2 from le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hβ hw.le) h'.le) (le_of_eq (by unfold v';field_simp;norm_num)))]
    obtain ⟨hL',hV'⟩:= prolonged C N k m p d H w h o u' D' Z' hN.le ht hk hZ' hη (fun i=> (Extra.Multi.Occupancy.of_injective (Edition.injected _ _ (C.path.levels.budget m|>.B_pos) hA) i).trans (h.back m)) (show Drake (Bt) _ (o m) from ⟨fun _ _ i _ j _=> hA i j⟩) hh (by
       have hx' : (fun i=> W₀.copy i f)= w':= funext fun i=> (handneg C N p J _ _ i).symm
       let Y' (i:V):= (center C.S p J' 0).copy i ℓ'
       have hZc:= (hZ.jelly (L:=Y')); rw [show birth (Bt) (R N) (fun i=> (center C.S p (hV.1.trans (hk.trans hN.le)) 0).copy i f) = K' from congr_arg (birth (Bt) (R N)) hx'] at hZc
       let xF:=fun i=> radiant (alto T k d) (hands C p J i) (Mix.camp C p J k i) (Q.exponentialEntry 0 Y! (R k)); let xK:= fun i=>sunny (R k) Q.forced (hands C p J i) (Mix.camp C p J k i) (alto T k d)
       have hF : (fun i=>∑ j,D' i j • liftF T Y! N p (u' i) (fun l=> o l i) (Z' j) k) = xF+Y':=funext fun i=> (hy' i).1
       have hT : (fun i=>∑ j,D' i j • liftK T N p (u' i) (fun l=> o l i) (Z' j) k)=xK:=funext fun i=> (hy' i).2
       dsimp only; erw [hF,hT]; exact hZc) hw  hxx hpX

    let s':=Stock.final V; let W':= moment (C.beta N p) (Joint.cutoff T N p J' hN.le V' ℓ' s'.val)
    let Qp:= paceFactor T m J*w; have hw': 0<Qp:= mul_pos (pace_pos ..) hw
    let L':= gust T N p k Y J J'
    have hl: Integrable L' (prior G _):=gust_live T N p k Y hZ' J'
    have hWind(j:I): Club T C.params Y! (ζ d) ψ J m N p (fun _=>x' j) D (Z' j) (g' j) (hk.trans hN.le):=club_restrict C N k m p d J (φ:=φ) hk (by cases j; exact hK; exact hγ _)
    obtain ⟨hp,hq⟩:=decks C N m p d J H w h o u' D' Z' (hk.trans hN.le) hG K htJ hV.1 (gust_live T N p k Y hZ' hk) ⟨fun i hj _=>funext fun v=>Work.I03.camp_step C p hj v⟩ (fun i hi _=> (by rw [show Mix.camp C p J i=(C.S.toDepth hi p).embed from funext fun v=>dif_pos hi]; exact Ratio.embed_injective _) ) hWind (show Served _ _ _ U' _ _ _ _ from hL') hw hxx hpX
    have hz:L'=gust T N p m U' J hV.1:=gust_cross hV.1 hk; rw [←hz] at hp
    have hS:=spiker C N J p H s' W' (J'.trans hN.le) (fun _=>hw') hp hq hl (conducts T N p J' hN.le V' ℓ' H.wilson hi (Envelope.compactC hf.neg) hW hR s' J J')
    let t:=Vac.treasury (T).levels J+ (5:ℝ); let Xp:= Fintype.card V
    unfold Tiling.rootTest; rw [endpointT,div_div]; refine Stock.spacer ‖W'‖ t Qp Xp (norm_nonneg _) hw' Fintype.card_pos ?_
    rw [show Poly.toll (fun _ : (V)=>Qp) s'=Qp^Xp from by simp [Poly.toll,Xp,s',Stock.final], show (Fintype.card (Site (C.side J p)):ℝ)*Vac.treasury C.path.levels J+(Xp:ℝ)*(2+1+2*1)=Xp*t from by unfold t Xp; ring] at hS; exact hS
end
end YM.MergeProof

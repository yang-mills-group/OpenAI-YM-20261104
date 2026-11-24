import YM.WilsonCoeffUV.Root.Step.OrbitMap
/-! # One unreset pivot map; cumulative tracking scopes.
Chorus prior calibration. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Soil
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior
open scoped Topology BigOperators ContDiff
variable {n c L:Side}{U α β V ι E : Type*}{k r l j i D:ℕ} {G:Gauge} {P:Patch}{K:KernelChoices}
section
variable [AddCommGroup V] [Module ℝ V]
lemma mu_shellG {P:Pal V U}(h:shellK k P)(c:ℝ):shellK k (c•P):=by intro i j h'; simp_rw [Pi.smul_apply,h _ _ h',smul_zero]
omit [Module ℝ V] in
lemma shelf {A:Finset ι}{P:ι→ Pal V U}(h:∀ i∈A,shellK k (P i)):shellK k (∑ i∈A,P i):=by
    intro i j h'; simp_rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun d hd=> h d hd _ _ h'
end
lemma wreathe_mix {P Q:Pal (Vote D) (Woods G n)}{s}(H: Wreathe P Q s)(p:shellK l P)(q:shellK l Q) {A:Cost}(he:constantCoeff A=1): Wreathe (mix A P) (mix A Q) s:=by
    intro c; have hx (T:Pal (Vote D) (Woods G n))(b:Volume D): jot b (mix A T)= mix A (jot b T):=by ext k r x; rw [jot_here]; simp_rw [mix,Finset.sum_apply, Pi.smul_apply,_root_.sum_apply, _root_.smul_apply,jot_here]
    intro Z I x X X' hi; rw [hx,hx]; exact rollMix (by intro S T v y y' hh; exact H c hh) (jot_length c q) (jot_length (spinV s D c) p) he hi

lemma gather_mark (P:Patch)(u:Pal (Vote D) (Co n α))(x:Site P.L)(b:Site n)(p:shellK k u): shellK k (gatherT P x b u):=by
   intro i j h; ext1 z; unfold gatherT revolve; rw [Function.comp_apply,p _ _ h]; exact map_zero _
lemma gather_pure (P:Patch)(u:Pal (Vote D) (Co n α))(x:Site P.L)(b:Site n)(p:Pure (u i)): Pure (gatherT P x b u i):=by
   intro j q v; change soprano P x _ (u i j ((jog (-b) ∘ v) ∘ q))=_; rw [p j q]; rfl

section
variable (P) (K) (Ñ:ChartRatio G)(H Y:FaceRow)(Q:(n:Side)→ Matrix (Body 1 (n*P.L)) (Body 1 n) ℝ)(l' k':ℕ)
local notation "S⤀" => stepAt P K n
local notation "F⤀" => xree P K n
local notation "nℓ" => n*P.L
-- actual root positions as stipulated (unmasked).
abbrev Vell (G:Gauge)(n:Side)(D) := Pal (Vote D) (Woods G n)

def bellOne (D:ℕ)(v:Site P.L) (t:PChart G (n*P.L))(u:Vell G (n*P.L) D): Vell G n D:= reed S⤀ F⤀ H (Q n) Ñ t l' (gatherT P v (wrap (n*P.L) (lift v)) u)
def collarT (D:ℕ)(t:PChart G (n*P.L))(u:Vell G (n*P.L) D): Vell G n D:= ((P.L.val:ℝ)^l'/(P.L.val:ℝ)^4) • ∑ w:Site P.L,bellOne P K Ñ H Q l' D w t u
lemma pin_swell (h:LocalRatio Ñ)(v: Site P.L)(t:PChart G (n*P.L))(u:Vell G (n*P.L) D)(p:shellK 2 t)(e:shellK k' u): shellK k' (bellOne P K Ñ H Q l' D v t u):=by
    unfold bellOne reed; apply fade_shell; intro i r ht; simp_rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun _ _=> srStops S⤀ F⤀ H (Q n) k' p h (gather_mark P u v _ e) _ _ _ (Or.inl ht)
lemma pin_test (h:LocalRatio Ñ)(t:PChart G (n*P.L))(u:Vell G (n*P.L) D)(p:shellK 2 t)(e:shellK k' u): shellK k' (collarT P K Ñ H Q l' D t u):= by
    unfold collarT; apply mu_shellG; exact shelf fun i _=> pin_swell P K Ñ H Q l' k' h i t u p e
lemma pin_valid (t:PChart G (n*P.L))(u:Vell G (n*P.L) D)(p:∀ j,Pure (u j))(i): Pure (collarT P K Ñ H Q l' D t u i):=by
    intro r; unfold collarT; rw [Pi.smul_apply,Pi.smul_apply,Finset.sum_apply,Finset.sum_apply]; apply Blue.Smooth.smul; apply Blue.Smooth.sum; intro j _; exact reed_smooth S⤀ F⤀ H (Q n) l' Ñ t (fun i=> gather_pure P u j _ (p i)) i r

lemma bells (h:LocalRatio Ñ)(e:P.Branches K G)(u:IsUnit (treeMatrix G S⤀ F⤀ H).det)(ha:Inputs S⤀ (Q n) (H.acts _) (Y.acts n))(hb:(H.acts (n*P.L)).transpose= H.acts _) (x:PChart G (n*P.L))(y: Interlace H x) {F H':Vell G (n*P.L) D}(s:Signed)(p:shellK l' F)(q:shellK l' H')(hp:∀ i,Pure (F i))(hq:∀ i,Pure (H' i))(d: Wreathe F H' s) (w:Site P.L):
    Wreathe (bellOne P K Ñ H Q l' D w x F) (bellOne P K Ñ H Q l' D (s.act w) x H') s:= by
    intro c
    let t:= spinV s D c; let R (z: Pal (Vote D) _) := reed S⤀ F⤀ H (Q n) Ñ x l' z
    let B:=gatherT P w (wrap (n*P.L) (lift w)) F; let A:=gatherT P (s.act w) (wrap (n*P.L) (lift (s.act w))) H'
    change rollTest (flash (jot c (R A))) (flash (jot t (R B))) s 0
    have hx (a:Volume D) (z:Pal (Vote D) _): jot a (R z)=reed S⤀ F⤀ H (Q n) Ñ x l' (jot a z):= reed_maps S⤀ F⤀ H (Q n) l' (((ContinuousLinearMap.apply ℝ ℝ) a).toLinearMap)
    rw [hx,hx]; apply reed_turn S⤀ F⤀ H (Q n) Y y.lamp y.stem h l' (jot_length c (gather_mark P _ (s.act w) _ q)) (jot_length t (gather_mark P _ w _ p)) e hb y.shape (fun i=>jot_code (W:=A) c (gather_pure P H' _ _ (hq i))) (fun i=>jot_code (W:=B) t (gather_pure P F _ _ (hp i))) u ha y.valid
    rw [show (stepAt P K n).ratio.embed 0=0 from map_zero (stepAt P K n).ratio.root]; exact tryst P F H' p q s d w c
lemma bells_act (h:LocalRatio Ñ)(e:P.Branches K G)(u:IsUnit (treeMatrix G S⤀ F⤀ H).det)(ha:Inputs S⤀ (Q n) (H.acts _) (Y.acts n))(hb:(H.acts (n*P.L)).transpose= H.acts _) (x:PChart G (n*P.L))(y: Interlace H x) {F H':Vell G (n*P.L) D}(s:Signed)(p:shellK l' F)(q:shellK l' H')(hp:∀ i,Pure (F i))(hq:∀ i,Pure (H' i))(d: Wreathe F H' s) : Wreathe (collarT P K Ñ H Q l' D x F) (collarT P K Ñ H Q l' D x H') s:=by
    let S w:= bellOne P K Ñ H Q l' D (n:=n) w x F; let T w:=bellOne P K Ñ H Q l' D (n:=n) w x H'
    have ht : ∑ w:Site P.L,T w =∑ w:Site P.L,T (s.act w):= Eq.symm (Equiv.sum_comp s.actEquiv.toEquiv T)
    unfold collarT; rw [ht]
    have hr w (_:w∈Finset.univ): shellK l' (S w):=pin_swell P K Ñ H Q l' l' h w x F y.lamp p
    have he w (_:w∈Finset.univ): shellK l' (T (s.act w)):=pin_swell P K Ñ H Q l' l' h (s.act w) x H' y.lamp q
    exact swellG (pulseJ _ (fun w _=> bells P K Ñ H Y Q l' h e u ha hb x y s p q hp hq d w) hr he) (shelf hr) (shelf he) _

lemma bells_period {W:Crude G}{T:Canvas G}(e:P.Branches K G)(h:LocalRatio Ñ)(p:∀ i r,Yields (fun n=>W n i r) (T i r)) {Γ M}(F:PaintKit P K G H Q Γ M){U:(n:Side)→ Vell G n D}{u:Pal (Vote D) (YForest G)}(f:∀ i r,Bends 0 (fun n=>U n i r) (u i r))(i r):
    Bends 0 (fun n=> collarT P K Ñ H Q l' D (W (n*P.L)) (U (n*P.L)) i r) (chorus P K Ñ Γ M T l' u i r):=by
    have he (w:Site P.L): Bends 0 (fun n=> bellOne P K Ñ H Q l' D w (W (n*P.L)) (U (n*P.L)) i r) (windsT P K Ñ Γ M T l' (gatherT P w (lift w) u) i r):=by
        apply river P K Ñ Γ M T e h F p l' w (U:=fun n=> gatherT P w (wrap n (lift w)) (U n)); intro i r; exact ((f i r).turn (lift w)).touch (soprano P w D)
    unfold collarT chorus; simp_rw [Pi.smul_apply,Finset.sum_apply]
    have hx:= (Bends.sum (s:=Finset.univ) (fun i _=>he i)).congr (Q:=fun n=> ∑ w:Site P.L,bellOne P K Ñ H Q l' D w (W (n*P.L)) (U (n*P.L)) i r) (Eventually.of_forall fun n=>by rw [Finset.sum_apply])
    exact hx.μ _
end
end YM.WilsonCoeffUV.Soil

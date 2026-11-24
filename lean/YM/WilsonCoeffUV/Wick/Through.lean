import YM.WilsonCoeffUV.Wick.Carve
/-!
# Boundary Wick certificates through each raw iteration
- preimage phase retained. Remove dependence of test order >D separately. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Carp
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Soil Cosmos
open Exterior Next.Free Tree Precision Power Embroider Source
open scoped Topology BigOperators ContDiff
variable {c f n:Side}{U V W α β: Type*} {r e j k m D h N:ℕ}{G:Gauge}{x s ξ σ A' B:ℝ}
variable (A:Levels G)(Ñ:ChartRatio G)(X: Single G D)
local notation "P°" => ll A m
local notation "K°" => A.clock.kernel
local notation "V°" => freeForms A N (m+1)

-- vector linearized identity
lemma windsR0 (g:G.Simple)(p:m<N)(hp:LocalRatio Ñ) (Z: Estate G D)(h:∀ n,shellK k (Z n))(hs:∀ n:Side,∀ i,Pure (Z n i)) (w:Site (ll A m).L)(t:Bid.Larger (mStep A n m) (G:=G))(hx:∀ (b:Volume D), NullTop (fun r=> revolve (wrap (n*(ll A m).L) (lift w)) (jot b (Z (n*(ll A m).L)) 0 r))):
    let c:=n*(ll A m).L; let C:= (story A Ñ N (m+1)).1 c; let X:= extractV G (mStep A n m) (xree P° K° n) (roam A N m n)
    let Q:=carve k (blues A N (m+1) c) (Z c 0); let M:=fun r=>soprano P° w D ∘ revolve (wrap c (lift w)) (Q r)
    carve k (blues A N m n) (bellOne P° K° Ñ V° (roam A N m) k D w C (Z c) 0)= fade X M:=by
   intro c C X Q M; let F:=xree P° K° n; let S:=mStep A n m
   let T:= gatherT P° w (wrap c (lift w)) (Z c); let R:= bellOne P° K° Ñ V° (roam A N m) k D w (n:=n) C (Z c); let W b:= (ContinuousLinearMap.apply ℝ ℝ (b:Volume D)).toLinearMap
   have hc := (old A Ñ g hp N (m+1) p).basis c
   ext1 i; funext x; ext1 b; let P:=jot b T; let Y:=foldWord P° w D b; let I:=W b
   have hb:P= fun i r=> revolve (wrap c (lift w)) (jot Y (Z c) i r):=rfl
   have hR : jot b R= reed S F V° (roam A N m n) Ñ C k P:= reed_maps S F V° (roam A N m n) k I (P:=C) (w:=T) (Ñ:=Ñ)
   have hx0:shellK k P:= jot_length b (gather_mark P° _ w _ (h c)); have hL j:Pure (P j):=jot_code (W:=T) _ (gather_pure P° _ w _ (hs c _))
   have hs := (inheritedG A Ñ F p hp C hc.lamp hc.shape P hx0 hL (by exact hx Y) t).2
   let U := blues A N (m+1) c; let K:= blues A N m n
   rw [← hR] at hs
   have he:shellK k (jot b R):= jot_length b (pin_swell P° K° Ñ V° (roam A N m) k k hp w _ _ hc.lamp (h _)); have hz j :Pure (R j):= reed_smooth _ _ _ _ _ _ _ (fun i=>gather_pure P° _ _ _ (‹∀ n:Side,∀ i,Pure (Z n i)› c _)) j
   have hy (W:Pal ℝ (Woods G n))(p:shellK k W): still (W 0) (k+1):= fun i hi=>p 0 i (by omega)
   have hz' : still (P 0) (k+1):= fun i hi=>hx0 0 i (by omega)
   let Z':=carve k K (jot b R 0); let P':=carve k U (P 0); have hZ:Pure Z':= sculpt k K (jot_code (W:=R) b (hz _))
   have hP:Pure P':= sculpt k U (hL _)
   have hO : Z'=fade X P':=by
       apply gen_inj ⟨_,carved k K (hy _ he)⟩ (fade_finite ⟨_,carved k U hz'⟩ X) hZ (fade_pure hP X); rw [fade_visible X _ ⟨_,carved k U hz'⟩, show totalR P'=_ from carving k U hz' (hL _),show totalR Z'= _ from carving k K (hy _ he) (jot_code (W:=R) _ (hz _))]; exact hs
   have hV : P'=cloaks I M:= by
       unfold P'; rw [show P 0=(fun i=> revolve (wrap c (lift w)) (jot Y (Z c) 0 i)) from rfl, stars_step (n:=c) (A:=A)]; change (fun i=> revolve _ (carve k U (cloaks (W Y) (Z c 0)) i))=_; rw [masonmaps]; rfl
   rw [hV,← cloak_fade] at hO; unfold Z' at hO
   rw [show jot b R 0=cloaks I (R 0) from rfl] at hO
   rw [show carve k K _=cloaks I (carve k K (R 0)) from masonmaps K _ I _] at hO
   exact congr_fun (congr_fun hO i) x
abbrev dign (A:Levels G)(m N:ℕ)(n:Side):= extractV G (mStep A n m) (xree (ll A m) A.clock.kernel n) (roam A N m n)
lemma fade_v (P:Gen (Vote D) (YForest G)){T:(n:Side)→ Gen (Vote D) (Woods G n)}(p:m<N)(v:Site (ll A m).L)(hs:Bends 0 (fun n=>T n r) (P r)): Bends 0 (fun n=> fade (dign A m N n) (fun i=>soprano P° v D ∘ revolve (wrap _ (lift v)) (T (n*(ll A m).L) i)) r) (pulseS P° v (shuttleM (feedA A N m)) (P r)):=by
   let L:=(ll A m).L
   let Q:= fun n i=>soprano P° v D ∘ revolve (wrap _ (lift v)) (T n i)
   let V:= fun i=>soprano P° v D ∘ revolve (lift v) (P i)
   let b n:=bend (weaveFine (ratioN L n) G) (Q (n*L)); let t:=tiles L V
   have hp:Bends 0 (fun n=> b n r) (t r):= (((hs.turn (lift v)).touch _).ciphers v)
   unfold pulseS; rw [inspectFace]; apply (solo_flash (r:=r) (Q:=b) (P:=t) (resin A N m p).mark hp).congr
   refine Eventually.of_forall fun n=>?_; change fade _ _ r=fade (dign A m N n) _ r; unfold b; exact congr_fun (bend_fade (weaveFine (ratioN L n) G) (Equiv.refl (Woods G n)) (dign A m N n) (Q (n*L))).symm r

def paveS (A:Levels G)(m N k:ℕ)(P:Gen V (YForest G))[NormedAddCommGroup V][NormedSpace ℝ V]:= mason (sea A N m) P k
lemma descent (p:m<N)(g:G.Simple)(hp:LocalRatio Ñ)(u:shellK k X)(he:Stakes X)(hs:∀ i r, Standby (X i r)): paveS A m N k (marchT A Ñ N m k X 0)= fun r=>hall P° k (shuttleM (feedA A N m)) (paveS A (m+1) N k (X 0) r) :=by
    let Xn:=canonP X; choose s a hS H using hs
    let l:= (ll A m).L
    have hX i r: Bends 0 (fun n=> Xn n i r) (X i r):= caisson (H i r) (hS i r)
    let P(n:Side):= cloakP A Ñ N m k n (Xn (n*l)); have H' := old A Ñ g hp N (m+1) p
    have hV i r: Bends 0 (fun n=>P n i r) (marchT A Ñ N m k X i r):=by
       let B n:=collarT P° K° Ñ V° (roam A N m) k D (n:=n) ((story A Ñ N (m+1)).1 (n*l)) (Xn (n*l)); apply whirlB (P:=B) _ (ratioHigh A Ñ N m); exact fun i r=>bells_period P° K° Ñ V° (roam A N m) k (U:=Xn) (A.blocks m 0).branches hp H'.patch (resin A N m p) hX i r
    funext r; apply (mason_path (recruit A N m) (Q:=fun n=>P n 0) k (hV 0) r).exten
    let V:=paveS A (m+1) N k (X 0)
    let Q n:= carve k (blues A N (m+1) n) (Xn n 0)
    have hr w: Bends 0 (fun n=> fade (dign A m N n) (fun i=>soprano P° w D ∘ revolve (wrap (n*l) (lift w)) (Q (n*l) i)) r) (pulseS P° w (shuttleM (feedA A N m)) (V r)):= fade_v A V p w (T:=Q) (mason_path (recruit A ..) k (Q:=fun n=> Xn n 0) (hX 0) r)
    apply ((Bends.sum (s:=(Finset.univ)) (fun i _=>hr i)).μ (tiara P° k)).congr; filter_upwards [tundra A m] with n hn
    let C:=(story A Ñ N (m+1)).1 (n*l); let U w:=bellOne P° K° Ñ V° (roam A N m) k D w (n:=n) C (Xn (n*l))
    have he' : P n 0=tiara P° k •∑ w:Site l,U w 0:=by
       let T:= collarT P° K° Ñ V° (roam A N m) k D (n:=n) C (Xn (n*l)); have hC :P n 0=T 0:=mix_lead (A:=ratioHigh A Ñ N m) (back_cc (angle_tilt g hp p)) T; rw [hC]; unfold T collarT; rw [Pi.smul_apply,Finset.sum_apply]; rfl
    rw [he', iceSum,Pi.smul_apply, Finset.sum_apply]; rw [Pi.smul_apply,Finset.sum_apply]; apply congr_arg; apply Finset.sum_congr rfl; intro i _
    exact congr_fun (windsR0 A Ñ g p hp Xn (cargo X u) (fun n i=> chore X he.pur i n) i hn (pieces X he u (fun i r=>⟨_,_,hS i r,H i r⟩) (lift i))).symm r
end YM.WilsonCoeffUV.Bank.Carp

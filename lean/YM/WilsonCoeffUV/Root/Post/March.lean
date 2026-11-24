import YM.WilsonCoeffUV.Root.Post.Chain
/-! # Formal coat procession. Coupling may be shared only after Mix. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V E:Type*}{r h D l j e k N m:ℕ} {G:Gauge}{F:Labels.Frame G h}
lemma raft [AddCommGroup V][Module ℝ V][Fintype U] (S:StepData n c)(K:Forest S.ratio) (H:FaceRow)(Q:Matrix (Body 1 c) (Body 1 n) ℝ)(Ñ:ChartRatio G)(P:PChart G c)(l:ℕ)(p:U→Pal V (Woods G c))(u:U→ℝ): reed S K H Q Ñ P l (∑ i,u i • p i)=∑ i,u i • reed S K H Q Ñ P l (p i):=by
   let M: Pal (U→V) (Woods G c):= fun e k x i=> p i e k x; let f: (U→V)→ₗ[ℝ]V:= ∑ i:U,u i • LinearMap.proj i
   let T:=reed S K H Q Ñ P l M
   have hg i e k x: T e k x i=reed S K H Q Ñ P l (p i) e k x:=by
       exact congr_fun (congr_fun (congr_fun (reed_maps S K H Q l (LinearMap.proj (R:=ℝ) (φ:=fun _:U=> V) i) (w:=M)) _) _) _
   have hv : ∑ i:U,u i • p i=fun i=> cloaks f (M i):=by
       ext i k x; simp_rw [Finset.sum_apply,Pi.smul_apply]; change (∑ j,u j • _)=(∑ j,u j • (LinearMap.proj (R:=ℝ) (φ:=fun _:U=> V) j)) (M i k x); rw [LinearMap.sum_apply]; rfl
   rw [hv,← reed_maps (w:=M)]; ext i k x; change f (T i k x)=_; simp_rw [Finset.sum_apply,Pi.smul_apply]; unfold f; rw [LinearMap.sum_apply]; exact Finset.sum_congr rfl (fun j _=>congr_arg (u j • ·) (hg j i k x))

variable (A:Levels G)(Ñ:ChartRatio G)
open Realm
abbrev ll (A: Levels G)(m):=loose A m

def cloakP (N m h:ℕ) (n:Side) (u:Vell G (n*(ll A m).L) D): Vell G n D:= Blue.mix (ratioHigh A Ñ N m) (collarT (ll A m) A.clock.kernel Ñ (freeForms A N (m+1)) (roam A N m) h D ((story A Ñ N (m+1)).1 (n*(ll A m).L)) u)

def marchT (N m h:ℕ)(X:Single G D): Single G D:= Blue.mix (ratioHigh A Ñ N m) (chorus (ll A m) A.clock.kernel Ñ (shuttleM (conditional A N m)) (shuttleM (feedA A N m)) (actionW A Ñ N (m+1)) h X)
lemma stencilStep (N m h:ℕ)(p:m<N)(g:G.Simple)(hv:LocalRatio Ñ)(V:Usage A Ñ m)(X:Single G D): marchT A Ñ N m h X=fanfare V.gear (V.postStand p g hv) h X := rfl
lemma cloakP_sum (v: U→ℝ)[Fintype U]{X:U→ Vell G (n*(ll A m).L) D} : cloakP A Ñ N m h n (∑ i,v i • X i)=∑ i,v i • cloakP A Ñ N m h n (X i):=by
   let T:= ll A m; let f:=n*T.L
   let K n:=stepAt T A.clock.kernel n; let Q n:=xree T A.clock.kernel n; let P:= (story A Ñ N (m+1)).1 f; let c:=roam A N m; let L:= freeForms A N (m+1)
   let R:= collarT T A.clock.kernel Ñ L c h D P; let V:=ratioHigh A Ñ N m; let S:=bellOne (n:=n) T A.clock.kernel Ñ L c h D
   have hf w:S w P (∑ i,v i • X i)=∑ i, v i • S w P (X i):= by
       let B : Vell G f D → Vell G f D :=gatherT T w (wrap f (lift w)); let M:= fun i=> B (X i)
       change reed (K n) (Q n) L (c n) Ñ P h _=_
       rw [show gatherT T w (wrap (n*T.L) (lift w)) (∑ i,v i • X i)=∑ i,v i • M i from ?_]
       exact raft (K n) (Q n) L (c n) Ñ P h M v
       ext i j x; unfold gatherT revolve; simp only [Function.comp_apply,Pi.smul_apply,Finset.sum_apply,map_sum,map_smul]; rfl
   have hR : R (∑ i,v i • X i)=∑ i,v i • R (X i):=by
       change tiara T h • (∑ w:Site T.L,S w P (∑ i,v i • X i))=∑ i,v i • (tiara T h • (∑ w,S w P (X i)))
       rw [Finset.smul_sum]; simp_rw [hf, Finset.smul_sum]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun _ _=> smul_comm ..
   change Blue.mix V (R _) = ∑ i,v i • Blue.mix V (R _); rw [hR]; funext k j; simp only [Blue.mix, Pi.smul_apply, Finset.sum_apply,Finset.smul_sum]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun _ _=> smul_comm ..
omit A Ñ in lemma whirlB {P:(n:Side)→ Vell G n D}{Q:Single G D}(p:∀ i r,Bends 0 (fun n=>P n i r) (Q i r))(A:Blue.Cost)(i r): Bends 0 (fun n=>Blue.mix A (P n) i r) (Blue.mix A Q i r):=by
    simp_rw [Blue.mix]; exact anzas (P:=fun k n=>coeff (i-k) (A^k*(A⁻¹)^r) • P n k r) (Finset.range (i+1)) (fun i _=> Soil.Bends.μ (p ..) _)
lemma running {W:PatchPanel F D}{Y:Thesis F D} (p:m<N)(g:G.Simple)(hg:LocalRatio Ñ)(e:Chain F W Y): Chain F (fun n i=> cloakP A Ñ N m h n (W (n*(ll A m).L) i)) (fun i=> marchT A Ñ N m h (Y i)):=by
   let K:= ll A m; let k:= A.clock.kernel; let t:= (story A Ñ N (m+1)).1; let s:=freeForms A N m; let F':=freeForms A N (m+1); let L:=roam A N m; let T (n:Side):= t (n*K.L); let R(n):=collarT K k Ñ F' L h D (n:=n) (T n); let b:=ratioHigh A Ñ N m
   have hx := old A Ñ g hg N (m+1) p
   have hp (n:Side): Interlace F' (T n):= hx.basis _
   have he (n:Side) (l:ℕ)(U:Vell G (n*K.L) D)(p:shellK l U): shellK l (R n U):=pin_test K k Ñ F' L h l hg _ U (hp n).lamp p
   have hh (s0:Signed)(n:Side)(F G':Vell G (n*K.L) D)(a:Wreathe F G' s0)(q:shellK h F)(q':shellK h G')(pF: ∀ i,Pure (F i))(pG:∀ i,Pure (G' i)): Wreathe (cloakP A Ñ N m h n F) (cloakP A Ñ N m h n G') s0:= by
       have hb :constantCoeff b=1:=back_cc (angle_tilt g hg p)
       apply wreathe_mix _ (he n _ _ q) (he n _ _ q') hb; exact bells_act K k Ñ F' s L h hg (A.blocks m 0).branches ((cond_laws A m N).1 n (n*K.L) rfl) (horizon_step A m N p n (n*K.L) rfl) (age_sym A ..) _ (hp n) s0 q q' pF pG a
   have hZ (i:Alma F) n: shellK h (W n i):= shell_mon ((e.solo i).launch n) (valence_cap ..)
   refine ⟨fun i=> ⟨?_,fun n=>mix_length (he n _ _ ((e.solo _).launch _)),fun n j=>mix_pure ?_ j,fun n=> hh 1 n _ _ ((e.solo i).oneS _) (hZ _ _) (hZ _ _) (fun k=>(e.solo i).evenS _ k) (fun k=>(e.solo i).evenS _ k)⟩,fun s n i=>?_⟩
   · intro r j; apply whirlB (P:=fun n=> R n (W (n*K.L) i)); intro j r; exact bells_period K k Ñ F' L h (A.blocks m 0).branches hg hx.patch (resin A N m p) (U:=fun n=> W n i) ((e.solo _).shore) j r
   · intro i'; exact pin_valid K k Ñ F' L h _ _ (fun j=> (e.solo _).evenS _ j) i'
   let t':= impose (W (n*K.L)) (paintC F s)
   have ht:= hh s n _ _ (e.spirit s (n*K.L) i) (hZ i _) (shell_mon ((Solo.affixing W Y e.solo (paintCap F s) i).launch _) (valence_cap ..)) (fun j=> (e.solo _).evenS _ j) (fun j=> (Solo.affixing W Y e.solo (paintCap F s) i).evenS _ j)
   simp_rw [canvasF,cloakP_sum] at ht; rw [canvasF]; exact ht
end YM.WilsonCoeffUV.Cosmos

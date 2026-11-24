import YM.WilsonCoeffUV.Marked.Bounds.FiniteInterval
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric Shard Realm PathCost
open scoped Topology BigOperators
variable {c f:Side}{ι α U V t:Type}{J K I T:Finset ι}{D k K':ι→ℕ}{i j i' j' a e r h N n m b l:ℕ}{G:Gauge}{σ τ u g B C z ρ:ℝ}
variable [DecidableEq ι]
lemma logSingle {X Y:Sac ι (Ink U)}(h:Equation X Y)(i:ι): X {i}=Y {i}:=by
   have he:= congr_fun h.2.2 ({i}:Finset ι)
   have hv: ({i}:Finset ι).powerset=insert ∅ {{i}}:=by
       have H:= Finset.powerset_insert (∅:Finset ι) i; simpa using! H
   simpa [dial,shells,h.1,hv] using he
lemma levSingle {K:family G D}(p:K ∅=0)(u:Eu k K)(i:ι): levelsO K {i}=K {i}:= read_ext _ _ (placedO K u _) (u _) fun p' n=> logSingle (levels_exp K u p p' n) i
lemma shifted_add [NormedAddCommGroup V][NormedSpace ℝ V] (Z:Era G V) (p q:Cover): shifted Z (p+q)=shifted (shifted Z q) p:= by
   refine Prod.ext (funext fun n=>funext fun i=>funext fun j=>?_) (funext fun i=>funext fun j=>?_)
   · unfold shifted skewV; dsimp only; rw [map_add, rollCup]
   exact rollCup ..
lemma singletonStamp (s:ι)(A: Vote (D s))(P:Patch)(v:ι→ Site P.L): mend P v D {s} (petal D s A)=petal D s (soprano P (v s) (D s) A):=by apply pen_inj; intro h; rw [mend_v P,petal_hit,petal_hit]; rfl
lemma spire {Z:Outerm G D}(A: Levels G)(L:ChartRatio G)(K k:ι→ℕ)(v:Wellness k Z)(p:G.Simple)(b:LocalRatio L)(x:m<N)(s:ι)(w:ι→Cover):
     stout A L m N K k Z w {s}= unite (ll A m) K (fun i S=>verseI A L m N (mass k S) (Z i S)) w {s}:=by
   let Q:=ll A m; let P:= stout A L m N K k Z; let V i S:=verseI A L m N (mass k S) (Z i S)
   rw [← levSingle ((Seating A L Z p b x v K).quiet' w) ((Seating A L Z p b x v K).level' w),← oneStep_log _ _ _ p b x v]
   apply Finset.sum_congr rfl; intro i _; unfold portV edV; dsimp only; rw [levSingle (v.quiet' _) (v.level' _)]

def cn (D:ι→ℕ)(s:ι)(T:TowerS G (D s))(p:Cover):= shifted (tuftV (petal D s) T) p
-- kernel eigenshift (preparing address budget). In shops we take Engineering scale/exponent = k of horizon.
section
variable {A: Levels G}{L:ChartRatio G}{Z:Outerm G D}
lemma byPetal (p:G.Simple)(b:LocalRatio L)(x:m<N)(s:ι)(w:Cover)(v:Site (ll A m).L)(v':ι→Site (ll A m).L)(q:v' s=v)(X:TowerS G (D s))(h: On (k s) X):
   let P:=ll A m; tuftV (mend P v' D {s}) (verseI A L m N (k s) (cn D s X (P.L.val • w + lift v)))=
       shifted (tuftV (petal D s) (verseI A L m N (k s) (shifted (tuftV (soprano P v (D s)) X) (lift v)))) w :=by
   intro P; unfold cn
   have hp := On_auth h
   let Q:=petal D s; rw [ply_verse A x p b ((hp.tuft Q).shifted _)]
   have H: tuftV (mend P v' D {s}) (tuftV Q X)= tuftV Q (tuftV (soprano P v (D s)) X):=by
       subst v; apply Prod.ext <;> first | (exact funext (fun n=>funext fun i=>funext fun j=>funext fun x=>singletonStamp ..)) | exact funext (fun i=>funext fun j=>funext fun x=>singletonStamp ..)
   change verseI A L m N (k s) (shifted (tuftV (mend P v' D {s}) (tuftV Q X)) (P.L.val • w + lift v))=_
   rw [H,shifted_add]
   let Z:=tuftV (soprano P v (D s)) X; have he:=hp.tuft (soprano P v (D s)); change verseI A L m N (k s) (shifted (tuftV Q (shifted Z (lift v))) ((A.S.block m).val • w))= _; rw [outing A x p b ((he.shifted (lift v)).tuft Q) w]; exact congr_arg (fun y=>shifted y w) (Eq.symm (ply_verse A x p b (he.shifted (lift v)) Q))
lemma rawSc (p:G.Simple)(b:LocalRatio L)(x:m<N)(s:ι)(v:Wellness k Z)(w:ι→ Cover)(X: TowerS G (D s))(h:On (k s) X)(u:∀ p,Z p {s}=cn D s X (p s)):
     stout A L m N k k Z w {s} = cn D s (Spout A L N m (k s) (k s) X) (w s):=by
    rw [spire _ _ _ _ v p b x s w]; let P:= ll A m; let T r V:= verseI A L m N r (V:Era G (Pen D {s})); let Q y S:= verseI A L m N (mass k S) (Z y S)
    let V:=unite P k Q w {s}; let Y:=Spout A L N m (k s) (k s) X; let a:=cn D s Y (w s)
    have he : Solo k Q:=fun i S=> Auth.verse A x p b (v.level' i S); have hQ:Auth (k s) V:=by have H:=cone_L P k Q he w ({s}:Finset ι); rw [mass,Finset.sum_singleton] at H; exact H
    have hT:=On_auth (ShedG A L (h:=k s) x p b h le_rfl); apply Auth.ext hQ ((hT.tuft (petal D s)).shifted _)
    let W:=backRow P.L ({s}: Finset ι); let f(i:W):=i (⟨s,by simp⟩); let U:= Equiv.ofBijective f (show Bijective f from ⟨fun i j e=> funext fun b=> by have hv:b=(⟨s,by simp⟩:↥({s}: Finset ι)):=Subtype.ext (Finset.mem_singleton.mp b.property); rw [hv]; exact e,fun i=>⟨fun _=>i,rfl⟩⟩); let C:=tiara P (k s); let K:= P.L.val; let R:=petal D s
    let pV (i:Site P.L):= shifted (tuftV (soprano P i (D s)) X) (lift i); let L' (i:Site P.L):= verseI A L m N (k s) (pV i); let E (i:Site P.L):= shifted (tuftV R (L' i)) (w s)
    have hx i:portV P k Q w {s} i=C • E (f i):=by
        let I:= inflate P {s} i; let W:=splitQ P w {s} i; have hy : I s=f i:=dif_pos (by simp); unfold portV Q; rw [u, mass, Finset.sum_singleton,show scalesK _ _ _=C from Finset.prod_singleton _ _,show splitQ P w {s} i s= K • w s+ lift (f i) from congr_arg (fun i=> K • w s+lift i) hy]; exact congr_arg _ (byPetal (D:=D) p b x s (w s) (f i) I hy X h)
    funext n; change (∑ i:W,portV P k Q w {s} i).1 n=_; simp_rw [hx]; rw [show (∑ i:W,C • E (f i)) =∑ i:Site P.L,C • E i from Equiv.sum_comp U (fun i=>C • E i), Prod.fst_sum,Finset.sum_apply]
    -- Spout finite unfold
    let F:=stepAt P A.clock.kernel n; let J i:= reed F (xree P A.clock.kernel n) (freeForms A N (m+1)) (roam A N m n) L ((story A L N (m+1)).1 _) (k s) ((pV i).1 (n*P.L)); let b:=ratioHigh A L N m
    have hy: Y.1 n=C • (∑ i:Site P.L,Blue.mix b (J i)):=by
        change gradeH P (k s) (k s) • Blue.mix b (C • (∑ i:Site P.L,J i))= _; rw [show gradeH P (k s) (k s)=1 from div_self (by positivity) (a:= (P.L.val:ℝ)^k s),one_smul]; ext1 i; funext v; simp only [Pi.smul_apply, Finset.sum_apply,Blue.mix]; simp_rw [Finset.smul_sum]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j _=> smul_comm ..))
    change _=skewV _ (ply R.toLinearMap (Y.1 n)); rw [hy,map_smul,map_sum]; ext1 i; funext j y; simp only [skewV,revolve,Finset.smul_sum, Pi.smul_apply,Prod.smul_fst, Finset.sum_apply]; rfl
end
end YM.WilsonCoeffUV.Wheel.Mark

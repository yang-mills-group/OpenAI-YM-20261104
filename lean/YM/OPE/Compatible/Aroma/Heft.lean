import YM.OPE.Compatible.Aroma.Mica
/-! # Derivative emission from M on graded radial jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Exterior Tensor WithLp Work.F08 Matrix Bloch Planned.PrimaryIntegral295.Carrier Precision
open scoped Topology BigOperators Classical
variable {r d' m n j:ℕ}{b e s:ℝ}{I J W K:Type*} {G:Gauge}
namespace Script
open Page
lemma joined2 (p:Axis)(j:Fin n→Axis)(a:I) (v:fieldX I)(x:Cover): swipe p (roamsX j v) (x,a) = roamsX (Fin.cons p j) v (x,a):=by
    rw [swipeGear]; change movesX ℝ p (trainX ℝ n j (sea a v)) x= trainX ℝ n j (movesX ℝ p (sea a v)) x
    suffices he:∀ (n:ℕ) (j:Fin n→Axis)(f:Cover→ℝ), movesX ℝ p (trainX ℝ n j f)=trainX ℝ n j (movesX ℝ p f) from congr_fun (he n j _) x
    intro n j f; induction n generalizing f with
    | zero=> rfl
    | succ n ih=> rw [trainX, LinearMap.comp_apply, LinearMap.comp_apply, ih]; apply congr_arg; ext x; simp_rw [moveX_eq]; rw [add_right_comm]; ring
abbrev shadew (u:G.ColorIndex)(v:fieldX (Shade G)):fieldX (TypeFace 1):=fun t=> v (t.1,axisEquiv.symm t.2,u)
lemma quietShade {v:fieldX (Shade G)}(hp:Quiet v n)(j:G.ColorIndex): Quiet (shadew j v) n:=by obtain ⟨x,c,h⟩:= hp; exact ⟨x,c,fun i=> h _⟩
lemma orchid {v:fieldX (Shade G)}(h:Low v n)(g:n≤d')(i:G.ColorIndex)(j:Fin d'→Axis):roamsX j (meetsX (cobound 1) (shadew i v))=0:=by
    ext1 ⟨x,k⟩; obtain ⟨a,rfl⟩:= plaqEquiv.surjective k; let p:=shadew i v
    have ht (a b:Axis): trainX ℝ d' j (movesX ℝ a (sea (axisEquiv b) p))=0:=by
       obtain ⟨f,hF,hv⟩:= h (b,i); have he : sea (axisEquiv b) p=f ∘ translit:=funext (fun t=>by unfold p sea shadew; rw [axisEquiv.symm_apply_apply,hv];rfl)
       rw [he]; have hh:=trackL f hF (Fin.cons a j) ((Nat.lt_succ_of_le g)); rw [trainX, Fin.tail_cons, LinearMap.comp_apply, Fin.cons_zero] at hh; exact hh
    change trainX ℝ d' j (sea (plaqEquiv a) (meetsX (cobound 1) p)) x=_; let s:= a.val.1; let t:=a.val.2; rw [show sea (plaqEquiv a) _ = movesX ℝ s (sea (axisEquiv t) p)- movesX ℝ t (sea (axisEquiv s) p) from funext fun j=> coarea (quietShade (low_quiet h) i) _ _,map_sub,ht,ht,sub_zero];rfl
lemma poiseMark (u:G.ColorIndex)(A:Labels.Taylor G d')(z:Fin d'→Axis) (x:Cover)(k:PlaqAxes) :
    roamsX z (meetsX (cobound 1) (shadew u (ledge A.val))) (x,plaquette k)=(d'.factorial :ℝ)* takeCurl A k.val.1 k.val.2 (basis∘z) u:=by
     let p:= shadew u (ledge A.val); let a:= k.val.1; let b:= k.val.2; let f (a:Axis):= (chin u) ∘ A.value a ∘ fromX
     let Q:= (chin u).compContinuousMultilinearMap (takeCurl A a b)
     have hE(a:Axis): sea (coord a) p=f a∘translit:=funext (fun i=> by change ((A.val (axisEquiv.symm (coord a))) _) u=_; rw [show Exterior.coord a= _ from (coord_map a).symm,axisEquiv.symm_apply_apply]; rfl)
     have ht (i t:Axis): trainX ℝ d' z (movesX ℝ i (sea (coord t) p))=trainX ℝ d' z (breeze (basis i) (f t)∘translit):=by
        rw [hE]; exact breezedL (f t) (tgon ((chin u).compContinuousMultilinearMap (A.val t))) i z
     have he(i t:Axis)(x:Lieu Axis): breeze (basis i) (f t) x= chin u (grad i (A.value t) (fromX x)):=by
        let D:= chin u; unfold breeze; rw [show f t∘invertX=D∘diagonal (A.val t) from rfl,fderiv_comp _ D.differentiableAt ((diag_smooth (A.val t) ⊤).differentiable (by simp) (fromX x)),D.fderiv];rfl
     let F:=sea (plaquette k) (meetsX (cobound 1) p); have hh: trainX ℝ d' z F=trainX ℝ d' z (diagonal Q∘fromX ∘translit):=by
       rw [show F=movesX ℝ a (sea (coord b) p)-movesX ℝ b (sea (coord a) p) from funext fun i=> coarea (quietShade (low_quiet (ledgeL _)) u) k i,map_sub,ht,ht,← map_sub]; apply congr_arg; ext i; change breeze _ _ _-breeze _ _ _= chin u (diagonal (takeCurl A a b) _); rw [he,he,takeCurl_diag, Pi.sub_apply,map_sub]; rfl
     change trainX ℝ d' z F x=_; rw [hh,totX]; rfl; exact fun v s=>congr_arg (chin u) ((closedCurl A).coeffSym a b v s)
abbrev barrage (H:FreeResolvent.FaceRow):Row (TypeFace 1) (TypeFace 1):=composeRows (transRows (cobound 1)) (composeRows H (cobound 1))
lemma barrageH {H:FreeResolvent.FaceRow}(h:Whole H): Whole (barrage H):= (Whole.boundary 1).flipped.prod (h.prod (Whole.boundary 1))
lemma peck {H:FreeResolvent.FaceRow}(h:Whole H)(x:Fin d'→Axis){p:fieldX (TypeFace 1)}(hp:Quiet p m)(i:Cover)(a:Axis):
   roamsX x (meetsX (barrage H) p) (i,coord a)=-(∑ k:Axis,∑ j, left ℝ 1 k j (coord a)* meetsX H (roamsX (Fin.cons k x) (meetsX (cobound 1) p)) (i-step k,j)):=by
      let b:=meetsX (cobound 1) p; let f:=meetsX H b; have hb:=proper (Whole.boundary _) hp; have he:=proper h hb
      have hu{n:ℕ}{v:fieldX (TypeFace 2)}(j: Fin n→Axis)(g:Quiet v m): Quiet (roamsX j v) m:=by
          induction n generalizing v with | zero=>exact g| succ n ih=> rw [← Fin.cons_self_tail j,swipeGear]; exact ih _ (swipeQuiet g _)
      rw [show meetsX (barrage H) p = meetsX (transRows (cobound 1)) f from by unfold barrage f b; rw [jointX h (Whole.boundary _) _ hp,jointX _ _ _ hp];exact (Whole.boundary _).flipped; exact h.prod (Whole.boundary _),← swarm (Whole.boundary _|>.flipped) x (show Quiet f m from he),reverseFace (hu _ he)]; simp_rw [joined2,swarm h _ hb];
end Script
end YM.OPE.Flume

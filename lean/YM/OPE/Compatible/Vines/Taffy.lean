import YM.OPE.Compatible.Vines.Plate
/-! # Classical stencil coordinates. Needed only at grading, plus free leading F covariance. Actual overlay maps no such locality granted. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Labels Tensor ContinuousMultilinearMap WithLp YM.Pert.Bare
open scoped Topology BigOperators Classical
variable {r d m n:ℕ}{c:ℝ}{V W:Type*}{G:Gauge}
namespace Script
open Page
-- color linear coefficients. use repr only
abbrev chin (i:G.ColorIndex) : G.Color→L[ℝ] ℝ:= EuclideanSpace.proj i
def heal (G:Gauge) (a:Axis): fieldX (Shade G)→ₗ[ℝ] (Cover→G.Color) where
   toFun v x:= toLp 2 (fun i=> v (x,(a,i)))
   map_add' _ _:=rfl
   map_smul' _ _:=rfl
def curve (G:Gauge) (a b: Axis): fieldX (Shade G)→ₗ[ℝ] (Cover→G.Color):= movesX _ a ∘ₗ heal G b - movesX _ b ∘ₗ heal G a
def slopeH (G:Gauge)(d:ℕ): fieldX (Shade G)→ₗ[ℝ] Response G d:= LinearMap.pi (fun a=> LinearMap.pi (fun b=>LinearMap.pi (fun k: Fin d→Axis=>
    (d.factorial:ℝ)⁻¹ • (LinearMap.proj (R:=ℝ) (0:Cover) ∘ₗ trainX G.Color d k ∘ₗ curve G a b))))
def templateX (G:Gauge)(d:ℕ): fieldX (Shade G)→ₗ[ℝ] Taylor G d:= radialMap ∘ₗ slopeH G d
-- gauge
lemma curl_zero (w:fieldX G.ColorIndex) (a b:Axis):curve G a b (mountain w)=0:=by
    ext i j; change (((mountain w (i+step a,(b,j)))- (mountain w (i,(b,j))))-(mountain w (i+step b,(a,j))-mountain w (i,(a,j)))) =0; unfold mountain; rw [add_right_comm i]; ring
lemma temp_zero (w:fieldX G.ColorIndex):templateX G d (mountain w)=0:= by
    have he : slopeH G d (mountain w)=0:=by funext a b x; change (d.factorial:ℝ)⁻¹ • (trainX _ d x (curve G a b _) _) = 0; rw [curl_zero,_root_.map_zero]; exact smul_zero _
    change radialMap (slopeH G d _) = 0 -- fill
    rw [he,_root_.map_zero]
-- color paint
abbrev plumeX (g:G.El)(v:fieldX (Shade G)):fieldX (Shade G):=fun p=> G.adjoint g (heal G p.2.1 v p.1) p.2.2
lemma color_curve (v:fieldX (Shade G))(a b:Axis)(g:G.El): curve G a b (plumeX g v)=G.adjoint g∘ curve G a b v:=by
    have he(i:Axis): heal G i (plumeX g v)= G.adjoint g ∘ heal G i v:=rfl; have hx(j:Axis)(a:Cover)(b:Axis): movesX _ j (G.adjoint g ∘ heal G b v) a = G.adjoint g ((movesX _ j (heal G b v)) a):= (map_sub (G.adjoint g) _ _).symm; change movesX _ a _-movesX _ b _=G.adjoint g ∘ (movesX _ _ _-movesX _ _ _); rw [he a,he b]; ext1 i; rw [Pi.sub_apply,hx,hx]; exact (map_sub ..).symm
lemma color_template (v:fieldX (Shade G))(g:G.El): templateX G d (plumeX g v)=Taylor.paint g (templateX G d v):=by
    change radialize (slopeH G d (plumeX g v)) = Taylor.paint g (radialize (slopeH G d v)); rw [← (show _= _ from radial_color (j:=d) g (slopeH G d v))]; apply congr_arg radialize; funext i j x; change (d.factorial:ℝ)⁻¹ • (trainX _ d _ (curve G i j _) _) = G.adjoint g ((d.factorial:ℝ)⁻¹ • (trainX _ d _ (curve G i j _) _)); rw [color_curve,tracksX,map_smul]; rfl
lemma plume_ledge (v: Taylor G d) (g:G.El):plumeX g (ledge v.val)=ledge (Taylor.paint g v).val:=rfl
-- ingredient axis coord
lemma tracks_color (v:fieldX (Shade G)) (a b:Axis) (j:G.ColorIndex) (p:Fin d→Axis):
    (chin j)∘ trainX G.Color d p (curve G a b v)=trainX ℝ d p (movesX ℝ a (fun i: Cover=> v (i,(b,j))))-trainX ℝ d p (movesX ℝ b (fun i:Cover=>v (i,(a,j)))):=by
      let f(i t:Axis):=movesX ℝ t (fun x:Cover=> v (x,(i,j))); have he: (chin j) ∘ curve G a b v=f b a-f a b:=rfl; change (chin j).toLinearMap∘ _=_; rw [← tracksX,← map_sub]; exact congr_arg (trainX ℝ d p) he
lemma decisions (A: Taylor G d): templateX G d (ledge A.val)=A:=by
   let v:=ledge A.val; suffices h : slopeH G d v = components A from congr_arg radialize h|>.trans (complete A)
   ext a b p j
   let w:=takeCurl A a b; let B:= fun a=> (chin j).compContinuousMultilinearMap (A.val a); let f(a:Axis):=diagonal (B a) ∘ fromX; let T := (chin j).compContinuousMultilinearMap w
   have he(i k:Axis) (x:Lieu Axis) : breeze (basis i) (f k) x= chin j (grad i (A.value k) (fromX x)):=by
       let D:= chin j; unfold breeze; rw [show f k∘invertX=D ∘ diagonal (A.val k) from rfl, fderiv_comp (fromX x) D.differentiableAt ((diag_smooth (A.val k) ⊤).differentiable (by simp) _),D.fderiv];rfl
   have ht : trainX ℝ d p (movesX ℝ a ((f b) ∘ translit))- trainX ℝ d p (movesX ℝ b ((f a) ∘ translit))= trainX ℝ d p (diagonal T ∘fromX ∘translit):=by
       rw [breezedL _ (tgon (B b)), breezedL _ (tgon (B a)),← map_sub]; apply congr_arg; ext x; change breeze _ _ _-breeze _ _ _=chin j (diagonal (takeCurl A a b) (fromX (translit x))); rw [takeCurl_diag,he,he]; simp
   have hv := (tracks_color v a b j p).trans ht
   have hx := congr_fun hv 0|>.trans (totX T (fun u s=>congr_arg (chin j) ((closedCurl A).coeffSym _ _ u s)) p 0)
   change (d.factorial:ℝ)⁻¹ * ((chin j)∘trainX _ d p (curve G a b v)) 0 = _; rw [hx,inv_mul_cancel_left₀ (by positivity)]; rfl
lemma retainedX (p:fieldX (Shade G))(hp:Low p d)(hh:d<n+1): templateX G n p=0:=by
   suffices h:slopeH G n p=0 from (show radialMap (slopeH G n p)=_ by rw [h,_root_.map_zero])
   ext a b k i; choose f hf h using hp
   have he(a b:Axis) : trainX ℝ n k (movesX ℝ a (fun x:Cover=> p (x,(b,i))))=0:=by
      let q:Lieu Axis→ℝ:=f (b,i); let Q: Flavor Axis d:=⟨q,hf _⟩; rw [show (fun x:Cover=>p (x,(b,i)))=Q.val∘translit from funext fun x=>h ..,moveLow]
      have hz:=sudden q Q.property (basis a); by_cases ht:d=0; · rw [hz.2 ht]; exact _root_.map_zero _
      exact trackL _ hz.1 _ (by omega)
   have ht:=tracks_color (d:=n) p a b i k; rw [he a b, he b a, sub_zero] at ht
   change (n.factorial:ℝ)⁻¹ * ((chin i)∘trainX _ _ k _) 0 = 0; rw [ht]; simp
end Script
end YM.OPE.Flume

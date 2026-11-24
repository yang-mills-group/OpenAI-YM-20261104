import YM.OPE.Compatible.Seeds.Glide
/-!
# Opus Ward charge per step by fresh/installed. All. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Exterior Matrix FreeResolvent Precision Tree Woody Bloch Work.F08 Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {r d' j k n m:ℕ}{U:ℝ}{V I W:Type*}{G:Gauge}{c f:Side}{L:KernelChoices}{P:Flight j k}
namespace Script
open Page
-- color
variable {S:StepData c f}
def chipHue (u:G.El)(x:Vec G c 1):= (deckW G c).symm (hue u (deckW G c x))
lemma plume_chip (u:G.El)(x:Vec G c 1)(i:G.ColorIndex):
   component (chipHue u x) i=(fun p=> G.adjoint u (toLp 2 (fun j=>component x j p)) i):=by
      ext1 ⟨p,a⟩; obtain ⟨a,rfl⟩:= axisEquiv.surjective a
      change chipHue u x (station G c (p,a,i))= G.adjoint u (toLp 2 _) _; rw [← shipEq (chipHue u x) (p,a,i),chipHue, LinearEquiv.apply_symm_apply];rfl
lemma chromatic (u:G.El)(A:Matrix (Body 1 c) (Body 1 f) ℝ)(x:Vec G f 1):
   tensor G A *ᵥ chipHue u x=chipHue u (tensor G A *ᵥ x):=by
       ext ⟨p,b,i⟩; change component (tensor G A *ᵥ chipHue u x) i (p,b)=component (chipHue u _) i (p,b); simp_rw [component_mul, plume_chip, component_mul]; let z(q:Body 1 f):G.Color:=toLp 2 (fun j=>component x j q); have he:toLp 2 (fun j=>(A *ᵥ component x j) (p,b))=(∑ q:Body 1 f, A (p,b) q • z q):=by
          ext1 a; simp only [WithLp.ofLp_sum,Finset.sum_apply]; rfl
       rw [he,map_sum]; change ∑ q:Body 1 f, A (p,b) q * G.adjoint u (z q) i = chin i _; rw [map_sum]; exact sum_congr rfl fun q _=>by rw [map_smul,map_smul]; rfl
lemma voyage (u:G.El)(A:Cross S.ratio.count (TypeFace 1) (TypeFace 1)) (x:deck (Shade G) c):
   installed S.ratio (chrome G.ColorIndex A) *ᵥ hue u x=hue u (installed S.ratio (chrome G.ColorIndex A) *ᵥ x):=by
       let z:= (deckW G c).symm x; rw [stage_mul, stage_mul, show (deckW G c).symm _=chipHue u z by unfold z chipHue; rw [LinearEquiv.apply_symm_apply],chromatic,chipHue,LinearEquiv.apply_symm_apply]
variable {p:Script (Shade G) r} (B:Woody.Medal P.patch G L j)
private lemma homeLayout (N:Side)(v:ℝ)(h:0<v) (hk:4≤ k) (p:Script (Shade G) r)(hp:Summable p)(x:Fin r→deck (Shade G) N) (K: KernelChoices):
   let g:=P.visit (c:=N) (f:=N*P.L) K rfl
   scribe 0 (opal G.ColorIndex P v p) x=scribe (0:Site (N*P.L)) p (fun i=> installed g.ratio (chrome G.ColorIndex (linesOf P v)) *ᵥ x i):=by
     intro g
     have hx:=chrome_sum (W:=G.ColorIndex) (stored P _ h hk); have hg:Whole (chrome G.ColorIndex (linesOf P v)):= hx -- check arguments
     change _=scribe _ p _; unfold opal; erw [bridge_torque (g:=g.ratio) hg 0 0 p hp]; simp only [_root_.map_zero, add_zero]; congr 1; ext; simp [Ratio.embed]; -- tag
lemma hubTint (P:Flight j k)(K:KernelChoices)(p:Script (Shade G) r)(hk:4≤k)(h:Summable p)(ht:p.painted): (opal G.ColorIndex P K.penalty p).painted:=by
     intro n v u; rw [homeLayout _ _ K.penalty_pos hk p h _ K,homeLayout _ _ K.penalty_pos hk p h _ K]; simp_rw [voyage]; exact ht ..
lemma hubWorks (P:Flight j k)(K:KernelChoices)(p:Script (Shade G) r)(hp:P.patch.Branches K G)(hk:4≤k)(h:Summable p)(ht:p.abides): (opal G.ColorIndex P K.penalty p).abides:=by
    intro i n v a; let f:=n*P.L; let g:= P.visit (c:=n) (f:=f) K rfl; let F:=forest g.ratio P.odd
    let A:=chrome G.ColorIndex (linesOf P K.penalty); let M(j):= installed g.ratio A *ᵥ v j
    obtain ⟨B⟩:= Woody.medal_buy (P:=g.patch) (show Odd g.patch.L.val from P.odd) (show g.patch.Branches g.kernel G from hp) P.legal -- find name
    obtain ⟨w,hw⟩:=glide g _ _ F (B.measure_pos g P.odd P.wing P.legal) (linesOf P K.penalty) (P.tangent K hk (c:=n) (f:=f) rfl).1 a
    rw [homeLayout _ _ K.penalty_pos hk p h _ K]; change scribe (0:Site f) p (fun j=> installed g.ratio A *ᵥ update v i (cliff a) j)=_; rw [show (fun j=> installed g.ratio A *ᵥ update v i (cliff a) j)= update M i (cliff w) from funext fun j=> by
       by_cases he:j=i
       · subst j;rw [Function.update_self,Function.update_self]; exact hw
       unfold M; rw [Function.update_of_ne he,Function.update_of_ne he]]; exact ht ..
end Script
end YM.OPE.Flume

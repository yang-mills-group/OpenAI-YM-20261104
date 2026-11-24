import YM.OPE.Compatible.Squalls.Fan
/-! Taylor leading by loops. Full inertia. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier Asymptotics WardBin
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
variable [Fintype I] {x:I→fieldX (Shade G)} {k:I→ℕ}
abbrev xspout (x:I→fieldX (Shade G))(k:I→ℕ)(t:ℝ):= lotU (spout x k t)
lemma smoothBeam (u:Chant G n):ContDiffAt ℝ ⊤ (fun t:ℝ=>verseX u (xspout x k t)) 0:=by
    simp_rw [xspout,← permit_atom u, spout,map_sum,map_smul]; exact (permitS u).contDiffAt.comp _ (ContDiffAt.sum (fun i _=> (monoSmooth ..).contDiffAt)) -- lambda
lemma lead_at {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](f:ℝ→E)(h:ContDiffAt ℝ ⊤ f 0){k:ℕ}(v:E)(hf:sideLimit (fun t:ℝ=>(t^k)⁻¹ • f t) v) (hn:n ≤ k): leading n f=if n=k then v else 0:=by
    split; next he=> subst k; exact leading_of_lim (h.of_le le_top) v hf
    next he=> exact leading_of_lim (h.of_le le_top) _ (falls (lt_of_le_of_ne hn he) hf)
-- generic p of legSlots along xspout
abbrev tileK (u: Fin n→RG.Slot)(s:Signed)(v:Fin n→ G.ColorIndex):Chant G n:=fun i=>slotBeam (u i) s (v i)
lemma spinShot (h:radiantX x k)(p:Fin n→ RG.Slot)(s:Signed)(i: Fin n→ G.ColorIndex)(hy:m ≤ n*2):
   leading m (fun t=> verseX (tileK p s i) (xspout x k t))= if m=n*2 then ∏ j, CurlX x k s (p j).plaq (i j) else 0:=by
       refine lead_at _ (smoothBeam _) _ ?_ hy
       have he:=tendsto_finsetProd univ fun j (_:j∈univ)=> (chin (i j)).continuous.tendsto (CurlX x k s (p j).plaq)|>.comp (ticket_spice h s (p j)); apply he.congr; intro t
       change (∏ j:Fin n,chin (i j) ((t^2)⁻¹ • _))= (t^(n*2))⁻¹* verseX _ _; simp_rw [map_smul, smul_eq_mul]; rw [prod_mul_distrib, prod_const, card_univ,Fintype.card_fin, inv_pow,← pow_mul,Nat.mul_comm 2 n]; congr 1; exact Finset.prod_congr rfl fun j _=> (slotBeamEq (p j) s (i j) _).symm
lemma twinShot (h:radiantX x k)(R:PathData G)(p:PlaqAxes)(a b:ℕ)(i:G.ColorIndex)(s:Signed)(hz:m ≤4): leading m (fun t=> verseX (duetU R p s i (a,b)) (xspout x k t))= if m=4 then CurlX x k s (Claw R p a).plaq i*CurlX x k s (Claw R p b).plaq i else 0:=by
     let F := (![Claw R p a, Claw R p b]); let v:=fun _ : Fin 2=> i; rw [show duetU R p s i (a,b)=tileK F s v from funext fun i=> by fin_cases i<;>rfl, spinShot h F s v (by omega),Fin.prod_univ_two]; rfl
lemma priceShot (h:radiantX x k)(p:PlaqAxes)(s:Signed)(hz:m ≤4): leading m (fun t=>verseX (gateUnit G p s ()) (xspout x k t))= if m=4 then ‖CurlX x k s p‖^2/2 else 0:=by
    let V t:=xspout x k t; refine lead_at _ (smoothBeam _) _ ?_ hz; unfold verseX; simp_rw [Fin.prod_univ_one]; convert! (ticket_curve (fun t=>faceValue (Bark x k s t) (0,p)) (CurlX x k s p) 2 (face_spine h s p 0)).1 using 1; exact funext fun i=> congr_arg (fun z:ℝ=> (i^4)⁻¹*z) (plaqBeamEq ..)
end Script
end YM.OPE.Flume

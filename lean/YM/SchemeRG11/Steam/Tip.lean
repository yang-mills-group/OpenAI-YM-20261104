import YM.SchemeRG11.Steam.Bloom
/-! Exactly at an apex heat face in the differentiated star. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.SchemeRG11.Steam
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter Cluster MSbar
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
local notation "Tri" => Nodes 4

lemma drift_step {V : Tri→ℝ} (x : Tri) (q : Tri) (hv : DifferentiableAt ℝ V x) :
    HasDerivAt (fun r:ℝ=> V (x+r • q)) (fderiv ℝ V x q) 0 := by
  let g:= fun r:ℝ=> x+r • q
  have h : g 0=x:=by simp [g]
  have hh:= (show DifferentiableAt ℝ V (g 0) from h.symm ▸ hv).hasFDerivAt.comp_hasDerivAt (f:=g) (0:ℝ) (drift ..)
  rw [h] at hh; exact hh

private lemma crest0 (x : Tri) (p q : ℝ) (hp : 0<p) (hq : 0<q) :
    trio (0,p,q) x=tint [] p (x 1-x 0)*tint [] q (x 2-x 0) := by
  change _=gauze p _*gauze q _
  unfold trio; rw [expan,gauze,gauze]; simp only [knot,zero_mul,zero_add,norm_sub_rev (x 0)]
  rw [show -((p*‖x 2-x 0‖^2+q*‖x 1-x 0‖^2)/(4*(p*q)))=(-α p*‖x 1-x 0‖^2)+(-α q*‖x 2-x 0‖^2) by unfold α; field_simp; ring,Real.exp_add]; ring
lemma arrive (p q : ℝ) (hp : 0<p) (hq : 0<q) (V W : Sl) : ∀ x : Tri,
    orb [] V W (0,p,q) x=tint V p (x 1-x 0)*tint W q (x 2-x 0) := by
  induction V with
  | nil =>
     induction W with
     | nil => exact fun x=> crest0 x p q hp hq
     | cons a l ih =>
         intro x
         let g : Tri→ℝ:=orb [] [] l (0,p,q)
         have hh : DifferentiableAt ℝ g x:= (series_calm (trio_diff (0,p,q)) _).differentiable (by simp) x
         let v := atEye (2,a)
         have hm (r:ℝ) : (x+r • v : Tri) 0=x 0 := by norm_num [v,atEye,Eye,Pi.single_apply,Fin.ext_iff]
         have hn (r:ℝ) : (x+r • v : Tri) 1=x 1 := by norm_num [v,atEye,Eye,Pi.single_apply,Fin.ext_iff]
         have hk (r:ℝ) : (x+r • v : Tri) 2 - x 0=x 2-x 0+r • basis a:= by simp only [v,Pi.add_apply,Pi.smul_apply,atEye,Pi.single_eq_same]; abel
         have he:=drift_step x v hh
         simp_rw [g,ih _,hm,hn,hk] at he
         convert! he.unique ((pulls l a q (0:ℝ) (x 2-x 0)).const_mul (tint [] p (x 1-x 0))) using 1; simp
  | cons a l ih =>
     intro x
     let g := orb [] l W (0,p,q)
     let v := atEye (1,a)
     have hm (r:ℝ) : (x+r • v : Tri) 0=x 0:=by norm_num [v,atEye,Eye,Fin.ext_iff]
     have hn (r:ℝ) : (x+r • v : Tri) 2=x 2:=by norm_num [v,atEye,Eye,Fin.ext_iff]
     have hk (r:ℝ) : (x+r • v : Tri) 1-x 0=x 1-x 0+r • basis a:= by simp only [v,Pi.add_apply,Pi.smul_apply,atEye,Pi.single_eq_same]; abel
     have hh : DifferentiableAt ℝ g x:= (series_calm (trio_diff (0,p,q)) _).differentiable (by simp) x
     have he:=drift_step x v hh
     simp_rw [g,ih _,hm,hn,hk] at he
     convert! he.unique ((pulls l a p 0 (x 1-x 0)).mul_const (tint W q (x 2-x 0))) using 1; simp
end YM.SchemeRG11.Steam

import YM.OPE.Compatible.Seas.Angles
/-!
# Three-index contractions with field Maxwell harmonics.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nestle.Pose
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
open Balsam Extra.FD.OPE
open Next.Rank.Radian (dV stroll)
variable (p q: Pose) {F:E4→ℝ}{s:ℝ}
lemma genK (g:Axis→Axis→ℝ): ∑ i:Axis,p.Lck (g i) i=g p.b p.a-g p.a p.b:=by unfold Lck; simp
lemma turn_in (f:Axis→Axis→ℝ)(a b:Axis): p.Lck (fun i=> q.Lck (f i) b) a=q.Lck (fun i=> p.Lck (fun j=>f j i) a) b:=by unfold Lck; split_ifs<;> ring
lemma gradWheel (l m:List Axis)(f:E4→ℝ):dV (l++m) f=dV l (dV m f):=by induction l with | nil=>rfl | cons a l ih=> rw [List.cons_append]; change grad a (dV _ f)= grad a (dV l _); rw [ih]
lemma segG {f:E4→ℝ}(h:seg f)(l:List Axis):seg (dV l f):=by rw [seg,contDiff_iff_contDiffAt];exact fun x=>stroll l h.contDiffAt
lemma cede (a b t) (h:Spherical F (p.aLen []+q.aLen []+1)): dV (p.path [] b++q.path [] t) (grad a F) 0= dV (p.path [] a ++q.path [] t) (grad b F) 0:=by
    let l:=p.m++q.path [] t
    change grad b (dV l (grad a F)) 0=grad a (dV l (grad b F)) 0; rw [←twist_d l h.size.smooth,← twist_d l h.size.smooth]; exact grad_exchange (stroll l h.size.smooth.contDiffAt) ..
lemma slouch (hs:0<s)(b:Axis)(h:Spherical F (p.aLen []+q.aLen []+1)): ∑ i:Axis, fineI s (p.pureD [] i*q.pureD [] b* grad i F)=0:=by
     have hh i:= p.toQ q hs [] [] i b (sph_der h i); simp_rw [hh,← Finset.mul_sum, p.genK]; have he(t):= cede p q p.b p.a t h; simp_rw [he,sub_self,mul_zero]
lemma stint (hs:0<s)(b:Axis)(h:Spherical F (p.aLen [0]+q.aLen [])): ∑ i:Axis,fineI s (p.pureD [i] b*q.pureD [] i*F)=0:=by
    have he (i):= p.toQ q hs [i] [] b i (F:=F) h; simp_rw [he, show ∀ i, p.aLen [i]= p.aLen [0] from fun i=>rfl,p.turn_in q, ← Finset.mul_sum,q.genK]
    have hv(d): dV (p.path [q.a] d++q.path [] q.b) F=dV (p.path [q.b] d++q.path [] q.a) F:=by
       let L:=p.path [] d; let t:=dV q.m F
       rw [gradWheel,gradWheel _ (q.path [] q.a)]; change grad q.a (dV L (grad q.b t))=grad q.b (dV L (grad q.a t)); rw [←twist_d L (segG h.size.smooth _), ← twist_d L (segG h.size.smooth _)]; exact funext fun x=> grad_exchange (segG (segG h.size.smooth q.m) L).contDiffAt _ _ -- h should segG t not grad!
    simp_rw [hv,sub_self,mul_zero]
lemma bary (hs:0<s){V:Axis→E4→ℝ}(hp:∀ a,Spherical (V a) (p.aLen [0]+q.aLen []))(he:∑ a:Axis, grad a (V a)=0)(i j:Axis):∑ a:Axis,fineI s (p.pureD [a] i*q.pureD [] j * V a)=0:=by
     simp_rw [fun a=>p.toQ q hs [a] [] i j (hp a),show ∀ a,p.aLen [a]=p.aLen [0] from fun a=>rfl,← Finset.mul_sum]
     have H(t v):∑ a:Axis,dV (p.path [a] t++q.path [] v) (V a) 0=0:=by
         let M:=p.path [] t++q.path [] v; have hh(a): dV (p.path [a] t++q.path [] v) (V a) = dV M (grad a (V a)):= twist_d M (hp a).size.smooth a
         simp_rw [hh,←Finset.sum_apply]; rw [←tourM,he,monoZ]; simp; exact fun a=> grad_diff_all (hp a).size.smooth a
     apply mul_eq_zero_of_right; unfold Lck; split_ifs <;> simp only [Finset.sum_sub_distrib,H,sub_self,Finset.sum_const_zero]
where
  tourM (l:List Axis)(W:Axis→E4→ℝ)(hp:∀ i,seg (W i)): dV l (∑ i,W i)= ∑ i,dV l (W i) :=by
     induction l with
     | nil=> rfl
     | cons a l ih=> change grad a (dV l _)= ∑ i,grad a (dV l (W i)); rw [ih]; funext x; rw [grad_sum_f _ (fun i _=> (segG (hp i) l).contDiffAt), Finset.sum_apply]
  monoZ (l:List Axis):dV l (0:E4→ℝ)=0:=by
     induction l with
     | nil=> rfl
     | cons a l ih=> change grad a (dV l _)=0; rw [ih]; funext x;simp [grad,D]
end YM.OPE.Nestle.Pose

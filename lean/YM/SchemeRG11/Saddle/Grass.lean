import YM.SchemeRG11.Saddle.Symbol
/-! Shift and homogeneous insertion control. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.SchemeRG11.Sway
open Lam
open Function Filter Lattice Pert Full Bare Labels Pert.Orb Local Haze Atoll MvPolynomial
open scoped Classical ContDiff Topology Matrix.Norms.Frobenius PowerSeries
variable {G:Gauge}{n:Side}

lemma x_weight(R:Type*)[CommRing R](a:ℂ→+*R){p:Pol G}{n:ℕ}(hp:MvPolynomial.IsHomogeneous p n)(ψ:Key G→R)(x:R):
 eval₂Hom a (fun i=>x*ψ i) p=x^n* eval₂Hom a ψ p:=by
 conv_lhs=> rw [← p.support_sum_monomial_coeff]
 conv_rhs=> rw [← p.support_sum_monomial_coeff] -- separate
 rw [_root_.map_sum,_root_.map_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun i hi=>?_
 have hi:n=∑j∈i.support,i j:=by rw [←hp (mem_support_iff.mp hi), Finsupp.weight_apply,Finsupp.sum];simp
 rw [hi,eval₂Hom_monomial,eval₂Hom_monomial]; unfold Finsupp.prod; simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; ring

/-- Literal unscaled `valuesU 1`; no external Wick data. -/
def terrain (x:Site n)(h:ℝ)(p:Pol G)(U:Wilson.Config G n):ℂ:= exactColumn 1 h U x p
lemma terrain_eq(x:Site n)(h:ℝ)(p:Pol G)(a:Potential G n): terrain x h p (positiveLinks a) = aeval (R:=ℂ) (fun i:Key G=> datum h x i a) p:=by
 unfold terrain exactColumn Labels.read; have he(j:Key G): coord (valuesU 1 h (positiveLinks a) x) j=datum h x j a:=by unfold coord datum valuesU; rw [inv_one,one_smul]
 rw [funext he]
section coord
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](e:E→L[ℝ]Potential G n)(x:Site n)(h:ℝ)
def layout (i:Key G): JetArray E:= fun a=>PowerSeries.mk (fun k=> PowerSeries.coeff (k+1) (ChartC (datum h x i ∘ e) a))
def tabs (p:Pol G):JetArray E:= fun t=> eval₂Hom PowerSeries.C (fun i=>layout e x h i t) p
lemma layouts (i:Key G) (a:E):PowerSeries.X * layout e x h i a=ChartC (datum h x i ∘ e) a:=by
 ext k; cases k with
 | zero=>simp [ChartC] -- check
 | succ k=> rw [mul_comm,PowerSeries.coeff_succ_mul_X,layout,PowerSeries.coeff_mk]
lemma datum_slick(i:Key G): ContDiffAt ℝ ∞ (datum h x i ∘ e) 0:= by
 apply ContDiffAt.comp
 · rw [map_zero]; exact (datum_diff ..).of_le le_top
 exact e.contDiff.contDiffAt
lemma terrainII(p:Pol G): ContDiffAt ℝ ∞ (fun y:E=>terrain x h p (positiveLinks (e y))) 0:=by
 simp_rw [terrain_eq]; induction p using MvPolynomial.induction_on with
 | C c=> simp only [aeval_C]; exact contDiffAt_const
 | add a b ha hb=> simp only [map_add]; exact ha.add hb
 | mul_X p i hp=> simp only [map_mul, aeval_X]; exact hp.mul (datum_slick e x h i)
lemma shift_eval(p: Pol G)(t:E): ChartC (fun v:E=>terrain x h p (positiveLinks (e v))) t= MvPolynomial.eval₂Hom PowerSeries.C (fun i=>PowerSeries.X* layout e x h i t) p:=by
 induction p using MvPolynomial.induction_on with
 | C c=> simp_rw [terrain_eq,aeval_C]; rw [Lam.chart_const,eval₂Hom_C];rfl
 | add p q hp hq=>
    simp only [_root_.map_add]; rw [show (fun v:E=>terrain x h (p+q) (positiveLinks (e v)))=(fun v=>terrain x h p (positiveLinks (e v))+terrain x h q (positiveLinks (e v))) from funext fun v=>by rw [terrain_eq,terrain_eq,terrain_eq,map_add],chart_add (terrainII e x h _) (terrainII e x h _),Pi.add_apply,hp,hq]
 | mul_X p i hp=>
    let D:= datum h x i
    simp only [_root_.map_mul,eval₂Hom_X']; rw [show (fun v:E=>terrain x h (p* X i) (positiveLinks (e v)))=(fun v=>terrain x h p (positiveLinks (e v))* (D ∘ e) v) from funext fun v=>by rw [terrain_eq,terrain_eq,map_mul,aeval_X];rfl,chart_mul (f:=fun v=> terrain x h p (positiveLinks (e v))) (g:=D ∘ e) (terrainII e x h _) (datum_slick e x h _),Pi.mul_apply,hp,layouts]
lemma shift_motif{p: Pol G}{m:ℕ}(hp:IsHomogeneous p m):
    ChartC (fun v:E=>terrain x h p (positiveLinks (e v)))=(fun _=> PowerSeries.X^m)*tabs e x h p:= funext fun t=> Eq.trans (shift_eval e x h p t) (x_weight ℂ⟦X⟧ _ hp _ _)
lemma layout_ready(i:Key G):Ready (layout e x h i):=Ready.maker fun _=>chart_ready (datum h x i ∘ e) _
lemma tabs_ready(p:Pol G): Ready (tabs e x h p):=by
 unfold tabs; induction p using MvPolynomial.induction_on with
 | C c=> simp only [eval₂Hom_C]; exact Ready.constant _
 | add p q hp hq=> simp only [_root_.map_add]; exact hp.add hq
 | mul_X p i hp=> simp only [_root_.map_mul,eval₂Hom_X']; exact hp.mul (layout_ready e x h i)
end coord
abbrev Fsup(x:Site n)(h:ℝ)(p:Pol G):=tabs (ContinuousLinearMap.id ℝ (Potential G n)) x h p
abbrev Lsup(x:Site n)(h:ℝ)(p:Pol G):=tabs (E:=Land G n) (g0 G n) x h p
lemma transmit(x:Site n)(h:ℝ){d:ℕ}(p:Pol G)(hp:Full.within p d):
    Full.column d h x p = Fsup x h (dream h p) ∘ blue G n:=by
 funext v
 rw [inventory d h x p hp]
 let f:=ContinuousLinearMap.id ℝ (Potential G n)
 have hj: seriesLex h x v=(fun i=> layout f x h i (blue G n v)):=by
    funext j; ext1 k; simp only [seriesLex,layout,ChartC,PowerSeries.coeff_mk];rfl
 change (MvPolynomial.eval₂Hom PowerSeries.C (seriesLex h x v)) (dream h p)=_; rw [hj];rfl
lemma gleam {x:Site n}{h:ℝ}{p:Pol G}(hp:p∈invariantSpace G): WatchC (terrain x h p) where
 gauge t ht v:=by
    change Labels.read (valuesU _ _ _ _) _= _
    rw [show valuesU 1 h (Lattice.gauge t v) x= colored (t x) (valuesU 1 h v x) from funext fun j=>by simp [valuesU,colored,tensor_gauge]]; exact hp (valuesU 1 h v x) (t x)
 tame:=terrainII (ContinuousLinearMap.id ℝ (Potential G n)) x h p
end YM.SchemeRG11.Sway

import YM.SchemeRG11.Saddle.Grass
import YM.Pert.Lattice.Bundles
/-! Exact normalized amplitudes for all FULL stencils in continuum symbols,
here at finite orbital regulator. Keep center as user data. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.SchemeRG11.Sway
open Function Filter Set Lattice Pert Full Bare Labels Pert.Orb Lam Local Haze Atoll MvPolynomial
open scoped Classical ContDiff Topology Matrix.Norms.Frobenius PowerSeries
variable {G:Gauge}{n:Side}
lemma tabs_waist {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](f:E→L[ℝ]Potential G n)(x:Site n)(h:ℝ)(p:Pol G): (∑ i∈ Finset.range (p.totalDegree+1),tabs f x h (homogeneousComponent i p))=tabs f x h p:=by
 ext1 i; rw [Finset.sum_apply]; simp only [tabs,← _root_.map_sum]; rw [sum_homogeneousComponent]
lemma tab_join {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](f:E→L[ℝ]Potential G n){O: Wilson.Config G n→ℂ}(H:WatchC O){x:Site n}{h:ℝ}{p:Pol G}{m:ℕ}(hp:IsHomogeneous p m):
 let j:= positiveLinks ∘ f
 ChartC ((O*terrain x h p)∘j)= (fun _=>PowerSeries.X^m)*(ChartC (O ∘ j)*tabs f x h p):=by
 intro j
 have hd: ContDiffAt ℝ ∞ (O ∘ j) 0:= by
    exact ContDiffAt.comp (g:=O ∘ positiveLinks) (f:=f) 0 (by rw [map_zero]; exact H.tame) f.contDiff.contDiffAt
 rw [show ((O*terrain x h p)∘j)=(fun v:E=> (O∘j) v * terrain x h p (positiveLinks (f v))) from rfl, chart_mul hd (terrainII f x h p), shift_motif _ _ _ hp, mul_left_comm]
lemma warm_times{O P: Wilson.Config G n→ℂ}(h:WatchC O)(H:WatchC P): WatchC (O*P):=⟨fun t ht v=> by simp only [Pi.mul_apply,h.gauge t ht,H.gauge t ht], h.tame.mul H.tame⟩
lemma lsup_ready(x:Site n)(h:ℝ)(p:Pol G): Ready (Lsup x h p):=by unfold Lsup; apply tabs_ready (E:=Land G n) (g0 G n) x h p
lemma sum_formula{I:Type*}(T:Finset I)(W:I→JetArray (Potential G n))(Q:I→JetArray (Land G n))(hw:∀ i, Ready (W i))(hq:∀ i, Ready (Q i))(HH:∀ i, Fentry (W i)= Lentry (Q i)): Fentry (∑ i∈T,W i)=Lentry (∑ i∈T,Q i):=by
 induction T using Finset.induction_on with
 | empty=>
    rw [Finset.sum_empty, Finset.sum_empty]; unfold Fentry Lentry; rw [Pert.Orb.normalize,show ((0:JetArray (Potential G n))∘blue G n)=0 from rfl, mul_zero, Pert.Orb.expect_zero, zero_mul]; unfold Lam.choir; rw [mul_zero,show heart (chosen G n) LAND (0:JetArray (Land G n))=0 by ext1 k; simp [Lam.heart,Lam.Cost],zero_mul]
 | insert j t hj HJ=> rw [Finset.sum_insert hj, Finset.sum_insert hj,entry_add (hw j) (Ready.sum (fun k _=>hw k)),Lentry_add (hq j) (Ready.sum (fun k _=>hq k)),HH,HJ]

lemma bare_squares {I:Type}(s:Finset I)(x:I→Site n)(h:ℝ)(p:I→Pol G)(H:∀i∈s,p i∈invariantSpace G)(hn:Admissible n){O:Wilson.Config G n→ℂ}(ht:WatchC O): Fentry (ChartC (O∘positiveLinks) * ∏ i∈s,Fsup (x i) h (p i))=Lentry (ChartC (O ∘ positiveLinks ∘ g0 G n) *∏ i∈s,Lsup (x i) h (p i)):=by
 induction s using Finset.induction_on generalizing O with
 | empty=> simp only [Finset.prod_empty,mul_one]; exact rigidFl hn ht
 | insert i s he ih=>
   let U:= ∏ j∈s,Fsup (x j) h (p j); let V:= ∏ j∈s,Lsup (x j) h (p j)
   let P:= p i
   let f:= ContinuousLinearMap.id ℝ (Potential G n); let g:=g0 G n
   let a:=ChartC (O∘positiveLinks); let b:=ChartC (O∘positiveLinks∘g)
   let W(m):= a*(Fsup (x i) h (homogeneousComponent m P)*U); let Q(m):= b*(Lsup (x i) h (homogeneousComponent m P)*V)
   have hw(m:ℕ): Ready (W m):= Ready.mul (chart_ready _) ((tabs_ready f (x i) h (homogeneousComponent m P)).mul (Ready.prod (fun j _=> tabs_ready f (x j) h (p j))))
   have hq(m:ℕ): Ready (Q m):= by
     have h': Ready b:= by exact chart_ready (O∘positiveLinks∘g)
     have hz(j:ℕ): Ready (Lsup (x i) h (homogeneousComponent j P)):=lsup_ready _ _ _
     have hv(j): Ready (Lsup (x j) h (p j)):=lsup_ready _ _ _
     exact h'.mul ((hz m).mul (Ready.prod fun j _=>hv j))
   let T:= Finset.range (P.totalDegree+1)
   rw [Finset.prod_insert he, Finset.prod_insert he]
   change Fentry (a*(Fsup _ _ P*U))= Lentry (b*(Lsup _ _ P*V))
   have hz: (∑ j∈T,Lsup (x i) h (homogeneousComponent j P))=Lsup (x i) h P:=by
      unfold Lsup T; apply tabs_waist
   rw [show Fsup (x i) h P= ∑ j∈T,Fsup (x i) h (homogeneousComponent j P) by unfold Fsup T; symm;apply tabs_waist,← hz]; simp_rw [Finset.sum_mul,Finset.mul_sum]
   have HH(m:ℕ): Fentry (W m)= Lentry (Q m):=by
      let w:= homogeneousComponent m P; let Y:= PowerSeries.X (R:=ℂ) ^ m
      have hl: IsHomogeneous w m:= homogeneousComponent_isHomogeneous m P
      have heq:= ih (fun j hj=> H j (Finset.mem_insert_of_mem hj)) (warm_times ht (gleam (x:=x i) (h:=h) (homogeneous_inv (hp:=H i (Finset.mem_insert_self ..)) m)))
      have hv: (fun _=>Y)*W m=ChartC ((O*terrain (x i) h w) ∘ positiveLinks)*U:=by
         rw [show ChartC ((O*terrain (x i) h w) ∘ positiveLinks)= (fun _=>Y)*(a*Fsup (x i) h w) from tab_join f (x:=x i) (h:=h) ht hl,mul_assoc,mul_assoc]
      have hr: (fun _=>Y)*Q m=ChartC ((O*terrain (x i) h w) ∘ (positiveLinks ∘ g))*V:=by
         rw [show ChartC ((O*terrain (x i) h w) ∘ (positiveLinks ∘ g))= (fun _=>Y)*(b*Lsup (x i) h w) from by unfold b Lsup g; apply tab_join (E:=Land G n) (g0 G n) (x:=x i) (h:=h) ht hl,mul_assoc,mul_assoc]
      apply mul_left_cancel₀ (show Y ≠ 0 from pow_ne_zero _ PowerSeries.X_ne_zero)
      rw [← entry_scale (hw m),← Lentry_scale (hq m), hv,hr]
      exact heq
   change Fentry (∑ j∈T,W j)=Lentry (∑ j∈T,Q j)
   exact sum_formula T W Q hw hq HH
lemma topCut {I:Type}(s:Finset I)(x:I→Site n)(d:I→ℕ)(h:ℝ)(p:(i:I)→Label G (d i))(hn:Admissible n): amplitude d h s x (fun i=>(p i).val)= Lentry (∏ i∈s,Lsup (x i) h (dream h (p i).val)):=by
 have h1: WatchC (n:=n) (G:=G) (fun _=>1):=⟨fun _ _ _=>rfl,contDiffAt_const⟩
 let w(i:I):= dream h (p i).val
 have hh:= bare_squares s x h w (fun i _=> dream_inv (p i).property.2 h) hn h1
 rw [show ChartC ((fun _=>(1:ℂ))∘positiveLinks)= (1:JetArray (Potential G n)) from Eq.trans (chart_const _) (funext fun i=> map_one _),one_mul,
     show ChartC ((fun _=>(1:ℂ))∘positiveLinks ∘ g0 G n)=(1:JetArray (Land G n)) from Eq.trans (chart_const _) (funext fun i=>map_one _), one_mul] at hh
 rw [← hh]; apply congrArg (Pert.Orb.normalize); ext1 v; simp_rw [Full.product,Function.comp_apply,Finset.prod_apply]; exact Finset.prod_congr rfl fun i _=>congrFun (transmit (x i) h _ (height_le (p i))) v
lemma axisCut (d:ℕ){m:ℕ}(h:ℝ)(hn:Admissible n)(x:Fin m→Site n)(F:Labels.Frames G)(p:Fin m→Full.Source (Frame:=F) d): row d F h x p=Lentry (∏ i, Lsup (x i) h (dream h (Full.sections d F (p i)))):=by
 rw [row_def]; exact topCut _ x _ h (fun i=>RawLabels.physicalLabel F d (p i)) hn
end YM.SchemeRG11.Sway

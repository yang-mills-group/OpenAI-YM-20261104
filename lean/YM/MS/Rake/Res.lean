import YM.MS.Rake.Magic
/-!
# Integrating instantiated source equations. worldview.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Geo
open Book.Convolve
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W]{G:Gauge}{P: Geo I}{n:ℕ}{b:Bool} {x:Position W I}{K L: Planet G I}{F X Y:Site G I}{A:W→ Site G I}{S:Dance G I W}
structure Record (μ:I→Measure QP)(L:Planet G I)(F H:Glade G I): Prop where
   smooth: Warm F false
   motion: ∀ i w t, HasDerivAt (fun t:ℝ=>F i t w) (( sailP μ L F+H ) i t w ) t
abbrev Ven (μ:I→Measure QP)(K L:Planet G I)(F X:Site G I) := ∀ n, Record μ L ( X n ) ( lonely K F X n )
lemma degreeF (U: Edge G)(V:Law G)(a:QP)(l:Legs (Lane4 G)): trc (spread U) a V l=(aisle a:ℂ)*trc U a V l:= by
   simp_rw [at_trc,spread,mul_assoc,← Finset.mul_sum]
lemma homePeriod (P:Edge G)(U: Law G)(w:Legs (Lane4 G))(hp:City.Near P)(h:City.Perk U): City.Gate (fun p=> trc P p U w):= by
   intro x p; simp_rw [ at_trc ]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; rw [neg_add,show -Tone.rep x=Tone.rep (- x) from (map_neg ..).symm, hp, show U ((i,p+rep x)::(j,-p+rep (-x))::w) = Tone.veil x i*U ((i,p)::(j,-p+rep (-x)) ::w) from h [] ((j,_)::w) i p x, show U ((i,p)::(j,-p+rep (-x))::w)= _ from h [(i,p)] w j (-p) (-x)]; simp only [ backv,List.cons_append,List.nil_append ]; ring_nf; simp [pow_two,testX]
lemma startCycle (u:ℝ→ Law G) (x:ℤ)(h:Bon b x u)(z y:ℝ) : cycle (PlanetL G z) planeF ( u y )= cycle ( LowP G z ) μzone ( u y ):= by
   ext k; let U(p:QP):=trc (LowP G z) p ( u y ) k; have hh:Continuous U:= by
       unfold U; simp_rw [ scaleL, at_trc ]; refine continuous_finsetSum _ fun i _=> continuous_finsetSum _ fun j _=>?_ ; have hp:= ( ( main_f G i j ).continuous.comp (f:=fun p:QP=> (exp z,p)) ( by fun_prop ) ).const_smul (exp z:ℂ)
       refine hp.mul ?_; let w:Wire (BH G) ( QP × ℝ ) QP := ( i,ContinuousLinearMap.fst ℝ QP ℝ )::(j,-ContinuousLinearMap.fst ℝ QP ℝ)::Wire.lift (ray k) (ContinuousLinearMap.snd ℝ QP ℝ);
       convert ( (h.joint.routine w y).continuous.comp (f:=fun p:QP=>(p,(1:ℝ))) (by fun_prop)) using 1; ext; simp [w]
   unfold cycle PlanetL; simp_rw [degreeF]; exact shineZ (F:=U) hh (homePeriod _ _ k (nearL G z) ( h.perk y ))
variable {Fp Q: Recount G}{η:I→ℝ}
def circle (η:I→ℝ)(F:Recount G): Site G I:= fun i=> nameR (F i) η
lemma pour (Qd:Needle G)(h:Domain.Flow Qd false 0 1 Fp Q) (i:ℝ)(w:Legs (Lane4 G)) (n:ℕ)(y:ℝ): HasDerivAt (fun t=> Q n (i,t) w) ((Domain.recu Qd 0 1 Fp Q n (i,y)) w) y:= by
   obtain ⟨hp,hv,ht⟩:= h ℝ (ray w) n (by omega) (fun v=> Bool.noConfusion v) (fun v=> Bool.noConfusion v); have he := ht i y (1:ℝ) 0;
   let U:= continuousMultilinearCurryFin0 ℝ ℝ ℂ; convert! U.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt y he using 1
   · ext; simp [U, Domain.tape,Chart]
   simp [ U,Domain.tape,Chart ]
lemma ergo (Qd:Needle G)(i n y): Domain.recu Qd 0 1 Fp Q n (η i,y)= sailP (fun _=>Qd.measure) (constantP G I Qd.meter) (circle η Q n) i y+ lonely (constantP G I Qd.meter) (circle η Fp) (circle η Q) n i y:= by unfold Domain.recu Domain.using_tree circle lonely; simp_rw [Finset.sum_apply,one_smul]; rfl
end YM.MS.Rake

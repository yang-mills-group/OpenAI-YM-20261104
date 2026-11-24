import YM.FVAAlt2.Mass.Weights
import YM.FVAAlt2.Mass.Damp
/-! Exact rigidity of engineering-power-only part of correlation expansion.
Use all profiles in continuum (even though Poll finite would suffice). This
is why the grading selector constructed using a Wilson-only criterion is unique. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Mass
open Function Finset Filter MeasureTheory Topology Set Metric
open Labels Precision Extra.FD Maxwell Extraction FormalOPE FormalOPE.RG10 RG10.Position.Grade
open PertExtension PertExtension.LatticePT PertExtension.Position PertExtension.Position.Triangle RG10.Position RG10.Gazebo RG10.Carryon RG10.InversionTop
open MS MS.Koszul MS.Menus MS.Book MS.Local.Physical MS.Land MS.FVA.Currency
open PowerSeries (C coeff constantCoeff)
open Home Home.Report Matrix Home.Profiles Convert Next.UVStress
open Real
open scoped Topology BigOperators PowerSeries ContDiff Classical Matrix
variable {G:Gauge}{F:Frames G}{d k n:ℕ}
local notation "V"=> RG10.Position.Deck F d
local notation "ζ"=> Deck.price F d
local notation "Ω"=> constantCoeff (R:=ℝ)
local notation "FW"=> Matrix (RG10.Position.Deck F d) (RG10.Position.Deck F d) fps
namespace EvenCost
section
variable {p:Datum ( RG10.Position.Deck F d )→fps}(hp: EvenCost (Deck.price F d) p)
include hp
lemma coastal (W:Warp) : EvenCost ζ (W.charge ∘ p):=by
 intro v i; simp_rw [Function.comp_apply, Warp.turning, AlignSeries.subst_finite W.atOrigin, Finset.mul_sum, ← mul_assoc ]; refine Polys.sum _ _ (fun j _=> Polys.muls (?_:Polys (fun x=> moving _ _ * coeff j (p (nearD x v)))) (Polys.const _)); exact hp v j
lemma tilted {T: Matrix (RG10.Position.Deck F d) (RG10.Position.Deck F d) fps}(h:Layer ζ T): EvenCost ζ (mix p T):=by
 intro w k; obtain ⟨⟨m,f⟩,z⟩:=w; let H(i:Fin m):=ζ ( z i ); let q:=∑ i:Fin m,H i; let A:=Fin m
 let b(v:A→V):= ∏ i:A, T (z i) (v i); let D(v:Fin m→V): Datum V:= ⟨⟨m,f⟩,v⟩; let μ(v:A→V)(t:ℝ):=p (nearD t (D v))
 change Polys (fun x:ℝ=> moving q x * ( coeff k (∑ i:(Fin (PertExtension.Physical.Profile.n (nearD x (D z)).1)→ V), μ i x*b i))) -- careful dependent Fintype; defeq
 -- adjust dependent rewriting
 change Polys (fun x:ℝ=> moving q x * ( coeff k (∑ i:Fin m→V, μ i x*b i) ) )
 simp_rw [map_sum,Finset.mul_sum]; refine Polys.sum (fun (i:A→V) (x:ℝ)=>_) Finset.univ ?h; intro i hi
 by_cases hv: ∃ j:A,ζ (z j)≠ ζ (i j); · obtain ⟨j,hj⟩:=hv; simp_rw [show b i=0 from Finset.prod_eq_zero (mem_univ j) (f:=fun j:A=>T (z j) (i j)) (h _ _ hj),mul_zero, map_zero,mul_zero]; exact Polys.const _
 push Not at hv; rw [show q=tallyW ζ (D i) from Finset.sum_congr rfl fun j _=> hv j]; simp_rw [PowerSeries.coeff_mul, Finset.mul_sum,←mul_assoc]; refine Polys.sum _ _ (fun k hk=> Polys.muls ( hp ( D i ) _ ) ( Polys.const _ ))
end
variable (F)
def spare (v:Datum V)(i:Fin v.1.n)(j: V):Datum V:= ⟨v.1,update v.2 i j⟩
lemma ranking (s:ℝ)(v: Datum V)(i:Fin v.1.n)(j:V) : nearD s (spare F v i j)=spare F (nearD s v) i j:=rfl
lemma ranked (v: Datum V)(i:Fin v.1.n)(j:V): style F ( spare F v i j )+ ζ ( v.2 i )=style F v+ ζ j:=by
 let A:= Fin v.1.n; let g:= fun a:A=>ζ (v.2 a); let t:=fun a:A=>ζ (update v.2 i j a); change (∑ a:A,t a)+ ζ ( v.2 i )=(∑ a:A,g a)+ζ j; rw [ ← Finset.add_sum_erase (s:=univ) _ ( mem_univ i ),← Finset.add_sum_erase (s:=univ) g (mem_univ i) ]; rw [sum_congr (s₁:=univ.erase i) ( s₂:=univ.erase i ) (f:=t) (g:=g) rfl (fun j h=> by unfold t; rw [update_of_ne (Finset.ne_of_mem_erase h)])]; have he:t i=ζ j:=by simp [t]
 rw [he]; unfold g; omega
variable {F}
lemma appears {f: Datum ( RG10.Position.Deck F d )→fps} (hb:tents F d)(ht: Trim ζ (of hb.val)) (hp: EvenCost (Deck.price F d) f) {k:ℕ} (h:∀ v,coeff k (f v)= Gazebo.beam v hb) (v:Datum V): Gazebo.beam v hb=0:=by
 let FF(x:ℝ):= moving (style F v) x * coeff k (f (nearD x v)); obtain hs: Polys FF:=hp v k
 let n:=v.1.n; let X:=Fin n × RG10.Position.Deck F d; let c(p:X):= style F v-style F (spare F v p.1 p.2); let A (t:X)(x:ℝ):= ( Gazebo.raw F d ) (nearD x (spare F v t.1 t.2))*hb.val (v.2 t.1) t.2; -- give t binder type
 let b(t:X):= ( Gazebo.raw F d ) (spare F v t.1 t.2)*hb.val (v.2 t.1) t.2
 have he : Gazebo.beam v hb=∑ i:X,b i:= (Fintype.sum_prod_type b).symm; rw [he];
 have ht(t:X)(hx : c t=0): hb.val ( v.2 t.1 ) t.2=0:= ht (v.2 t.1) t.2 (show ζ (v.2 t.1)≤ ζ t.2 from (by have hh:= ranked F v t.1 t.2; unfold c at hx; omega) )
 refine dampen Finset.univ c b (fun i _ hv=> mul_eq_zero_of_right _ (ht i hv)) (?_)
 rw [ show ( fun x:ℝ=> (∑ i∈ Finset.univ, _ ) ) = FF from ?_ ]; exact hs
 funext x; unfold FF; rw [ h, show Gazebo.beam (nearD x v) hb= ∑ i:X,A i x from by rw [Fintype.sum_prod_type]; simp_rw [ A,ranking ]; rfl,Finset.mul_sum ]; apply Finset.sum_congr rfl; intro i _; by_cases hv:c i=0; · simp [hv,A,b, ht i hv]
 unfold A b; rw [← mul_assoc,← mul_assoc ] ; refine congr_arg ( · * hb.val _ _ ) ?_; nth_rw 1 [← free_tally F (spare F v i.1 i.2) x]; rw [ ← mul_assoc, moving, moving, ← pow_add, show c i+style F (spare F v i.1 i.2)=style F v from (by unfold c at *; omega) ];rfl
-- parent support.Kick. frame shape emission
lemma degree_diff {b a:Datum ( RG10.Position.Deck F d )→fps}(h: EvenCost (Deck.price F d) a)(hx: EvenCost ζ b): EvenCost ζ (b-a):= by intro p k; simp_rw [Pi.sub_apply,map_sub,mul_sub]; exact Polys.sub ( hx _ k ) ( h _ k )
lemma relation {L M:Matrix (RG10.Position.Deck F d) (RG10.Position.Deck F d) fps} (h:Weight L)(hp:∀ i<n, stamp L i=stamp M i)(hn:0<n)(b:tents F d)(he:(of b.val)=stamp M n-stamp L n){f: Datum (RG10.Position.Deck F d)→fps}(hg:Ω∘ f=Gazebo.raw F d)(v:Datum V) : coeff n (mix f L v)+Gazebo.beam v b=coeff n (mix f M v):=by
 have hv(i j:V): Strike n (L i j) (M i j) (b.val i j):= by
    refine ⟨ fun q h=> congr_fun₂ (hp q h) i j, ?_⟩; rw [← stamp_apply,← stamp_apply,show b.val i j= (stamp M n-stamp L n) i j from congr_fun₂ he i j, Matrix.sub_apply, add_sub_cancel]
 let N(i j:RG10.Position.Deck F d):= C ( Ω ( L i j )) + C ( b.val i j )* PowerSeries.X; obtain hx:= Strike.evaluation (arity:=PertExtension.Physical.Profile.n) (v:=v) (a:=f) hn hv |>.value; simp only [show ∀ i, Ω ( f i )=(Gazebo.raw F d) i from congrFun hg] at hx; change coeff n (mix _ _ _)+coeff 1 (PertExtension.Position.insert _ _ _ N v)=coeff n (mix _ _ _) at hx; rw [show N=Gazebo.pulse b.val from ?_ ] at hx; rw [ ← ray_force v b ]; exact hx
 have ht(i j:V): Ω ( L i j )=PertExtension.Physical.diag (V) i j:= congr_fun₂ ( h.at_zeroW.trans Carryon.diag_one ) i j
 funext i j; unfold N; rw [ht]
-- core determination across all n.Use D.inspect.
theorem forces {D:Stock F}(hD:Official D) {f: Datum ( RG10.Position.Deck F d )→fps}(hf:Ω ∘ f= Gazebo.raw F d)(hp:EvenCost ζ f) {X:Matrix (RG10.Position.Deck F d) (RG10.Position.Deck F d) fps}(h:Weight X) (hx:EvenCost ζ (mix f X)): tile ζ X=X:=by
 let L:=tile ζ X; have hy:=h.tiled; have hu: EvenCost ζ (mix f L):= hp.tilted tile_layer
 suffices he : ∀ i, stamp L i=stamp X i by ext j k n; exact congr_fun₂ (he n) j k
 intro i; induction i using Nat.strong_induction_on with
 | h i ih=>
    rcases Nat.eq_zero_or_pos i with e|e; · subst i; exact hy.zeroA.trans h.zeroA.symm
    let r:=stamp X i-stamp L i; have hxR : r∈tents F d:= (tents F d).sub_mem (h.later e) (hy.later e)
    let b: tents F d:=⟨r,hxR⟩; have hz: ∀ v,Gazebo.beam v b=0:= by
       let H:= relation hy ih e b rfl hf; apply appears b (show Trim ζ r from Cut.crush ((h.held i).sub (hy.held i)) ?_) ( degree_diff hu hx ) (k:=i)
       · unfold L; intro v; rw [Pi.sub_apply,map_sub, ← H v ]; simp
       unfold r L; rw [ tile_sub,  canvas_tile, layer_fixed (tile_layer),sub_self ]
    let Y:= D d; have hr:r∈Y.Z:= (Carryon.agree hD (d:=d)) ▸ hxR; let z:Y.Z:=⟨r,hr⟩; have ht:= (hD.fresh d).rank.1
    have hm(v): coeff 1 (PertExtension.Position.insert (V) PertExtension.Physical.Profile.n (PowerSeries.C ∘ (Gazebo.raw F d)) (Gazebo.pulse z.val) v)=0:=(ray_force v b).trans (hz v)
    have Hi : Y.inspect ( Gazebo.raw F d ) z=0:= by rw [ TestSystem.lieDeriv, show Y.baseline=PertExtension.Physical.diag (V) from hD.normal d ]; change Y.select (fun v=> coeff 1 (PertExtension.Position.insert (V) PertExtension.Physical.Profile.n _ (Gazebo.pulse z.val) _ ))=_; simp_rw [hm]; exact map_zero _
    have hi:z=0:=ht (Hi.trans (map_zero _).symm)
    exact Eq.symm (sub_eq_zero.mp (congr_arg Subtype.val hi))
end EvenCost
end YM.FVAAlt2.Mass

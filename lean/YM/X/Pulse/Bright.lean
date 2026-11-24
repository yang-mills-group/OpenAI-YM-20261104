import YM.X.Journey.Quiet
import YM.Next.RANK.Inks
/-!
# reality, Unit and Signed spin of unheated stencil α families. independent of ℒ
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Pulse
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open Stems hiding X
open Crate Crate.Fund Hinge Spindle
open scoped Topology ContDiff BigOperators Classical
variable {q:ℕ+}{n:Side}{k d:ℕ}{R:ℝ}{I V T:Type*}{G:Gauge}
section real
lemma cost_retro (p:Curly G)(A:Brush G): snap A (retro (Hair G) p)=star (snap A p):= escorted (Stems.text A) p -- Name
lemma shock_retro (A:Symmetric V) (h:∀i j,star (A.cov i j)=A.cov i j)(p:poly V): Hinge.shock A (retro V p)=star (Hinge.shock A p):= by
    unfold Hinge.shock; rw [blend_components,blend_components, flashed _ h]; let f:= fun _ : V=> (0:ℝ); have hx : (0:V→ℂ)=fun v=>↑(f v):= funext (fun i=> Complex.ofReal_zero.symm);rw [hx]; exact escorted f _
lemma retro_scale (p:poly V)(z:ℂ) : retro V (z • p)=star z • retro V p:= by rw [← C_mul',map_mul, retro,MvPolynomial.map_C, C_mul']; rfl
lemma retro_fire (i:PlaqAxes): retro (Hair G) (vertex i)=vertex i:= by apply snap_ext; intro A;rw [cost_retro];unfold vertex; simp only [mark_test,Complex.star_def, Complex.conj_ofReal]
lemma retro_hair (x:Site n)(p:Curly G): retro (Jam n G) (hairAt x p)=hairAt x (retro (Hair G) p):= MvPolynomial.map_rename ..
lemma retro_book (W:Word G)(i:ℕ): retro (Hair G) (bookMark W i)=bookMark W i:= by unfold bookMark ; rw [map_sum]; apply Finset.sum_congr rfl; intro i _ ; rw [retro_scale,Complex.star_def, Complex.conj_ofReal]; congr 1; apply snap_ext; intro A; rw [cost_retro]; unfold hut; simp [mark_test]
end real
section unit
variable {F:Labels.Frames G}(S:Bare.Shop F)
lemma unit_stamp (W:Word G)(he: W.axis=0): bookMark W k=if k=0 then 1 else 0:= by
    unfold bookMark; rw [he,topBasis_unit, Finset.sum_eq_single_of_mem 0 (Finset.mem_univ _), Pi.single_eq_same, Complex.ofReal_one,one_smul]; swap; · intro q _ h; rw [Pi.single_eq_of_ne h,Complex.ofReal_zero,zero_smul]
    have ht: (along (evalS W.S 0) : Brush G→ℝ→ℝ)= fun _ _=>1:= by funext A r; change (W.S.evaluate W.F.e0 _).re=_; rw [W.sound.unit];rfl
    apply snap_ext; intro A; rw [hut,mark_test,ht,number', W.F.zero_degree]; simp only [Nat.zero_add]; by_cases h:k=0; · subst k; simp [Jet.someJ]
    rw [if_neg h]; simp [Jet.someJ, iteratedDeriv_const (n:=k),h]
lemma base_un : Bare.base F (0:(F.level d).Index)=0:= by
    have he:= Bare.base_grade F (0:(F.level d).Index); by_contra hz; have ht:= (F.level _).factors_pos _ hz; unfold Bare.grade at he; rw [he,(F.level d).zero_degree] at ht;exact Nat.lt_irrefl _ ht
lemma billet_unit (W:Word G)(hz:W.axis=0)(v:Floor R): Gravity.billet (q:=q) S W v k=0:= by
    let T:=flow G (side q k); have hr : ∀ i, multi T 1 i=0:= by
       intro i; unfold multi; rw [pone,one_mul,sub_self]; have he : hit T 1=0:= by ext; rw [hit_point,Derivation.map_one_eq_zero]; rfl
       rw [he]; simp -- usually zero mem neg
    apply Bare.core_in S; rw [sold,exposed,warp,crisp,unit_stamp W hz,unit_stamp W hz,if_neg (by decide : ¬ (1:ℕ)=0),if_pos rfl,Normal.pure,map_zero,hr,sub_self,map_zero,map_zero,map_zero] -- reduceIf
lemma engine_unit (v:Floor R): Gravity.billet (q:=q) S (Bare.useWord S (0:(F.level d).Index)) v k=0:= by refine billet_unit S _ ?_ v; change Bare.base F _=0; apply base_un
end unit
end YM.PositionX.Pulse

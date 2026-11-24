import YM.WilsonCoeffUV.Root.Post.Stakes
/-! # Matching gear with flight. post costs, pre specified before L.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V E:Type*}{r h D l j e k a m:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t t' A X B C δ:ℝ}{I:Bulb G}
-- a rolling demand. l=current, j=future
structure Cloister (G:Gauge)(h:ℕ) where
   lamp : Bulb G
   j:ℕ
   l:ℕ
   inlet : 4≤l
   post: 4≤j
   horizon : h≤j

abbrev inkPin (I:Cloister G h):=I.lamp.path
abbrev xota (I:Cloister G h):= (inkPin I).kernel.penalty

structure Courant (I:Cloister G h)(R:Stand (inkPin I)) where
    g: Flight I.j I.l
    shape: (inkPin I).patch.L=g.L
    line: Carrier.Lines (inkPin I).patch.L
    same: HEq line (linesOf g (xota I))
    Qmat: R.M=Agate (inkPin I).patch line G
    price: Crank R.M (h+1) I.lamp.s I.lamp.preD

-- cost pre independent of shape and paths, called at source only
def tempS (H:Hol G)(F:Frame G h)(r)(p:h<D)(t s C:ℝ)(ht:0<t)(hs:0<s) := (hall_pay F H r p C hs ht).choose
namespace Bulb
abbrev anger (B:Bulb G):= B.positive.trans B.vio
def dues (I:Bulb G)(r:ℕ): Prop:= (r:ℝ)*(I.s/I.path.patch.L.val)≤ I.input/2
def velo (H:Hol G)(F:Labels.Frame G h)(p:h<D)(I:Bulb G)(r):= tempS H F r p I.input I.s I.preD I.inlet I.anger
lemma velo_nn (H:Hol G)(F:Labels.Frame G h)(p:h<D)(I:Bulb G)(r):0≤ velo H F p I r:=(hall_pay F H r p I.preD I.anger I.inlet).choose_spec.1
-- denominator L scaling in crossing
end Bulb
open Bulb
variable {T:Cloister G h}
lemma tower_gain (F: Frame G h)(H:Hol G)(I:Cloister G h)(h0:h<D)(k r:ℕ): ∃ E:ℝ,0≤ E∧∀ (P:Stand (inkPin I))(_L:Courant I P)(Y:Single G D) (A X:ℝ), I.lamp.dues r→0≤A → Stakes Y →(∀ i<k,∀ j,Twig 0 I.lamp.input A (Y i j))→ (∀ i,valence F i=r → ‖glean F Y k i‖≤ A) → dragCup Bank.terrain I.lamp.s I.lamp.path.D P.Q → Twig 0 I.lamp.input X (Y k r) →
   let B:= I.lamp; let t:= hall B.path.patch h P.Q (Y k r)
   Twig 0 B.exitS ((velo H F h0 B r)/(B.path.patch.L.val:ℝ)*X + E*A) t ∧ Hears F h (E*A) t:= by
    let B:= I.lamp; let s:=B.exitS; let t:= B.input; let d:=B.s; have hd:0<d:= B.anger; let P:=B.path.patch; let C:=B.preD; let Y:= B.path.D; let L:ℝ:=P.L.val; have hY:0≤ Y:= zero_le_one.trans (inkPin I).bill_nn; have hh:0<L:=by unfold L; positivity
    let c:= max (C/L) Y; have hc':Y≤ c:= le_max_right ..; have hc:0≤ c:= hY.trans hc'
    obtain ⟨A,ha,H'⟩:= lower_lease F r D k t B.inlet
    obtain ⟨q,hq,hq'⟩:= paid_echo F s B.positive r D
    let u:= xota I; have he:0<u:= (inkPin I).kernel.penalty_pos
    choose T hT ht using fun i:Alma F=> hall_dear (k:=0) r H F h0 (Nat.zero_le h) u he I.post I.inlet I.horizon (notar F i) (weigh_cap F i) t B.inlet
    let v:=∑ i,T i; have hv:0 ≤ v:= Finset.sum_nonneg fun _ _=>hT _
    let b:=velo H F h0 B r; have hb :0≤ b:= velo_nn ..
    let U:=blur G P d s c r; have hU : 0≤U:= blur_nn G P d s c B.vio hc _
    let E:=(U + b)+q*U+v
    have hE: U + b ≤ E:= (le_add_of_nonneg_right (mul_nonneg hq hU)).trans (le_add_of_nonneg_right hv)
    have hV: q*U+v≤E:=by unfold E; linarith
    refine ⟨L^h * E * A,mul_nonneg (mul_nonneg (by positivity) ((add_nonneg hU hb).trans hE)) ha, ?_⟩
    intro R Q P' A' X stepsOk ha' T rt Ht hU' ht0 B0 X'
    let N:= P' k r; let V:= Q.line; let a:= A*A'; have hA':0≤ a:=by unfold a; positivity
    obtain ⟨hH,S⟩:= H' P' T A' ha' rt Ht
    let J:=hall P h R.M N
    have heq:=hall_cross P R.Q R.M N h (T.pur k r) ht0 S R.T R.rule (dragCup.le (dragCup.mono R.rolls (B.outlet.trans B.path.holds.le)) hc') (hU'.le hc') (Q.price.polish.le (le_max_left ..)) B.ports B.positive.le B.vio
    change Cork Bank.terrain 0 s (L^h * (U*a)) (X'-J) at heq
    have hy : Twig 0 d (b/L*X + L^h*b*a) J:= (hall_pay F H r h0 C B.anger B.inlet).choose_spec.2 P R.M N X a Q.price stepsOk (T.pur k r) (T.m k r) ht0 S hH
    have hy : Cork Bank.terrain 0 s _ J:= Cork.mono hy B.vio.le
    have hz:= heq.add hy; rw [sub_add_cancel] at hz
    constructor
    · apply hz.cost; rw [show L^h*(U*a)+_= b/L*X+L^h*(U+b)*A*A' from by unfold a; ring]; exact add_le_add_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by positivity)) ha) ha') _
    refine ⟨mul_nonneg (by exact mul_nonneg (mul_nonneg (by positivity) ((add_nonneg hU hb).trans hE)) ha) ha',fun i _ hj=>?_⟩
    have ht' : ‖echoS F J i‖ ≤ L^h * v * a:=by
       have hp: R.M= Agate P V G:= Q.Qmat
       let u i:=ht i Q.g P Q.shape Q.line Q.same N X d (C/L) a ht0 hd (hp ▸ Q.price.polish) B.ports (T.pur k r) (T.m k r) S (fun v=>by omega) (fun i hi=>by omega) hH J (by unfold J; rw [hp]) (hall_grace P R.M N h (T.pur k r))
       have hv := le_trans (Complex.abs_re_le_norm (trellis F J i)) (norm_le_pi_norm (Bell F (weave F i) (valence F i) (arret (brow F i D) J h (valence F i))) (sheet F i)); refine hv.trans ?_
       rw [hj]
       apply (u i).trans; simp only [Nat.sub_zero]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _=> hT j) (Finset.mem_univ i)) (by positivity)) hA'
    have hh:= hq' i (X'-J) _ heq
    change ‖echoS F X' i‖≤ _
    rw [show echoS F X' i= echoS F (X'-J) i+echoS F J i from (by rw [echo_minus F i hz hy B.positive B.positive, sub_add_cancel])]; apply (norm_add_le ..).trans; apply (add_le_add hh ht').trans; exact le_trans (le_of_eq (show q*(L^h*(U*a))+L^h*v*a=L^h*(q*U+v)*A*A' by unfold a; ring)) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV (by positivity)) ha) ha')
end YM.WilsonCoeffUV.Cosmos

import YM.MS.ScaleForest.DeliveryLine
/-!
# Actually reading the Laurent geometry at two placements, through Test

Uniform IR, UV Laurent prescription on arbitrary geometry given by the
configuration window. Here restrict to a fixed inter-anchor gap. Also OK
on every compact subset of binary Points. Don't get values on the
position diagonal. Use
four open physical axes for the test distances as everywhere else.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle Snap XSpace XSpace.Chiral Cylinder Planted Beamline Quadratic
open scoped Topology ContDiff
variable {G : Gauge} {I J: Type} (μ : ℝ)

def alongMap (q:J→I)(F:Curtain G I): Curtain G J:= fun z t=> F z t ∘ q
variable {μ} (q:J→I) {b c:Bool} (F:Curtain G I)
lemma verticalFrames : vertical (alongMap q F)=alongMap q (vertical F):= rfl
lemma along_plus (L:Curtain G I) : alongMap q (F+L)=alongMap q F+ alongMap q L:= rfl
lemma alongLeaf (X:Flats G)(w:ℕ) : asLeaf (I:=J) X μ w=alongMap q (asLeaf X μ w):= by
    have h(z:ℂ)(s:ℝ)(j:J): startPaid (I:=J) μ w X z s j=startPaid (I:=I) μ w X z s (q j):= by simp only [startPaid,slicePage,Finset.sum_apply]
    funext z t j; unfold alongMap asLeaf populated; split <;> rename_i he; · exact congr_arg (fun F=>ruby F 0) (funext fun z=>h z t j)
    exact h ..

namespace Planted
-- commuting the read through the parameter-index convention

def curve (q:J→I) : {b:Bool} → Planted G I b → Planted G J b
 | _,bed F=>bed F
 | _,U K F=>U K (curve q F)
 | _,B K H F=> B K H (curve q F)
 | _,P K A X Y=> P K (A ∘ q) (curve q X) (curve q Y)

variable (μ)
lemma forAuth (F:Planted G I b) : resolve μ (curve q F)=alongMap q (resolve μ F) := by
    induction F with
    | bed X=> exact alongLeaf ..
    | U K X ih=> rw [curve,resolve,ih,resolve]; rfl
    | B K H F ih=> rw [curve,resolve,ih,alongLeaf q,resolve]; rfl
    | P K A X Y ih it=> rw [curve,resolve,ih,it,resolve]; rfl
lemma map_nominal (L:Plan G I b) : nominal μ (L.map (curve q))=alongMap q (nominal μ L):= by
   induction L with| nil=>rfl| cons l L ih=> unfold nominal; rw [List.map_cons,List.map_cons,List.map_cons,List.sum_cons,List.sum_cons,forAuth,along_plus]; exact congr_arg (_ + ·) ih
variable {μ}
lemma windowMap (m:ℕ)(z:ℂ) : WindowIR (alongMap q F) m z=WindowIR F m z ∘ q := rfl

variable [TopologicalSpace I][FirstCountableTopology I]
lemma nominal_sway {L:Plan G I b}(ht:Hired L):∃ R,Enough R∧ Sway (ScaleForest.probe (nominal μ L) R):= by
   induction L with
   | nil=> exact ⟨ _, Enough.simple,fun _ _=>continuous_const⟩
   | cons i L ih=>
       obtain ⟨R,hR,hX⟩:= observer μ i (ht i (by simp)); obtain ⟨r,hr,hL⟩:= ih (fun i h=> ht i (List.mem_cons_of_mem _ h)); let V:= min R r; let f : Atlas I V → Atlas I r:= fun x=> (⟨ x.1.val, Metric.ball_subset_ball (min_le_right ..) x.1.property⟩,x.2);
       exact ⟨ _, hR.pair hr,Sway_plus ((hX.shrink (min_le_left R r)).sway) (repaint hL f (by unfold f; fun_prop))⟩
end Planted

namespace Placement
open Planted Triangle
local notation "C"=> Points 2
variable (W:GraphSum G true 4) (X Y:Pupil)
lemma curves (A:I→QP) : triangle X Y (A ∘ q) W=(triangle X Y A W).map (curve q):= by unfold triangle streets nearX nearY nearB mid; simp only [List.map_cons, List.map_nil,curve]
abbrev Uat (A:Points 2) := Theater.out (A 1 - A 0) -- larger index first, NOT Tri.unit order

variable (μ)

def foundry (μ:ℝ) (z:ℂ)(t:ℝ)(x:C):= nominal μ (triangle X Y (I:=Unit) (fun _=> Uat x) W) z t () 0 []
def completed (μ:ℝ)(z:ℂ)(x:C) := WindowIR (nominal μ (triangle X Y (I:=Unit) (fun _=> Uat x) W)) 0 z ()
-- Along-map identity, to focus on any compact separated placements
lemma center (x:C) (A:I→QP)(i:I)(he:Uat x=A i)(z:ℂ)(s:ℝ) : foundry W X Y μ z s x= nominal μ (triangle X Y A W) z s i 0 [] := by
    let f (_:Unit):= i; change _= _; unfold foundry; rw [he, show (fun _:Unit=> A i)=A ∘ f from rfl, curves f W, map_nominal ]; rfl
lemma completedX (x:C) (A:I→QP)(i:I)(he:Uat x=A i)(z:ℂ) : completed W X Y μ z x= WindowIR (nominal μ (triangle X Y A W)) 0 z i:= by unfold completed WindowIR; apply congr_arg ( limUnder atTop ); funext t; exact center μ W X Y _ _ _ he z t
lemma contUat : Continuous Uat:= by let X := Theater.out.toContinuousLinearEquiv; apply X.continuous.comp ( show Continuous ( fun x:Points 2=> x 1 - x 0) by fun_prop )
lemma test_conf {x:C} : x∈conf 2 ↔ x 1 ≠ x 0:= by
   constructor; · exact fun (h:Injective x.ofLp)=> h.ne (by decide)
   intro h i j he; fin_cases i <;> fin_cases j <;> first| rfl| exact (h he).elim| exact (h he.symm).elim
lemma test_gap {x:C} : x∈conf 2 ↔ Uat x ≠ 0:= by unfold Uat; rw [test_conf,map_ne_zero_iff ..,sub_ne_zero]; exact Theater.out.injective

variable {K:Set C}
lemma portable (hK:IsCompact K)(hp:K⊆ conf 2): AdmittedGap (K.restrict Uat) := by
    constructor
    · exact contUat.comp continuous_subtype_val
    all_goals rcases Set.eq_empty_or_nonempty K with rfl|he
    · exact ⟨ _,(zero_lt_one : 0<(1:ℝ)),fun i=> i.property.elim⟩
    · obtain ⟨i,hi,H⟩:= hK.exists_isMaxOn he contUat.norm.continuousOn; refine ⟨ _, norm_pos_iff.mpr (test_gap.mp (hp hi)),fun v=> H v.property⟩
    · exact ⟨ _,(zero_lt_one : 0<(1:ℝ)),fun i=> i.property.elim⟩
    obtain ⟨i,hi,H⟩:= hK.exists_isMinOn he contUat.norm.continuousOn; exact ⟨ _, norm_pos_iff.mpr (test_gap.mp (hp hi)),fun v=> H v.property⟩

lemma royal_eq {K:Set C}(x:K) (z:ℂ)(t:ℝ) : foundry W X Y μ z t x= nominal μ (triangle X Y (K.restrict Uat) W) z t x 0 [] := center μ W X Y x _ x rfl z t
lemma complete_eq {K:Set C}(x:K)(z:ℂ) : completed W X Y μ z x= WindowIR (nominal μ (triangle X Y (K.restrict Uat) W)) 0 z x:= completedX μ W X Y x _ x rfl z

lemma city (hK:IsCompact K)(hp:K⊆ conf 2)(a:ℝ)(ha:0<a)(he:a<1) : ∃R,Enough R ∧ (∀ s, Continuous (fun (i:↥(disc R) × K)=> foundry W X Y μ i.1 s i.2 )) ∧ Continuous (fun (i:↥(disc R) × K)=> completed W X Y μ i.1 i.2 ) ∧ ∃ C':ℝ,0<C'∧∀ z∈disc R,∀ x∈K, ∀ t:ℝ,0≤t→ ‖foundry W X Y μ z t x-completed W X Y μ z x‖ ≤ C'*exp (-a*t) := by
    let V:= triangle X Y (K.restrict Uat) W; have hv: Hired V:= hiredFamily X Y (K.restrict Uat) W (portable hK hp)
    obtain ⟨R,hR,hT⟩:= (abide μ V hv).2.1 a ha he; obtain ⟨r,hr,hℓ⟩:= nominal_sway (μ:=μ) hv; obtain ⟨_,h,hP,hV⟩:= Frontier.enter (hT.shrink (min_le_left R r)) ha 0;
    obtain ⟨T,hC,hU⟩:= hP; refine ⟨ _, hR.pair hr, fun s=>?_, (by simp_rw [complete_eq μ W X Y ]; exact h), T,hC, fun z hz i hi t ht=>?_ ⟩;
    · simp_rw [royal_eq μ W X Y ]; let f(i:disc (min R r) × ↥K):Atlas ↥K r:= ((⟨ (i.1:ℂ),Metric.ball_subset_ball (min_le_right R r) i.1.property⟩:disc r),s,i.2); change Continuous ((fun x:Atlas ↥K r=> ScaleForest.probe (nominal μ V) r x 0 []) ∘ f); exact (hℓ 0 []).comp (f:=f) (by unfold f; fun_prop)
    rw [show foundry W X Y μ z t i=_ from royal_eq μ W X Y (⟨i,hi⟩:↥K) z t, show completed W X Y μ z i=_ from complete_eq μ W X Y (⟨i,hi⟩:↥K) z ]; exact hU z hz _ t ht

lemma cityX (s:ℝ) : ContinuousOn (completed W X Y μ 0) (conf 2) ∧ ContinuousOn (foundry W X Y μ 0 s) (conf 2) := by
   have ht (x:C) (hx:x∈conf 2) : ContinuousAt (completed W X Y μ 0) x ∧ ContinuousAt (foundry W X Y μ 0 s) x:= by
      obtain ⟨r,hr,hR⟩:= Metric.mem_nhds_iff.mp ( (conf_open 2).mem_nhds hx ); let V:= Metric.closedBall x (r/2); obtain ⟨R,hR',H,hT,hV⟩:= city μ W X Y (K:=V) (isCompact_closedBall ..) (Subset.trans (Metric.closedBall_subset_ball (half_lt_self hr)) hR) (1/2) (by norm_num) (by norm_num)
      let g(i:↥V):= ((⟨ 0,hR'.top⟩:disc R),i); have hg : Continuous g:= by unfold g; fun_prop
      have hv:= Metric.closedBall_mem_nhds x (half_pos hr)
      have he(f:C→ℂ)(h:Continuous (V.restrict f)):ContinuousAt f x:= (((continuousOn_iff_continuous_restrict).mpr h) x (mem_of_mem_nhds hv)).continuousAt hv
      have hℓ:Continuous ((fun p:disc R × ↥V=> completed W X Y μ p.1 p.2) ∘ g):= hT.comp hg
      refine ⟨ he (completed W X Y μ 0) hℓ, he _ ?_ ⟩; change Continuous ( (fun p:disc R × ↥V=> foundry W X Y μ p.1 s p.2) ∘ g); exact (H s).comp hg
   exact ⟨ fun i hi=> (ht i hi).1.continuousWithinAt, fun i hi=> (ht i hi).2.continuousWithinAt⟩
lemma bloom (x:C)(h:x∈conf 2) : Tendsto (fun t=>foundry W X Y μ 0 t x) atTop (𝓝 (completed W X Y μ 0 x)) := by
    let A:= fun _:Unit=> Uat x; apply limit_s μ X Y A ?_ G W (); have ht: 0<‖Uat x‖:= norm_pos_iff.mpr (test_gap.mp h); exact ⟨continuous_const,⟨ _,ht,fun _=> le_rfl⟩,⟨_,ht,fun _=>le_rfl⟩ ⟩
end Placement
end YM.MS.ScaleForest

import YM.MS.Tide.Lion
/-!
# Rank.Moment cost.Some tools for Diagonal change supporting actual use.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tide
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Rake Rake.Geo Vista Vane Port
open Puff Engine SplitP Actors Dynamics Puff.Mom
open Fleet Swirl Swirl.Near SpaceOut
open scoped Topology ContDiff Interval
variable {U I J W:Type}{P:Geo I}{l:Filter I}{V:Visa I}{L:I→Side}[LinearOrder W]
  {x:ℝ}{s:Finset W}{n:ℕ}{f g:I→ℂ}{φ γ:I→ J→ℂ}{F Z:Terrify W I}{X H U':I→ J→T ℂ}
namespace PeakT
lemma peakS (s:Finset J)(hp:∀ i∈s,PeakT l P x (fun t=>φ t i)): PeakT l P x (fun t=>∑ i∈s,φ t i):= by classical induction s using Finset.induction_on with| empty=>simp_rw [Finset.sum_empty]; exact PeakT.zero| insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact ( hp i (by simp) ).plus ( ih fun j hj=> hp j ( Finset.mem_insert_of_mem hj ))
-- comparison.Downgrade.Story.
def twin (l:Filter I)(P:Geo I)(x:ℝ)(f g:I→ℂ): Prop:= PeakT l P 0 g∧ PeakT l P x ( f-g )
lemma retain (hp:twin l P x f g)(hv:0≤x): PeakT l P 0 f:= ( sub_add_cancel f g ) ▸ ( (downs hv hp.2).plus hp.1 ) -- cast
lemma twin0 : twin l P x 0 0:= ⟨PeakT.zero,(by rw [sub_self]; exact PeakT.zero)⟩ -- orientation
lemma joinTwin (s:Finset J)(he:∀ i∈s,twin l P x (fun k=>φ k i) (fun k=> γ k i)): twin l P x (fun t=>∑ i∈s,φ t i) (fun t=>∑ i∈s,γ t i):= by
    refine ⟨ peakS s (fun i hi=> ( he i hi ).1),?_⟩; suffices H: PeakT l P x (fun t=>∑ i∈s,(φ t i-γ t i)) by change PeakT _ _ _ (fun t=> (∑ i ∈ s,φ t i) - ∑ i∈s,γ t i); simpa only [Finset.sum_sub_distrib] using H
    exact peakS s fun i hi=> ( he i hi ).2 -- let t.Binder error `suffices ... ;`.
lemma productT {F H:I→ℂ}(h:twin l P x f g) (hx:twin l P x F H)(he:0≤x): twin l P x ( f*F ) ( g*H ):= by
    refine ⟨ ?_,?_⟩; · simpa only [add_zero] using (h.1.mul hx.1)
    rw [show f*F-g*H=f*(F-H)+( f-g )*H from (by ring)]; apply PeakT.plus
    · simpa only [zero_add] using ((retain h he).mul hx.2)
    simpa only [add_zero] using (h.2.mul hx.1)
lemma always (c:ℂ): twin l P x (fun _=>c) (fun _=>c):= by
   refine ⟨ ⟨ max 1 ‖c‖,lt_max_of_lt_left zero_lt_one, ?_⟩,?_⟩; · exact Eventually.of_forall fun i=> by simp [lake]
   rw [sub_self]; exact PeakT.zero
-- lift on T/E convolution both.
local infix:70 " ⋆ "=> Actors.core Trunk
abbrev SeriesP (l:Filter I)(P:Geo I)(x:ℝ)(X H:I→ J→ T ℂ): Prop:= ∀ a n,twin l P x (fun i=> X i a n) (fun i=> H i a n)
lemma multiply (S:SplitP J){F:I→ J→ T ℂ} (hv: 0≤x)(hp:SeriesP l P x X H)(he:SeriesP l P x U' F): SeriesP l P x (fun i=> S.Lift (Trunk.core) ( X i ) (U' i)) (fun i=>S.Lift Trunk.core ( H i ) ( F i )):= by
    intro a n; simp_rw [ S.loan,Finset.sum_apply ]; exact joinTwin _ fun i _=> joinTwin (antidiagonal n) (fun k _=> productT ( hp i.1 k.1 ) (he i.2 k.2) hv)
lemma path (S:SplitP J)(hv:0≤x)(hp:SeriesP l P x X H)(n:ℕ): let Z:= Trunk.stack S; SeriesP l P x (fun i=> Z.power ( X i ) n) (fun i=> Z.power ( H i ) n):= by induction n with| zero=> intro Y i k; exact always _| succ k ih=> exact multiply S hv hp ih
lemma powT (S:SplitP J)(hv:0≤x)(hp:SeriesP l P x X H)(u:J)(n:ℕ): twin l P x (fun i=> Cheer Trunk S ( X i ) u n) (fun i=>Cheer Trunk S ( H i ) u n):= by
    unfold Cheer cheers; simp_rw [Finset.sum_apply]; exact joinTwin _ fun i hi=> productT ( always (Actors.phase i)) ( path S hv hp i u n) hv
abbrev ordZ (F:Terrify W I): Terrify W I:= fun s n i=>bury i s F n
lemma projection (hp:∀ s n, PeakT l P mildG ( F s n-Z s n )∧ PeakT l P 0 (Z s n))(s:Finset W)(n:ℕ): twin l P mildG (ordZ F s n) (ordZ Z s n):= by
    let Q(t:I)(a:Terrify W I):= fun i n=> a i n t; apply powT ( S:=marked W ) ( H:=fun t=> Q t Z ) mild_p.le ( X:=fun t=> Q t F ) _; exact fun i n=>(hp i n).symm -- `apply` missing placeholders
-- ∑ scaling.Ψ
variable (w:W→ℕ)
--abbrev Trade (S:Finset W)(s: SplitP J)(i:I):= s -- remove
lemma norm_add (r t:Finset W)(u:Finset W)(h:( r,t )∈ ( marked W ).pieces u)(i:I): higher P (Vane.charge w u) i=higher P (Vane.charge w r) i * higher P (Vane.charge w t) i:= by
    obtain ⟨ha,hb⟩:= SplitP.joins.mp h; unfold higher Vane.charge; rw [T_add, ← ha,Finset.sum_union hb, Nat.cast_add]
def Tarν (w:W→ℕ)(P: Geo I)(i:I): Linear ( Finset W→ T ℂ ) ( Finset W→ T ℂ ):={
    toFun v u:= higher P (Vane.charge w u) i • v u
    map_add' _ _:= funext fun _=> smul_add ..
    map_smul' x _:= funext fun _=> smul_comm _ x _ }
local notation "T'"=> Tarν w P
lemma ν_norm (i:I)(U:Terrify W I): ordZ ( fare w P U ) s n i= fare w P (ordZ U) s n i:= by
    let V:= (Trunk.stack ( marked W )); have H : Tether ( T' i ) V V:= by
       refine ⟨ funext fun p=>?_,fun x y=>funext fun u=>?_⟩
       · change higher P (Vane.charge w p) i • ( marked W ).refineV Trunk.unit p =( marked W ).refineV Trunk.unit p; unfold refineV; split
         next h=> rw [ h ]; simp [higher,Vane.charge,Port.τ, marked]
         next _ => exact smul_zero _
       change higher P _ i • (( marked W ).Lift Trunk.core x y u)=( marked W ).Lift Trunk.core _ _ u; simp_rw [loan,Finset.smul_sum]; refine Finset.sum_congr rfl fun j hj=>?_ ; change _=( higher P _ i • x _ ) ⋆ ( higher P _ i • y _ ); rw [ norm_add w _ _ u hj i,map_smul,map_smul, LinearMap.smul_apply, mul_smul, smul_comm ] -- smul orientation
    let F(s:Finset W)(n:ℕ):= U s n i; change V.cheers ( T' i F ) s.card s n=higher P _ i * V.cheers F s.card s n; rw [← H.cheersV]; rfl
end PeakT
end YM.MS.Tide

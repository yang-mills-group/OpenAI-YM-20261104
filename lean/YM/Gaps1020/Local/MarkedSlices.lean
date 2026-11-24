import YM.Gaps1020.Local.MarkedRecognition
import YM.Gaps1020.Local.Leaf
import YM.MergeProof.TeamFlow
/-!
# Exponent Taylor orders under the shared conditional integral

Reassembly of the exp-power moments holds as an identity of germs on
`Healthy`. Off masked domain our choice will define the residual by exact
subtraction, so need no integrability claims about the extensions there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open March Next.Foundations YM.GapsLocal.ExpShares
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k M : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g ρ ℓ : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {z : Air f G} {V:E→ Config G c}{x:E}

variable {H : Cash W s μ L Q o C T R}

open PhysicalNext.Repeat.Lotus

open YM.RG01.Survive
-- extension at the actual Cash taking many marks. Clusters still carry
-- exact requirement: if even one support sees a flag, mask occurs at p.
-- All marked models are ZERO without p alive and all signs present.
-- classify dormant by purely label criterion (not fieldwise).
variable (H)
def awake (p:H.ThinP)(U:Team R):Prop:=Ac.Spark H.supportP p.val ∧ troupe T R Q.halo (radiusB s) p.val ∧ U.signs S⊆p.val
def writtenBy (χ:Chi)(p:H.ThinP)(U:Team R)(w:MulData (others U p.val)) (V:Config G c) := if awake H p U then
     Pond.likely fun i:Greenbelt.Reserve S=>teamWeightFringe (prism T s χ o.K V (Greenbelt.allot i)) p.val R U w Q.table W o.a Q.halo
    else 0
def preserved (χ:Chi)(p:H.ThinP)(U:Team R)(V:Config G c):=writtenBy H χ p U (emptyTeamData U p.val) V
def narrowMix (M:ℕ)(p:H.ThinP)(U:Team R) := (blaze p.val=∅ ∧ Cash.numP p.val=0 ∧ H.shapeW p.val < till s ∧ (others U p.val).card ≤ M)
def shortMix (χ:Chi)(M:ℕ)(p:H.ThinP)(U:Team R)(k:ℕ)(V:Config G c):= if narrowMix H M p U then
    ∑ π ∈ (univ : Finset (Assign (others U p.val) M)).filter (fun π=> Thermal1020.degree _ π=k), writtenBy H χ p U (assignment (others U p.val) π) V
    else 0
def sliceMix (χ:Chi)(M:ℕ)(p:H.ThinP)(U:Team R)(k:Orders M)(V:Config G c):= if k.val=M+1 then preserved H χ p U V-∑ i∈ range (M+1), shortMix H χ M p U i V else shortMix H χ M p U k.val V
variable {H} (p:H.ThinP) (U:Team R)
lemma sleepy (h:¬ awake H p U)(V:Config G c)(j:Orders M): sliceMix H χ M p U j V=0:=by
  have ht(i):shortMix H χ M p U i V=0:= by
    unfold shortMix; split; next ha=> unfold writtenBy; simp [h]
    next=> rfl
  unfold sliceMix; split; next ha=> unfold preserved writtenBy; simp only [if_neg h,ht,sum_const_zero,sub_zero]
  next=> exact ht _
lemma script (w:MulData (others U p.val))(hw:∀ i,Measurable (w i)) : Measurable (writtenBy H χ p U w) ∧ LocalOn (H.smallAt p) (writtenBy H χ p U w) ∧ GaugeInvariant (writtenBy H χ p U w) := by
  unfold writtenBy; split
  next h=>
    let X i := prism T s χ o.K 1 (Greenbelt.allot (S:=S) i); let f i V:= teamWeightFringe (vary (X i) V) p.val R U w Q.table W o.a Q.halo
    have he i:= teamWeightSeam (H:=H) (X:=X i) p.val U w rfl rfl hw
    change Measurable (fun V=> likely (fun i=> f i V)) ∧ LocalOn (H.smallAt p) (fun V=>likely (fun i=> f i V)) ∧ GaugeInvariant (fun V=> likely (fun i=> f i V))
    exact ⟨measurable_const.mul (Finset.measurable_fun_sum _ fun i _=> (he i).1),fun U V h=>congr_arg likely (funext fun i=> (he i).2 U V h), fun z V=>congr_arg likely (funext fun i=> teamWeightFrieze (X i) W o.a p.val _ _ w Q.table Q.halo z V)⟩
  exact ⟨measurable_const,fun _ _ _=>rfl,fun _ _=>rfl⟩
lemma short_global (k:ℕ): Measurable (shortMix H χ M p U k) ∧ LocalOn (H.smallAt p) (shortMix H χ M p U k) ∧ GaugeInvariant (shortMix H χ M p U k):=by
  unfold shortMix; split
  · exact ⟨Finset.measurable_fun_sum _ fun i _=> (script p U _ (fun _=> (share_contDiff 0 ..).continuous.measurable)).1, fun V W h=> sum_congr rfl fun i _=> (script p U (assignment _ i) (fun _=> (share_contDiff 0 ..).continuous.measurable)).2.1 V W h,fun z V=> sum_congr rfl fun i _=> (script p U _ (fun _=>(share_contDiff 0 ..).continuous.measurable)).2.2 z V⟩
  exact ⟨measurable_const,fun _ _ _=>rfl,fun _ _=>rfl⟩
lemma globalMix (k:Orders M): GaugeInvariant (sliceMix H χ M p U k) ∧ Measurable (sliceMix H χ M p U k) ∧ LocalOn (H.smallAt p) (sliceMix H χ M p U k) :=by
  unfold sliceMix preserved; split
  next h=>
    obtain ⟨hm,hL,hG⟩:= script (χ:=χ) p U (emptyTeamData U _) fun _=> measurable_const
    refine ⟨fun z W=>congr_arg₂ (·-·) (hG z W) (Finset.sum_congr rfl (fun i _=> (short_global (M:=M) p U i).2.2 z W)), ?_,fun W V h=>congr_arg₂ (·-·) (hL W V h) (Finset.sum_congr rfl (fun i _=> (short_global (M:=M) p U i).2.1 W V h))⟩
    exact hm.sub (Finset.measurable_fun_sum _ fun i _=> (short_global p U i).1)
  next=> exact ⟨(short_global p U _).2.2, (short_global p U _).1,(short_global p U _).2.1⟩
lemma recoversMix (V:Config G c)(M:ℕ): ∑ i:Orders M,sliceMix H χ M p U i V=preserved H χ p U V:=by
  rw [Fin.sum_univ_castSucc]; have h (k: Fin (M+1)): sliceMix H χ M p U k.castSucc V=shortMix H χ M p U k.val V := if_neg k.isLt.ne
  rw [sum_congr rfl fun i _=> h i, Fin.sum_univ_eq_sum_range (fun k=>shortMix H χ M p U k V),sliceMix, Fin.val_last,if_pos rfl]; ring
variable (N: Captain H j C' d v Y A b r B q k χ)
omit N in
lemma teamMasked (X:Coat T F)(hX:X.x=s)(hD:¬awake H p U ∨ ¬ Healthy (Pressure.temp s) (H.smallAt p) X.V):
    U.bloom X W o.a Q.table Q.halo p.val=0:=by
   unfold Team.bloom; split
   next h=>
    have hp: X.B=radiusB s:=congr_arg _ hX; rcases h with ⟨hv,he,hv'⟩; rw [hp] at hv he hv'; rw [p.prop.2,hX] at hv'
    have hy : Healthy (Pressure.temp s) (H.smallAt p) X.V := disjoint_comm.mp (Finset.disjoint_iff_inter_eq_empty.mpr hv')
    have he : ¬U.signs S ⊆ p.val:= fun ht=> hD.elim (fun h=>h ⟨hv,he,ht⟩) (fun h=> h hy)
    unfold Team.steep likely; simp_rw [Team.tithe_off _ _ _ p.val he]; simp
   next=>rfl
include N
lemma paysTeam (V:Config G c): U.lotus T s χ o.K W o.a Q.table Q.halo V p.val=masked (Pressure.temp s) (H.smallAt p) (preserved H χ p U) V:=by
  let X i:=prism T s χ o.K V (Greenbelt.allot (S:=S) i)
  by_cases hu:Healthy (Pressure.temp s) (H.smallAt p) V
  · rw [masked_eq _ _ _ _ hu]; unfold preserved writtenBy; split
    next h=>
      exact congr_arg likely (funext fun i=> teamSame (X:=X i) p.val N.oboe rfl rfl rfl hu N.position.le h.1 h.2.1 p.prop.2 U)
    next h=> unfold Team.lotus Pond.likely; rw [sum_eq_zero (fun i _=> teamMasked p U (X i) rfl (Or.inl h)),mul_zero]
  unfold Team.lotus Pond.likely; rw [masked_ne _ _ _ _ hu,sum_eq_zero (fun i _=>teamMasked p U (X i) rfl (Or.inr hu)),mul_zero]
omit N
lemma remainingCost {p:H.ThinP}{U:Team R}(h:narrowMix H M p U)(hf:awake H p U): HeadsAreLog p.val:=by
   have hQ:Narrow p.val.card (till s) p:=by
     have ht:=hf.2.1
     have hw:p.val.toLeft=∅:= by
       apply Finset.not_nonempty_iff_eq_empty.mp; rintro ⟨b,hb⟩
       have hv:1≤b.shares:=by rw [← Packets.seeds_card]; exact Finset.card_pos.mpr (ht.1.checkpoints b hb).1
       have hp': b.shares ≤ Cash.numP p.val:=single_le_sum (f:= Mixed.shares S) (fun _ _=>Nat.zero_le _) (mem_toLeft.mp hb)
       rw [h.2.1] at hp'; omega
     refine ⟨hf.1,ht,hw,?_,hf.1.1,le_rfl,h.2.2.1⟩
     apply Finset.not_nonempty_iff_eq_empty.mp; rintro ⟨i,hi⟩; obtain ⟨x,hx⟩:= (R.activities.forced i).inventory_ne; obtain ⟨b,hb,-⟩:= ht.2.2 i hi x hx; unfold roster Packets.store at hb; rw [hw] at hb; simp at hb
   exact notWarning_isLog hQ.unmaskedLetters h.1
include N
-- statutorily chosen order proof of actual marked-power interpretation via Recognition:
lemma interpretation (M:ℕ)(V:Config G c)(hv : Healthy (Pressure.temp s) (H.smallAt p) V)(hf:awake H p U) (h:narrowMix H M p U) (π:Assign (others U p.val) M) (he:Thermal1020.degree (others U p.val) π ≤ M) (hX:HasClutch N.conduit A) (hh: charge Q L s r j (till s)≤ρ⁻¹)(hρ:2 ≤ ρ):
    let Z (i:Greenbelt.Reserve S) := prism T s χ o.K V (Greenbelt.allot i)
    let h:=fun (i:Greenbelt.Reserve S)=> Pond.likely fun u:S.Choices=> teamMomentBars ((planted (Z i) p.val).taggedL u) p.val R U π o.a Q.table
    writtenBy H χ p U (assignment _ π) V=Pond.likely h ∧ ∀ i u, MeasureTheory.Integrable
       (teamMoment ((planted (Z i) p.val).taggedL u) p.val R U π o.a Q.table) ((((Greenbelt.allot i).order G).prod ((planted (Z i) p.val).taggedL u).dice)) := by
  intro X' h'
  have T i:= teamPowerSlice (X:=X' i) p.val hX N.oboe (remainingCost h hf) hf.2.1 rfl rfl rfl hv h.2.2.1.le hh hρ N.position.le U π hf.2.2 hf.1 p.prop.2 he
  rw [writtenBy,if_pos hf]; exact ⟨congr_arg likely (funext fun i=>(T i).1),fun i j=> (T i).2 j⟩

end YM.ConnectedActivityE6.Blaze.Thermal1020.Shared

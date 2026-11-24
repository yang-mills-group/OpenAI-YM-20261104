import YM.LocalLTE.Port.Page
import YM.LocalLTE.Port.Costume
import YM.LocalLTE.Sapphire.Rose
/-! # Insertion.T stamps. The represented difference before the step can contain arbitrary
sources which are NOT Z0-priced in any hypothetical polynomial norm. Give separately
Analyst and Forecast.Error; all other weights & masks the same. Boo.δ Mark denominator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus FrameBox Cabana Push
open Progress.DirectedRecipe MergeProof Menu Marker Accent Overlay Fan
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}{c f : Side}{Q : Rep G f} {S:StepData c f} {σ κ Λ μ' w t v : ℝ}
variable {V I J : Type}[DecidableEq V][Fintype V] {R:Marker.Census V}(B A C:Bands R Q)(r:V→ℝ) (hr:∀ i,0<r i) (o:V→Site f)
open Extra.Trajectories Next.Foundations
variable {d U:ℕ} {a b Y η D X E θ ρ:ℝ}
local notation "P"=> Q.p
local notation "ν"=> Q.p.threshold
local notation "W₀"=> Config G f
-- B forecast, A exact, C rem. Weight reserve use independently. Unit allocation forecast gets global price, remits zero. only tiny. T. “Shine”: degree cap.Input complete. Step.Budget
variable (h:B.Active)(hB:B.Radial r a b Y θ)(hp:Shine R B d U κ) (hA:A.Active)(hC:C.Active) (hx:A.Radial r a X Y θ) (hh:C.Radial r 0 η D θ)(hy:Fan.Tabs Q R A B C) -- actual Prop
variable (hm:HasSlots Q.p Q.activities)
include h hB hA hC hx hh hy hp hm
local notation "cQ"=> (codes C)
local notation "TZ"=> (liners B U)
local notation "QT"=> (costumes C)
local notation "ℐ"=> Mosaic B C U
local notation "Vd"=> Q.p
-- For later independence call Prod. Analyst selection from B alone before.C. Stamp.RM heights.Op Ope. Error.Count.All.
omit hA hx

-- any prefix book from empty slots.before forecast. NO need to compose regulator family separately. labels fixed. costs and β from forecast.X.s alone.
def firstSide (I:Type)[Countable I]: I↪ℕ:= (pair (Q':=I) (H:=ℕ)).1
def secondSide (I K:Type)[Countable I][Countable K]:K↪ℕ:= (show K↪ℕ from ⟨Extra.Trajectories.pin,Extra.Trajectories.pin_injective⟩).trans (pair (Q':=I) (H:=ℕ)).2
variable (κ d b U)
structure Aurora (F:liners B U→ Menu.Hat R Q)(Vp:liners B U→ Config G f→ℝ):Prop where
    coins j: (F j).M.turn=.logKey (blankRow f (pedestal B j.1,(firstSide _) j))
    books : PL B.origins F
    tax:∑ i, ActT r (F i) ≤ turnQ Q.p U V b
    tunes: Beaut F d U κ Vp
    waves: ∀ Vp, roll F Vp=∑' i,B.ray i Vp
variable {κ b U d}
omit hy hh hC in
lemma aurora : ∃ F Vp,Aurora κ B r d U b F Vp:=by
    obtain ⟨F,hF,hP,hQ,⟨u,h⟩,hv⟩:= Port.roses B r h hB hp hm (firstSide _)
    exact ⟨F,u,hF,hP,hQ,h,hv⟩
omit hp
set_option maxHeartbeats 400000 in
lemma drafted (F':liners B U→ Menu.Hat R Q)(Vp:liners B U→ Config G f →ℝ) (hL:Aurora κ B r d U b F' Vp) (x:ℝ)(hX:0≤x) : ∃ F:Mosaic B C U →Menu.Hat R Q,(∀ i,originQ R A.origins (F i)) ∧ tags R F ∧ F ∘ Sum.inl=F' ∧ ((∑ i: ℐ, if star B C i then ActT r (F i) else x*ActT r (F i)) ≤ Port.capacity Q.p V b η θ D x U) ∧ (∀ V, Menu.roll F V=∑' i,A.ray i V)∧ ∀ V p,Menu.board F p V=∑' i:{i//barcode Q.activities i=p},∑' j,A.tagged i.val j V:=by
   let e:= secondSide (liners B U) (codes C)
   let F:= F'; change Aurora κ B r d U b F Vp at hL; obtain ⟨hF,h',hE,hG,hL⟩:=hL
   obtain ⟨W,hW,hG,hM,hk⟩:= Port.stow C r hC hh hm e
   obtain ⟨Y,hY,hθ,hr⟩:= Port.cargoK C r hC hh hm
   let M:= Sum.elim F (Sum.elim W Y)
   have ha i:= (hY i).2
   have hZp p V: Menu.board M p V= Menu.board Y p V:=by rw [show board M p V= _ from Port.registered _ F (Sum.elim W Y) V p, Port.registered _ W Y,recordedE _ F h'.segment, recordedE _ W hG.segment]; exact zero_add _|>.trans (zero_add _) -- arg?
   refine ⟨M,fun i=> ?_,?_,rfl,?_,fun V=> ?_,fun V p=>?_⟩
   · rcases i with i|(i|i); exact hy.lit.symm ▸ h'.mark i; exact hy.rig.symm ▸ hG.mark i; exact hy.rig.symm ▸ (hY i).1
   · intro k i j hi hj;
     have hx (i:QT)(p:ℕ) (h:(Y i).M.turn=.logKey p): False:=by obtain ⟨b,hp⟩:= ha i; rw [h] at hp; contradiction
     have hp(i:TZ)(j:cQ)(h:(F i).M.turn=(W j).M.turn): False:= by rw [hF,hW] at h; exact divides i (Extra.Trajectories.pin j) (congr_arg Prod.snd ((blankRow f).injective (Wing.logKey.inj h)))
     rcases i with i|(i|i) <;> rcases j with j|(j|j)
     · rw [h'.ID _ _ _ hi hj]
     · exact (hp i j (hi.trans hj.symm)).elim
     · exact (hx j _ hj).elim
     · exact (hp j i (hj.trans hi.symm)).elim
     · rw [hG.ID _ _ _ hi hj]
     · exact (hx j _ hj).elim
     all_goals exact (hx i _ hi).elim
   · unfold capacity; unfold Mosaic; rw [Fintype.sum_sum_type];
     have hp': (∑ i:TZ, if star B C (.inl i) then ActT r (F i) else x*ActT r (F i))=∑ i:TZ,ActT r (F i):= sum_congr rfl fun i _=> if_pos rfl
     apply add_le_add
     · exact (hp'.trans_le hE)
     have hz (i:cQ⊕QT): (if star B C (U:=U) (.inr i) then ActT r (M (.inr i)) else x*ActT r (M (.inr i)))= _:= (if_neg (show ¬star B C (U:=U) (.inr i) from by simp [star]))
     simp_rw [hz]; rw [← mul_sum]; refine mul_le_mul_of_nonneg_left ?_ hX; rw [Fintype.sum_sum_type]; exact add_le_add hM hθ
   · rw [show Menu.roll M V= _ from Port.grouped _ F (Sum.elim W Y) V, hL,Port.grouped _ W Y, Port.recordedK _ Y ha, hk];
     change (∑' i,B.ray i V)+((∑' i,C.ray i V)+(0:Poly R))=_; rw [add_zero, ← Summable.tsum_add (B.bulkBound h hB V|>.1) (C.bulkBound hC hh V|>.1)]; apply tsum_congr; intro i;
     have he: A.H i=B.H i+C.H i:= by rw [← hy.hess];change A.H i=B.H i+(A.H i-B.H i); abel
     unfold Bands.ray; rw [← hy.index,← hy.bits,← hy.outer, ← hy.reach,he]; by_cases hv:Healthy ν (A.support i) V
     · rw [masked_eq _ _ _ _ hv,masked_eq _ _ _ _ hv,masked_eq _ _ _ _ hv]; ext u; simp only [Poly.part_plus, Poly.part_send, Pi.add_apply]; split <;> ring
     rw [masked_ne _ _ _ _ hv,masked_ne _ _ _ _ hv,masked_ne _ _ _ _ hv];simp
   rw [hZp,hr]; apply tsum_congr; intro i; apply tsum_congr; intro j; unfold Bands.tagged; rw [hy.tags,hy.pilot]
end YM.LocalLTE.Port

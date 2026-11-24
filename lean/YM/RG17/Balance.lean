import YM.RG17.Grade
import YM.OPE.Levy.Measured

/-!
# Ordinary OPE *spatial* error available in the comparison.

Slacks before test norm. Spectators *not* moving inward. True in
all views (bound uniform); exact Reader F. No nested assertions here.
`Located` premise only used if applying it to that measurement frame.
Kept the adjacent-lift correction through each homogeneity class; thus
no loss of negative powers from lower grades hidden by calling inputs
all of degree d.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter Spec Extraction Table OPE OPE.Orbits
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    {F:Final C f S} (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {I J:Type} [Fintype I] [Fintype J] (d:I→ℕ)
set_option quotPrecheck false
local notation "Q"=> F.sector.derivatives
local notation "ρ"=> OPE.run

/-- Generalize evaluated from Levy/Conversion to arbitrary reported fields
with each true grade paid. -/
def GradePrice (v:ℝ→Labels S d) (cost:I→ℝ) : Prop := ∀ i:I,∀ j:ℕ,
    RateLE home ρ (fun r=>P.cutTest j (d i) (v r i)) (-(j:ℝ)+cost i)

variable {d} {v:ℝ→Labels S d} {c:I→ℝ}
include P
set_option maxHeartbeats 600000 in
lemma cardinalityCharged {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E] {φ:Filter ℝ} [φ.NeBot]
    (hl:φ≤home) (H:GradePrice P d v c) (b:ℝ)
    (M:ℝ→∀ e:I→ℕ,MultilinearMap ℂ (fun i=>S.Field (e i)) E)
    (hr:∀ (e:I→ℕ)(he:e≤d),∀ᶠ k in φ,∀ u:Labels S e,
        M k e u=M k d (fun i=>F.sector.derivatives.rise (he i) (u i)))
    (hf:∀ (e:I→ℕ)(_he:e≤d)(u:Labels S e),RateLE φ ρ (fun k=>M k e u) (weight e + b)):
    RateLE φ ρ (fun r=> M r d (v r)) (b+∑ i,c i):=by
     have hA:= ageLarge.mono_left hl
     let J:=fun i=>Fin (d i+1)
     let cost(j:(i:I)→J i):I→ℕ:=fun i=>(j i).val
     let u(k:ℝ)(i:I)(j:J i):= P.cutTest j (d i) (v k i)
     let f(k:ℝ)(i:I)(j:J i): S.Field (d i):= F.sector.derivatives.rise (Nat.le_of_lt_succ j.isLt) (u k i j)
     have ht(k):v k=fun i=>(∑ j:J i,f k i j):=by
       funext i
       have hx:= P.reconstruct (d i) (d i) (le_refl _) (v k i)
       rw [F.sector.derivatives.arrival P.continuum.laws.toSymmetric P.lifts] at hx; exact hx.symm
     have hEq:∀ᶠ k in φ, ∀ j: (i:I)→ J i,
          M k d (fun i=>f k i (j i)) = M k (cost j) (fun i=> u k i (j i)):=by
        exact eventually_all.mpr fun j=>((hr _ (fun i=>Nat.le_of_lt_succ (j i).isLt))).mono
          (fun k he=>(he (fun i=> u k i (j i))).symm)
     apply RateLE.congr (RateLE.sum (f:=fun j k=> M k (cost j) (fun i=>u k i (j i))) (S:=Finset.univ) hA
        (fun j _=> ?_)) (hEq.mono fun k hk=> by rw [ht k,MultilinearMap.map_sum]; exact Finset.sum_congr rfl fun _ _=>(hk _).symm )
     let e:=cost j
     have he(q):=hf e (fun i=>Nat.le_of_lt_succ (j i).isLt) q
     have hw(i):RateLE φ ρ (fun k=> u k i (j i)) (-(e i:ℝ)+c i):=(H i _).shrink hl
     refine (Orbits.contract hA (fun k=> M k e) he (fun k i=> u k i (j i)) (fun i=> -(e i:ℝ)+c i) hw).mono (le_of_eq ?_)
     unfold weight
     rw [Finset.sum_add_distrib,Finset.sum_neg_distrib]
     abel

variable {T η δ:ℝ} (h:Services C f S) (hT:0≤T) (hη:0<η)
variable {e:J→ℕ}(w:Labels S e) (D:ℕ)
include h hT hη
set_option maxHeartbeats 600000 in
lemma formulaOn (p:GradePrice P d v c) {φ:Filter ℝ} [φ.NeBot]
    (hl:φ≤home) (x:ℝ→I→E4) (o:ℝ→E4) (y:ℝ→J→E4) (view:ℝ→Viewers F)
    (he:∀ᶠ r in φ,WithinRoom r T η (x r) (o r))
    (hδ:0<δ)(hv:∀ᶠ r in φ,ClearOf (o r) (y r) δ) :
    RateLE φ ρ (fun r=>formula F P (x r) (o r) (v r) (y r) w D (view r))
      (-(D+1:ℝ)+∑ i,c i) := by
     let M(r:ℝ)(e':I→ℕ):=OPE.Levy.invoice F P (o r) w (view r) D (x r) (y r) (d:=e')
     have hA:= ageLarge.mono_left hl
     obtain ⟨hx,hk⟩:= room_regime (r:=id) (show Tendsto id φ home from hl) hT hη he
     obtain ⟨hy,hp⟩:= free_clear hA hδ hv
     have hEq(r:ℝ)(d':I→ℕ)(u:Labels S d'):formula F P (x r) (o r) u (y r) w D (view r)=M r d' u := (tested_fields ..).symm.trans (Levy.invoice_paid ..)
     refine (cardinalityCharged P hl p _ M ?_ ?_).congr (Eventually.of_forall fun r=> (hEq ..).symm)
     · intro e' he'
       filter_upwards [(clearance_both hA hx hk hp hy (show (0:ℝ)<1 from zero_lt_one) (le_refl 0)).2] with r hr u
       rw [← hEq,← hEq, ← show balance ..=formula F P (x r) (o r) u _ w D _ from tested_fields .., ← show balance .. = formula .. from tested_fields (v:=(fun i=>F.sector.derivatives.rise (he' i) (u i))) ..]
       unfold balance whole
       congr 1
       · let f:=Sum.elim e' e
         let f':=Sum.elim d e
         let a:Labels S f:= stages u w; let a':Labels S f':=stages (fun i=>F.sector.derivatives.rise (he' i) (u i)) w
         have h₁:f≤f':=fun i=>by cases i; apply he'; exact le_rfl
         have ha(i):a' i=F.sector.derivatives.rise (h₁ i) (a i):=by
            cases i with
            | inl => rfl
            | inr i => exact (F.sector.derivatives.arrival P.continuum.laws.toSymmetric P.lifts (a (.inr i))).symm
         exact (Levy.inclusionMoment F _ _ h₁ a _ (view r) hr).trans
            (congr_arg (Orbits.moment (spectator F (view r)) _) (funext (fun i=> (ha i).symm)))
       exact Finset.sum_congr rfl (fun i _=> congr_arg (upon (spectator F (view r)) (i:Fin (D+1)).val _ (y r) w) (P.fresh_inclusions ..).symm)
     · intro e' _ z
       have h' := all_rate (b:=0) (c:=0) F P h z w hA hx hk (show (0:ℝ)<1 from zero_lt_one) hp hy le_rfl le_rfl zero_lt_one view D
       simp only [mul_one,sub_zero,mul_zero,add_zero] at h'
       exact (h'.congr (Eventually.of_forall fun _=>hEq ..)).mono (by linarith only)

lemma formulaCharged (p:GradePrice P d v c)(hδ:0<δ) {ε:ℝ}(hε:0<ε) :
   ∀ᶠ r in home,∀ (x:I→ E4) (o:E4)(y:J→E4), WithinRoom r T η x o → ClearOf o y δ →
      ∀ view:Viewers F, ‖formula F P x o (v r) y w D view‖≤r^((D+1:ℝ)-(∑ i,c i)-ε):=by
    let X:= Loc I J × Viewers F
    let M (r:ℝ) (z:X):= WithinRoom r T η z.1.1 z.1.2.1 ∧ ClearOf z.1.2.1 z.1.2.2 δ
    let U (r:ℝ) (z:X):= formula F P z.1.1 z.1.2.1 (v r) z.1.2.2 w D z.2
    let a:= (D+1:ℝ)-(∑ i,c i)-ε
    have hf:∀ᶠ r in home,∀ z,M r z → ‖U r z‖ ≤ r^a:=by
        apply refine_geometry; intro f φ hφ hl hM
        refine ⟨_,hφ,le_rfl,?_⟩
        refine (((lengthRate.rpow a).shrink hl).outweigh (formulaOn P h hT hη w D p hl
          (fun r=>(f r).1.1) (fun r=>(f r).1.2.1) (fun r=>(f r).1.2.2) (fun r=>(f r).2)
          (hM.mono fun _ x=>x.1) hδ (hM.mono fun _ x=>x.2)) ?_ (ageLarge.mono_left hl))
        dsimp only [a]; linarith only [hε]
    filter_upwards [hf] with r hr x o y hx hy view using hr ((x,o,y),view) ⟨hx,hy⟩

end YM.RG17

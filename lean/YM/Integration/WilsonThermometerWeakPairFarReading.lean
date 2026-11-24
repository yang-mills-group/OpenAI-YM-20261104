import YM.Integration.WilsonThermometerWeakPairFarBill
import YM.Integration.WilsonThermometerWeakMovingCorner

/-! The two true occupied arms are a tested child packet and its original reflected, running detector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairFarReading
open Function Finset Filter Set Table Spec OPE OPE.Orbits OPE.Nesting OPE.Prescription EveryPhase
open Climb Trace Trace.Pilot RG17 PhysMS PhysMS.Frame GapsContact GapsContact.Ascent GapsContact.Seams
open OPE.Levy Extraction Maxwell XSpace XSpace.Normalize Frontier6 Frontier6.Tale PhysicalNext.Repeat.Legato
open WilsonThermometerWeakMovingCorner WilsonThermometerWeakCornerRows
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
universe u
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
private lemma payment (q:Viewers F){h e:ℕ}(c:S.Field h)(u:S.Field e)(z:E4)(pos:z≠0):
    peal F q (assembly S (sole (0:E4)) (sole (⟨h,c⟩:S.Tag))*
      assembly S (sole z) (sole (⟨e,u⟩:S.Tag))) =
      upon (spectator F q) h 0 (sole z) (sole u:Labels S (fun _:Unit=>e)) c:=by
  have sep:Injective (beside (sole (0:E4)) (sole z)):=beside_distinct.mpr
    ⟨fun _ _ _=>Subsingleton.elim ..,fun _ _ _=>Subsingleton.elim ..,fun _ _=>Ne.symm pos⟩
  let v:Labels S (fun _:Unit=>h):=sole c
  let w:Labels S (fun _:Unit=>e):=sole u
  have cov:=peal_meter F q sep (names v) (names w)
  have a:S.classTokens ∘ names v=sole (⟨h,c⟩:S.Tag):=by
    funext j;change (⟨h,S.project h (S.representative h c)⟩:S.Tag)=_;rw [S.rep];rfl
  have b:S.classTokens ∘ names w=sole (⟨e,u⟩:S.Tag):=by
    funext j;change (⟨e,S.project e (S.representative e u)⟩:S.Tag)=_;rw [S.rep];rfl
  rw [a,b,read_algebra F q sep] at cov;exact cov

theorem original {simple:G.Simple}{A:EveryPhase.Almanac F}(H:Roll.{u} F simple A)
    (J:ℝ→tower S)(V:Store G)(lead:Leading F J)
    (h e:ℕ)(w:RG17.Free R.family e){s ε:ℝ}(sp:0<s)(paid:0<ε):
    ∃(C:ℝ)(m:ℕ),0≤C ∧ ∀ᶠ t in trail,∀(z:E4),s≤‖z‖→∀(q:Viewers F)(c:S.Field h),
      ‖upon (spectator F q) h 0 (sole (t • z)) (sole ((far F J e t w).2):Labels S (fun _:Unit=>e)) c‖≤
        C*dock t^m/t^((h:ℝ)+ε)*‖c‖:=by
  obtain ⟨B,m,bp,hear⟩:=exterior F H (fun _:Unit=>h) (fun _:Unit=>e) [] sp
  obtain ⟨K,kp,cash⟩:=WilsonThermometerWeakPairFarBill.original F H h paid
  obtain ⟨W,wp,farCost⟩:=WilsonNormalizedReflectedForm.uniform F J V lead e (norm_nonneg (reflect e w))
  refine ⟨B*K*W,m,by positivity,?_⟩
  have limit:∀ᶠ t in trail,t≤1:=(ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [cash,farCost,lead.equivariant e,limit,self_mem_nhdsWithin] with t near paid0 eq top tp
  change 0<t at tp
  intro z hz q c
  let u: S.Field e := (far F J e t w).2
  have nonzero:(t • z)≠0:=smul_ne_zero tp.ne' (norm_pos_iff.mp (sp.trans_le hz))
  have clear:Pairwise (fun i j:Unit⊕Unit=>s*Sum.elim (fun _:Unit=>t) (fun _:Unit=>t) i ≤
      ‖Sum.elim (sole (0:E4)) (sole (t • z)) i-Sum.elim (sole (0:E4)) (sole (t • z)) j‖):=by
    intro i j ne
    rcases i with ⟨⟩|⟨⟩ <;> rcases j with ⟨⟩|⟨⟩
    · exact (ne rfl).elim
    · simpa [sole,norm_smul,Real.norm_eq_abs,abs_of_pos tp,mul_comm] using mul_le_mul_of_nonneg_left hz tp.le
    · simpa [sole,norm_smul,Real.norm_eq_abs,abs_of_pos tp,mul_comm] using mul_le_mul_of_nonneg_left hz tp.le
    · exact (ne rfl).elim
  have live:=hear t ⟨tp,top⟩ t ⟨le_rfl,top⟩ (sole 0) (sole (t • z)) clear q
    (sole (⟨h,c⟩:S.Tag)) (sole (⟨e,u⟩:S.Tag)) (fun _=>rfl) (fun _=>rfl)
  change ‖t^([]:List (Unit×Axis)).length • peal F q (assembly S (sole 0) (sole (⟨h,c⟩:S.Tag))*
    assembly S (sole (t • z)) (sole (⟨e,u⟩:S.Tag)))‖≤_ at live
  rw [List.length_nil,pow_zero,one_smul,payment F q c u _ nonzero] at live
  have fcost:cost F e t u≤W:=by
    have change0:u=J t e (reflect e w):=(PhysMS.Frame.flip_coupled F e J t eq w).symm
    rw [change0];exact paid0 false (reflect e w) le_rfl
  simp only [billSlots,crestSet,Fintype.prod_unique,sole] at live
  apply live.trans
  calc
    _ ≤ B*dock t^m*(K/t^((h:ℝ)+ε)*‖c‖)*W:=by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (near c)
        (mul_nonneg (zero_le_one.trans bp) (pow_nonneg (zero_le_one.trans (dock_valid t ⟨tp,top⟩)) _)))
        fcost (Ascent.cost_pos ..) (mul_nonneg (mul_nonneg (zero_le_one.trans bp)
          (pow_nonneg (zero_le_one.trans (dock_valid t ⟨tp,top⟩)) _))
          (mul_nonneg (div_nonneg kp.le (Real.rpow_nonneg tp.le _)) (norm_nonneg _)))
    _ = _:=by ring
end YM.Integration.WilsonThermometerWeakPairFarReading
end

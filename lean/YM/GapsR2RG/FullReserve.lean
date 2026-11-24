import YM.RG17.Heading
import YM.OPE.Vitrines.Funding

/-! # Reserve at the unlopped marks of `Matric.Piano` before and after pull.
Goal is to combine the actual mixed-sector estimate with this one-column and full-volume
construction, which does not by its type *ask* for the reservedMass estimate on its
actual played voice. We *earn* it from the proof inputs AGAIN with identical tools.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{c f:Side}

abbrev Staked (P:Coefficient F c)(R:Rep G c)(r:ℝ) := ∃ a:ℝ, Blown P 0 R a ∧ turnCost R.p.order R.p.power*a ≤ r
lemma Staked.more {P:Coefficient F c}{R:Rep G c}{u v:ℝ} (h:Staked P R u)(hu:u≤v): Staked P R v:= by obtain ⟨a,ha,hq⟩:=h; exact ⟨a,ha,hq.trans hu⟩

lemma fancyStaked {t r w:ℝ}{Y:Hol G}{H:History G}{N i p : ℕ}{B:SectionData F}{T}{X:ℕ→Support (H.S.side i p)}{M:Push.Local.Raw F (H.S.side i p)}{lead} (h:Fancy B H N p i Y T X M lead w t r)
    (S : Berths (H.rep N p i).p (H.rep N p i).activities (fun q => joint B 0 (X q)))(he:Readable Y B (H.rep N p i).p (H.S.side i p) w) : Staked (mint S M Y) (H.rep N p i) r := by
 obtain ⟨a,b,c,⟨h₁,_⟩,_,hv,⟨pQ,q,hq,h₃⟩,hA,_⟩:=h
 have hκ:0<kappa H i:=Real.sqrt_pos.mpr (forcedPos ..)
 have hb:=hv.bulk.choose_spec.2.2
 obtain ⟨e,ht,hE⟩:=hv.packets
 have hv1:=sumBudget_credit hb; have hv2:=sumBudget_credit ht
 exact ⟨a,h₃ ▸ Blown.deck S h₁ he hq, le_trans (le_add_of_nonneg_right (by nlinarith only [hv1,hv2,hκ])) hA⟩
open Matric
lemma Blown.wages {Y:Hol G} {k:ℝ} {P:Coefficient F c} {R:Rep G c} (hP:P.Format 0 Y R)(K:Guard.Keeper R.p R.activities)(hp:Blown P 0 R k): Blown (tell (closeK K P)) 0 R k := by
   obtain ⟨A,hA,hC⟩:=hp; let f:=tongue P.support; let t:=Function.extend f A 0
   have hz i:t (f i)=A i:=f.injective.extend_apply ..
   refine ⟨t,?_ ,fun i=>?_⟩
   · refine Push.Local.sumBudget_pass f _ ?_ ?_
     · change SumBudget (fun i=> reservedMass R.p (mapSeat (n:=c) (f i)) (t (f i))) k
       have he i: mapSeat (f i)=P.support i:= leased _ hP i
       simp_rw [he,hz]; exact hA
     · intro i hi; rw [show t i=0 from Function.extend_apply' _ _ _ hi,reservedMass,mul_zero]
   · change R.p.supBounds 0 (mapSeat i) (liveE P i) (t i)
     by_cases he:i∈ Set.range f
     · obtain ⟨i,rfl⟩:= he; rw [hz,show mapSeat (f i)=P.support i from leased P hP i,show liveE P (f i)=P.regular i from f.injective.extend_apply ..]; exact hC i
     rw [liveE,Function.extend_apply' _ _ _ he,show t i=0 from Function.extend_apply' _ _ _ he]; exact (regular0 ..).2
lemma Staked.closes {Y:Hol G} {k:ℝ} {P:Coefficient F c} {R:Rep G c} (hP:P.Format 0 Y R)(K:Guard.Keeper R.p R.activities)(hp:Staked P R k):Staked (tell (closeK K P)) R k:=by obtain ⟨a,h,h'⟩:=hp; exact ⟨a,Blown.wages hP K h,h'⟩
structure Reserves (H:History G)(N p m:ℕ) (Y:Hol G) (Z:Plate F (H.S.side (m+1) p) (H.S.side m p)) (u ζ:ℝ):Prop where
  main i:let x:= Size.axis F i; Staked (tell (Z.main i)) (H.rep N p m) (u * F.coeffSize (vowel F (H.S.block m) (F.core x)))
  regular i T t: let b:= mapSeat (n:=H.S.side (m+1) p) i; let Rp:=H.rep N p (m+1); RegFit Rp 0 d Y b T→ Rp.p.supBounds 0 b T t→ Staked (tell (Z.tint i T)) (H.rep N p m) (ζ * Rp.p.mass b t)
  forced i T t: let Rp:= H.rep N p (m+1); T≠0→ SlotFit Rp 0 i T→ 0 ≤ t → (∀ U, ‖T U‖ ≤ t) → Staked (tell (Z.ink i T)) (H.rep N p m) (ζ*(Rp.p.mass (Rp.activities.forced i).support t / Real.sqrt (H.levels.clock.forcedAllowance (m+1))))
end YM.MergeProof


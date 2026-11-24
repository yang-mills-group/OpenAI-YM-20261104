import YM.Integration.WilsonOffsetJointConditional
import YM.Integration.WilsonOffsetWickScene

/-! One genuine two-location conditional comparison with the complete old 
planted Wilson exterior held inside the expectation. Its two foreground centers
may be independently chosen. No restriction is placed on their relative order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetJointWick
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision Tree Pressure
open PhysicalNext.Repeat.Legato MSbar MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Midpoint MSbar.Rolling Push.Uniform
open FVA1Physical.Wilson FVA1Physical.Round2.Curvature RGComparison.Core16.Spool
open WilsonConditionalTaylorLabels WilsonOffsetConditionalCharge WilsonOffsetMarkComparison WilsonOffsetJointRoster
open scoped Classical BigOperators
variable {G:Gauge}

def seated (a:Roster G) (s:Finset (Fin a.length)) {f:Side} (o:Fin a.length→Site f) (i:Fin a.length) (z:Site f):
    ↥s→Site f:=fun j=>Function.update o i z j.val

def fits (a:Roster G) (s:Finset (Fin a.length)) {f:Side} (o:Fin a.length→Site f) (i:Fin a.length) (z b:Site f) (L:ℕ) (y:ℝ):Prop:=
  ∀t:Slice (packet ⟨a,s⟩),separation b (legs (packet ⟨a,s⟩) (seated a s o i z) t).1 ≤ L*closeN y

def price (R:Run G) (a:Roster G) (s:Finset (Fin a.length)) (k:ℕ) (A:MSbar.Mosaic.Issue G)
    (Z:Positions (Primary A.c G)) (o:Fin a.length→Site A.f) (i:Fin a.length) (z:Site A.f) (part:Bool):ℝ:=
  MSbar.Bakery.taste k (bulkColumn A R.metals.O (A.fClock • Z)
    (jointFieldBank (packet ⟨a,s⟩) A (seated a s o i z) part) k) A.fClock

theorem purchased (R:Run G) (u:G.ColorIndex) (rows:∀a:Roster G,FluctuationMaskReadings (lamps a) R u)
    (a:Roster G) (k L:ℕ) (D:ℝ) (hD:0≤D) :
    ∀ᶠ m:ℕ in atTop,∀ N n,(hm:m<N) →
      (∃ S:Scene R.family.path.levels n (k+2),Realized R.alloy.B.kin N n m (k+2) (Lis.sun G u) S) ∧
      ∀ (S:Scene R.family.path.levels n (k+2)) (ready:Realized R.alloy.B.kin N n m (k+2) (Lis.sun G u) S),
        let F:=(ready.step m hm le_rfl).choose;let v:=(ready.step m hm le_rfl).choose_spec.choose
        let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v;let y:=R.family.path.levels.clock.hatBeta (m+1)
        ∀ Z:Positions (Primary A.c G),‖A.fClock • Z‖≤D*Heath.Cottage.room y →
        ∀ (s:Finset (Fin a.length)) (i:Fin a.length),i∈s → ∀(o:Fin a.length→Site A.f) (z e bz be:Site A.f),
        fits a s o i z bz L y → fits a s o i e be L y →
        let V:=postcard G A.c A.fClock Z
        ‖conditional A.S A.pre V (fun U=>field a (s.erase i) o U*(WilsonOffsetJointRoster.one a i z U-WilsonOffsetJointRoster.one a i e U))-
          (paint (price R a s k A Z o i z)-paint (price R a s k A Z o i e))‖≤4*A.fClock^k:=by
  filter_upwards [rows a k 6 L (by norm_num) D 1 hD zero_lt_one] with m sold N n hm
  obtain ⟨w,all⟩:=sold N n hm.le
  refine ⟨w,?_⟩
  intro S ready
  dsimp only
  intro Z hZ s i hi o z e bz be cz ce
  let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S (ready.step m hm le_rfl).choose
    (ready.step m hm le_rfl).choose_spec.choose
  let y:=R.family.path.levels.clock.hatBeta (m+1)
  let V:=postcard G A.c A.fClock Z
  have paid (loc b:Site A.f) (covered:fits a s o i loc b L y) (part:Bool):
      |expect A.S A.pre V (fun U=>look part (field a s (Function.update o i loc) U))-price R a s k A Z o i loc part|≤A.fClock^k:=by
    have h:=(((all S ready m le_rfl hm).2 b Z hZ s part) (seated a s o i loc) covered)
    change |expect A.S A.pre V (fun U=>look part (field a s (Function.update o i loc) U))-price R a s k A Z o i loc part|≤A.fClock^((k:ℝ)+1-1) at h
    simpa only [add_sub_cancel_right,Real.rpow_natCast] using h
  have hk:A.S.IsKernel A.pre.beta G:=R.family.path.levels.transition_mass m n A.pre.beta
  have hp:RG.Envelope A.pre.eval:=A.pre.envelope (R.makes.wilson.represents N n (m+1) hm).good
  exact WilsonOffsetJointConditional.tested hk hp V a s i hi o z e _ _ _ (paid z bz cz) (paid e be ce)

end YM.Integration.WilsonOffsetJointWick

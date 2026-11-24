import YM.Integration.WilsonReportingUnitCells

/-! Physical scalar counterterms in a genuinely positive declared grade go
through every displaced source step of the original presold Wilson spine. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingUnitOrbit
open Function Set Finset Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open RG05Readout Address Native Many WilsonReportingUnitCells
open scoped Classical BigOperators
variable {G:Gauge} {C:Family G} {m N p b d:ℕ}

def primary (d:ℕ) : Letter d := ⟨⟨0,Nat.succ_pos _⟩,Suede.pip.2⟩
def phase : ℂ := (Native.line Suede.pip).val 0
def coordinate (C:Family G) (d N:ℕ) (z:ℂ) : Palette C d :=
  ((C.S.a N:ℂ)^d*z) • ticket (⟨primary d,0⟩:Mark C d)

theorem corner (h:C.Makes) (o:Site (C.side N p)) (f:Body) :
    entrance C d N p (ticket (⟨primary d,0⟩:Mark C d)) o f = readJ (primary d) 0 f • 1 := by
  change Slide (ticket (⟨primary d,0⟩:Mark C d)) (fun i:Mark C d=>
    readJ i.1 0 f • Push.Local.presented (C.localSection (kept i.1)) o
      (C.path.rep N p N).p.threshold (Size.axis (C.labels.level (kept i.1)) i.2))=_
  rw [ticket_self]
  change _ • ((C.localSection d).places ((C.labels.level d).scaled _ (C.labels.level d).e0) o)=_
  rw [Frame.scaled_unit]
  congr 1
  funext U
  exact congr_fun ((h.sections d).unit) _

theorem seed (h:C.Makes) (starts:∀i ≤ d,C.ref i ≤ N) (z:ℂ) :
    Priced C N p N d (pulseOut (basisTop C d N p (coordinate C d N z))) (‖z‖/‖phase‖) := by
  intro f q cap
  refine ⟨((C.S.a N:ℂ)^d*z)*readJ (primary d) 0 f,?_,?_⟩
  · funext W
    change (basisTop C d N p (coordinate C d N z) f).1 W=_
    rw [coordinate,map_smul]
    change ((C.S.a N:ℂ)^d*z) * (basisTop C d N p (ticket (⟨primary d,0⟩:Mark C d)) f).1 W=_
    rw [basis_agrees C d N p h starts f W,corner h]
    change _*( ((C.path.rep N p N).eval W:ℂ)*(readJ (primary d) 0 f*1)) =
      _* ((C.path.rep N p N).eval W:ℂ)
    ring
  · have hphase : 0<‖phase‖:=norm_pos_iff.mpr (Suede.pitch_pos Suede.pip)
    have value:‖f.val 0‖ ≤ q:=by simpa only [norm_iteratedFDeriv_zero] using cap 0 le_rfl 0 box0
    have read: ‖readJ (primary d) 0 f‖ ≤ q/‖phase‖ := by
      apply (le_div_iff₀ hphase).2
      rw [← norm_mul,show readJ (primary d) 0 f*phase=f.val 0 from Suede.prompt f]
      exact value
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos N).le]
    calc
      _ ≤ C.S.a N^d*‖z‖*(q/‖phase‖) := mul_le_mul_of_nonneg_left read
        (mul_nonneg (pow_nonneg (C.S.a_pos N).le _) (norm_nonneg _))
      _ = _ := by ring

theorem through (h:C.Makes) {D:Rail C} {B:ℕ→ℕ→ℝ} {V:Sight C d p} {U:Emblems C d}
    (spine:Spine D B h b p d N V U) (y:Palette C d) {A:ℝ}
    (upper:Priced C N p N d (pulseOut (V N y)) A) (m:ℕ) (live:m ≤ N) (above:b ≤ m) :
    Priced C N p m d (pulseOut (V m (Many.point U y N m))) A := by
  revert above
  induction live using Nat.decreasingInduction with
  | self =>
    intro _
    simpa only [Many.point_here] using upper
  | of_succ j hj ih =>
    intro above
    have paid := WilsonReportingUnitCells.next h hj (ih (above.trans (Nat.le_succ _)))
    have e:pulseOut (V j (Many.point U y N j))=
        journey C p j N d (pulseOut (V (j+1) (Many.point U y N (j+1)))) := by
      rw [← Many.nearpoints U y j]
      funext f
      exact travels h spine hj above f _
    rw [e]
    exact paid

theorem original (h:C.Makes) {D:Rail C} {B:ℕ→ℕ→ℝ} {V:Sight C d p} {U:Emblems C d}
    (spine:Spine D B h b p d N V U) (starts:∀i ≤ d,C.ref i ≤ N) (m:ℕ) (live:m ≤ N)
    (above:b ≤ m) (z:ℂ) :
    Priced C N p m d (pulseOut (V m (Many.point U (coordinate C d N z) N m))) (‖z‖/‖phase‖) := by
  refine through h spine _ ?_ m live above
  rw [spine.starts]
  exact seed h starts z

end YM.Integration.WilsonReportingUnitOrbit

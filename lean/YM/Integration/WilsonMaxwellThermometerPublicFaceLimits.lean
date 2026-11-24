import YM.Integration.WilsonMaxwellThermometerPublicFaces
import YM.Integration.WilsonPositionThermometerGradedReading
import YM.PhysMS.Frame.Tensor

/-! Every full and proper moment of the real lower Schur probe has its
Maxwell limit on compact separated shapes. The public changes move the
two off-origin fields at the actual radius. The physical cutoff is
removed with that radius fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicFaceLimits
open Filter Function Set Metric MeasureTheory Lattice Wilson Labels RG Source PhysicalNext.Repeat.Legato
open RG17 XSpace XSpace.Normalize OPE OPE.Orbits Climb Table Spec Extraction Trace Trace.Pilot Next.UVStress PhysMS PhysMS.Frame
open Maxwell Maxwell.Free WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonMaxwellThermometerPublicFaces
open private rounded projected lift_entry from YM.Integration.WilsonPositionThermometerGradedReading
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
  (F:Final R.family f S) (J:ℝ→tower S) (V:Store G) (A:ℝ→Group R.family 6)
local notation "D" => ((fun _:Fin 3=>(4:ℕ)):Caps 3)
local notation "d₄" => (⟨4,by decide⟩:Fin 7)
abbrev Badge₃:=Finset (Fin 3)

def leg (e:RG17.Free R.family 4) (i:Fin 3):RG17.Free R.family 4:=
  if i=0 then e else (fields R.family.labels 4).symm (WilsonPositionThermometerGradedSource.lower G)
def slots (v:Fin 3→RG17.Free R.family 4) (s:Badge₃) (i:Fin 3):RG17.Free R.family 4:=
  if i∈s then v i else (Bel R.family.book).unit 4
def ground (e:RG17.Free R.family 4) (x:Points 3) (s:Badge₃):ℂ:=WickGoal (C:=R.family) (d:=D) (slots R (leg R e) s) x

def shifted (r:ℝ) (e:RG17.Free R.family 4) (s:Badge₃):MaxwellSlots R.family D:=
  slots R (upper R F J V r e) s

theorem limit (lead:Leading F J) (e:RG17.Free R.family 4) (s:Badge₃) (i:Fin 3):
    Tendsto (fun r=>shifted R F J V r e s i) trail (𝓝 (slots R (leg R e) s i)):=by
  by_cases h:i∈s
  · by_cases j:i=0
    · subst i
      simp only [shifted,slots,if_pos h,WilsonMaxwellThermometerPublicFaces.upper,leg,if_true,tendsto_const_nhds]
    · simp only [shifted,slots,if_pos h,WilsonMaxwellThermometerPublicFaces.upper,leg,if_neg j]
      change Tendsto (fun r=>WilsonPositionPrescribedLift.field F J V 4 r _) _ _
      exact
        WilsonPositionPrescribedLeading.applied F J V lead 4 ((fields R.family.labels _).symm (WilsonPositionThermometerGradedSource.lower G))
  · simp only [shifted,slots,if_neg h,tendsto_const_nhds]

theorem leading (lead:Leading F J) (e:RG17.Free R.family 4) (s:Badge₃) {E:Set (Points 3)}
    (compact:IsCompact E) (legal:E⊆conf 3) (δ:ℝ) (hδ:0<δ):
    ∀ᶠr in trail,∀x∈E,‖PhysMS.measured F none (J r) (shifted R F J V r e s) r x-ground R e x s‖<δ:=by
  have A:=measured_tensor F (r:=id) (v:=fun _=>none) (l:=trail) (P:=J) (w:=fun r=>shifted R F J V r e s) (u:=slots R (leg R e) s) RG17.positiveLength D 0 (fun _=>whole R.family 4) compact legal
    (fun _=>lead.lead 3 D _ 0 E compact legal) (limit R F J V lead e s)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp A δ hδ] with r paid x hx
  have h:=paid x hx
  rw [dist_comm,dist_eq_norm] at h
  let a:=PhysMS.measured F none (J r) (shifted R F J V r e s) r
  let b:= WickGoal (C:=R.family) (d:=D) (slots R (leg R e) s)
  change ‖iteratedFDeriv ℝ 0 a x-iteratedFDeriv ℝ 0 b x‖<δ at h
  have jets:iteratedFDeriv ℝ 0 a x-iteratedFDeriv ℝ 0 b x=iteratedFDeriv ℝ 0 (a-b) x:=by ext;simp
  rw [jets,norm_iteratedFDeriv_zero] at h
  exact h

variable {Y:Ultrafilter (ℕ×ℕ)} {H:(Bel R.family.book).Hierarchy}
  (simple:G.Simple) (hl:(Y:Filter _)≤f.fuse) (book:Book (f:=f) (l:=Y) (H:=H) A J)

private theorem economy (Z:Group R.family 6) (r:ℝ) (e:RG17.Free R.family 4) (s:Badge₃)
    (unit:Z.change 4 ((Bel R.family.book).unit 4)=(Bel R.family.book).unit 4):
    ∀i:Fin 3,WilsonPositionThermometerStationUnit.slot (index Z d₄) (fun j=>Z.change 4 (WilsonMaxwellThermometerPublicFaces.upper R F J V r e j)) s i=
        Z.change 4 (shifted R F J V r e s i):=by
  intro i
  by_cases h:i∈s
  · simp only [WilsonPositionThermometerStationUnit.slot,shifted,slots,if_pos h]
  · simp only [WilsonPositionThermometerStationUnit.slot,shifted,slots,if_neg h,unit]
    rfl

private theorem row (r:ℝ) (e:RG17.Free R.family 4) (s:Badge₃) (z:ℕ×ℕ) (x:Points 3)
    (unit:(A r).change 4 ((Bel R.family.book).unit 4)=(Bel R.family.book).unit 4):
    let Z:=A r
    faces R F J V A r e z (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z x) s=
      R.family.ensemble (N:=z.1) (p:=z.2) D (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z x)
        (fun i=>Z.station.wheel.atCut z (index Z d₄) (Z.change 4 (shifted R F J V r e s i))):=by
  dsimp only
  unfold faces WilsonPositionThermometerStationUnit.face
  change R.family.ensemble (N:=z.1) (p:=z.2) D _ (fun i=>(A r).station.wheel.atCut z (index (A r) d₄) _) = _
  congr 1
  funext i
  exact congrArg ((A r).station.wheel.atCut z (index (A r) d₄)) (economy R F J V (A r) r e s unit i)

include simple hl in
private theorem one (r:ℝ) (rp:0<r) (e:RG17.Free R.family 4) (s:Badge₃) {E:Set (Points 3)}
    (compact:IsCompact E) (legal:E⊆conf 3) (ε:ℝ) (hp:0<ε)
    (ready:projects (f:=f) (Y:=Y) H (fun i:Address R.family 6=>i.1) entry (A r) (J r) 0 r):
    ∀ᶠ z:ℕ×ℕ in (Y:Filter _),∀x∈E,
      ‖faces R F J V A r e z (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z x) s-
        PhysMS.measured F none (J r) (shifted R F J V r e s) r x‖<ε:=by
  let Z:=A r
  let U:=shifted R F J V r e s
  let m: R.family.book.Vector D:=fun i=>Z.lift (index Z d₄) (Z.change 4 (U i))
  let M (z:ℕ×ℕ): R.family.book.Vector D:=fun i=>Z.station.wheel.atCut z (index Z d₄) (Z.change 4 (U i))
  have move:=ready.2.2.2.1
  have moves (i:Fin 3):Tendsto (fun z=>M z i) (Y:Filter _) (𝓝 (m i)):=
    lift_entry (index Z d₄) (Z.change 4 (U i)) move
  have project (i:Fin 3):S.project 4 (m i)=J r 4 (U i):=((ready.2.2.2.2.1 d₄).2.2 (U i)).symm
  have bank:=rounded F r simple hl D M m moves rp compact legal hp
  filter_upwards [bank] with z bank x hx
  have p:=projected F D m (fun i=>J r 4 (U i)) project (Work.A05.smul_conf rp (legal hx))
  rw [row R F J V A r e s z x (ready.2.2.2.2.1 d₄).2.1]
  change ‖R.family.ensemble (N:=z.1) (p:=z.2) D _ (M z)-S.classMoment S D (r•x) (fun i=>J r 4 (U i))‖<ε
  rw [p]
  have bound:=bank x hx
  rw [dist_eq_norm] at bound
  exact bound

include simple hl book in
theorem original (lead:Leading F J) (e:RG17.Free R.family 4) (s:Badge₃) {E:Set (Points 3)}
    (compact:IsCompact E) (legal:E⊆conf 3) (ε:ℝ) (hp:0<ε):
    ∀ᶠw:ℝ×(ℕ×ℕ) in trail.curry (Y:Filter _),∀x∈E,
      ‖faces R F J V A w.1 e w.2 (WilsonSeparatedOriginalThermometerCells.positions (R:=R) w.1 w.2 x) s-ground R e x s‖<ε:=by
  apply eventually_curry_iff.mpr
  filter_upwards [book 0,RG17.positiveLength,leading R F J V lead e s compact legal (ε/2) (half_pos hp)] with r ready rp approx
  filter_upwards [one R F J V A simple hl r rp e s compact legal (ε/2) (half_pos hp) ready] with z paid x hx
  calc
    _ ≤ _ := norm_sub_le_norm_sub_add_norm_sub _ (PhysMS.measured F none (J r) (shifted R F J V r e s) r x) _
    _ < ε/2+ε/2:=add_lt_add (paid x hx) (approx x hx)
    _ = ε:=add_halves ε

end YM.Integration.WilsonMaxwellThermometerPublicFaceLimits

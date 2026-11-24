import YM.RG04B.Vac.Production
import YM.Trace.Physicalv2.GermSplit

/-!
# One designated root of the same path

This module uses the literal held root of `C.family`. Not identifying
it with a test-preimage-average kernel. In Mark step tests/germs/forced
callbacks ALWAYS for the same compassing route, with ancestry/root translation separate.
Keeps eligibility extraTest, invoice powers and output projection surviving
alignment. It's important to be able to read the actual intrinsic germ coordinate even when the
marked `q` is priced against NEW gas labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG04B.Mark
open Function Set Filter MeasureTheory Lattice Wilson RG Source Analysis Labels
open Extra.Histories Relay Push.Local
open Next.Foundations ProjectorNext.Equivariance Bid PhysicalNext.Repeat.Legato.Bandage
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n:Side}

variable {C: Family G} {d : ℕ}
set_option quotPrecheck false
local notation "Ft" => C.labels.level d
local notation "Γ" => C.params
local notation "A" => C.path.rep
local notation "S" => C.localSection d
abbrev Fiber (C:Family G)(d p m : ℕ) := Coefficient (C.labels.level d) (C.side m p)
abbrev fares (C:Family G)(m : ℕ) := GermGraph.safety C m
abbrev FlagCost {p m : ℕ} (X:Rep G (C.side m p))(x:Fiber C d p m) (r : ℝ) :=
    x.remBound 0 X (fares C m) r
structure Holds {p m : ℕ} (X:Rep G (C.side m p))(x:Fiber C d p m) (r : ℝ) : Prop where
    form : x.Format 0 C.params X
    bill : FlagCost X x r

/-- The full exact *unnormalized* density entry on this overlay vacuum. -/
def levelVal {p m : ℕ}(x:Fiber C d p m)(X:Rep G (C.side m p)) := x.density 0 S X
abbrev feePage {p m : ℕ} (x:Fiber C d p m) := GermGraph.page d p m x
abbrev atWeight (C:Family G) (d : ℕ) := (C.labels.level d).coeffSize
local notation "F" => atWeight C d

/-! Remove forced for reading the local page ONLY. The returned
object has same legal regular probes on the old inventory; outside the
noFlag germ its density need not agree. -/
def purge {F': Frame G d}(x:Coefficient F' n): Coefficient F' n := {x with forced:=0}
section Geometry
variable {p m N : ℕ} (hC : C.Makes) {X:Rep G (C.side m p)} {x y:Fiber C d p m} {r s : ℝ} (h : Holds X x r)
  (hx : Remodeled C N p m X)
include h
lemma Holds.widen (ht : r ≤ s) : Holds X x s := ⟨h.form,rem_increase d h.bill ht⟩
lemma Holds.nonnegative :0≤r:=by obtain ⟨a,b,ha,hb,hc,h⟩:=h.bill; linarith only [hc,ha,hb]
lemma Holds.joint (he : Holds X y s): Holds X (beside x y) (r+s) :=
    let H:=presentation h.form h.bill he.form he.bill; ⟨H.1,H.2⟩
lemma Holds.keepRead {Y:Rep G (C.side m p)} (hw:X.p=Y.p) : Holds Y (purge x) r := by
  obtain ⟨⟨hs,ho,hj,hP,hK⟩,a,b,ha,hb,hr,hx,hE,hV⟩:=h
  refine ⟨⟨?_,ho,hj,hP,fun i U H=>False.elim (H rfl),fun i H=>False.elim (H rfl),fun _ _ _=>rfl,fun _ _ _ _ _=>rfl, fun _=>measurable_const⟩,a,0,ha,le_rfl,(add_le_add le_rfl hb).trans hr,hx,?_,?_⟩
  · exact hw ▸ hs
  · exact hw ▸ hE
  rw [mul_zero]
  exact ⟨fun i=>0,budget0 _ _,fun i=> ⟨le_rfl,fun U=> (norm_zero (E:=ℂ)).le⟩⟩

omit h
lemma page_clean (x:Fiber C d p m): feePage (purge x)=feePage x:= rfl
include h hC hx
-- noFlag use valid even independently of membership.
set_option linter.unusedSectionVars false in
lemma Holds.peek (he:m ≤ N) : levelVal (purge x) (A N p m) =ᶠ[𝓝 1] levelVal x X := by
   have hz : X.p=(A N p m).p:= hx.point.trans (hC.wilson.represents N p m he).vac.symm
   filter_upwards [offFlags X.p.threshold X.p.threshold_pos] with U hu
   unfold levelVal
   rw [noFlagCharge _ _ _ (hC.sections d) hu,noFlagCharge _ _ _ (hC.sections d) (hz ▸ hu),hx.exact_eval,hz]
   rfl
lemma Holds.intrinsic (hi : C.ref d ≤ m) (he:m ≤ N) {q : Fiber C d p m}
      (hw:Holds (A N p m) q s) (hp : levelVal q (A N p m) =ᶠ[𝓝 1] levelVal x X) : feePage x = feePage q := by
   have hz : X.p=(A N p m).p:=hx.point.trans (hC.wilson.represents N p m he).vac.symm
   apply Eq.symm
   exact same_page (s:=purge x) hC he hi (show reads d N p m q _ from ⟨hw.form,hw.bill⟩) ⟨(h.keepRead hz).form,(h.keepRead hz).bill⟩ (hp.trans (h.peek hC hx  he).symm)
lemma Holds.at_close (hi : C.ref d ≤ m) (he:m ≤ N) : F (feePage x - x.x) ≤ invoice (C:=C) d m p * r := by
   let hp:= h.keepRead (hx.point.trans (hC.wilson.represents N p m he).vac.symm)
   exact measured_diff d N p m (q:=purge x) hC hi he (show reads d N p m (purge x) r from ⟨hp.form,hp.bill⟩)
lemma Holds.coarse (hi:Opened C d m p)(he:m≤N)(hw : F x.x ≤ r) : F (feePage x) ≤ 2*r:=by
   let hp:= h.keepRead (hx.point.trans (hC.wilson.represents N p m he).vac.symm)
   exact control_page hC hi he (purge x) (show reads d N p m (purge x) _ from ⟨hp.form,hp.bill⟩) hw
lemma Holds.sumPage (hy : Holds X y s) (hi : C.ref d ≤ m) (he:m ≤ N) :
    feePage (beside x y) = feePage x + feePage y := by
   have ht:= dimensions d N p m hC hi he
   rw [← show X.p=(A N p m).p from hx.point.trans (hC.wilson.represents N p m he).vac.symm] at ht
   simpa only [feePage,page,hx.point,plank] using add_projection d x y h.form hy.form ht.1 ht.2 ⟨_,_,h.bill⟩ ⟨_,_,hy.bill⟩

omit hC
lemma Holds.sumValue (hy : Holds X y s) : levelVal (beside x y) X = levelVal x X + levelVal y X :=
   plus hx.valid h.bill hy.bill S
lemma Holds.volume : Integrable (levelVal x X) (prior G (C.side m p)) := by
  have he := Coefficient.envelope S hx.valid h.bill h.form
  obtain ⟨c,hc⟩ := he.cost
  exact Integrable.of_bound he.meas.aestronglyMeasurable c (.of_forall hc)

omit hx h
lemma owns (hi:Opened C d m p)(hC:C.Makes)(hm:m ≤ N)(v:C.label d) :
    Holds (A N p m) ((C.factory d N p).entries m v) (2*stock C m* F (fitting d N p m hC hi hm v)) :=
     let H := graph_cost d N p m hC hi hm v; ⟨H.1,H.2⟩

lemma basic_proof (X:Rep G (C.side m p))(v:C.label d) : Holds X (show Fiber C d p m from primary 0 v) 0 :=
    ⟨primary_format _,primary_rem _ (Real.sqrt_pos.2 (Extras _ _))⟩ where
  Extras := Extra.Histories.forcedPos
lemma basic_page (v:C.label d) : feePage (show Fiber C d p m from primary 0 v) = v := by
    unfold feePage page projection
    have hz (i:ℕ) : vector Ft Γ (plank C m).threshold 0
       ((primary (0:Site (C.side m p)) v).regular i) = 0:= by
       unfold vector
       have he (f:Config G (C.side m p) → ℂ) (hf:f=0): label Γ 0 f d=0:=by
          subst f
          have hx : JetTest Γ (0:Site (C.side m p)) (0 : Label G d) 0:=by
             exact (jetTest_zero_iff C.params 0 _ _).mpr (Extra.Histories.vanishing0 d _ Γ)
          have hh :∃ l:Label G d,JetTest Γ (0:Site (C.side m p)) l 0:=⟨0,hx⟩
          rw [label,dif_pos hh]; exact JetTest.unique hh.choose_spec hx
       change (Ft|>.scaled _) ((Ft|>.coords) (label _ (0:Site (C.side m p)) 0 _)) = _
       rw [he _ rfl,_root_.map_zero,_root_.map_zero]
    simp_rw [hz,tsum_zero,add_zero]
    rfl
end Geometry
end YM.RG04B.Mark

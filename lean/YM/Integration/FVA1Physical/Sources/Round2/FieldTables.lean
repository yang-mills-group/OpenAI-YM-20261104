import YM.Integration.FVA1Physical.Sources.Round2.FieldQuiet
import YM.Integration.FVA1Physical.Sources.Round2.FieldMarkerBound

/-! The physically normalized complex mixed table and the independently
constructed full Wilson action/Haar table on precisely the same coarse field. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Finset Filter Marker MeasureTheory Lattice RG Tree Exterior Push.Uniform Pressure
open RGComparison.Core16 RGComparison.Core16.Spool MSbar MSbar.Bulk MSbar.Heath MSbar.Heath.Stock
open MSbar.Mosaic MSbar.Cacao MSbar.Rolling MSbar.Bakery YM.Integration.FVA1Physical.Wilson
open Comparison.RG02.Order Extra.Trajectories
open Precision MSbar.Bakery.Film
open scoped Classical Topology BigOperators
variable {G:Gauge} {ι:Type} [DecidableEq ι] [Fintype ι] (J:ι→Lamp G) (C:Census ι)

def fullFieldTable (A:Issue G) (Z:Positions (Primary A.c G)) (o:ι→Site A.f) : Poly C :=
  Poly.inject fun s=>
    let sub:=fun i:s.val=>J i.1
    let atSites:=fun i:s.val=>o i.1
    let E:=expect A.S A.pre (postcard G A.c A.fClock Z)
    ⟨E (fun U=>look false (tally sub atSites U)),E (fun U=>look true (tally sub atSites U))⟩

def wilsonFieldTable (A:Issue G) (χ:ChartRatio G) (p:ℕ) (Z:Positions (Primary A.c G))
    (o:ι→Site A.f) : Poly C :=
  Poly.inject fun s=>
    let part:=fun mode:Bool=>taste p (bulkColumn A χ (A.fClock•Z)
      (jointFieldBank (fun i:s.val=>J i.1) A (fun i=>o i.1) mode) p) A.fClock
    ⟨part false,part true⟩

def maskEnvelope : ℝ := ∑ t:Finset ι,stencilBound (fun i:t=>J i.1)

omit [DecidableEq ι] in
theorem maskEnvelope_pos : 0 < maskEnvelope J := by
  refine (stencilBound_pos (fun i:(∅:Finset ι)=>J i.1)).trans_le ?_
  exact single_le_sum (fun (i:Finset ι) _=>(stencilBound_pos (fun j:i=>J j.1)).le) (mem_univ ∅)

omit [Fintype ι] in
theorem field_table_unit (A:Issue G) (χ:ChartRatio G) (p:ℕ) (Z:Positions (Primary A.c G))
    (o:ι→Site A.f) {σ h δ Λ w:ℝ} (adm:Admitted (postcard G A.c A.fClock Z) A.pre A.S σ h δ Λ w)
    (kind:Kind A.T) (pos:(mold A.pre A.F A.v).PosDef) :
    (fullFieldTable J C A Z o).part C.quiet=1 ∧ (wilsonFieldTable J C A χ p Z o).part C.quiet=1 := by
  letI:IsEmpty ↑C.quiet.val:=⟨fun i=>Finset.notMem_empty i.val i.property⟩
  have actual (part:Bool):
      expect A.S A.pre (postcard G A.c A.fClock Z)
        (fun U=>look part (tally (fun i:C.quiet.val=>J i.1) (fun i=>o i.1) U))=if part then 0 else 1 := by
    cases part <;> simpa [Spool.tally,look] using (e_const (postcard G A.c A.fClock Z) adm _)
  have formal (part:Bool):=empty_bulk_field (fun i:C.quiet.val=>J i.1) A χ (A.fClock•Z) p
    (fun i=>o i.1) part kind pos
  exact ⟨Complex.ext (actual false) (actual true),Complex.ext (formal false) (formal true)⟩

theorem field_table_cap (A:Issue G) (Z:Positions (Primary A.c G)) (o:ι→Site A.f)
    {σ h δ Λ w:ℝ} (adm:Admitted (postcard G A.c A.fClock Z) A.pre A.S σ h δ Λ w)
    (s:C.Mode) : ‖(fullFieldTable J C A Z o).part s‖ ≤ 2*maskEnvelope J := by
  let K:=fun i:s.val=>J i.1
  let loc:=fun i:s.val=>o i.1
  let O:=postcard G A.c A.fClock Z
  have step (part:Bool): |expect A.S A.pre O (fun U=>look part (tally K loc U))| ≤ maskEnvelope J := by
    let B:=stencilBound K
    let φ:=fun U=>look part (tally K loc U)
    have bound (U): |φ U|≤B := stencil_bounded K loc part U
    have enc:Envelope φ:=⟨((look part).continuous.comp (tally_cont K loc)).measurable,B,bound⟩
    have lo:=nn O adm enc (Envelope.const (-B)) (fun U=>(abs_le.mp (bound U)).1)
    have hi:=nn O adm (Envelope.const B) enc (fun U=>(abs_le.mp (bound U)).2)
    rw [e_const O adm] at lo hi
    apply (abs_le.mpr ⟨lo,hi⟩).trans
    exact single_le_sum (fun (i:Finset ι) _=>(stencilBound_pos (fun j:i=>J j.1)).le) (mem_univ s.val)
  exact (Complex.norm_le_abs_re_add_abs_im _).trans ((add_le_add (step false) (step true)).trans_eq (two_mul _).symm)

theorem field_mask_prices (A:Issue G) (χ:ChartRatio G) (p L:ℕ) (y η:ℝ) (b:Site A.f)
    (Z:Positions (Primary A.c G)) (o:ι→Site A.f) (w:ι→ℝ) (hw:∀i,0<w i)
    (near:∀l:Slice J,separation b (legs J o l).1 ≤ L*MSbar.Mosaic.closeN y)
    {σ h δ Λ t:ℝ} (adm:Admitted (postcard G A.c A.fClock Z) A.pre A.S σ h δ Λ t)
    (kind:Kind A.T) (pos:(mold A.pre A.F A.v).PosDef)
    (paid:∀ (s:Finset ι) (part:Bool),PhysicalFieldComparison (fun i:s=>J i.1) A χ y η p L part b Z)
    (small:A.fClock^((p:ℝ)+1-η)≤1) :
    let P:=fullFieldTable J C A Z o;let Q:=wilsonFieldTable J C A χ p Z o
    let E:=markerScale C w (2*maskEnvelope J)*A.fClock^((p:ℝ)+1-η)
    P.part C.quiet=1 ∧ Q.part C.quiet=1 ∧ Poly.price w (P-Q)≤E ∧ Poly.price w (connected P-connected Q)≤E := by
  intro P Q E
  obtain ⟨u,v⟩:=field_table_unit J C A χ p Z o adm kind pos
  have money (s:C.Mode) (part:Bool):=paid s.val part (fun i:s.val=>o i.1)
    (fun l=>near ⟨l.1.1,l.2⟩)
  refine ⟨u,v,marker_transfer C w hw (mul_nonneg zero_le_two (maskEnvelope_pos J).le)
    (Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _) small P Q u v
    (field_table_cap J C A Z o adm) ?_⟩
  intro s
  exact (Complex.norm_le_abs_re_add_abs_im _).trans ((add_le_add (money s false) (money s true)).trans_eq (two_mul _).symm)

end YM.Integration.FVA1Physical.Round2.Curvature

import YM.Integration.WilsonMacroscopicDetector

/-! The physical functional of the original far probes which reads one
retained positive component of a pair. The finite exterior coefficients
are fixed before either local input or the running coupling is supplied. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourOutputSensor
open Filter Finset Set MeasureTheory Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader
open Trace.Pilot RG17 PhysMS WilsonMacroscopicDetector
open scoped Topology Classical BigOperators
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
    (F:Spec.Final C f S) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def grade (c:Q.channels 4) : S.Field 4 →L[ℂ] ℂ :=
  ((Q.basis 4).coord c ∘ₗ (Q.cutTest 4 4).codRestrict (Q.stratum 4)
    (fun x=>Q.knife_mem 4 (Q.liftOne 4 4 x))).toContinuousLinearMap

theorem packet (c:Q.channels 4) {I:Type} [Fintype I] {d:I→ℕ} (x:I→E4) (v:Labels S d) (o:E4) :
    grade F Q c (Q.packet 4 x v o)=Q.coef 4 c x v o:=by
  let u:Q.stratum 4 := ⟨Q.cutTest 4 4 (Q.packet 4 x v o),Q.knife_mem 4 _⟩
  let v':Q.stratum 4 := ⟨Q.fresh 4 x o v,Q.fresh_mem 4 x o v⟩
  have same:u=v':=Subtype.ext (Q.filtered_packet 4 4 le_rfl x v o)
  change (Q.basis 4).repr u c=(Q.basis 4).repr v' c
  rw [same]

def coefficient (c:Q.channels 4) (X:probes F 4) : ℂ :=
  grade F Q c (restore F 4 (Pi.single X 1))

theorem finite (c:Q.channels 4) (a:probes F 4→ℂ) :
    grade F Q c (restore F 4 a) = ∑X:probes F 4,a X*coefficient F Q c X :=by
  have expand:a=∑X:probes F 4, a X • (Pi.single X 1:probes F 4→ℂ):=by
    ext i
    simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs => rw [expand]
  simp only [map_sum,map_smul,smul_eq_mul,coefficient]

theorem recovered (c:Q.channels 4) (x:S.Field 4) :
    (∑X:probes F 4,X.val.charge F 4 x*coefficient F Q c X)=grade F Q c x:=by
  rw [←show ∑X:probes F 4,read F 4 x X*coefficient F Q c X=
      ∑X:probes F 4,X.val.charge F 4 x*coefficient F Q c X from rfl]
  rw [←finite F Q c,exact_read]

def pairRead (c:Q.channels 4) (a:Fin 2→S.Field 4) (r:ℝ) (ψ:Test 2):ℂ :=
  ∑X:probes F 4,RG17.appeared F (d:=fun _:Fin 2=>4) a X.val r ψ*coefficient F Q c X

theorem measured (c:Q.channels 4) (a:Fin 2→S.Field 4) (r:ℝ) (ψ:Test 2):
    pairRead F Q c a r ψ=grade F Q c (fromProducts F 4 (d:=fun _:Fin 2=>4) a r ψ):=
  (finite F Q c _).symm

theorem full_error (c:Q.channels 4) (a:Fin 2→S.Field 4) (r:ℝ) (ψ:Test 2) (u:S.Field 4):
    pairRead F Q c a r ψ-grade F Q c u=
      ∑X:probes F 4,coefficient F Q c X*(RG17.appeared F (d:=fun _:Fin 2=>4) a X.val r ψ-
        X.val.charge F 4 u):=by
  rw [←recovered F Q c u]
  unfold pairRead
  rw [←Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun X _=>?_ )
  ring

end YM.Integration.WilsonCenteredFourOutputSensor

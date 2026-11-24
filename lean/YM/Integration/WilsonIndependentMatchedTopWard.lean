import YM.Integration.WilsonIndependentMatchedTopFilm
import YM.Integration.WilsonOriginalPivotWardEuler

/-! Local covariant group vectors on the actual inversion board. Each
transported curvature is the curvature of one based closed walk. Wick
subtractions, signed differences and finite contractions may be kept in
their common equivariant tensor before applying the full Haar identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedTopWard
open Lattice RG Wilson Source Labels PowerSeries PertExtension PertExtension.Orb XSpace
open FormalOPE.RG10 FormalOPE.RG10.InversionTop FormalOPE.RG10.InversionWard
open XSpace.Rose XSpace.Cirrus FVA2 PhysicalNext.Repeat.Legato SlotEvaluation
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonIndependentMatchedNamedPair (sectionAt placed printed admitted ranked)
open WilsonIndependentMatchedTopFilm (dose word)
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}

def path (s:RG.Slot) : Walk := (s.walk ++ square s.plaq.val.1 s.plaq.val.2) ++ reverse s.walk

private theorem closed (s:RG.Slot)(x:Site n) : stop x (path s)=x := by
  simp only [path,stop_append,square_stop,reverse_stop]

theorem value (s:RG.Slot)(U:Config G n)(x:Site n) :
    s.atSite U x = G.curvature (travel U x (path s)) := by
  have coord:=travel_at x U (0:Cover) (path s)
  rw [map_zero,zero_add] at coord
  rw [←coord]
  change G.adjoint _ (G.curvature _) = _
  rw [path,travel_append,travel_append,stop_append,square_stop,travel_reverse,G.curvature_conjugate]
  rfl

variable {ι:Type} [Fintype ι]

/-- A finite equivariant function of actual covariant slot values admits
the nonlinear direction, including both oriented links of its Ward motion. -/
theorem issued (b:Edge (Site n))(slots:ι→RG.Slot)(Z:(ι→G.Color)→G.Color)
    (smooth:ContDiff ℝ ∞ Z)(eqv:∀ a q,Z (fun i=>G.adjoint a (q i))=G.adjoint a (Z q)) :
    Direction b (fun U=>Z (fun i=>(slots i).atSite U b.1)) := by
  have prox (i:ι) : Proxy (fun U:Config G n=>(slots i).atSite U b.1) := by
    simp_rw [value]
    exact proxy_curvature (proxy_path ..)
  refine ⟨?_,?_⟩
  · choose p hp eq using prox
    refine ⟨fun u=>Z (fun i=>p i u),smooth.comp (contDiff_pi.2 hp),?_⟩
    funext U
    exact congrArg Z (funext fun i=>congrFun (eq i) U)
  · intro a _ U
    simp_rw [value,travel_gauge,closed,G.curvature_conjugate]
    exact eqv _ _

variable {p:Period}(T:p.Tree)
def force (b:Edge (Site p.side))(Z:Config G p.side→G.Color) : Bare.Series T G :=
  BareOrb.stencil T (effort b Z) - Bare.scalar T (X^2)*BareOrb.stencil T (fallout b Z)

/-- The same normalized ordinary expectation tests the whole peer product. -/
theorem hearing (b:Edge (Site p.side))(Z:Config G p.side→G.Color)(h:Direction b Z)
    {O:Config G p.side→ℝ}(proxy:Proxy O)(valid:PreTest O) :
    Bare.normalized T G (force T b Z * BareOrb.stencil T O) =
      X^2 * Bare.normalized T G (BareOrb.stencil T (coupled b Z O)) := by
  rw [force,sub_mul,mul_assoc,map_sub,Bare.normalized_scalar,
    ←WilsonOriginalPivotWardProduct.product T h.effort valid,
    ←WilsonOriginalPivotWardProduct.product T h.fallout valid]
  exact WilsonOriginalPivotWardTree.contact T h proxy valid.gauge

theorem silent (b:Edge (Site p.side))(Z:Config G p.side→G.Color)(h:Direction b Z)
    {O:Config G p.side→ℝ}(proxy:Proxy O)(valid:PreTest O){S:Set (Site p.side)}
    (locality:LocalOn S O)(apart:off b S) :
    Bare.normalized T G (force T b Z * BareOrb.stencil T O) = 0 := by
  rw [hearing T b Z h proxy valid,BareOrb.diagram_eq T (h.contact proxy valid.gauge),
    isolated b locality apart Z]
  change X^2 * replyCoeff (0:Config G p.side→ℝ) = 0
  rw [reply_nil (G:=G) (even_iff_two_dvd.mpr p.even),mul_zero]

end YM.Integration.WilsonIndependentMatchedTopWard

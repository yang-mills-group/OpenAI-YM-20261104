import YM.SignedWilsonExpansion.F9.Looms
import YM.Integration.IndependentSourcePathFamily
import YM.Integration.SignedShiftedMeasuredCurrent
/-!
# Actual socket power and regulator operator (27) on all sides simultaneously.

Check without imposing a size limit on Fourier register (nor requiring qlocal
cut of new vertices). `mount` does **not** evaluate power-series at real g. Instance
will be combined over the product and put through normalized vacuum reset.
-/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.Integration.Liner
open Function Matrix Lattice RG Laurent Bloch Gauge
open WilsonCoeffUV WilsonCoeffUV.Blue FreeResolvent Tree WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Power
open WilsonCoeffUV.Bank WilsonCoeffUV.Soil Exterior Source WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Mer.Xa
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark Lattice Laurent Labels Precision PowerSeries
open WilsonCoeffUV.Bank.Mosaic
open PhysicalNext.Repeat.Legato Wilson Stationary
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{J:Type}{M S:Finset J}{K:Levels G}{d k f r ℓ:ℕ}{A:ChartRatio G}
variable (D:J→ℕ) [DecidableEq J]

def knob (x:ℕ):Knob x:=⟨0,Fin.elim0⟩
def starS (x:ℕ):Scroll x:= ⟨fun _=>1,show ContDiff ℝ (↑x) (fun _=>1) from contDiff_const⟩
def lamp (D:J→ℕ):Case D:=fun i=> page _ (starS (D i))
omit [DecidableEq J] in
lemma crest (j:J)(p:Chamber): claim (D j) (knob (D j)) p (lamp D j)=1:=by change crease (starS (D j)) Fin.elim0 p.val=1; simp [crease,starS,iteratedFDeriv_zero_apply]

abbrev Ur (j:J)(T:Seed G (D j)):Atom G T.rank :=colour T.path T.color T.weight T.quadrant
abbrev mount (j:J)(T:Seed G (D j))(o:Cover): Era G ℝ:= tuftV (touch (lamp D) {j}) (source D j (Ur D j T) T.knob T.point T.head o)

lemma certifiedL (j:J)(T:Seed G (D j))(r:T.rank≤ d+T.head)(o:Cover): Auth d (mount D j T o) := (OriginalMarkedSourceComet.certified D j _ (OriginalMarkedSourceComet.invariant _ _ _ _) _ _ _ d r _).tuft _

lemma sprig_seal {n:Side}(T:Atom G r)(a:Site n): (PowerSeries.X:Blue.Ink (Woods G n))^r*Blue.flash (sprig (meter T a) r)=jet (meter T a):=by
    apply moves; intro i hi
    have h:=(rays_jet ((meter_hot T a).contDiffAt (x:=0)).analyticAt r).mp (meter_shell T a) i hi
    rw [jet_apply, show rye (meter T a) i=0 from funext (fun _=>by rw [rye,h]; simp),map_zero] -- import
lemma push_cost {T:Atom G r}{V:Type}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]{P:Comet G V r}(n:Side)(L:V→L[ℝ]ℝ)(he:meter T (0:Site n)=meter (dip P L) 0):
    Blue.flash ((tuftV L (volumeR P ℓ)).1 n)=(PowerSeries.X:Blue.Ink (Woods G n))^ℓ * Blue.flash (sprig (meter T (0:Site n)) r):=by
    change Blue.flash (ply L.toLinearMap _) = _; rw [volume_probe,he]; apply PowerSeries.ext; intro i; rw [coeff_X_pow_mul']; unfold Blue.flash; simp only [coeff_mk]; split_ifs <;> simp [totalR]

lemma shot (j:J)(T:Seed G (D j))(v:T.knob=knob (D j))(ry:r+T.head=T.rank)(n:Side)(o:Cover):
    (PowerSeries.X:Blue.Ink (Woods G n))^r * Blue.flash ((mount D j T o).1 n)=jet (meter (Ur D j T) (wrap n o)):=by
    let K:=Ur D j T; let a:= claim _ T.knob T.point; let p:= current K a
    let Q:= volumeR p T.head; let L:= touch (lamp D) {j}; let U:= petal D j; let L':= L.comp U
    have he : dip p L'=K:=by
        let x:= T.knob; change { leg:=_, coeff:= fun v=> (L.comp U) ( K.coeff v • a ) }=K
        congr; ext1 i; rw [(L.comp U).map_smul]; change _ * touch (lamp D) _ (petal D j (claim _ T.knob T.point))=_; rw [petal_hit,v,crest,mul_one]; rfl
    let P:= tuftV U Q; change PowerSeries.X^r * readO (lamp D) (shifted P o) n=_
    have hp:Auth r (shifted P 0):=OriginalMarkedSourceComet.certified _ _ (Ur D j T) (OriginalMarkedSourceComet.invariant _ _ _ _) _ _ _ r ry.ge 0
    have hu : shifted P 0=P:=by
       unfold shifted; apply Prod.ext; · funext n i j x; simp [Mer.skewV,revolve,jog,comp_def]
       funext i j x; simp [Mer.skewV,revolve,jog,comp_def]
    rw [hu] at hp; rw [Wheel.Motion.transportPage _ hp]; -- unshifted
    let H:=SignedShiftedMeasuredCurrent.shift (G:=G) (f:=n) o
    have hx: readO (lamp D) P n=X^T.head * Blue.flash (sprig (meter K (0:Site n)) T.rank):=push_cost n L' (Eq.symm (congr_arg (fun T:Atom G _=>meter T (0:Site n)) he)) -- might need diff fderiv norm
    rw [hx, map_mul,map_pow]; change PowerSeries.X^r*((loom H PowerSeries.X)^ T.head * _) = _
    rw [show loom H PowerSeries.X=PowerSeries.X from (by simp [loom]),←mul_assoc, ←pow_add,ry]; exact Eq.trans (congr_arg (_ * ·) (SignedShiftedMeasuredCurrent.sprig_at K o)) (sprig_seal ..)
end YM.Integration.Liner

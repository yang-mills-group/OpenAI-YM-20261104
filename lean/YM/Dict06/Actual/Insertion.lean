import YM.Dict06.Wilson.Budget
import YM.Dict06.Wilson.Tags
import YM.Extraction.LatticeFamily
/-! Bind the stencils and top coefficient prescription to the SAME Family
and section. `auth` is before any masked re-expression. Encoded at ref? We
use the physical **restored** O at cutoff lattice here, whose Prefactor is
a_N^-d, threshold scaling to raw link stencil and factory.terminal.symm on
its ref coordinates. Its denominator/forced components as a source law
still need the RG01-05 estimates; Based.encode reassembles top unnormalized
representation at the origin *exactly*, avail for composition on this Family.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dict06.Actual
open PowerSeries Function Set Filter Series Lattice Wilson Labels Source Source.Drops Wil
open Marker Extra.Trajectories
open scoped BigOperators ContDiff Matrix.Norms.Frobenius Topology Classical
variable {G : Gauge}(C:Family G) (N p:ℕ)

def unroll {n:Side}(x:Site n)(A:Links (Per n) G.Color) : Links ℤ G.Color :=
  fun e=>A (wrap n e.1+x,e.2)
lemma opens {n:Side}(x:Site n)(A:Links (Per n) G.Color)(t:ℝ) :
    expandAt x (positive A t)=positive (unroll x A) t:=rfl

abbrev matrix (d:ℕ) : C.label d→ₗ[ℂ]C.label d := (C.labels.level d).scaled (C.path.levels.clock.threshold N)⁻¹ ∘ₗ (C.factory d N p).terminal.symm.toLinearMap
def factor (d:ℕ):ℂ:=((C.S.a N:ℂ)^d)⁻¹
lemma names {d:ℕ}(v:C.label d)(x:Site (C.side N p))(U:Config G _):
    C.O N p v x U = factor C N d * (C.localSection d).evaluate (matrix C N p d v) (expandAt x U):=rfl

def auth (d:ℕ)(x:Site (C.side N p))(v:C.label d)(A:Links (Per (C.side N p)) G.Color):=
   PowerSeries.C (factor C N d)* book (C.localSection d) (matrix C N p d v) (unroll x A)
lemma honest (d:ℕ)(x:Site (C.side N p))(v:C.label d)(A:Links (Per (C.side N p)) G.Color) :
    ContDiffAt ℝ ∞ (fun t:ℝ=>C.O N p v x (positive A t)) 0 ∧ ps (fun t:ℝ=>C.O N p v x (positive A t))=auth C N p d x v A := by
   simp_rw [Actual.names C,opens]
   let f (t:ℝ):=(C.localSection d).evaluate (matrix C N p d v) (positive (unroll x A) t)
   have hf : ContDiffAt ℝ ∞ f 0:=by
     unfold f; simp_rw [echo_exact]
     exact ((echo_smooth (C.localSection d) _).comp (g:=echo (C.localSection d) _) (f:=fun t:ℝ=>t • restrictLog _ _) (contDiff_id.smul contDiff_const)).contDiffAt.of_le le_top
   change ContDiffAt _ _ ((fun _=>factor C N d)*f) _ ∧ ps ((fun _=>factor C N d)*f) = _
   rw [ps_mul _ _ contDiffAt_const hf,ps_const, show ps f= _ from echo_book (C.localSection d) _ (unroll x A)]
   exact ⟨contDiffAt_const.mul hf,rfl⟩
variable {V I:Type*}[DecidableEq V](R:Census V) (tag : I→R.Mode)
variable (d:I→ℕ)(x:I→Site (C.side N p))(v:(j:I)→C.label (d j))

def seriesOf (A:Links (Per (C.side N p)) G.Color) (s:Finset I):= Tags.occurrences R tag (fun j=>auth C N p (d j) (x j) (v j) A) s
def many (s:Finset I) (U:Config G (C.side N p)) : Marker.Poly R:= ∏ j∈s,Poly.send (tag j) (C.O N p (v j) (x j) U)
lemma read_all (A:Links (Per (C.side N p)) G.Color)(s:Finset I)(q:R.Mode) :
   ps (fun t=> (many C N p R tag d x v s (positive A t)).part q) = PowerSeries.mk (fun n=> (coeff n (seriesOf C N p R tag d x v A s)).part q):=by
   classical
   by_cases h:Fits tag s
   · unfold many seriesOf; simp_rw [tagged_prod tag _ h, Poly.part_send,Tags.separate _ _ _ _ h,Tags.wear_at,Poly.part_send]
     split
     next h'=>
       have he (j:I): ps (fun t=> C.O N p (v j) (x j) (positive A t))= auth C N p (d j) _ _ _ := (honest ..).2
       let f:=fun (i:I) (t:ℝ)=> C.O N p (v i) (x i) (positive A t)
       rw [show (fun t:ℝ=> ∏ i∈s,C.O N p (v i) (x i) (positive A t))=∏ i ∈ s,f i from funext (fun t=> (Finset.prod_apply t s f).symm),(Tags.ps_product f _ (fun j _=>(honest ..).1)).2]
       simp_rw [f,he]; ext1 n;rw [coeff_mk]
     ext1 n; rw [ps_at,ordinary_const,ite_self,coeff_mk]
   unfold seriesOf; rw [Tags.clash _ _ _ s h]
   rw [show (fun t=> (many C N p R tag d x v s (positive A t)).part q)=fun _=>0 from ?hv]
   case hv=>funext t;rw [show many C N p R tag d x v s (positive A t)=0 from by contrapose! h; exact Extra.Trajectories.fits_of_tagged_prod tag h, Poly.part_nil]
   ext1 n; rw [ps_at,coeff_mk,map_zero,Poly.part_nil,ordinary_const,ite_self]

-- Explicit map for converting Wilson normalized input label i to reference
-- coordinates at the cutoff; uses threshold^l on INPUT. Also include
-- engineering factors separately or track them in units of kernel eval.
def calibrate (d:ℕ): Label G d→ₗ[ℂ] C.label d:=
  (C.factory d N p).terminal.toLinearMap ∘ₗ ((C.labels.level d).scaled (C.path.levels.clock.threshold N) ∘ₗ (C.labels.level d).coords.toLinearMap)
def paint (d:ℕ): C.label d→ₗ[ℂ] Label G d:=
  (C.labels.level d).coords.symm.toLinearMap ∘ₗ matrix C N p d

private lemma active (N:ℕ) : C.path.levels.clock.threshold N ≠ 0:= (C.path.levels.budget N).threshold_pos.ne'
lemma meet (d:ℕ)(v:Label G d): matrix C N p d (calibrate C N p d v)=(C.labels.level d).coords v:=by
   let F:=C.labels.level d
   unfold matrix calibrate; simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
   let t:=C.path.levels.clock.threshold N
   have h:=F.scaled_inv (inv_ne_zero (active C N)) (F.coords v)
   simpa only [inv_inv] using h
lemma paint_basis (d:ℕ)(v:Label G d):paint C N p d (calibrate C N p d v)=v := by
   unfold paint; rw [LinearMap.comp_apply, meet]; exact (C.labels.level d).coords.symm_apply_apply _
lemma read_basis (d:ℕ)(v:C.label d):calibrate C N p d (paint C N p d v)=v:=by
  unfold calibrate paint matrix
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,(C.labels.level d).scaled_inv (active C N)]
lemma calibrated_series (d:ℕ) (h:Bid.pop (C.localSection d)) (j:(C.labels.level d).Index)
    (o:Site (C.side N p))(A:Links (Per (C.side N p)) G.Color):
    let F:=C.labels.level d
    auth C N p d o (calibrate C N p d (F.basis j)) A =
      PowerSeries.C (factor C N d) * (letter (C.localSection d) j (unroll o A)* PowerSeries.X^(F.grades j).2):=by
  unfold auth
  dsimp only []
  rw [meet, (C.labels.level d).coords_basis,← powered_letter (C.localSection d) h]
end YM.Dict06.Actual

import YM.Integration.WilsonOriginalNullReleasedNominated
import YM.Integration.WilsonOriginalNullReleasedReading
import YM.Integration.WilsonMaxwellThermometerNominatedOrientation
noncomputable section
namespace YM.Integration.WilsonOriginalNullReleasedOrientation
open Function Filter RG Lattice Wilson Source Labels Next.Rank Next.Rank.Price Next.Rank.Atlas
open Next.Rank.Station Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open Spec OPE OPE.Orbits RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize WilsonPositionCapTransport
open WilsonMaxwellThermometerMaximalHead WilsonMaxwellThermometerStationHeads
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G)
local notation "C₀"=>R.family
local notation "road"=>R.family.path.levels


open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph ConnectedActivityE6
open WilsonPositionThermometerGradedReading WilsonMaxwellThermometerNominatedOrientation
/-- A signed maximal row on the actual cutoff inverse. The real external
currency is retained when comparing it with the separately normalized star axis. -/
theorem original (A:Group C₀ 6) (S:Finset (Fin 3))(arm:Fin 3){N p:ℕ}
    (live:A.station.k ≤ N)(home:Opened C₀ (index A (grade arm)) A.station.k p)
    (W:Rep G ((C₀).side A.station.k p))(tier:W.p=(road).budget A.station.k)
    (beta:W.beta=((C₀).path.rep N p A.station.k).beta)
    (c:(C₀).label (index A (grade arm)))(r E:ℝ)(pos:0≤r):
    let d:ℕ:=index A (grade arm)
    let F:=(C₀).labels.level d
    let k:=A.station.k
    let t:=Coat.gStep W.beta/W.p.threshold
    let v:=A.station.wheel.atCut (N,p) (index A (grade arm)) (vector A S arm)
    let ω:=awake C₀ d k N p v
    let raw:=((C₀).factory d N p).terminal.symm v
    let M:=fitting (C:=C₀) d N p k R.makes home live
    let zoom:=Station.mag road A.station.b k
    let fee:=(2:ℝ)^WilsonOriginalAdjacentMicroscopicPrice.height R d*
        invoice (C:=C₀) d k p*stock C₀ k*(C₀).S.a k^d*F.coeffSize ω
    F.coeffSize (c-F.scaled t (M raw)) ≤ E→
    ∀j:F.Index,F.grades j=(d,d/2)→
      ‖(((r/(C₀).S.a k)^d:ℝ):ℂ)*c j -
         (((r*zoom)^d:ℝ):ℂ)*(ladder C₀ (index A (grade arm)) (source C₀ S arm)) j‖ ≤
      (r/(C₀).S.a k)^d*(E+fee)+(r*zoom)^d*deviation R A N p S arm:=by
  classical
  intro d F k t v ω raw M zoom fee paid j cell
  let χ:=(shrink C₀ k N p)^(d/2)/zoom^d
  let u:=ladder C₀ (index A (grade arm)) (source C₀ S arm)
  have shr:t=shrink C₀ k N p:=by change Coat.gStep W.beta/W.p.threshold=_;rw [tier,beta];rfl
  have base:=WilsonOriginalNullReleasedReading.original R d home live W tier beta v c r E pos paid j
  have deg:(F.grades j).2=d/2:=congrArg Prod.snd cell
  have direct:‖(χ:ℂ)*ω j-u j‖ ≤ deviation R A N p S arm:=by
    change _ ≤ ∑l:F.Index,if F.grades l=(d,d/2) then ‖(χ:ℂ)*ω l-u l‖ else 0
    have hs:=Finset.single_le_sum (f:=fun l:F.Index=>if F.grades l=(d,d/2) then ‖(χ:ℂ)*ω l-u l‖ else 0)
      (s:=Finset.univ) (fun l _=>by split <;> positivity) (Finset.mem_univ j)
    simpa only [if_pos cell] using hs
  have zoompos:0<zoom:=Station.mag_pos _ _ _
  have cash:(r*zoom)^d*χ=r^d*t^(F.grades j).2:=by
    dsimp only [χ];rw [deg,shr,mul_pow];field_simp [pow_ne_zero d zoompos.ne']
  have second:‖((r^d*t^(F.grades j).2:ℝ):ℂ)*ω j - (((r*zoom)^d:ℝ):ℂ)*u j‖ ≤
      (r*zoom)^d*deviation R A N p S arm:=by
    rw [←cash,Complex.ofReal_mul,mul_assoc,←mul_sub,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg (mul_nonneg pos zoompos.le) _)]
    exact mul_le_mul_of_nonneg_left direct (pow_nonneg (mul_nonneg pos zoompos.le) _)
  let field:=(((r/(C₀).S.a k)^d:ℝ):ℂ)*c j
  let middle:=((r^d*t^(F.grades j).2:ℝ):ℂ)*ω j
  let named:=(((r*zoom)^d:ℝ):ℂ)*u j
  have tri:‖field-named‖≤‖field-middle‖+‖middle-named‖:=by
    simpa only [dist_eq_norm] using (dist_triangle field middle named)
  exact tri.trans (add_le_add base second)

/-- The public position input already contains the inverse mesh power from the original
microscopic cylinder. At its elected star radius the magnification cancels exactly. -/
theorem landed (A:Group C₀ 6) (S:Finset (Fin 3))(arm:Fin 3){N p:ℕ}
    (live:A.station.k ≤ N)(home:Opened C₀ (index A (grade arm)) A.station.k p)
    (W:Rep G ((C₀).side A.station.k p))(tier:W.p=(road).budget A.station.k)
    (beta:W.beta=((C₀).path.rep N p A.station.k).beta)
    (c:(C₀).label (index A (grade arm)))(r E:ℝ)(radial:Station.gap road A.station.b A.station.k=r):
    let d:ℕ:=index A (grade arm)
    let F:=(C₀).labels.level d
    let k:=A.station.k
    let v:=A.station.wheel.atCut (N,p) (index A (grade arm)) (vector A S arm)
    let raw:=((C₀).factory d N p).terminal.symm v
    let M:=fitting (C:=C₀) d N p k R.makes home live
    let fee:=(2:ℝ)^WilsonOriginalAdjacentMicroscopicPrice.height R d*
        invoice (C:=C₀) d k p*stock C₀ k*(C₀).S.a k^d*F.coeffSize (awake C₀ d k N p v)
    F.coeffSize (c-F.scaled (Coat.gStep W.beta/W.p.threshold) (M raw)) ≤ E→
    ∀j:F.Index,F.grades j=(d,d/2)→
      ‖(((r^d)⁻¹:ℝ):ℂ)*c j - (ladder C₀ (index A (grade arm)) (source C₀ S arm)) j‖ ≤
        (r^d)⁻¹*(E+fee)+deviation R A N p S arm:=by
  intro d F k v raw M fee paid j cell
  let z:=Station.mag road A.station.b k
  have rad:(C₀).S.a k*z=r:=radial
  have rp:0<r:=rad ▸ mul_pos ((C₀).S.a_pos _) (Station.mag_pos _ _ _)
  have units:(C₀).S.a k/r*z=1:=by rw [div_mul_eq_mul_div,rad,div_self rp.ne']
  have mass:(C₀).S.a k/r/(C₀).S.a k=r⁻¹:=by field_simp [rp.ne',((C₀).S.a_pos _).ne']
  have bill:=original R A S arm live home W tier beta c ((C₀).S.a k/r) E
    (div_nonneg ((C₀).S.a_pos _).le rp.le) paid j cell
  change ‖((((C₀).S.a k/r/(C₀).S.a k)^d:ℝ):ℂ)*c j-(((((C₀).S.a k/r)*z)^d:ℝ):ℂ)*
    (ladder C₀ (index A (grade arm)) (source C₀ S arm)) j‖ ≤
      ((C₀).S.a k/r/(C₀).S.a k)^d*(E+fee)+((C₀).S.a k/r*z)^d*deviation R A N p S arm at bill
  simpa only [mass,units,one_pow,Complex.ofReal_one,one_mul,inv_pow] using bill

end YM.Integration.WilsonOriginalNullReleasedOrientation

import YM.Integration.WilsonThermometerOffsetTrajectory
import YM.Integration.WilsonReportingUVReturn

/-! The chosen child graph represents one literal translated microscopic
cylinder against the original Wilson density at every coarse field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOffsetPhysical
open Function Set MeasureTheory Lattice Wilson RG Source Labels RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest MergeProof Accent PhysicalNext.Repeat.Legato
open WilsonPositionSeparatedProfileCenteredBranch WilsonThermometerOffsetTrajectory
open scoped Classical BigOperators
variable {G : Gauge} {C : Family G} {m p N d : ℕ}

def cell (C : Family G) (p m N d : ℕ) (b : Bud C p m)
    (F : Body → Goods G (C.side (m+1) p)) (φ : Body) : Goods G (C.side m p) :=
  blast C.path N p m d (F (headFee C p m b φ) ∘ Lattice.pull 1 (child C p m b))

theorem push {h : C.Makes} {live : m<N}
    {b : Bud C p m} {D : GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    {V : Palette C d →ₗ[ℂ] Tape G (C.side (m+1) p)}
    {W : Palette C d →ₗ[ℂ] Tape G (C.side m p)} {r : Emblems C d}
    (H : WilsonThermometerOffsetGraph.Transfer (D:=D) h live b V W (r m)) (x : Palette C d) :
    pulseOut (W (r m x)) = cell C p m N d b (pulseOut (V x)) := by
  funext φ
  obtain ⟨t,_,cap⟩ := Native.Cap.cost φ (d+2)
  exact (H.travel x φ t cap).exactStep

variable (R : Run G) (N p : ℕ)
def shift (m d : ℕ) (live : m+1≤N) (b : Bud R.family p m)
    (F : Bin G (R.family.side N p)) : Bin G (R.family.side N p) :=
  fun φ => ((R.family.S.block m).val:ℂ)^d • arrangement R N p live F φ b

theorem represent {m d : ℕ} (live : m+1≤N) (b : Bud R.family p m)
    (F : Bin G (R.family.side N p)) (cont : timely F) (φ : Body) :
    cell R.family p m N d b (fun ψ => dyes R.family (m+1) N p live (F ψ)) φ =
      dyes R.family m N p (m.le_succ.trans live) (shift R N p m d live b F φ) := by
  unfold shift
  rw [dye_pitch]
  unfold cell blast
  congr 1
  rw [← covariance R N p live (child R.family p m b) _ (cont _)]
  exact (gust_step R.family.path N p N _ live).symm

def route (m d : ℕ) (sites : ∀ i, Bud R.family p i) :
    (q : ℕ) → m+q≤N → Bin G (R.family.side N p) → Bin G (R.family.side N p)
  | 0,_,F => F
  | q+1,live,F => route m d sites q (by omega) (shift R N p (m+q) d live (sites _) F)

private theorem shifted {m d : ℕ} (live : m+1≤N) (b : Bud R.family p m)
    (F : Bin G (R.family.side N p)) (cont : timely F) :
    timely (shift R N p m d live b F) :=
  fun _ => ((cont _).comp (continuous_pull (G:=G) 1 _)).const_smul _

theorem descend {m base d : ℕ} {D : Rail R.family} {B : ℕ → ℕ → ℝ}
    {V : Sight R.family d p} {r : Emblems R.family d} {sites : ∀i,Bud R.family p i}
    (H : Enrolled R.makes D B base N p d sites V r) (entered : base ≤ m)
    (x : Palette R.family d) (q : ℕ) (live : m+q≤N)
    (F : Bin G (R.family.side N p)) (cont : timely F)
    (top : pulseOut (V (m+q) (Many.point r x N (m+q))) =
      fun φ => dyes R.family (m+q) N p live (F φ)) :
    pulseOut (V m (Many.point r x N m)) = fun φ =>
      dyes R.family m N p (by omega) (route R N p m d sites q live F φ) := by
  induction q generalizing F with
  | zero => exact top
  | succ q ih =>
    apply ih (by omega) _ (shifted R N p live (sites _) F cont)
    rw [← Many.nearpoints r x (m+q)]
    calc
      _ = _ := push (r:=r) (H.follows (m+q) (by omega) (by omega)) (Many.point r x N (m+q+1))
      _ = _ := (congrArg (cell R.family p (m+q) N d (sites _)) top).trans
        (funext (represent R N p live _ F cont))

private theorem same (m d : ℕ) (sites : ∀ i,Bud R.family p i)
    (i j : ℕ) (eq : i=j) (hi : m+i≤N) (hj : m+j≤N) (F : Bin G (R.family.side N p)) :
    route R N p m d sites i hi F = route R N p m d sites j hj F := by
  cases eq; rfl

theorem original {m base d : ℕ} {D : Rail R.family} {B : ℕ → ℕ → ℝ}
    {V : Sight R.family d p} {r : Emblems R.family d} {sites : ∀i,Bud R.family p i}
    (H : Enrolled R.makes D B base N p d sites V r) (entered : base ≤ m) (live : m ≤ N)
    (starts : ∀ e ≤ d, R.family.ref e ≤ N) (t : Letter d) (x : R.family.label (kept t)) :
    pulseOut (V m (Many.point r (chunk t ((R.family.factory (kept t) N p).terminal.symm x)) N m)) =
      fun φ => dyes R.family m N p live
        (route R N p m d sites (N-m) (by omega) (WilsonReportingUVReturn.raw R N p t x) φ) := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le live
  rw [same R _ p m d sites (m+q-m) q (by omega) (by omega) le_rfl]
  apply descend R _ p H entered _ q le_rfl _ (WilsonReportingUVReturn.raw_smooth R _ p t x)
  rw [Many.point_here,H.starts]
  exact WilsonReportingUVReturn.incoming R _ p t x starts

end YM.Integration.WilsonThermometerOffsetPhysical
end

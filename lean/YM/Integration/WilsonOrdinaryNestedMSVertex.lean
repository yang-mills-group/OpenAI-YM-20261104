import YM.Integration.WilsonOrdinaryNestedMSPoint
import YM.Integration.WilsonPublicOutputRows
import YM.Integration.WilsonOrdinaryNestedCourse
import YM.Integration.WilsonCenteredNestedProjectedShadow

/-! A vertex of the nested program in the actually calibrated public frame.
Rescaling its physical inputs and testing its complete output preserves the
precise paid engineering factor even if lower grades mix under the frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOrdinaryNestedMSVertex
open Function Spec Table PhysMS Climb RG17 PhysicalNext.Repeat.Legato OPE OPE.Orbits OPE.Orbits.Reader
open OPE.Nesting OPE.Nesting.Atom WilsonPositionHomogeneousFrame WilsonCenteredNestedProgram
open Maxwell XSpace XSpace.Normalize Pert Pert.Position MS MS.Land MS.Menus MS.Theater
open FVA2 FVA2.Register FVA2.Scale WilsonCenteredNestedProjectedShadow
open scoped Classical BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S) (Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
local notation "pub" => homogeneous F J Z

def placed {n:ℕ} (r:ℝ) (x:Fin n→E4) (o:E4) : Points n :=
  WithLp.toLp 2 fun i=> r⁻¹ • (x i-o)

def incoming {n:ℕ} (r:ℝ) (v:Fin n→S.Tag) (i:Fin n) : (Bel R.family.book).Field (degrees v i) :=
  (pub r (v i).1).symm (v i).2

def raised {n:ℕ} (r:ℝ) (v:Fin n→S.Tag) (i:Fin n) : (Bel R.family.book).Field (degrees v i) :=
  (r:ℂ)^(v i).1 • incoming F J Z r v i

def ear (r:ℝ) (m:ℕ) (c:Q.channels m) (a:Free R.family m) : ℂ :=
  read F Q m m c (pub r m a)

def program (q:ℕ) : Rule F Q:=fun _ m c r θ x v o=>
  ear F Q J Z r m c (WilsonOrdinaryNestedMSPoint.field Z M ν R.family (degrees v) m
    (incoming F J Z r v) (placed r x o) q θ)

variable {n:ℕ}

theorem geometry (r:ℝ) (rp:0<r) (x:Fin n→E4) (o:E4) (i:Fin n) :
    r • placed r x o i=x i-o := by
  change r • (r⁻¹ • (x i-o))=_
  rw [smul_smul,mul_inv_cancel₀ rp.ne',one_smul]

theorem physical (m:ℕ) (r:ℝ) (rp:0<r) (x:Fin n→E4) (o:E4) (v:Fin n→S.Tag) :
    WilsonPublicOutputRows.packet F pub Q m (degrees v) (raised F J Z r v) r (placed r x o) =
      (∏i,(r:ℂ)^(v i).1) • Q.packet m x (voices v) o := by
  have pos : (fun i=>r • placed r x o i) = fun i=>x i+-o :=funext fun i=>geometry r rp x o i
  have restore : Frame.born pub r (raised F J Z r v) =
      fun i=>(r:ℂ)^(v i).1 • voices v i := by
    funext i
    change pub r (v i).1 ((r:ℂ)^(v i).1 • (pub r (v i).1).symm (v i).2) = _
    rw [map_smul,LinearEquiv.apply_symm_apply]
    rfl
  unfold WilsonPublicOutputRows.packet Reader.packet
  rw [pos,Finset.smul_sum]
  change ∑j : Fin (m+1),_ = _
  erw [restore]
  apply Finset.sum_congr rfl
  intro j _
  rw [MultilinearMap.map_smul_univ,map_smul]
  have move:=Q.fresh_transport (m:=j.val) (x:=x) (o:=o) (v:=voices v) (-o)
  simp only [add_neg_cancel] at move
  rw [move]

def residual (m:ℕ) (c:Q.channels m) (q:ℕ) (r θ:ℝ) (x:Fin n→E4) (o:E4) (v:Fin n→S.Tag) : ℂ :=
  let z:=placed r x o
  let a:=raised F J Z r v
  let current:=WilsonPublicOutputRows.packet F pub Q m (degrees v) a r z
  let target:=WilsonOrdinaryNestedMSPoint.field Z M ν R.family (degrees v) m a z q θ
  ear F Q J Z r m c ((pub r m).symm current-target) / (r:ℂ)^m

theorem signed (m:ℕ) (c:Q.channels m) (q:ℕ) (r θ:ℝ) (rp:0<r)
    (x:Fin n→E4) (o:E4) (v:Fin n→S.Tag) :
    residual F Q J Z M ν m c q r θ x o v =
    ((∏i,(r:ℂ)^(v i).1)/(r:ℂ)^m) *
      (express Q m c x v o - program F Q J Z M ν q n m c r θ x v o) := by
  dsimp only [residual]
  rw [physical F Q J Z _ _ rp]
  unfold program ear
  simp only [map_sub,LinearEquiv.apply_symm_apply]
  rw [←show (fun i=>(r:ℂ)^(v i).1 • incoming F J Z r v i)=raised F J Z r v from rfl]
  erw [WilsonOrdinaryNestedMSPoint.multi]
  simp only [map_smul,smul_eq_mul]
  rw [on_packet F Q m m le_rfl c x (voices v) o]
  unfold express
  ring

theorem relative (m:ℕ) (c:Q.channels m) (q:ℕ) (r θ:ℝ) (rp:0<r)
    (x:Fin n→E4) (o:E4) (v:Fin n→S.Tag) :
    ‖express Q m c x v o - program F Q J Z M ν q n m c r θ x v o‖ =
      (r^m / ∏i,r^(v i).1) * ‖residual F Q J Z M ν m c q r θ x o v‖ := by
  rw [signed F Q J Z M ν _ _ _ _ _ rp,norm_mul,norm_div,norm_prod]
  simp only [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos rp]
  have ne : (∏i,r^(v i).1)≠0:=Finset.prod_ne_zero_iff.mpr fun i _=>pow_ne_zero _ rp.ne'
  field_simp [ne]

end YM.Integration.WilsonOrdinaryNestedMSVertex

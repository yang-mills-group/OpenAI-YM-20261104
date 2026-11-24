import YM.Integration.WilsonMeasuredPublicFamily
import YM.Integration.WilsonMeasuredPublicLayout

/-! Two pools of one public hierarchy give a true microcell between the source support and the physical separation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicClearance
open Function Filter Set MeasureTheory Finset Table Lattice Wilson RG Cells Extraction Spec Climb OPE
open GapsContact GapsContact.Seams PhysicalNext.Repeat.Legato
open Maxwell Maxwell.Free RG05Readout Source Trace.Pilot PhysMS Frame GapsContact.Stamps
open FVA2 FVA2.Register MS MS.Land Trace.Terrace MergeProof.East
open WilsonThermometerUnitFilingFourPoolShell WilsonThermometerUnitFilingFourPoolClock
open WilsonMeasuredPublicSlots WilsonMeasuredPublicBank
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (l : Ultrafilter (ℕ×ℕ)) {z : Trace.Terrace.Arch R.family}
    {H : (Bel R.family.book).Hierarchy}

def deep (T : ℕ) := 3*T+5

structure Book (D T n : ℕ) (δ r : ℝ) where
  bank : Bank F l D (radius z (deep T) r) (dock (radius z (deep T) r)^T)
  micro : ℕ
  before : micro≤bank.m
  slack : 6*(n:ℝ)*R.family.S.a bank.m < R.family.S.a micro
  small : R.family.S.a micro < δ*r
  wallet : 1≤dock (radius z (deep T) r)

private theorem widths {D : ℕ} {s b : ℝ} (K : Bank F l D s b) :
    s < b*R.family.S.a K.j ∧ R.family.S.a K.m < s*b ∧ K.m≤K.j := by
  let Q:=K.department 0 (Nat.zero_le _)
  obtain ⟨j,m⟩:=Q.dated 0
  let L:=Q.print 0
  exact ⟨by simpa only [L,j] using L.breadth,by simpa only [L,m] using L.front,
    by simpa only [L,j,m] using L.fore⟩

private theorem monotone_fee {x C : ℝ} {T U:ℕ} (pos:0≤x) (c:1≤C)
    (le:T≤U) (price:x^U≤C) : x^T≤C := by
  rcases le_total x 1 with h|h
  · exact (pow_le_one₀ pos h).trans c
  · exact (pow_le_pow_right₀ h le).trans price

theorem original (simple:G.Simple) (bliss:Bliss F l z H) (D:ℕ) :
    ∃T:ℕ,∀ (n:ℕ) (δ:ℝ),0<δ → ∀ᶠ r in trail,Nonempty (Book F l (z:=z) D T n δ r) := by
  obtain ⟨T,pools⟩:=WilsonThermometerUnitFilingFourPool.original F simple bliss D
  let U:=deep T
  obtain ⟨C,hC,first⟩:=invoice F simple bliss T
  obtain ⟨B,hB,second⟩:=invoice F simple bliss U
  have limit:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have vanish:=limit.conforms simple
  have high:T≤U:=by dsimp [U,deep];omega
  refine ⟨T,?_⟩
  intro n δ hδ
  have cheap : Tendsto (fun r=>C*(wilson z r)^4) trail (𝓝 0) := by
    simpa using (vanish.pow 4).const_mul C
  have tight : Tendsto (fun r=>(6*((n:ℝ)+1)*B*C)*(wilson z r)^10) trail (𝓝 0) := by
    simpa using (vanish.pow 10).const_mul (6*((n:ℝ)+1)*B*C)
  have wake : ∀ᶠ u:ℝ in trail,1≤dock u := by
    have far:Tendsto LogV trail atTop:=Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    filter_upwards [far.eventually_ge_atTop 0] with a due
    dsimp [dock]
    linarith
  filter_upwards [(smaller F simple bliss T).eventually pools,(smaller F simple bliss U).eventually pools,
    (smaller F simple bliss U).eventually wake,first,second,limit.positive,self_mem_nhdsWithin,
    cheap.eventually (gt_mem_nhds hδ),tight.eventually (gt_mem_nhds zero_lt_one)] with r lo hi unit
      paid wide gp rp decays ratio
  change 0<r at rp
  let g:=wilson z r
  let s:=radius z T r
  let v:=radius z U r
  let Y:Bank F l D s (dock s^T):=(purchased F l lo.choose_spec.choose_spec).choose
  let W:Bank F l D v (dock v^T):=(purchased F l hi.choose_spec.choose_spec).choose
  obtain ⟨yLow,yHigh,yj⟩:=widths F l Y
  obtain ⟨_,wHigh,_⟩:=widths F l W
  have money : dock v^T*g^(2*T)≤B := by
    have p : (dock v*g^2)^U≤B := by simpa only [mul_pow,← pow_mul] using wide.2
    simpa only [mul_pow,← pow_mul] using monotone_fee (mul_nonneg wide.1.le (sq_nonneg g)) hB high p
  have physical : R.family.S.a Y.m < δ*r := by
    calc _ < s*dock s^T := yHigh
         _ = r*((dock s^T*g^(2*T))*g^4) := by dsimp [s,radius,g];rw [pow_add];ring
         _ ≤ r*(C*g^4) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right paid.2 (by positivity)) rp.le
         _ < δ*r := by rw [mul_comm δ];exact mul_lt_mul_of_pos_left decays rp
  have scale : r*g^(4*T+4)<C*R.family.S.a Y.m := by
    calc _ = s*g^(2*T) := by dsimp [s,radius,g];rw [show 4*T+4=2*T+4+2*T by omega,pow_add];ring
         _ < (dock s^T*R.family.S.a Y.j)*g^(2*T) := mul_lt_mul_of_pos_right yLow (pow_pos gp _)
         _ = (dock s^T*g^(2*T))*R.family.S.a Y.j := by ring
         _ ≤ C*R.family.S.a Y.m := mul_le_mul paid.2 (R.family.S.strictAnti.antitone yj)
                     (R.family.S.a_pos _).le (zero_le_one.trans hC)
  have narrow : R.family.S.a W.m < B*(r*g^(4*T+4))*g^10 := by
    calc _ < v*dock v^T := wHigh
         _ = ((dock v^T*g^(2*T))*(r*g^(4*T+4)))*g^10 := by
           dsimp [v,U,deep,radius,g]
           rw [show 2*(3*T+5)+4= 2*T+(4*T+4)+10 by omega,pow_add,pow_add];ring
         _ ≤ B*(r*g^(4*T+4))*g^10 := by gcongr
  have scaled : (6*((n:ℝ)+1))*R.family.S.a W.m ≤ ((6*((n:ℝ)+1)*B*C)*g^10)*R.family.S.a Y.m := by
    calc _ ≤ (6*((n:ℝ)+1))*(B*(r*g^(4*T+4))*g^10) := mul_le_mul_of_nonneg_left narrow.le (by positivity)
         _ ≤ (6*((n:ℝ)+1))*(B*(C*R.family.S.a Y.m)*g^10) := by gcongr
         _ = _ := by ring
  have smallerWall : (6*((n:ℝ)+1))*R.family.S.a W.m < R.family.S.a Y.m :=
    scaled.trans_lt (by simpa only [one_mul] using mul_lt_mul_of_pos_right ratio (R.family.S.a_pos Y.m))
  have one:1≤6*((n:ℝ)+1) := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have earlier : Y.m≤W.m := by
    by_contra! bad
    have later:=R.family.S.strictAnti bad
    have root : R.family.S.a W.m ≤ (6*((n:ℝ)+1))*R.family.S.a W.m := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right one (R.family.S.a_pos W.m).le
    exact (not_lt_of_ge (later.le.trans root)) smallerWall
  exact ⟨⟨W,Y.m,earlier,(mul_le_mul_of_nonneg_right (by linarith : 6*(n:ℝ)≤6*((n:ℝ)+1))
    (R.family.S.a_pos W.m).le).trans_lt smallerWall,physical,unit⟩⟩

end YM.Integration.WilsonMeasuredPublicClearance

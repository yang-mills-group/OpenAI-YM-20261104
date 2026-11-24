import YM.Integration.WilsonMeasuredPublicClearance
import YM.Integration.WilsonMeasuredPublicMesh

/-! Public fields at r and r g(r)^(-A) on one numerical original preframe, with a shared separated-cell clearance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicDocket
open Function Filter Set MeasureTheory Finset Table Spec Climb Maxwell Maxwell.Free RG05Readout
open Lattice Wilson RG Source Extraction OPE Trace.Pilot PhysMS Frame Cells
open GapsContact GapsContact.Seams GapsContact.Stamps PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land Trace.Terrace MergeProof.East
open WilsonPositionHomogeneousFrame WilsonThermometerUnitFilingFourSquare
open WilsonThermometerUnitFilingFourPoolShell WilsonThermometerUnitFilingFourPoolClock
open WilsonMeasuredPublicBank WilsonMeasuredPublicSlots WilsonMeasuredPublicClearance WilsonMeasuredPublicMesh
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ→tower S) (Z:WilsonPrescription G)
    {l : Ultrafilter (ℕ×ℕ)} {z : Trace.Terrace.Arch R.family} {H : (Bel R.family.book).Hierarchy}
    {I:Type} [Fintype I]
local notation "a" => R.family.S.a

/-- All lengths here are original physical lengths. The common microcell and the
source stencil wages have already been bought before any cutoff, site or period. -/
theorem located {D T count:ℕ} {δ r:ℝ} (board : WilsonMeasuredPublicClearance.Book F l (z:=z) D T count δ r)
    (size:Fintype.card I ≤ count) {coarse packet N p:ℕ} (outerSeat:coarse≤packet)
    (room:10*a packet<a coarse) (floor:δ*r≤a packet) (fresh:board.bank.m≤N)
    {m:I→ℕ} (walls:∀i,board.bank.m≤ m i) (live:∀i,m i≤N)
    (anchor:Site (R.family.side N p)) (u:I→Site (R.family.side N p)) (displacement:I → Cover)
    (address:∀i,u i=wrap (R.family.side N p) (displacement i)+anchor)
    (reach:∀i k,a N*((displacement i k).natAbs:ℝ) < 3*a packet)
    (apart:∀i j,i≠j→δ*r≤ a N*(separation (u i) (u j):ℝ)) :
    Nonempty (WilsonMeasuredPublicLayout.Placed R.family m u) := by
  have before : packet≤board.micro := by
    by_contra! bad
    exact (not_lt_of_ge (board.small.le.trans floor)) (R.family.S.strictAnti bad)
  have edge:=before.trans (board.before.trans fresh)
  apply WilsonMeasuredPublicLayout.original R.family outerSeat before board.before fresh walls live anchor u displacement address _ room _ _
  · intro i k
    apply (Nat.cast_lt (α:=ℝ)).mp
    apply lt_of_mul_lt_mul_left _ (R.family.S.a_pos N).le
    have scale : a N*(Cells.span R.family.S edge p:ℝ)=a packet := R.family.S.embeds_scale _
    rw [Nat.cast_mul,Nat.cast_ofNat,← mul_left_comm,scale]
    exact reach i k
  · have hs : (Fintype.card I:ℝ)≤count := by exact_mod_cast size
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤6))
      (R.family.S.a_pos _).le).trans_lt board.slack
  · exact fun i j ne=>board.small.trans_le (apart i j ne)

variable (d A:I→ℕ) (v:∀i,RG17.Free R.family (d i)) (D:ℕ) (cap:∀i,d i≤D)
local notation "target" i:max r:max => homogeneous F J Z (outer z (A i) r) (d i) (v i)
local notation "height" T:max r:max => radius z (deep T) r
local notation "wage" T:max i:max r:max => dock (height T r)^T * Ascent.cost F (d i) (height T r) (target i r)
local notation "exponent" T:max i:max => WilsonThermometerUnitFilingFourPoolBill.exponent (deep T) (A i) (d i)

theorem original (simple:G.Simple) (bliss:Bliss F l z H) (lead:Leading F J)
    (frame:∀e:ℕ,∀ᶠ r in trail,Frame.obedient F H (J r) e) :
    ∃ (T:ℕ) (K:I→ℝ), (∀i,0≤K i) ∧ ∀ (count:ℕ) (δ:ℝ),0<δ→∀ᶠ r in trail,
    ∃ board:WilsonMeasuredPublicClearance.Book F l (z:=z) D T count δ r,
    let L (i:I) := ((board.bank.department (d i) (cap i)).print (target i r))
    (∀i,wage T i r*(wilson z r)^(exponent T i) ≤ K i) ∧
    (∀i N p,board.bank.j<N→Next.UVStress.quota R.family (d i) board.bank.j N p ((L i).arm.source (N,p))*
        (wilson z r)^(exponent T i) ≤ a board.bank.j^(d i)*K i) ∧
    (∀n (i:Fin n→I) (t:Test n),Tendsto (fun q:ℕ×ℕ=>Order.smears R.family q.1 q.2 (tokens (fun j=>L (i j)) q) t)
      (l:Filter _) (𝓝 (t.applyTo (fun x=>S.classMoment S (fun j=>d (i j)) x (fun j=>target (i j) r))))) ∧
    (∀n (i:Fin n→I) (t:Test n),(∀ᶠ q:ℕ×ℕ in f.fuse, Admits (fun j=>L (i j)) t q) →
       ‖t.applyTo (fun x=>S.classMoment S (fun j=>d (i j)) x (fun j=>target (i j) r))‖ *
         (∏j,(wilson z r)^(exponent T (i j))) ≤ (∫x:Points n,‖t x‖)*(∏j,K (i j))) ∧
    ∀ᶠ q:ℕ×ℕ in f.fuse, ∀keep:Finset I,WilsonMeasuredPublicRough.Offers (fun i:keep=>L i.1) q := by
  obtain ⟨T,sale⟩:=WilsonMeasuredPublicClearance.original F l simple bliss D
  choose K pos cash using fun i=>WilsonThermometerUnitFilingFourPoolBill.original F J Z simple bliss lead frame
     (deep T) (A i) (d i) (v i)
  refine ⟨T,K,pos,fun count δ hp=>?_⟩
  filter_upwards [sale count δ hp,eventually_all.mpr cash,
    (wilson_link F simple bliss.budgets bliss.keen bliss.lies).positive] with r sold price gp
  let board:=sold.some
  let L (i:I) := (board.bank.department (d i) (cap i)).print (target i r)
  have width:dock (height T r)^T≤dock (height T r)^deep T :=
    pow_le_pow_right₀ board.wallet (by dsimp [deep];omega)
  have fees (i:I) : wage T i r*(wilson z r)^(exponent T i) ≤ K i := by
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right width (Ascent.cost_pos ..))
      (pow_nonneg gp.le _)).trans (price i)
  refine ⟨board,fees,?_,?_,?_,?_⟩
  · intro i N p live
    have ij:=((board.bank.department (d i) (cap i)).dated (target i r)).1
    have h:=(L i).numerical N p (ij.symm ▸ live)
    rw [ij] at h
    refine (mul_le_mul_of_nonneg_right h (pow_nonneg gp.le _)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (fees i) (pow_nonneg (R.family.S.a_pos _).le _)
  · exact fun n i t=>WilsonMeasuredPublicCopies.smooth bliss.lies (fun j=>L (i j)) t
  · intro n i t admit
    have priced:=WilsonMeasuredPublicMesh.continuum (fun j=>L (i j)) bliss.lies t admit
    have restores : 0≤∏j,(wilson z r)^(exponent T (i j)) := prod_nonneg fun _ _=>pow_nonneg gp.le _
    apply (mul_le_mul_of_nonneg_right priced restores).trans
    rw [mul_assoc,← prod_mul_distrib]
    apply mul_le_mul_of_nonneg_left _ (integral_nonneg fun _=>norm_nonneg _)
    exact prod_le_prod (fun j _=>mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans board.wallet) _)
      (Ascent.cost_pos ..)) (pow_nonneg gp.le _)) (fun j _=>fees (i j))
  · exact eventually_all.mpr fun (keep:Finset I)=>WilsonMeasuredPublicRough.original (fun i:keep=>L i.1)

end YM.Integration.WilsonMeasuredPublicDocket

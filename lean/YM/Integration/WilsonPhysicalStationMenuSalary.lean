import YM.Integration.WilsonPhysicalAbsoluteVaneMaster
import YM.Integration.WilsonMasterCoordinatePrice
import YM.Integration.WilsonIndependentMeasuredFaceSalary

/-! The total variation of the signed weak reference menu on the actual N-vacuum,
before applying a physical, thermal or spatial error estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMenuSalary
open Function Filter Finset Spec Climb Table PhysMS Trace.Pilot Trace.Target Extraction
open PhysicalNext.Repeat.Legato Next.Rank Next.Rank.East Next.Rank.Station Further.CorrectedLift
open MergeProof MergeProof.East Next.Rank.Tapes Next.Rank.Price Perch Glimmer Atlas
open OPE Next.Extract RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonOriginalTwoFlatPublicBooks (Book)
open scoped Classical BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S){H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
  {D T:ℕ}{r:ℝ}(B:Book F (l:=l) H arch D T r)

def height (d:ℕ):ℕ:=Finset.univ.sup (fun i:(R.family.labels.level d).Index=>((R.family.labels.level d).grades i).2)

theorem scale {N p h b:ℕ}(top:B.W.k≤N):
    ‖(WilsonPhysicalStationSignedBlock.scale R B.W N p h b)⁻¹‖≤(2:ℝ)^b:=by
  let k:=B.W.k
  let clock:=R.family.path.levels
  have heat:shrink R.family k N p≤2:=by
    have raw:=WilsonMasterCoordinatePrice.threshold R.makes (N:=N) (p:=p) top
    rw [(R.makes.wilson.represents N p k top).vac] at raw
    exact raw
  have low:0<shrink R.family k N p:=shrink_pos R.family R.makes top p
  have monitor:1≤clock.clock.monitor k:=by
    rw [Atlas.fire_bill clock k]
    exact Glimmer.costed _ _ zero_le_one
  have increase:1 ≤ mag clock B.W.b k:=Real.one_le_rpow monitor (by linarith [B.checked.high.1])
  have good:‖(WilsonPhysicalStationSignedBlock.scale R B.W N p h b)⁻¹‖=
      ((mag clock B.W.b k)^h)⁻¹*(shrink R.family k N p)^b:=by
    simp [WilsonPhysicalStationSignedBlock.scale,clock,k,abs_of_pos (mag_pos R.family.path.levels B.W.b B.W.k),
      abs_of_pos (shrink_pos R.family R.makes top p),mul_comm]
  rw [good]
  exact (mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ (one_le_pow₀ increase)) (pow_nonneg low.le _)).trans
    (by simpa using pow_le_pow_left₀ low.le heat b)

def weight (d:Fin (D+1))(x:(Bel R.family.book).Field d)(N p:ℕ)
    (i:(R.family.labels.level d).Index):ℂ:=
  (ladder R.family d x) i*(WilsonPhysicalStationSignedBlock.scale R B.W N p
    ((R.family.labels.level d).grades i).1 ((R.family.labels.level d).grades i).2)⁻¹

theorem original {N p:ℕ}(top:B.W.k≤N)(d:Fin (D+1))(x:(Bel R.family.book).Field d):
    ∑i,‖weight F B d x N p i‖≤(2:ℝ)^(height (R:=R) d)*(R.family.labels.level d).coeffSize (ladder R.family d x):=by
  unfold weight Labels.Frame.coeffSize
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,mul_comm ((2:ℝ)^_)]
  exact mul_le_mul_of_nonneg_left ((scale F B top).trans
    (pow_le_pow_right₀ one_le_two (Finset.le_sup (f:=fun j=>(R.family.labels.level d).grades j |>.2) hi))) (norm_nonneg _)

theorem roster {I:Type*}[Fintype I]{ρ:I→ℝ}(books:(i:I)→Book F (l:=l) H arch D T (ρ i))
    (d:I→Fin (D+1))(x:∀i,(Bel R.family.book).Field (d i)){N p:ℕ}(live:∀i,(books i).W.k≤N):
    ∑b:((i:I)→(R.family.labels.level (d i)).Index),‖∏i,weight F (books i) (d i) (x i) N p (b i)‖≤
      ∏i,(2:ℝ)^(height (R:=R) (d i))*(R.family.labels.level (d i)).coeffSize (ladder R.family (d i) (x i)):=by
  simp only [norm_prod]
  rw [← Fintype.prod_sum (fun i:I=>fun b:(R.family.labels.level (d i)).Index=>‖weight F (books i) (d i) (x i) N p b‖)]
  exact Finset.prod_le_prod (fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _)
    (fun i _=>original F (books i) (live i) (d i) (x i))

end YM.Integration.WilsonPhysicalStationMenuSalary

import YM.Integration.WilsonVacuumPreResetFiniteHeatHistory
import YM.Integration.WilsonVacuumPreResetWindingWindow
import YM.Integration.WilsonMarkedIndependentBareWinding
import YM.Integration.WilsonMarkedIndependentPhysicalIntake

/-! Restoration of the native rooted spatial receipt at the original
fine side. Translation is qualitative. The new rooted tariff comes
from the cutoff-uniform discrepancy and the independently issued shelf. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteHeatSpatial
open Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open Next.Foundations PhysicalNext.Repeat.Legato
open WilsonVacuumPreResetFiniteHeatTable WilsonVacuumPreResetFiniteHeatScale
open WilsonMarkedIndependentPhysicalIntake
open scoped Classical BigOperators Topology
variable {G:Gauge} {e:ℕ}

/-- The true finite translation laws hold on every side. Their qualitative
induction may choose its widths after the cutoff. -/
theorem translations (R:Run G)(Q:Realm G (e+1) Credit.leanC)
    (draws:Q.draws=R.family.path.levels)(O:Q.paid=R.metals.O)
    (N m:ℕ)(here:Q.anchor ≤ m)(live:m ≤ N):
    ∀n:Side,∀a,0<a→a ≤ e→∀r,r+1 ≤ a+2→stroll ((story R.family.path.levels R.metals.O N m).1 n a (r+1)):=by
  obtain ⟨C,hC,bare⟩:=WilsonMarkedIndependentBareWinding.original R e (s:=1) zero_lt_one
  have down(d:ℕ):∀j,Q.anchor ≤ j→j+d=N→∃s B:ℝ,0<s ∧ 1 ≤ B ∧
      WilsonFiniteVacuumWindingDate.positive Q.draws Q.paid e N j s B:=by
    induction d with
    | zero =>
      intro j _ tag
      have eqj:j=N:=by omega
      rw [eqj,draws,O]
      exact ⟨1,C,zero_lt_one,hC,bare N⟩
    | succ d ih =>
      intro j hj tag
      obtain ⟨s,B,hs,hB,input⟩:=ih (j+1) (by omega) (by omega)
      obtain ⟨D,c,t,hc,ht,paid⟩:=WilsonFiniteVacuumWindingReset.original Q hj hs
      exact ⟨t,c*B^D,ht,one_le_mul_of_one_le_of_one_le hc (one_le_pow₀ hB),
        fun n a _ ha r _=>paid N (by omega) B hB input n a ha (r+1)⟩
  obtain ⟨s,B,_,_,pos⟩:=down (N-m) m here (by omega)
  rw [draws,O] at pos
  exact fun n a hp ha r hr=>(pos n a hp ha r hr).strollT

/-- At the actual reporting birth, one independently funded folded shelf
and the full finite table give a rooted receipt uniformly before both regulators. -/
theorem filed (R:Run G)(Q:Realm G (e+1) Credit.leanC)
    (draws:Q.draws=R.family.path.levels)(O:Q.paid=R.metals.O)(clock:Q.y=zz R.family.path.levels)
    (j:ℕ)(hj:Q.anchor ≤ j)
    (received:∀N p:ℕ,j+1 ≤ N→table R.family.path.levels R.metals.O e N (j+1)
      (R.family.side (j+1) p) (rate R.family.path.levels (j+1) p)):
    ∃s B:ℝ,0<s ∧ 1 ≤ B ∧ ∀N p:ℕ,j+1 ≤ N→PositiveAt R.family.path.levels R.metals.O e N (j+1)
      (R.family.side (j+1) p) s B:=by
  let L:=R.family.path.levels
  let z:=zz L (j+1)
  have hz:1 ≤ z:=by simpa only [clock] using Q.depth (j+1) (by omega)
  have hzp:0<z:=by linarith
  let H:=holt Q j hj 1 zero_lt_one
  let C:=admissionA (Q.mint j hj).gear e*Q.cash (costXV G e Credit.leanC) j
  have hc:1 ≤ C:=one_le_mul_of_one_le_of_one_le (admissionSeal _) (Credit.purchase _ (Q.depth _ hj))
  let s:=min H.s (1/(64*z))
  have hs:0<s:=lt_min H.h (by positivity)
  refine ⟨s,C+1,hs,by linarith,?_⟩
  intro N p hN a ha0 ha r hr
  let n:=R.family.side j p
  let f:=R.family.side (j+1) p
  have geometry:f=n*(loose Q.draws j).L:=by
    rw [draws]
    exact Subtype.ext (R.family.path.levels.clock.op j p).sizes
  let phase:=cloVent Q j N n hj (by omega) 1 zero_lt_one
  have baseline:=phase.fare a ha (r+1)
  change Sight (emera (actionW Q.draws Q.paid N (j+1)) (n*(loose Q.draws j).L) a (r+1))
    (actionW Q.draws Q.paid N (j+1) a (r+1)) H.s C at baseline
  have named:actionW Q.draws Q.paid N (j+1)=actionW L R.metals.O N (j+1):=by rw [draws,O]
  rw [←geometry,named] at baseline
  have at_s:=baseline.mono (min_le_left H.s (1/(64*z)))
  let P:=(story L R.metals.O N (j+1)).1 f a (r+1)
  let F:=actionW L R.metals.O N (j+1) a (r+1)
  let T:=emera (actionW L R.metals.O N (j+1)) f a (r+1)
  have step:stroll P:=translations R Q draws O N (j+1) (by omega) hN f a ha0 ha r hr
  have h₄:4*s ≤ 1/(16*z):=calc
    4*s ≤ 4*(1/(64*z)):=mul_le_mul_of_nonneg_left (min_le_right ..) (by norm_num)
    _ = _:=by field_simp; ring
  have tiny(x):|pruce (P-T) x| ≤ 1*1*Real.exp (-s*(4*f.val)):=by
    change |P x-T x| ≤ _
    have orig:=received N p hN a ha (r+1) x
    apply orig.trans
    rw [one_mul,one_mul]
    apply Real.exp_le_exp.mpr
    change -(f.val:ℝ)/(16*z) ≤ -s*(4*f.val)
    have pay:=mul_le_mul_of_nonneg_right h₄ (Nat.cast_nonneg (α:=ℝ) f.val)
    calc
      -(f.val:ℝ)/(16*z) = -((1/(16*z))*(f.val:ℝ)):=by ring
      _ ≤ -((4*s)*(f.val:ℝ)):=neg_le_neg pay
      _ = _:=by ring
  have paid:=WilsonVacuumPreResetWindingWindow.submitted s 1 C 1 1 hs.le zero_le_one zero_lt_one
    (by norm_num) P T F step at_s tiny
  simpa only [div_one,one_smul,add_sub_cancel] using paid

end YM.Integration.WilsonVacuumPreResetFiniteHeatSpatial

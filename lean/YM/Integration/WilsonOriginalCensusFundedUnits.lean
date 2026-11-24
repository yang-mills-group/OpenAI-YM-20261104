import YM.Integration.WilsonOriginalCensusUnitMenu
import YM.Integration.WilsonOriginalCensusAllUnits

/-! The full independently prescribed Wilson basis sum equals the one booked positive census. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFundedUnits
open Function Finset Lattice RG Wilson Source Labels
open MergeProof MergeProof.Accent MergeProof.East MergeProof.Replicums
open PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open WilsonThermometerDeclaredSeeds WilsonReceivedFixedDigitCanonical WilsonReceivedFixedDigitHistory
open WilsonIndependentCollarOrbitalBasisPayment WilsonIndependentCollarPaidWindingPanel
open WilsonOriginalCensusUnitVerse (observed)
open WilsonOriginalCensusUnitLamp (fee)
open WilsonOriginalCensusPositiveSites (Group names part)
open WilsonOriginalCensusPositiveDose (reduced)
open WilsonOriginalCensusUnitDose (enrolled)
open scoped BigOperators Classical

variable {G:Gauge}{n:ℕ}(R:Run G)(k:Fin n→ℕ){h:Fin n→ℕ}(κ:(j:Fin n)→Knob (h j))(pt:Fin n→Chamber)
    (N K i:ℕ)(digit:Digits R.family.path.levels (Fin n))(o:Fin n → Cover)(A:Case h)

def ordinary (s:Finset (Fin n))(a:Choices R k s):Era G ℝ:=
  observed (fixed R k κ pt N K i digit (enrolled R k s a) o) A s

theorem receipt (simple:G.Simple)(called:i≤K)(live:K≤N)(s:(Replicum.Bud (Fin n)).Mode)(a:Choices R k s.val)
    (paid:∀j:s.val,k j=0 → a j=.inl ()):
    let e:=names k
    ordinary R k κ pt N K i digit o A s.val a=(∏j∈s.val.filter (fun j=>k j=0),fee κ pt A j) •
      ordinary R (k ∘ e) (h:=h ∘ e) (fun j=>κ (e j)) (pt ∘ e) N K i (fun d=>digit d ∘ e) (o ∘ e)
        (fun j=>A (e j)) (part k s).val (reduced R k s a):=by
  intro e
  let q:=enrolled R k s.val a
  have approved:∀j∈s.val,k j=0 → q j=.inl ():=by
    intro j hj zero
    simpa only [q,enrolled,dif_pos hj] using paid ⟨j,hj⟩ zero
  have result:=WilsonOriginalCensusAllUnits.original R k κ pt q simple N K i called live digit o A s approved
  have docket:(fun j=>q (e j))=enrolled R (k ∘ e) (part k s).val (reduced R k s a):=
    funext (WilsonOriginalCensusUnitMenu.enrollment R k s a)
  change ordinary R k κ pt N K i digit o A s.val a=_ • observed (fixed R (k ∘ e) (h:=h ∘ e)
    (fun j=>κ (e j)) (pt ∘ e) N K i (fun d=>digit d ∘ e) (fun j=>q (e j)) (o ∘ e)) (fun j=>A (e j)) (part k s).val at result
  rw [docket] at result
  exact result

theorem original (simple:G.Simple)(called:i≤K)(live:K≤N)(per m:ℕ)(x:(j:Fin n)→R.family.label (k j))
    (s:(Replicum.Bud (Fin n)).Mode)(read:Era G ℝ→ℂ):
    let e:=names k
    let t:=(part k s).val
    let dropped:=s.val.filter (fun j=>k j=0)
    (∑a:Choices R k s.val,signed R k N per K m x s.val a*read (ordinary R k κ pt N K i digit o A s.val a))=
      (∏j∈dropped,x j 0)*∑b:Choices R (k ∘ e) t,signed R (k ∘ e) N per K m (fun j=>x (e j)) t b*
        read ((∏j∈dropped,fee κ pt A j) • ordinary R (k ∘ e) (h:=h ∘ e) (fun j=>κ (e j)) (pt ∘ e)
          N K i (fun d=>digit d ∘ e) (o ∘ e) (fun j=>A (e j)) t b):=by
  intro e t dropped
  let keep:=fun a:Choices R k s.val=>∀j:s.val,k j=0 → a j=.inl ()
  let pay:=fun a:Choices R k s.val=>signed R k N per K m x s.val a*read (ordinary R k κ pt N K i digit o A s.val a)
  have trim:∑a,pay a=∑a∈univ.filter keep,pay a:=by
    apply (sum_subset (filter_subset _ _) ?_).symm
    intro a _ no
    have off:¬WilsonOriginalCensusSocketUnit.retained R k s.val a:=by
      intro retained
      apply no
      exact mem_filter.mpr ⟨mem_univ _,fun j hj=>retained j (by omega)⟩
    exact mul_eq_zero_of_left (WilsonOriginalCensusSocketUnit.supported R simple k N per K x m s.val a off) _
  change ∑a,pay a=_
  rw [trim,Finset.mul_sum]
  refine Finset.sum_bij' (fun a _=>reduced R k s a) (fun b _=>WilsonOriginalCensusUnitMenu.fixed R k s b) ?_ ?_ ?_ ?_ ?_
  · exact fun _ _=>mem_univ _
  · exact fun b _=>mem_filter.mpr ⟨mem_univ _,WilsonOriginalCensusUnitMenu.funded R k s b⟩
  · exact fun a ha=>WilsonOriginalCensusUnitMenu.restored R k s a (mem_filter.mp ha).2
  · exact fun b _=>WilsonOriginalCensusUnitMenu.crop R k s b
  · intro a ha
    have done:= (mem_filter.mp ha).2
    change signed R k N per K m x s.val a*read (ordinary R k κ pt N K i digit o A s.val a)=_
    rw [WilsonOriginalCensusPositiveDose.original R k N per K m x s a done,
      receipt R k κ pt N K i digit o A simple called live s a done,mul_assoc]

end YM.Integration.WilsonOriginalCensusFundedUnits

import YM.Integration.WilsonThermometerWeakMixedGrouping
import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra

/- An independently chosen numerical direction at the final physical chamber.
   The actual regular family, original hard addresses and full vacuum are shared
   by all choices. No earlier-law estimate is needed to change these scalars. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPepperCapture
open Function MeasureTheory Finset Lattice RG Wilson Marker Source Push Ac
open MergeProof MergeProof.Accent MergeProof.Ribbons RG05Readout RG05Readout.Many
open GridApprox.Nil RG05Readout.Native RG05Readout.Address Extra.Histories Extra.Trajectories Extra.Multi
open Local MergeProof.Menu MergeProof.Ribbon PhysicalNext.Repeat.Legato Bandage RG05Readout.Many
open MergeProof.Float Pressure RG12 Records Copper RG05Readout.Harvest
open WilsonThermometerWeakMixedGrouping
open scoped BigOperators Classical

variable {G:Gauge}{n:Side}{I V:Type}[Fintype I][DecidableEq I][Fintype V][DecidableEq V]
variable (L:Fibers I V)(R:Rep G n)(S:Fibers.Salt V I L G n)
local notation "J" => Stock.census I

def planted (t:I→ℂ) : Fibers.Salt V I L G n := {S with pepper:=fun i=>t i+S.pepper i}

theorem field (t:I→ℂ)(quiet:∀i U,(S.air i U).part (J).quiet=0)(U):
    (planted L S t).income R U=Poly.pass (Mach (J) t)*S.income R U:=by
  have split:Mach (J) (fun i=>t i+S.pepper i)+∑i,S.air i U=
      Mach (J) t+(Mach (J) S.pepper+∑i,S.air i U):=by
    simp only [Mach,send_add,sum_add_distrib,add_assoc]
  have empty:(Mach (J) S.pepper+∑i,S.air i U).part (J).quiet=0:=by
    simp only [Poly.part_plus,Poly.part_sum,mute,quiet,Finset.sum_const_zero,add_zero]
  unfold Fibers.Salt.income play
  change (Real.exp (R.exponent U):ℂ) • (Poly.pass (Mach (J) (fun i=>t i+S.pepper i)+∑i,S.air i U)*_)=_
  rw [split,pass_add (mute _ _) empty,mul_assoc,mul_smul_comm]
  rfl

variable {inputs:I→Three G n}{o:I→Site n}{w:I→ℝ}{a f:ℝ}{H l s:ℕ}{η:ℝ}

theorem grouped {physical : Config G n → Poly (Stock.census I)} {z y:ℝ}(cap:Alcove R inputs physical o w f a (1/2))
    (market:Arsenal R)(valid:R.activities.Valid R.p z y)(nonzero:∀U,R.eval U≠0)
    (width:∀i,0<w i)(people:Occupancy o s)(order:0<H)(enough:∀v,(L.contents v).card≤H)
    (close:∀i,coverNumber R.p.B ({o (L.twig (L.bunch i)),o i}:Support n)≤l)
    (pos:0<η)(small:η≤1)(fee:
      (((R.p.B+R.p.B+1:ℕ):ℝ)^4*Ribbons.Salt.scent R.p.B s (R.p.supportExponent+1/2) 1 η 1 f≤1/2 ∧
       Real.exp (Ribbons.Salt.scent R.p.B s (R.p.supportExponent+1/2) 1 η 1 f)-1≤1))
    (t:I→ℂ)(direction:∀i,w i*‖t i‖≤1/2):
    ∃ g:V → Config G n→ℂ,∃K:V → ℕ → Config G n→ℂ,
      Served R g (fun v=>profile R.activities (K v))
        (fun U=>Fibers.reap L (Poly.pass (Mach (J) t)*physical U))
        (o ∘ L.twig) (radius L R H l η w) R.p.supportExponent 1 ∧
      ∀v,Dominated (K v) ∧ Blade R (o (L.twig v)) (g v) (profile R.activities (K v))
        0 (4*(1/radius L R H l η w v)):=by
  obtain ⟨E,K,ψ,μ,hE,hK,burn,flow,_,pay,vac,_,rep⟩:=Alcove.chamber (V:=I) (R:=Stock.census I) (Q:=R) (P:=inputs) (F:=physical) (o:=o) (w:=w) (t:=f) (a:=a) (c:=1/2) cap
  let Y:Fibers.Salt V I L G n:=⟨o,μ,E,K⟩
  let Z:=planted L Y t
  have paid (i:I):w i*‖Z.pepper i‖≤1:=by
    change w i*‖t i+μ i‖≤1
    have bill:=mul_le_mul_of_nonneg_left (norm_add_le (t i) (μ i)) (width i).le
    rw [mul_add] at bill
    linarith only [bill,pay i,direction i]
  obtain ⟨K0,returned⟩:=Z.materialize s l η 1 1 H order market
    (show Z.Breeze R.p.threshold from ⟨burn,flow⟩) valid vac width people
    zero_le_one paid R.p.B_pos pos small close (show 0≤(1/2:ℝ) by norm_num)
    hE hK enough nonzero (w:=radius L R H l η w) (fun _=>rfl) fee.1 fee.2
  have hs:Z.income R=(fun U=>Poly.pass (Mach (J) t)*physical U):=by
    funext U
    have actual:Y.income R=physical:=rep.symm
    rw [←actual]
    exact field L R Y t (fun i U=>(burn i).sil U) U
  rw [hs] at returned
  exact ⟨Z.debt R.p.threshold,K0,returned.served,returned.foot⟩
end YM.Integration.WilsonThermometerPepperCapture
end

import YM.Integration.WilsonThermometerWeakMixedMeasured
import YM.OPE.Grouping.Birth

/-! Group a whole original many-source chamber with its actual hard and regular inventories. The pre-existing half-unit of spatial width pays the new source support. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakMixedGrouping
open Function MeasureTheory Finset Lattice RG Wilson Marker Source Push Ac
open MergeProof MergeProof.Accent MergeProof.Ribbons RG05Readout RG05Readout.Many
open GridApprox.Nil RG05Readout.Native RG05Readout.Address Extra.Histories Extra.Trajectories Extra.Multi
open Local MergeProof.Menu MergeProof.Ribbon PhysicalNext.Repeat.Legato Bandage RG05Readout.Many
open MergeProof.Float Pressure RG12 Records Copper RG05Readout.Harvest
open scoped BigOperators Classical

variable {G:Gauge} {n:Side} {I V:Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (L:Fibers I V) (R:Rep G n) {inputs:I→Three G n} {X:Config G n→ Poly (Stock.census I)}
variable {o:I→Site n} {w:I→ℝ} {a f:ℝ} {H l s:ℕ} {η:ℝ}

def radius (H l:ℕ) (η:ℝ) (w:I→ℝ) (v:V) : ℝ :=
  ∏ j∈L.contents v,Fibers.Salt.tow w (R.p.supportExponent+1/2) (η/H) l j

theorem grouped {z y:ℝ} (cap:Alcove R inputs X o w f a (1/2))
    (market:Arsenal R) (valid:R.activities.Valid R.p z y) (nonzero:∀U,R.eval U≠0)
    (width:∀i,0<w i) (people:Occupancy o s) (order:0<H) (enough:∀ v,(L.contents v).card ≤ H)
    (close:∀i,coverNumber R.p.B ({o (L.twig (L.bunch i)),o i}:Support n) ≤ l)
    (pos:0<η) (small:η ≤ 1) (fee:
      (((R.p.B+R.p.B+1:ℕ):ℝ)^4*Ribbons.Salt.scent R.p.B s (R.p.supportExponent+1/2) 1 η 1 f ≤ 1/2 ∧
       Real.exp (Ribbons.Salt.scent R.p.B s (R.p.supportExponent+1/2) 1 η 1 f)-1 ≤ 1)) :
    ∃ g : V → Config G n→ℂ,∃ K:V→ℕ → Config G n→ℂ,
      Served R g (fun v=>profile R.activities (K v)) (fun U=>Fibers.reap L (X U))
        (o ∘ L.twig) (radius L R H l η w) R.p.supportExponent 1 ∧
      ∀ v,Dominated (K v) ∧ Blade R (o (L.twig v)) (g v) (profile R.activities (K v))
        0 (4*(1/radius L R H l η w v)) := by
  obtain ⟨E,K,ψ,μ,hE,hK,burn,flow,_,pay,vac,_,rep⟩:=cap.chamber
  let T:Fibers.Salt V I L G n:=⟨o,μ,E,K⟩
  have hs : T.income R=X := rep.symm
  have paid (i:I):w i*‖T.pepper i‖≤1:=(pay i).trans (by norm_num)
  obtain ⟨K0,returned⟩:=T.materialize s l η 1 1 H order market
    (show T.Breeze R.p.threshold from ⟨burn,flow⟩) valid vac width people
    zero_le_one paid R.p.B_pos pos small close (show 0 ≤ (1/2:ℝ) by norm_num)
    hE hK enough nonzero (w:=radius L R H l η w) (fun _=>rfl) fee.1 fee.2
  rw [hs] at returned
  exact ⟨T.debt R.p.threshold,K0,returned.served,returned.foot⟩

end YM.Integration.WilsonThermometerWeakMixedGrouping
end

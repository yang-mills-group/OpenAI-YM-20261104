import YM.Integration.WilsonOriginalPublicTrialPhaseLocated
import YM.Integration.WilsonOriginalPublicTrialPhaseGroup

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseCapture
open Finset Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local RelayDifference.Opening Next.Foundations
open MergeProof MergeProof.Accent PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open OPE.Therm Push.AbsoluteSums.Animals Extra.Multi
open WilsonPositionProgramBlockedTrialAddBack
open RG05Readout RG05Readout.Address Offsets
open Extra.Multi MergeProof.Ribbons
open scoped Classical BigOperators ContDiff
variable {G:Gauge} (R:Run G)
variable {m N per:ℕ}
local notation "C" => R.family
local notation "A" => R.alloy.B.a
local notation "S" => (C).path
local notation "P" => (S).rep N per (m+1)
local notation "Q" => (S).rep N per m
local notation "O" => (S).levels.clock.op m per


open ProjectorNext.Equivariance RG05Readout.View

private theorem plain (P₀:BudgetPoint) : permission P₀ 1=1:= if_pos fun _=>rfl

private theorem undo {k:Side} (b:Site k) (U:Config G k): pull 1 (-b) (pull 1 b U)=U:=by
  rw [pull_one,pull_one]
  funext i
  simp [Lattice.translate]

private theorem same_x {k:Side}{h:ℕ}{F:Frame G h}{P₀:Rep G k}
    (b:Site k)(π:P₀.activities.Moves 1 b)(q:Coefficient F k):(shifted π q).x=q.x:=
  Push.CutoffProjectors.turn_one ..

private theorem sky_back {k:Side}(o:Site k)(s:Support k):
    sky (1,false) (-o) (sky (1,false) o s)=s:=by
  simp only [shading,Finset.image_image]
  rw [show (Local.turnSites 1 (-o))∘(Local.turnSites 1 o)=(id:Site k→Site k) from ?_,Finset.image_id]
  funext i
  change affine 1 _ (affine 1 _ i)=_
  simp [affine]

private theorem return_hard {k:Side}(o:Site k)(f:MergeProof.Res G k):
    floatUp (1,false) o (floatUp (1,false) (-o) f)=f:=by
  have back (i):puff (1,false) (-o) (puff (1,false) o i)=i:=
    Prod.ext (sky_back o _) (sky_back o _)
  funext i U
  obtain ⟨i,rfl⟩:=(puff (1,false) o).surjective i
  unfold floatUp stepUp
  rw [Equiv.symm_apply_apply,undo o]
  rw [show (puff (1,false) (-o)).symm i=puff (1,false) o i from ?_]
  · rfl
  apply (puff (1,false) (-o)).injective
  rw [Equiv.apply_symm_apply]
  exact (back i).symm

set_option maxHeartbeats 700000 in
private theorem shifted_invoice {k:Side}{h:ℕ}{F:Frame G h}(P₀:Rep G k)(q:Coefficient F k)
    {H₀:Hol G}(loc:SectionData F)(hs:loc.Sound H₀)(o g:Site k)(π₀:P₀.activities.Moves 1 g):
    Signpost P₀ (1,false) g (invoice q o loc P₀) (invoice (shifted π₀ q) (affine 1 g o) loc P₀):=by
  refine ⟨ProjectorNext.Equivariance.shifted.density π₀ loc hs q o,?_,foyer (1,false) g π₀ q⟩
  exact funext (fun U=>ProjectorNext.Equivariance.shifted.expEntry π₀ loc hs q U o)

private theorem cancel {k:Side}(g:Site k)(f:Config G k→ℂ):
    stepUp (1,false) g (stepUp (1,false) (-g) f)=f:=by
  funext U
  change f (pull 1 (-g) (pull 1 g U))=f U
  rw [undo]



set_option maxHeartbeats 1000000 in
/-- Price the grouped tile on its genuine occupied root. The old stable salary is paid once,
before recentering the returned height-zero row. -/
theorem original (cater:Cater (C) R.doors)(live:m<N)(grade:3≤(S).levels.clock.J m)
    (o:Site ((C).side (m+1) per))(X:Three G ((C).side (m+1) per))(a:ℝ)(non:0≤a)
    (use:Useful (P) X)
    (cut:MergeProof.Float.Blade (P) o X.2.1 (profile (P).activities X.2.2) 0 a):
    let F:=(C).labels.level 0
    let loc:=(C).localSection 0
    let b:=(O).ratio.parent o
    let f:=bling (S).levels m
    ∃ k:Coefficient F ((C).side m per), k.Format b (C).params (Q) ∧
      k.remBound b (Q) (Push.Local.kappa (S) m) (f*a) ∧ F.coeffSize k.x≤f*a ∧
      Ride (O) o b (R.doors N per m live) 1 X (invoice k b loc (Q)) ((f+2)*a):=by
  intro F loc b f
  let g:=(O).ratio.embed b
  let origin:=affine (1:Signed) (-g) o
  have plus:affine (1:Signed) g origin=o:=by simp [origin,affine,Signed.act_one]
  have home:(O).ratio.parent origin=0:=by
    dsimp only [origin]
    rw [show -g=(O).ratio.embed (-b) from (map_neg (O).ratio.root b).symm,
      Local.parent_affine (O).ratio ((C).S.block_odd m)]
    simp [affine,Signed.act_one,b]
  let π:=((R.makes.wilson.represents N per (m+1) live).good.labels.moves 1 (-g)).some
  let μ:=((R.makes.wilson.represents N per m live.le).good.labels.moves 1 b).some
  let X₀:=spin (1,false) π X
  have back:Signpost (P) (1,false) (-g) X X₀:=View.spin_at ..
  have hcut:MergeProof.Float.Blade (P) origin X₀.2.1 (profile (P).activities X₀.2.2) 0 a:=by
    have h:=ManyCopies.Cadet.Studio.moved_blade (1,false) (-g) o cut π
    rw [MergeProof.scalar_z,←back.gate,←back.lens] at h
    exact h
  have X₀use:Useful (P) X₀:=View.signpost_use R.makes live (1,false) π use
  obtain ⟨aa,tt,course,-,-⟩:=cater.tiers m N per live
  have paid:=cater.throve 0 m N per live grade
  have hf:0≤f:=(Real.exp_pos _).le
  obtain ⟨k,f₁,cash₁,fee,step⟩:=Address.peppers R.makes paid home live
    course.publishes.propagate hf X₀use hcut non
  let k':=shifted μ k
  have right:affine (1:Signed) b 0=b:=by simp [affine]
  have f₂:k'.Format b (C).params (Q):=right ▸ ProjectorNext.Equivariance.shifted.format μ 0
    ((by decide : 2≤4).trans (Next.Foundations.actual_side_ge ..)) f₁
  have cash₂:k'.remBound b (Q) (Push.Local.kappa (S) m) (f*a):=by
    have h:=ProjectorNext.Equivariance.shifted.cap μ f₁ cash₁
    rw [plain,one_mul] at h
    exact Eq.mp (congrArg (fun site:Site ((C).side m per)=>
      k'.remBound site (Q) (Push.Local.kappa (S) m) (f*a)) right) h
  refine ⟨k',f₂,cash₂,?_,?_⟩
  · rw [show k'.x=k.x from same_x _ _ _]
    unfold Frame.coeffSize at fee ⊢
    convert! fee using 1
  have front:Signpost (P) (1,false) g X₀ X:=by
    refine ⟨?_,?_,?_⟩
    · rw [back.trade,cancel]
    · rw [back.gate,cancel]
    · rw [back.lens,return_hard]
  have lower:Signpost (Q) (1,false) b (invoice k 0 loc (Q)) (invoice k' b loc (Q) ) :=by
    have h:=shifted_invoice (Q) k loc (R.makes.sections 0) 0 b μ
    change Signpost (Q) (1,false) b _ (invoice k' (affine 1 b 0) loc (Q)) at h
    rw [right] at h
    exact h
  simp only [pow_zero] at step
  have sale:=View.paid R.makes live course.publishes.propagate rfl step use
    (Useful.invoice k' b loc (Q) (R.makes.wilson.represents N per m live.le).good cash₂ f₂) front lower
  change Ride (O) (affine 1 g origin) (affine 1 b 0) _ _ _ _ _ at sale
  rw [plus,right] at sale
  exact sale

end YM.Integration.WilsonOriginalPublicTrialPhaseCapture
end

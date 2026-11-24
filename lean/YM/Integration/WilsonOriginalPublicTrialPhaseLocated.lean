import YM.Integration.WilsonOriginalPublicTrialPhaseTileInvoice

/-! The full previously appointed invoice travels at an arbitrary actual K-site. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseLocated
open Finset Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local RelayDifference.Opening Next.Foundations
open MergeProof MergeProof.Accent PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open OPE.Therm Push.AbsoluteSums.Animals Extra.Multi
open WilsonPositionProgramBlockedTrialAddBack
open RG05Readout RG05Readout.Address Offsets
open Extra.Multi MergeProof.Ribbons
open scoped Classical BigOperators ContDiff
variable {G:Gauge} (R:Run G)
variable {m N per:ℕ}{T:Campaign R}
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


set_option maxHeartbeats 800000 in
/-- The occupied upper coefficient is supplied by the caller on its actual K site.
A translation to its genuine child and back spends no extra coordinate or hard salary. -/
theorem original (hG:G.Simple)(purchase:RG05Preconstruction.ReadoutPurchase R.b)
    (stock:RG05Readout.Many.Storage (C) R.doors)(live:m<N)(d:ℕ)(grade:d+3≤(A).clock.J m)
    (o:Site ((C).side (m+1) per))(q:Coefficient ((C).labels.level d) ((C).side (m+1) per))
    (hit:Push.Local.hitWidth (Q).p*Push.Local.kappa (S) m≤1)(fine:Push.Local.kappa (S) (m+1)≤1)
    (r:ℝ)(fmt:q.Format o (C).params (P))(rem:q.remBound o (P) (Push.Local.kappa (S) (m+1)) r):
    let F:=(C).labels.level d
    let loc:=(C).localSection d
    let L:=(C).S.block m
    let c:=R.y ((A).clock.J (m+1))
    let α:=Doors.rate ((A).S.block m)
    let β:=2*(Real.exp ((A).params (m+1)).supportExponent*PhysicalNext.Repeat.Cub.title G ((A).params (m+1)))
    let w:=F.coeffSize q.x
    let ℓ:=((L.val:ℝ)^d)*c
    let b:=(O).ratio.parent o
    ∃ k:Coefficient F ((C).side m per),k.Format b (C).params (Q) ∧
      k.remBound b (Q) (Push.Local.kappa (S) m) (ℓ*w+α*r) ∧ F.coeffSize k.x≤ℓ*w+α*r ∧
      Ride (O) o b (R.doors N per m live) ((L.val:ℂ)^d) (invoice q o loc (P)) (invoice k b loc (Q))
        ((1+ℓ+β)*w+(2+α)*r):=by
  intro F loc L c α β w ℓ b
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
  let Q₀:=shifted π q
  have right:affine (1:Signed) b 0=b:=by simp [affine]
  have f₀:Q₀.Format origin (C).params (P):=ProjectorNext.Equivariance.shifted.format π o
    ((by decide : 2≤4).trans (Next.Foundations.actual_side_ge ..)) fmt
  have cash₀:Q₀.remBound origin (P) (Push.Local.kappa (S) (m+1)) r:=by
    change (shifted π q).remBound (affine 1 (-g) o) (P) _ _
    have h:=ProjectorNext.Equivariance.shifted.cap π fmt rem
    rw [plain,one_mul] at h
    exact h
  obtain ⟨_,sale⟩:=WilsonCloseCaptureAddress.issued R hG purchase d m N per live grade hit fine
  obtain ⟨_,_,ticket,_⟩:=WilsonCloseCapturePositions.positions R hG purchase d N m per live grade
  have wage:(P).p.supportExponent=((A).params (m+1)).supportExponent:=
    congrArg BudgetPoint.supportExponent (R.makes.wilson.represents N per (m+1) live).vac
  rw [wage] at ticket
  obtain ⟨k,f₁,cash₁,step,fee⟩:=RG05Readout.Address.rough (C) N m per d origin (R.doors N per m live)
    R.makes live home ticket sale.a_pos Q₀ sale.posp sale.b_pos fine f₀ cash₀
  have sourceAxis:Q₀.x=q.x:=same_x _ _ _
  rw [sourceAxis] at step fee cash₁
  let k':=shifted μ k
  have f₂:k'.Format b (C).params (Q):=right ▸ ProjectorNext.Equivariance.shifted.format μ 0
    ((by decide : 2≤4).trans (Next.Foundations.actual_side_ge ..)) f₁
  have cash₂:k'.remBound b (Q) (Push.Local.kappa (S) m) (ℓ*w+α*r):=by
    have h:=ProjectorNext.Equivariance.shifted.cap μ f₁ cash₁
    rw [plain,one_mul] at h
    apply Eq.mp (congrArg (fun site:Site ((C).side m per)=>
      k'.remBound site (Q) (Push.Local.kappa (S) m) (ℓ*w+α*r)) right)
    exact h
  refine ⟨k',f₂,cash₂,?_,?_⟩
  · simpa only [k',same_x] using fee
  have back:Signpost (P) (1,false) (-g) (invoice q o loc (P)) (invoice Q₀ origin loc (P)):=
    shifted_invoice (P) q loc (R.makes.sections d) o (-g) π
  have front:Signpost (P) (1,false) g (invoice Q₀ origin loc (P)) (invoice q o loc (P)):=by
    refine ⟨?_,?_,?_⟩
    · rw [back.trade,cancel]
    · rw [back.gate,cancel]
    · rw [back.lens,return_hard]
  have lower:Signpost (Q) (1,false) b (invoice k 0 loc (Q)) (invoice k' b loc (Q) ) :=by
    have h:=shifted_invoice (Q) k loc (R.makes.sections d) 0 b μ
    change Signpost (Q) (1,false) b _ (invoice k' (affine 1 b 0) loc (Q)) at h
    rw [right] at h
    exact h
  obtain ⟨a,a',paid⟩:=stock.exactMoon.days N per m live
  have course:RG05Readout.Many.Coursework (S) _ _ _ a a':=⟨paid.2,paid.1⟩
  have sale':=RG05Readout.View.paid R.makes live course.publishes.propagate rfl step
    (Useful.invoice q o loc (P) (R.makes.wilson.represents N per (m+1) live).good rem fmt)
    (Useful.invoice k' b loc (Q) (R.makes.wilson.represents N per m live.le).good cash₂ f₂) front lower
  change Ride (O) (affine 1 g origin) (affine 1 b 0) _ _ _ _ _ at sale'
  rw [plus,right] at sale'
  exact sale'

end YM.Integration.WilsonOriginalPublicTrialPhaseLocated
end

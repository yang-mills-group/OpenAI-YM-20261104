import YM.Integration.WilsonVacuumPreResetFiniteHistory

/-! The retained finite-to-cover vacuum discrepancy, heard inside the same
normalized Wick integral before its one-step fresh winding error. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteTilt
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Series FormalBulk08.Jets FormalBulk08.Shore FormalBulk08.Lava FormalBulk08.Wine
open FormalBulk08.Gorge FormalBulk08.Lotus FormalBulk08.Mesa FormalBulk08.Wick
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge} {c f:Side} {S:StepData c f} (F:Forest S.ratio) {U I:Type} [Fintype U] [DecidableEq U]

/-- A difference in the two incoming actions carries no new Haar or noise vertex. -/
def lifted (D:Pap (wire G f)):Pap (Pine G S F⊕wire G c):=
  Wick.roam ℝ (Jets.motor (Reef.graft F (G:=G))) (PowerSeries.map (MvPolynomial.rename Sum.inl).toRingHom D)

theorem moved (tag:S.Choices) (O:ChartRatio G) (P Q:Pap (wire G f)):
    Reef.flush F tag O Q-Reef.flush F tag O P=lifted F (Q-P):=by
  unfold Reef.flush Reef.vacuumU lifted
  simp only [map_sub]
  abel

/-- The old error is tested against the full shifted reference likelihood. -/
def income (H:Hull U I) (P D:Pap (U⊕I)):Pap I:=
  expan (-(covelog (vocal H P))) *
    beam (variation H.saddle I).call (expan (positive H P)*expan (toInk H D))

theorem hearing (H:Hull U I) (P Q D:Pap (U⊕I)) (hp:Solved H P) (hq:Solved H Q) (delta:Q-P=D):
    Orb.out H Q-Orb.out H P=covelog (income H P D):=by
  subst D
  have change:toInk H (Q-P)=positive H Q-positive H P:=by rw [map_sub,positive,positive];abel
  have hp0:=Orb.plur H P hp
  have hq0:=Orb.plur H Q hq
  have hd:coeff 0 (toInk H (Q-P))=0:=by rw [change,map_sub,hq0,hp0,sub_zero]
  have tilted:expan (positive H P)*expan (toInk H (Q-P))=expan (positive H Q):=by
    rw [expan_mul hp0 hd,change,add_sub_cancel]
  have ap:=Orb.voice H P hp
  have aq:=Orb.voice H Q hq
  have lp:=covelog_rank ap
  have lq:=covelog_rank aq
  have minus:coeff 0 (-covelog (vocal H P))=0:=by rw [map_neg,lp,neg_zero]
  have weight:income H P (Q-P)=expan (-covelog (vocal H P)+covelog (vocal H Q)):=by
    unfold income
    rw [tilted]
    change expan _*vocal H Q=_
    exact (congrArg (fun x=>expan (-covelog (vocal H P))*x) (expan_after aq).symm).trans (expan_mul minus lq)
  rw [weight,covelog_after (by rw [map_add,minus,lq,add_zero]),Orb.out,Orb.out]
  abel

variable (R:Run G) (u:G.ColorIndex)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun j:ℕ=>Flat.routes (R.family.path.levels.clock.op j 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun j:ℕ=>(R.family.path.levels.blocks j 0).branches)

/-- Exact on every true period and cutoff. The fresh fold error is kept outside this integral. -/
theorem original (simple:G.Simple) (N j:ℕ)(live:j<N)(n:Side)
    (tag:(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices):
    let P:=destination V N j
    let F:=Reef.floor (V).clock.kernel P (wood j) n
    let H:=Reef.ferry P (b j) (wood j) n
    let upper:=WilsonVacuumPreResetFiniteIntegral.read R N (j+1) (n*P.patch.L)
    let cover:=Mesa.stone (Dove.model V wood b R.metals.O u N (j+1)) (n*P.patch.L)
    WilsonVacuumPreResetFiniteIntegral.posted R N j n tag upper-
      WilsonVacuumPreResetFiniteIntegral.posted R N j n tag cover=
      covelog (income H (Reef.flush F tag R.metals.O cover) (lifted F (upper-cover))):=by
  intro P F H upper cover
  have yes:coeff 0 upper=Reef.crunch (Reef.kernelP G (V).clock.kernel.penalty P.wing _):=
    WilsonVacuumPreResetFiniteIntegral.head R simple live _
  have dossier:=(Dove.genu V wood b R.metals.O u R.alloy.B.ratio simple (i:=j+1) (N:=N) live).toStory
  obtain ⟨s,C,hs,hc,hv,-⟩:=colors G (V).clock.kernel.penalty (V).clock.kernel.penalty_pos P.legal
  have free:coeff 0 cover=Reef.crunch (Reef.kernelP G (V).clock.kernel.penalty P.wing _):=
    Mesa.stoned_main hs.le hc.le (hv _).1 dossier.toVivid dossier.ink _
  exact hearing H _ _ _ (Reef.consolidate P R.metals.O (b j) (wood j) n R.alloy.B.ratio tag cover free ((V).clock.adm j))
    (Reef.consolidate P R.metals.O (b j) (wood j) n R.alloy.B.ratio tag upper yes ((V).clock.adm j))
    (moved F tag R.metals.O cover upper)

end YM.Integration.WilsonVacuumPreResetFiniteTilt
end

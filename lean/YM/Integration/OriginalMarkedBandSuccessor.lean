import YM.Integration.OriginalMarkedBandMenu
import YM.Integration.OriginalMarkedSpringBand
import YM.Integration.QLocalFullRootedOffer

/-! Reissue the very same complete signed physical output at the next
original Spring, paying the full ordinary and hard fee before the period. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedBandSuccessor
open Function Finset Lattice Wilson RG Marker Overlay
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ConnectedActivityE6.Blaze.Thermal1020.Shared Extra.Trajectories
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G)

def ceiling (m seeds prev : ℕ) : ℝ := OriginalMarkedBandMenu.cost R seeds (m+1)
  (OriginalMarkedSpringBand.ordinary R (m+1) seeds) ((2:ℝ)^(prev+1))
  (Real.sqrt (R.alloy.B.a.clock.forcedAllowance (m+1)))

private theorem gain {N p k : ℕ} (hk : k ≤ N) :
    0 ≤ Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N p k ∧
    Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N p k ≤ 2 := by
  let β := (R.family.path.rep N p k).beta
  let y := R.family.path.levels.clock.hatBeta k
  have hy : 1<y := R.family.path.levels.fits.delayed k
  have band : y/2 ≤ β := (R.makes.wilson.represents N p k hk).band.1
  have pos : 0<β := by linarith
  have radius : Real.sqrt 2 ≤ 2*Real.sqrt β := calc
    _ ≤ Real.sqrt (4*β) := Real.sqrt_le_sqrt (by linarith)
    _ = 2*Real.sqrt β := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]; norm_num
  constructor
  · change 0≤Real.sqrt 2*(Real.sqrt β)⁻¹
    positivity
  · change Real.sqrt 2*(Real.sqrt β)⁻¹≤2
    rw [←div_eq_mul_inv,div_le_iff₀ (Real.sqrt_pos.2 pos)]
    exact radius

theorem pays {N p m : ℕ} (old : m+1<N) (seeds prev : ℕ) :
    OriginalMarkedBandMenu.cost R seeds (m+1) (OriginalMarkedSpringBand.ordinary R (m+1) seeds)
      ((Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N p (m+2))^(prev+1))
      (Real.sqrt (R.alloy.B.a.clock.forcedAllowance (m+1))) ≤ ceiling R m seeds prev := by
  have room := gain R (p:=p) old
  have hH : 0≤Overlay.GapsLocal.perStep seeds (R.family.path.levels.budget (m+1)).B := by
    unfold Overlay.GapsLocal.perStep Extra.Multi.siteFactor
    positivity
  unfold ceiling OriginalMarkedBandMenu.cost
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply mul_le_mul_of_nonneg_left _ hH
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ room.1 room.2 (prev+1)) (Real.sqrt_nonneg _)

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {Γ : Census V}
    {N p m : ℕ}
local notation "fine" => R.family.path.rep N p (m+1)
local notation "coarse" => R.family.path.rep N p m
local notation "op" => R.family.path.levels.clock.op m p
local notation "g" => Pert.Asymptotics.regulatorRun R.family N p (m+1)
local notation "oldg" => Pert.Asymptotics.regulatorRun R.family N p (m+2)

def Booked (x : Overlay.Bands Γ (fine)) (w : V→ℝ) (prev d : ℕ) : Prop :=
  let cap := ceiling R m (Fintype.card V) prev
  let δ := QLocalFullRootedOffer.radius 1 cap
  let next := fun i=>δ*w i
  0<δ ∧ δ≤1 ∧ ∃ (I : Type) (_ : Fintype I) (q : I→MergeProof.Menu.Hat Γ (fine)),
    Overlay.GapsLocal.Shard x q w cap ∧ GapsLocal.Full.given q 0=x.density ∧
    MergeProof.Menu.Offer x.origins q next (fine).p.B ((fine).p.supportExponent-4) 1 ∧
    OriginalMarkedSpringBand.Output (coarse) (op) (fine).beta x.density ((op).ratio.parent ∘ x.origins)
      next 0 0 ((Real.sqrt 2*g)^(d+1)) (OriginalMarkedSpringBand.ordinary R m (Fintype.card V))
      (Real.sqrt (R.alloy.B.a.clock.forcedAllowance m))

theorem enrolled (hG : G.Simple) (old : m+1<N)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (reserve : 100 ≤ (R.alloy.B.a.budget 0).supportExponent) (prev d : ℕ)
    (level : GapsLocal.Full.target 0 (Fintype.card V) d ≤ R.alloy.B.a.clock.J (m+1))
    (x : Overlay.Bands Γ (fine)) (w : V→ℝ) (hw : ∀i,0<w i) (units : x.units=0) (live : x.Active)
    (paid : x.Radial w 0 (OriginalMarkedSpringBand.ordinary R (m+1) (Fintype.card V))
      ((Real.sqrt 2*oldg)^(prev+1)) (Real.sqrt (R.alloy.B.a.clock.forcedAllowance (m+1)))) :
    Booked R x w prev d := by
  have hm : m<N := by omega
  obtain ⟨bought⟩ := OriginalMarkedBandMenu.complete R (upper:=N) (period:=p) (level:=m) hm x w live paid
  let I := bought.rows
  letI inst : Fintype I := bought.finite
  let q := bought.hats
  have ticket := bought.billed
  let δ := QLocalFullRootedOffer.radius 1 (ceiling R m (Fintype.card V) prev)
  have ceilingOffer := ticket.price.fatten (pays R (p:=p) old (Fintype.card V) prev)
  obtain ⟨pos,one,cover⟩ := QLocalFullRootedOffer.limited x.origins w hw q 1 zero_lt_one
    ((fine).p.supportExponent-4) (fine).p.B ceilingOffer
  have occurs : Extra.Multi.Occupancy ((op).ratio.parent ∘ x.origins) (R.family.path.levels.clock.J (m+1)) := by
    have markCount : Fintype.card V ≤ GapsLocal.Full.target 0 (Fintype.card V) d := by
      unfold GapsLocal.Full.target
      omega
    exact fun _=>(Finset.card_le_univ _).trans (markCount.trans level)
  have out := OriginalMarkedSpringBand.received R hG hm marks
    (reserve.trans (R.alloy.B.a.fits.deepExp (Nat.zero_le _)))
    (reserve.trans (R.alloy.B.a.fits.deepExp (Nat.zero_le _))) level x.origins
    (fun i=>δ*w i) (fun i=>mul_pos pos (hw i)) occurs q cover
  have reads : GapsLocal.Full.given q 0=x.density := by simpa only [units] using ticket.completes.symm
  exact ⟨pos,one,I,inst,q,{ticket with price:=ceilingOffer},reads,cover,reads ▸ out⟩

/-- Two successive receiving steps use the actual identical intermediate
band, with its ordinary and forced entries, for an arbitrary issued inlet. -/
theorem twice {ι : Type} [Fintype ι] (hG : G.Simple) (old : m+1<N)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (reserve : 100 ≤ (R.alloy.B.a.budget 0).supportExponent) (prev d : ℕ)
    (first : GapsLocal.Full.target 0 (Fintype.card V) prev ≤ R.alloy.B.a.clock.J (m+2))
    (second : GapsLocal.Full.target 0 (Fintype.card V) d ≤ R.alloy.B.a.clock.J (m+1))
    (o : V→Site (R.family.side (m+2) p)) (w : V→ℝ) (hw : ∀i,0<w i)
    (q : ι→MergeProof.Menu.Hat Γ (R.family.path.rep N p (m+2)))
    (offer : MergeProof.Menu.Offer o q w (R.family.path.rep N p (m+2)).p.B
      ((R.family.path.rep N p (m+2)).p.supportExponent-4) 1) :
    ∃ x : Overlay.Bands Γ (fine),
      (R.family.path.levels.clock.op (m+1) p).push (R.family.path.rep N p (m+2)).beta
        (GapsLocal.Full.given q 0)=x.density ∧
      x.origins=(R.family.path.levels.clock.op (m+1) p).ratio.parent ∘ o ∧
      x.units=0 ∧ x.Active ∧ Booked R x w prev d := by
  have occurs : Extra.Multi.Occupancy ((R.family.path.levels.clock.op (m+1) p).ratio.parent ∘ o)
      (R.family.path.levels.clock.J (m+2)) := by
    have markCount : Fintype.card V ≤ GapsLocal.Full.target 0 (Fintype.card V) prev := by
      unfold GapsLocal.Full.target
      omega
    exact fun _=>(Finset.card_le_univ _).trans (markCount.trans first)
  obtain ⟨x,_,_,origin,shares,roots,live,_,_,paid,_,_,_⟩ := OriginalMarkedSpringBand.received R hG old marks
    (reserve.trans (R.alloy.B.a.fits.deepExp (Nat.zero_le _)))
    (reserve.trans (R.alloy.B.a.fits.deepExp (Nat.zero_le _))) first o w hw occurs q offer
  exact ⟨x,origin,roots,shares.units.1,live,enrolled R hG old marks reserve prev d second x w hw shares.units.1 live paid⟩

end YM.Integration.OriginalMarkedBandSuccessor
end

import YM.Integration.WilsonMarkedIndependentNormalizedWallet

/-! Two independent geometric conditions on an occupied separated word:
clearance at its fixed reporting ancestor and room for its actual lifts in
the physical period. Both hold on every subcell and every proper face. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedGeometry
open Function Finset Lattice RG Wilson Laurent Precision WilsonCoeffUV
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.PathCost
open scoped Classical BigOperators
variable {G:Gauge}{ι:Type}[DecidableEq ι]{m j N e:ℕ}{D k K:ι→ℕ}

def room (n:Side)(y:ι → Cover)(I:Finset ι):Prop:=4*(crestCard y I+12)<n.val

omit [DecidableEq ι] in
theorem small {n:Side}{y:ι → Cover}{I:Finset ι}(h:room n y I):4*crestCard y I<n.val:=by
  dsimp [room] at h
  omega

omit [DecidableEq ι] in
theorem chart (P:Patch)(n:Side)(y:ι → Cover)(w:ι→Site P.L){J I:Finset ι}
    (three:3≤P.L.val)(sub:J⊆I)(space:room n y I):room (n*P.L) (chartIn P y w) J:=by
  let L:=P.L.val
  let move(v:ι):=L • y v
  have scale(a b:ι):terrain.gap (move a) (move b)=L*terrain.gap (y a) (y b):=by
    change size (L • y b-L • y a)=L*size (y b-y a)
    rw [←smul_sub]
    simp [size,Finset.mul_sum,Int.natAbs_mul]
  have d(s:ι):terrain.gap (move s) (chartIn P y w s)≤4*L:=by
    change size (_+lift (w s)-_)≤4*L
    rw [add_sub_cancel_left];exact crowd _
  have grew:crestCard (chartIn P y w) J≤L*crestCard y I+8*L:=by
    apply league_le
    intro a b
    let x:=chartIn P y w
    have ab:terrain.gap (y a.val) (y b.val)≤crestCard y I:=
      leg_le terrain (fun s:I=>y s.val) ⟨a.val,sub a.property⟩ ⟨b.val,sub b.property⟩
    have G:=terrain.tri (x a) (move a) (x b)
    have H:=terrain.tri (move a) (move b) (x b)
    rw [terrain.swap (x a) (move a)] at G
    rw [scale] at H
    have A:=d a
    have B:=d b
    change terrain.gap (move a) (x a)≤4*L at A
    change terrain.gap (move b) (x b)≤4*L at B
    have C:=Nat.mul_le_mul_left L ab
    change terrain.gap (x a) (x b)≤_
    omega
  have pad:8*L+12≤12*L:=by change 3≤L at three;omega
  have pay:crestCard (chartIn P y w) J+12≤L*(crestCard y I+12):=by rw [Nat.mul_add];omega
  change 4*(crestCard (chartIn P y w) J+12)<n.val*L
  exact calc _≤4*(L*(crestCard y I+12)):=Nat.mul_le_mul_left 4 pay
             _=(4*(crestCard y I+12))*L:=by ring
             _<n.val*L:=Nat.mul_lt_mul_of_pos_right space P.L.pos

omit [DecidableEq ι] in
theorem held (A:Levels G)(y:ι → Cover)(w:ι→Site (loose A j).L){ρ:ℝ}{J I:Finset ι}(mj:m≤j)
    (sub:J⊆I)(clear:cleared A.S m j ρ y I):cleared A.S m (j+1) ρ (chartIn (loose A j) y w) J:=by
  intro a ha b hb sep
  have parent(s:ι):parentC (A.S.block j) (chartIn (loose A j) y w s)=y s:=
    parent_pack (L:=A.S.block j) (α:=Unit) (y s,w s,())
  rw [upR _ mj,upR _ mj,parent,parent]
  exact clear a (sub ha) b (sub hb) sep

/-- The real input to one protected cover calculation, on each proper face.
A genuine mixed entry is controlled by the original separated graph estimate.
The marked scalar and the empty input keep their own roles. -/
theorem paid [Fintype ι](Q:Realm G (e+1) Credit.leanC)(P:Outerm G D)(W:Credit)(z ρ:ℝ)
    (income:Borealis Q D k K P m N W z)(opened:Cloze D k Q Credit.leanC)
    (gate:galeGate G D k K e W Credit.leanC Credit.leanC z≤ρ)
    (mj:m≤j)(live:j<N)(y:ι → Cover)(w:ι→Site (loose Q.draws j).L)(I:Finset ι)
    (clear:cleared Q.draws.S m j ρ y I):
    let b:=chartIn (loose Q.draws j) y w
    let old:=Gears Q.draws Q.paid K k N N (j+1) P b
    let A:=W.buy (z+snowP Q.draws.S m (j+1))
    1≤A ∧ Eu k old ∧ old ∅=0 ∧ safeB b old I e (Q.mint j (income.main.trans mj)).gear.past A:=by
  intro b old A
  have upper:=Cog Q.draws Q.paid (K':=K) le_rfl P income.head Q.hG Q.green (show j+1≤N from live)
  have date:m≤j+1:=by omega
  have hz:1≤z:=(Q.depth _ income.main).trans income.yell
  have available:1≤A:=W.purchase (hz.trans (le_add_of_nonneg_right (sub_nonneg.mpr (scales Q.draws.S date))))
  refine ⟨available,upper.level' b,upper.quiet' b,?_⟩
  intro J sub i hi r
  apply Wig.shave _ (Q.crossing j (income.main.trans mj))
  by_cases empty:J=∅
  · subst J;rw [show old ∅=0 from upper.quiet' b];exact Wig.zero.more (by simp)
  by_cases single:J.card=1
  · obtain ⟨s,rfl⟩:=card_eq_one.mp single
    exact income.sing (j+1) b date live s i hi r
  have mixed:1<J.card:=by have pos:=card_pos.mpr (nonempty_iff_ne_empty.mpr empty);omega
  have trueClear:=held Q.draws y w mj sub clear
  have linked:=coruscate income opened gate date live b trueClear mixed (r:=r) hi
  have zero:0≤ρ:=(gale_nn G D k K e W Credit.leanC Credit.leanC hz).trans gate
  have cap:=Real.exp_le_one_iff.mpr (neg_nonpos.mpr (penaltyBound (U':=Credit.leanC) hz zero (snowP Q.draws.S m (j+1))))
  exact linked.more (cap.trans (one_le_pow₀ available))

end YM.Integration.WilsonMarkedIndependentMixedGeometry
end

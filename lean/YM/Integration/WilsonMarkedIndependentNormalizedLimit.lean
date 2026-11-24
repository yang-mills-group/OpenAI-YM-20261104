import YM.Integration.WilsonMarkedIndependentNormalizedHistory
import YM.Integration.WilsonMarkedIndependentConnectedHistory

/-! Reporter-first comparison in the two expressly independent Wick programs.
The test, including a rank-zero marked output, sees the genuine finite old
vacuum in the numerator and the same field-dependent empty denominator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentNormalizedLimit
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Bank.Ticket
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonMarkedIndependentNormalizedWallet (gap)
open WilsonMarkedIndependentNormalizedScale (rate)
open WilsonMarkedIndependentNormalizedHistory (planted Filed)
open WilsonMarkedIndependentConnectedHistory (finite cover)
open Next.Foundations PhysicalNext.Repeat.Legato FormalBulk08
open FormalBulk08.Flat FormalBulk08.Mesa Next.Free Stationary Work.F03 Work.F05 Work.F08
open Tree Bloch Exterior
open scoped Classical BigOperators Topology
variable {G:Gauge}{a:ℕ}

private theorem vanishes (R:Run G)(m:ℕ)(positive:0<zz R.family.path.levels m):
    Tendsto (rate R.family.path.levels m) atTop (𝓝 0):=by
  have growth:Tendsto (fun p:ℕ=>(R.family.side m p).val) atTop atTop:=
    (show StrictMono (fun p:ℕ=>(R.family.side m p).val) from fun _ _ h=>
      Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator m).pos).tendsto_atTop
  let k:=-(4096*zz R.family.path.levels m)⁻¹
  have hk:k<0:=neg_neg_of_pos (inv_pos.mpr (mul_pos (by norm_num) positive))
  have kill:Tendsto (fun n:ℕ=>Real.exp (k*(n:ℝ))) atTop (𝓝 0):=
    Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg hk tendsto_natCast_atTop_atTop)
  convert kill.comp growth using 1
  funext p
  change Real.exp (-((R.family.side m p).val:ℝ)/(4096*zz R.family.path.levels m))=Real.exp (k*((R.family.side m p).val:ℝ))
  congr 1
  rw [div_eq_mul_inv]
  dsimp [k]
  ring

variable (R:Run G)(l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(m N j p:ℕ)
local notation "L" => R.family.path.levels
local notation "F" => deck (G:=G) l d h

def Heard (X:Herit F)(e:ℕ)(σ:ℝ):Prop:=
  let seed:=planted R l d h X m N
  let n:=R.family.side j p
  ∀(u:G.ColorIndex)(tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (_a:Loc G 1)(q:Fin (a+1) → Cover)(s:Fin (a+1))(A:Case d)(cap i r:ℕ),mass l {s}≤cap → i≤e →
    ∀x:Fin r → Woods G n,‖finite R u tags N N j l seed q A {s} n i r x-
      plume (cover R u N N j cap l seed q A {s} i r) n x‖≤‖touch A {s}‖*σ

theorem sampled (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (X:Herit F)(e:ℕ)(σ:ℝ)(live:j≤N)(well:Wellness l (planted R l d h X m N))
    (price:∀s,gap e (Gears L R.metals.O l l N N j (planted R l d h X m N)) s (R.family.side j p) σ):
    Heard R l d h m N j p X e σ:=by
  let seed:=planted R l d h X m N
  let n:=R.family.side j p
  let T:=Gears L R.metals.O l l N N j seed
  have legal:=Cog L R.metals.O (K':=l) le_rfl seed well simple R.alloy.B.ratio live
  intro u tags loc q s A cap i r enough read x
  obtain ⟨fin,cov⟩:=WilsonMarkedIndependentConnectedHistory.original R u tags simple v funded live le_rfl
    l l seed well loc q A {s} n cap enough
  rw [←fin,←cov]
  let f:=touch A {s}
  change ‖f ((T q {s}).1 n i r x)-plume (f ∘ (T q {s}).2 i r) n x‖≤‖f‖*σ
  obtain ⟨w,Z,hw,cork⟩:=((legal.level' q {s}).wing i r).land
  rw [plume_map ((T q {s}).2 i r) cork hw f n,Function.comp_apply,←map_sub]
  exact (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left (price s q i read r x) (norm_nonneg f))

/-- The period threshold is chosen with the physical reporter and the full
external source fixed. It precedes every ultraviolet cutoff, tensor rank,
angular position and normalized finite-coarse field. -/
theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (e:ℕ)(filed:Filed R l d h e):
    ∀ᶠm:ℕ in atTop,∀X:Herit F,∃B:ℝ,1≤B ∧
      (∀N p j:ℕ,m≤j → j≤N → Heard R l d h m N j p X e (B*rate L j p)) ∧
      ∀ε:ℝ,0<ε → ∀ᶠp:ℕ in atTop,∀N:ℕ,m≤N → Heard R l d h m N m p X e ε:=by
  obtain ⟨C,W,hist⟩:=filed
  obtain ⟨_,_,rows⟩:=WilsonMarkedIndependentNormalizedSingleton.original R simple v funded l d h e
  filter_upwards [hist,rows] with m issue registrar
  obtain ⟨Q,level,scheme,clock,anchor,_,school⟩:=registrar
  intro X
  obtain ⟨base,previous⟩:=issue X
  let B:=W.buy (zz L m+∑i,C.buy (zz L m)*WilsonConditionalTaylorSeparatedPurchase.fee (F i) (X i) e)
  have ok:1≤B:=base
  have health(N:ℕ)(safe:m≤N):Wellness l (planted R l d h X m N):=by
    have r:=(school X N safe).head
    rw [level,scheme] at r
    exact r
  have signed(N p j:ℕ)(lo:m≤j)(hi:j≤N):Heard R l d h m N j p X e (B*rate L j p):=
    sampled R l d h m N j p simple v funded X e _ hi (health N (lo.trans hi)) (previous N p j lo hi)
  refine ⟨B,ok,signed,?_⟩
  have positive:0<zz L m:=by rw [←clock];exact lt_of_lt_of_le zero_lt_one (Q.depth m anchor.le)
  intro ε hε
  have decay:Tendsto (fun p=>B*rate L m p) atTop (𝓝 0):=by simpa only [mul_zero] using (vanishes R m positive).const_mul B
  filter_upwards [decay.eventually_le_const hε] with p small
  intro N top u tags loc q s A cap i r maxgrade degree x
  exact (signed N p m le_rfl top u tags loc q s A cap i r maxgrade degree x).trans
    (mul_le_mul_of_nonneg_left small (ContinuousLinearMap.opNorm_nonneg (touch A {s})))

end YM.Integration.WilsonMarkedIndependentNormalizedLimit
end

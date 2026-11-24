import YM.Integration.WilsonMarkedIndependentMixedHistory
import YM.Integration.WilsonMarkedIndependentNormalizedLimit

/-! The full independently prescribed connected response on an actual
separated roster. The period exhaustion is uniform for all later ultraviolet
cutoffs, every retained subword, and all positions of bounded diameter. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedLimit
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Winding
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonMarkedIndependentNormalizedScale (rate)
open WilsonMarkedIndependentNormalizedHistory (planted)
open WilsonMarkedIndependentMixedGeometry (room)
open WilsonMarkedIndependentMixedStep (Entries)
open WilsonMarkedIndependentMixedHistory (Filed)
open WilsonMarkedIndependentConnectedHistory (finite cover)
open Next.Foundations PhysicalNext.Repeat.Legato FormalBulk08
open FormalBulk08.Flat FormalBulk08.Mesa Next.Free Stationary Work.F03 Work.F05 Work.F08
open Tree Bloch Exterior
open scoped Classical BigOperators Topology
variable {G:Gauge}{a:ℕ}

private theorem growth (R:Run G)(m:ℕ):Tendsto (fun p:ℕ=>(R.family.side m p).val) atTop atTop:=
  (show StrictMono (fun p:ℕ=>(R.family.side m p).val) from fun _ _ h=>
    Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator m).pos).tendsto_atTop

private theorem decay (R:Run G)(m:ℕ)(B:ℝ)(pos:0<zz R.family.path.levels m):
    Tendsto (fun p=>B*rate R.family.path.levels m p) atTop (𝓝 0):=by
  let k:=-(4096*zz R.family.path.levels m)⁻¹
  have hk:k<0:=neg_neg_of_pos (inv_pos.mpr (mul_pos (by norm_num) pos))
  have kill:Tendsto (fun p:ℕ=>Real.exp (k*((R.family.side m p).val:ℝ))) atTop (𝓝 0):=
    Real.tendsto_exp_atBot.comp ((Tendsto.const_mul_atTop_of_neg hk tendsto_natCast_atTop_atTop).comp (growth R m))
  convert kill.const_mul B using 1
  · funext p
    change B*Real.exp (-((R.family.side m p).val:ℝ)/(4096*zz R.family.path.levels m))=_
    congr 2
    dsimp [k];rw [div_eq_mul_inv];ring
  · simp

variable (R:Run G)(l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(m N j p:ℕ)
local notation "L" => R.family.path.levels
local notation "F" => deck (G:=G) l d h

def Heard (X:Herit F)(e:ℕ)(q:Fin (a+1) → Cover)(I:Finset (Fin (a+1)))(σ:ℝ):Prop:=
  let seed:=planted R l d h X m N
  let n:=R.family.side j p
  ∀(u:G.ColorIndex)(tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (_a:Loc G 1)(A:Case d)(cap i r:ℕ),mass l I≤cap → i≤e →
    ∀x:Fin r → Woods G n,‖finite R u tags N N j l seed q A I n i r x-
      plume (cover R u N N j cap l seed q A I i r) n x‖≤‖touch A I‖*σ

theorem sampled (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (X:Herit F)(e:ℕ)(ρ B η:ℝ)(live:j≤N)(well:Wellness l (planted R l d h X m N))
    (price:Entries (Gears L R.metals.O l l N N j (planted R l d h X m N)) R.family.S m j p e ρ B η)
    (q:Fin (a+1) → Cover)(I:Finset (Fin (a+1)))(wake:I.Nonempty)
    (safe:cleared R.family.S m j ρ q I)(fits:room (R.family.side j p) q I):
    Heard R l d h m N j p X e q I (B^I.card*η):=by
  let seed:=planted R l d h X m N
  let n:=R.family.side j p
  let T:=Gears L R.metals.O l l N N j seed
  have legal:=Cog L R.metals.O (K':=l) le_rfl seed well simple R.alloy.B.ratio live
  intro u tags loc A cap i r enough read x
  obtain ⟨fin,cov⟩:=WilsonMarkedIndependentConnectedHistory.original R u tags simple v funded live le_rfl
    l l seed well loc q A I n cap enough
  rw [←fin,←cov]
  let f:=touch A I
  change ‖f ((T q I).1 n i r x)-plume (f ∘ (T q I).2 i r) n x‖≤‖f‖*(B^I.card*η)
  obtain ⟨w,Z,hw,cork⟩:=((legal.level' q I).wing i r).land
  rw [plume_map ((T q I).2 i r) cork hw f n,Function.comp_apply,←map_sub]
  exact (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left (price I q wake safe fits i read r x) (norm_nonneg f))

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (e:ℕ)(filed:Filed R l d h e):
    ∀ᶠm:ℕ in atTop,∀X:Herit F,∃ρ B:ℝ,1≤B ∧
      (∀N p j:ℕ,m≤j → j≤N → ∀q I,I.Nonempty → cleared R.family.S m j ρ q I → room (R.family.side j p) q I →
        Heard R l d h m N j p X e q I (B^I.card*rate L j p)) ∧
      ∀(K:ℕ)(ε:ℝ),0<ε → ∀ᶠp:ℕ in atTop,∀N:ℕ,m≤N → ∀q I,I.Nonempty →
        cleared R.family.S m m ρ q I → crestCard q I≤K → Heard R l d h m N m p X e q I ε:=by
  obtain ⟨C,W,hist⟩:=filed
  obtain ⟨_,_,rows⟩:=WilsonMarkedIndependentNormalizedSingleton.original R simple v funded l d h e
  filter_upwards [hist,rows] with m issue registrar
  obtain ⟨Q,level,scheme,clock,anchor,_,school⟩:=registrar
  intro X
  obtain ⟨base,previous⟩:=issue X
  let z:=zz L m+∑i,C.buy (zz L m)*WilsonConditionalTaylorSeparatedPurchase.fee (F i) (X i) e
  let B:=W.buy z
  let ρ:=galeGate G d l l e W Credit.leanC Credit.leanC z
  have ok:1≤B:=base
  have health(N:ℕ)(safe:m≤N):Wellness l (planted R l d h X m N):=by
    have r:=(school X N safe).head
    rw [level,scheme] at r
    exact r
  refine ⟨ρ,B,ok,?_⟩
  have signed(N p j:ℕ)(lo:m≤j)(hi:j≤N)(q)(I:Finset (Fin (a+1)))(wake:I.Nonempty)
      (safe:cleared R.family.S m j ρ q I)(fits:room (R.family.side j p) q I):
      Heard R l d h m N j p X e q I (B^I.card*rate L j p):=
    sampled R l d h m N j p simple v funded X e ρ B _ hi (health N (lo.trans hi))
      (previous ρ le_rfl N p j lo hi) q I wake safe fits
  refine ⟨signed,?_⟩
  have positive:0<zz L m:=by rw [←clock];exact lt_of_lt_of_le zero_lt_one (Q.depth m anchor.le)
  intro K ε hε
  filter_upwards [(decay R m (B^(a+1)) positive).eventually_le_const hε,
    (growth R m).eventually_ge_atTop (4*(K+12)+1)] with p tiny enough
  intro N top q I present clear bounded u tags loc A cap i r maxgrade degree x
  have fits:room (R.family.side m p) q I:=by dsimp [room];omega
  have card:I.card≤a+1:=by simpa only [Fintype.card_fin] using Finset.card_le_univ I
  have bill: B^I.card*rate L m p≤ε:=(mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ ok card) (Real.exp_pos _).le).trans tiny
  exact (signed N p m le_rfl top q I present clear fits u tags loc A cap i r maxgrade degree x).trans
    (mul_le_mul_of_nonneg_left bill (ContinuousLinearMap.opNorm_nonneg (touch A I)))

end YM.Integration.WilsonMarkedIndependentMixedLimit
end

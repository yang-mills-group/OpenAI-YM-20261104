import YM.Integration.WilsonMarkedIndependentBareWinding

/-! Infinite-volume return of the independently computed finite marked history on the enrolled
physical periods, with the reporter, spatial rate, and norm of the test fixed before taking UV. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentPhysicalPeriod
open Function Filter Finset Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Mesa Next.Free Stationary Work.F03 Work.F05 Work.F08
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonMarkedIndependentConnectedHistory (finite cover)
open WilsonMarkedIndependentWinding (Folded)
open WilsonMarkedIndependentWindingCourse (received)
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{D:I→ℕ}
variable (R:Run G)(u:G.ColorIndex)
local notation "V" => R.family.path.levels
variable (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

def Cleared (j b e:ℕ)(K k:I→ℕ)(seed:ℕ→Outerm G D)(σ:ℝ):Prop:=
  ∀ (S:Finset I)(o:I),o∈S→∀ (r:ℕ)(U:ℝ),0≤U→∀ ε:ℝ,0<ε→∀ᶠp:ℕ in atTop,
    ∀ (N:ℕ),b<N→let n:=R.family.side j p
    ∀(z:I →Site n)(A:Case D),‖touch A S‖≤U→∀cap,mass k S≤cap→∀i,i≤e→
      let x:=PeriodicMarkedWinding.roots n z o
      Wig (tor n) z (σ/32/2) ε S
        (Carp.plume (cover R u N b j cap K (seed N) x A S i r) n-
          finite R u tags N b j K (seed N) x A S n i r)

omit [Fintype I] in
theorem before_uv {j b e:ℕ}{K k:I→ℕ}{seed:ℕ→Outerm G D}{σ B:ℝ}(hs:0<σ)(hB:0≤B)
    (hist:∀N,b<N→Folded R u tags (N:=N) (b:=b) (j:=j) (e:=e) K k (seed N) σ B):
    Cleared R u tags j b e K k seed σ:=by
  intro S o ho r U hU ε hε
  let F:=priceM (Hooks G) r σ+tiePay (Hooks G) r (σ/4)+1
  let A:=(|F|+1)*(U*B^S.card)
  have growth:Tendsto (fun p:ℕ=>(R.family.side j p).val) atTop atTop:=
    (show StrictMono (fun p:ℕ=>(R.family.side j p).val) from fun _ _ h=>
      Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator j).pos).tendsto_atTop
  have fall:Tendsto (fun n:ℕ=>Real.exp (-(σ/32/16)*(n:ℝ))) atTop (𝓝 0):=
    Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (by linarith : -(σ/32/16)<0) tendsto_natCast_atTop_atTop)
  have bill:Tendsto (fun p=>A*catchW (σ/32/16) (R.family.side j p)) atTop (𝓝 0):=by
    simpa only [catchW,mul_zero,Function.comp_apply] using (fall.comp growth).const_mul A
  filter_upwards [bill.eventually_le_const hε] with p fee
  intro N cut n z Φ bound cap enough i hi
  let E:=‖touch Φ S‖*B^S.card
  have hE:0≤E:=mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (pow_nonneg hB _)
  have sup:E≤U*B^S.card:=mul_le_mul_of_nonneg_right bound (pow_nonneg hB _)
  have greater:F*E+E≤A:=calc
    F*E+E≤ |F| * E+E:=by gcongr;exact le_abs_self F
    _=(|F|+1)*E:=by ring
    _≤A:=mul_le_mul_of_nonneg_left sup (by positivity)
  have receipt:=hist N cut n z Φ S o ho cap enough i hi r
  exact receipt.more ((mul_le_mul_of_nonneg_right greater (Real.exp_pos _).le).trans fee)

open IndependentSourcePathFamily
variable {I₀ I₁:I→Type}[∀i,Fintype (I₀ i)][∀i,Fintype (I₁ i)]

theorem deposited (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (e:ℕ)(K k:I→ℕ)(a:Loc G 1)(old:Finset I)(X:∀i,I₀ i → Seed G (D i))(Y:∀i,I₁ i → Seed G (D i))
    (hX:∀i z,(X i z).rank≤k i+(X i z).head)(hY:∀i z,(Y i z).rank≤k i+(Y i z).head){s:ℝ}(hs:0<s):
    ∀ᶠj:ℕ in atTop,∀ b:ℕ,j≤b→∃ σ:ℝ,0<σ ∧ ∀B:ℝ,1≤B→
      (∀N,b<N→WilsonFiniteVacuumWindingDate.positive V R.metals.O e N (b+1) s B)→
      Cleared R u tags j b e K k (fun N=>received R K k N b old X Y) σ:=by
  filter_upwards [WilsonMarkedIndependentWindingCourse.deposited R u tags simple v funded e K k a old X Y hX hY hs] with j bought
  intro b live
  obtain ⟨d,C,σ,hC,hσ,each⟩:=bought b live
  refine ⟨σ,hσ,?_⟩
  intro B hB upper
  exact before_uv R u tags hσ (mul_nonneg (by linarith) (pow_nonneg (by linarith) _))
    (fun N h=>each N h B hB (upper N h))

theorem leading (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (K k:I→ℕ)(a:Loc G 1)(old:Finset I)(X:∀i,I₀ i → Seed G (D i))(Y:∀i,I₁ i → Seed G (D i))
    (hX:∀i z,(X i z).rank≤k i+(X i z).head)(hY:∀i z,(Y i z).rank≤k i+(Y i z).head){s:ℝ}(hs:0<s):
    ∀ᶠj:ℕ in atTop,∀ b:ℕ,j≤b→∃ σ:ℝ,0<σ ∧
      Cleared R u tags j b 0 K k (fun N=>received R K k N b old X Y) σ:=by
  filter_upwards [WilsonMarkedIndependentWindingCourse.leading R u tags simple v funded K k a old X Y hX hY hs] with j bought
  intro b live
  obtain ⟨C,σ,hC,hσ,step⟩:=bought b live
  exact ⟨σ,hσ,before_uv R u tags hσ (by linarith) step⟩

end YM.Integration.WilsonMarkedIndependentPhysicalPeriod
end

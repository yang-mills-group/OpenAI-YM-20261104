import YM.Integration.WilsonMarkedIndependentPhysicalReceipt
import YM.Integration.WilsonMarkedIndependentPhysicalPeriod

/-! Rooted finite-minus-covered error on all enrolled physical periods, with the
chronological ultraviolet limit permitted first and the physical period second. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentEnrolledPeriod
open Function Filter Finset Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Mesa Next.Free Stationary Work.F03 Work.F05 Work.F08
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonFiniteMarkedHistoryStep
open WilsonMarkedIndependentConnectedHistory (finite cover)
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge}{I:Type}[DecidableEq I]{D:I→ℕ}

open WilsonMarkedIndependentPhysicalIntake (PositiveAt PairedAt)
open WilsonMarkedIndependentOnePeriod (Course)
open WilsonDepositedFreshFiniteHistory (bank lawful)
open WilsonMarkedIndependentWindingCourse (received)
open IndependentSourcePathFamily
variable (R:Run G)(u:G.ColorIndex)
local notation "V" => R.family.path.levels
variable (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

def FoldedAt {N b j e:ℕ}(K k:I→ℕ)(seed:Outerm G D)(σ B:ℝ)(n:Side):Prop:=
  ∀ (z:I → Site n)(A:Case D)(S:Finset I)(o:I),o∈S→∀cap,mass k S≤cap→∀i,i≤e→∀r,
    let x:=PeriodicMarkedWinding.roots n z o
    let E:=‖touch A S‖*B^S.card
    let price:=(priceM (Hooks G) r σ + tiePay (Hooks G) r (σ/4)+1)*E+E
    Wig (tor n) z (σ/32/2) (price*catchW (σ/32/16) n) S
      (Carp.plume (cover R u N b j cap K seed x A S i r) n - finite R u tags N b j K seed x A S n i r)

theorem folded (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    {N b j e:ℕ}(live:j≤b)(top:b≤N)(K k:I→ℕ)(seed:Outerm G D)(well:Wellness k seed)(a:Loc G 1)
    {σ B:ℝ}{n:Side}(hs:0<σ)(issued:PairedAt e (Gears V R.metals.O K k N b j seed) n σ B):
    FoldedAt R u tags (N:=N) (b:=b) (j:=j) (e:=e) K k seed σ B n:=by
  intro z A S o ho cap fee i cut r
  let x:=PeriodicMarkedWinding.roots n z o
  apply PeriodicMarkedWinding.periodized z o ho hs
  obtain ⟨here,there⟩:=WilsonMarkedIndependentConnectedHistory.original R u tags simple v funded live top
    K k seed well a x A S n cap fee
  change MarkU x S (finite R u tags N b j K seed x A S n i r)
    (cover R u N b j cap K seed x A S i r) σ (‖touch A S‖*B^S.card)
  rw [←here,←there]
  let f:=touch A S
  have h:=issued x S i cut r
  refine ⟨⟨mul_nonneg (ContinuousLinearMap.opNorm_nonneg (touch A S)) h.access.1,fun y=>?_⟩,
    ⟨mul_nonneg (ContinuousLinearMap.opNorm_nonneg (touch A S)) h.bill.1,fun y=>?_⟩,
    ⟨mul_nonneg (ContinuousLinearMap.opNorm_nonneg (touch A S)) h.gulf.coal,fun y hy=>?_⟩⟩
  · exact (f.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (h.access.2 y) (ContinuousLinearMap.opNorm_nonneg f)).trans_eq (mul_assoc ..).symm)
  · exact (f.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (h.bill.2 y) (ContinuousLinearMap.opNorm_nonneg f)).trans_eq (mul_assoc ..).symm)
  · change ‖f ((Gears V R.metals.O K k N b j seed x S).1 n i r (slideC n y)) -
        f ((Gears V R.metals.O K k N b j seed x S).2 i r y)‖ ≤ _
    rw [←map_sub]
    exact (f.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (h.gulf.local_w y hy) (ContinuousLinearMap.opNorm_nonneg f)).trans_eq (mul_assoc ..).symm)

def registered (p:ℕ):Course V where
  side j:=R.family.side j p
  next j:=Subtype.ext (R.family.path.levels.clock.op j p).sizes

variable [Fintype I] {I₀ I₁:I→Type}[∀i,Fintype (I₀ i)][∀i,Fintype (I₁ i)]

theorem deposited (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (e:ℕ)(K k:I→ℕ)(a:Loc G 1)(old:Finset I)(X:∀i,I₀ i → Seed G (D i))(Y:∀i,I₁ i → Seed G (D i))
    (hX:∀i z,(X i z).rank≤k i+(X i z).head)(hY:∀i z,(Y i z).rank≤k i+(Y i z).head){s:ℝ}(hs:0<s):
    ∀ᶠj:ℕ in atTop,∀ b:ℕ,j≤b→∃ (d:ℕ)(C σ:ℝ),1≤C ∧ 0<σ ∧ ∀N,b<N→
    ∀(p:ℕ)(V₀:ℝ),1≤V₀→PositiveAt V R.metals.O e N (b+1) (R.family.side (b+1) p) s V₀ →
    FoldedAt R u tags (N:=N) (b:=b) (j:=j) (e:=e) K k (received R K k N b old X Y) σ (C*V₀^d) (R.family.side j p):=by
  filter_upwards [FundedMarkedCoverRows.realm R simple v funded 0 (fun _=>0) (fun _=>1)
    (fun _=>Nat.zero_lt_succ _) e 0 0] with j h
  obtain ⟨Q,draws,scheme,_,anchor,_⟩:=h
  intro b live
  obtain ⟨d,C,σ,hC,hσ,step⟩:=WilsonMarkedIndependentPhysicalReceipt.original (D:=D) (k:=k)
    Q K j b anchor.le live old X Y hX hY hs
  unfold bank at step
  rw [draws,scheme] at step
  refine ⟨d,C,σ,hC,hσ,?_⟩
  intro N cut p V₀ hV quiet
  have upper:Wellness k (Gears V R.metals.O K k N (b+1) b (independent X)):=
    Cog V R.metals.O cut (independent X) (OriginalCoverReanchoring.deposited X hX).1 simple R.alloy.B.ratio (Nat.le_succ _)
  have income:Wellness k (received R K k N b old X Y):=lawful old upper (OriginalCoverReanchoring.deposited Y hY).1
  exact folded R u tags simple v funded live cut.le K k _ income a hσ (step N cut (registered R p) V₀ hV quiet)

omit [Fintype I] in
theorem before_uv {j b e:ℕ}{K k:I→ℕ}{seed:ℕ→Outerm G D}{σ B:ℝ}(hs:0<σ)(hB:0≤B)
    (hist:∀N,b<N→∀p,FoldedAt R u tags (N:=N) (b:=b) (j:=j) (e:=e) K k (seed N) σ B (R.family.side j p)):
    WilsonMarkedIndependentPhysicalPeriod.Cleared R u tags j b e K k seed σ:=by
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
  have receipt:=hist N cut p z Φ S o ho cap enough i hi r
  exact receipt.more ((mul_le_mul_of_nonneg_right greater (Real.exp_pos _).le).trans fee)

theorem ordered (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (e:ℕ)(K k:I→ℕ)(a:Loc G 1)(old:Finset I)(X:∀i,I₀ i → Seed G (D i))(Y:∀i,I₁ i → Seed G (D i))
    (hX:∀i z,(X i z).rank≤k i+(X i z).head)(hY:∀i z,(Y i z).rank≤k i+(Y i z).head){s:ℝ}(hs:0<s):
    ∀ᶠj:ℕ in atTop,∀ b:ℕ,j≤b→∃ σ:ℝ,0<σ ∧ ∀B:ℝ,1≤B→
      (∀N,b<N→∀p,PositiveAt V R.metals.O e N (b+1) (R.family.side (b+1) p) s B)→
      WilsonMarkedIndependentPhysicalPeriod.Cleared R u tags j b e K k (fun N=>received R K k N b old X Y) σ:=by
  filter_upwards [deposited R u tags simple v funded e K k a old X Y hX hY hs] with j bought
  intro b live
  obtain ⟨d,C,σ,hC,hσ,each⟩:=bought b live
  refine ⟨σ,hσ,?_⟩
  intro B hB upper
  exact before_uv R u tags hσ (mul_nonneg (by linarith) (pow_nonneg (by linarith) _))
    (fun N h p=>each N h p B hB (upper N h p))

end YM.Integration.WilsonMarkedIndependentEnrolledPeriod
end

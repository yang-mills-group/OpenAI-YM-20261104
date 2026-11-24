import YM.Integration.WilsonIndependentCollarCompletePrint
import YM.Integration.WilsonReceivedFixedDigitHistory

/-! Quote the actual fixed-child, fully reverted block before the original
period, incoming family and its physical dose. The post-length price can be
joined to the marked realm's own gate. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarEventQuote
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision FreeResolvent Work.F08 Gauge
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Cosmos WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Bank.Realm WilsonMarkedIndependentPhysicalIntake
open WilsonIndependentCollarCompletePrint (printed)
open scoped Classical BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k:ι→ℕ}
variable (e q r:ℕ)(hq:q≤e)(S:Finset ι)(a:ι)(root:a∈S)

abbrev grant := WilsonIndependentCollarCompletePrint.original (G:=G) (D:=D) (k:=k) e q r hq S univ
  (subset_univ _) root
abbrev debt := (grant (G:=G) (D:=D) (k:=k) e q r hq S a root).choose
abbrev quote (I:Arch G) := (grant (D:=D) (k:=k) e q r hq S a root).choose_spec I
abbrev width (I:Arch G) := (quote (D:=D) (k:=k) e q r hq S a root I).choose
abbrev gross (I:Arch G) := (quote (D:=D) (k:=k) e q r hq S a root I).choose_spec.choose

variable (inlet:Gear G → ℝ)(pos:∀I,0 < inlet I)
def localPrice (I:Gear G):ℝ:=open Classical in
  if path:I.patch.Branches I.kernel G ∧ LocalRatio I.angle then
    let P:=aerie (inlet I) I e (pos I) path.1 path.2
    let s:=width (D:=D) (k:=k) e q r hq S a root P
    let C:=gross (D:=D) (k:=k) e q r hq S a root P
    max (s/2)⁻¹ (max C (C*tiePay (Hooks G) r (s-s/2)))
  else 1

variable (Q:Realm G (e+1) Credit.leanC)(m:ℕ)(hm:Q.anchor ≤ m)
local notation "I₀" => (Q.mint m hm).gear
local notation "I₁" => holt Q m hm (inlet I₀) (pos I₀)

/-- Both L¹ readings and the winding are on the one actual queried digit.
The quote bounds the inverse output strip and both multiplicative factors.
Only the original positive-grade quiet and the original source dose remain. -/
theorem original (z:ℝ)
    (enrolled:localPrice (D:=D) (k:=k) e q r hq S a root inlet pos I₀≤z)
    (N:ℕ)(live:m<N)(n:Side)(Y:Outerm G D)(well:Wellness k Y)(cell:ι→Site (loose Q.draws m).L)
    (y:ι→ Cover)(V A:ℝ)(hV:1≤V)(hA:0≤A)
    (quiet:∀u≤e,∀l,Sight ((story Q.draws Q.paid N (m+1)).1 (n*(loose Q.draws m).L) u l)
      (actionW Q.draws Q.paid N (m+1) u l) (I₁).s V)
    (marked:∀T⊆univ,∀u≤e,∀l,let x:=chartIn (loose Q.draws m) y cell
      MarkU x T (((Y x) T).1 (n*(loose Q.draws m).L) u l) (((Y x) T).2 u l) (I₁).s (A^T.card)) :
    let b:=width (D:=D) (k:=k) e q r hq S a root I₁
    let O:=WilsonReceivedFixedDigitIntake.next Q.draws Q.paid m N k Y cell y S
    let fee:=V^(debt (G:=G) (D:=D) (k:=k) e q r hq S a root)*A^S.card*rimJ (ratioHigh Q.draws Q.paid N m) q r
    0<b ∧ (b/2)⁻¹≤z ∧ MarkU y S (O.1 n q r) (O.2 q r) b (z*fee) ∧
      (∑x,printed (tor n) (wrap n ∘ y) S (b/2) (O.1 n q r) x ≤ z*fee) ∧
      SumBudget (printed terrain y S (b/2) (O.2 q r)) (z*fee) := by
  intro b O fee
  let x:=chartIn (loose Q.draws m) y cell
  let K:=Y x
  let law:=well.level' x
  let blank:=well.quiet' x
  let previous := (old Q.draws Q.paid Q.hG Q.green N (m+1) live).basis (n*(loose Q.draws m).L)
  let current:ScrollV e I₁:={cloVent Q m N n hm live (inlet I₀) (pos I₀) with
    W:=(story Q.draws Q.paid N (m+1)).1,coin:=V,paid:=hV,fare:=quiet}
  let p:PackOne univ D k e I₁:=⟨current,y,cell,K,previous.lamp,previous.shape,blank,law,A,hA,marked⟩
  let quote':=quote (D:=D) (k:=k) e q r hq S a root I₁
  let C:=gross (D:=D) (k:=k) e q r hq S a root I₁
  obtain ⟨hot,_,sheets⟩:=quote'.choose_spec.choose_spec
  have cost:max (b/2)⁻¹ (max C (C*tiePay (Hooks G) r (b-b/2)))≤z:=by
    simpa only [localPrice,dif_pos (show (I₀).patch.Branches (I₀).kernel G ∧ LocalRatio (I₀).angle
      from ⟨(Q.draws.blocks m 0).branches,Q.green⟩)] using enrolled
  have hfee:0≤fee:=by
    dsimp only [fee]
    exact mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hV) _) (pow_nonneg hA _))
      (sum_nonneg fun _ _=>norm_nonneg _)
  have hs:=sheets p (ratioHigh Q.draws Q.paid N m)
  have fin:O.1 n=mist p.V.wheel p.V.shadow p.V.H (p.V.T p.V.n) (I₁).R p.V.W' p.K
      (ratioHigh Q.draws Q.paid N m) k S:=feeleg Q.draws Q.paid m N K k live Q.hG Q.green law n S
  have cov:O.2=Blue.mix (ratioHigh Q.draws Q.paid N m) (p.cabinJ S):=
    onSide Q.draws Q.paid m N K k blank law Q.hG Q.green live S
  rw [fin,cov]
  let T:=tiePay (Hooks G) r (b-b/2)
  have hC:C≤z:=((le_max_left C (C*T)).trans (le_max_right ..)).trans cost
  have ht:C*T≤z:=((le_max_right C (C*T)).trans (le_max_right ..)).trans cost
  let d:=debt (G:=G) (D:=D) (k:=k) e q r hq S a root
  have more:C*V^d*A^S.card*rimJ (ratioHigh Q.draws Q.paid N m) q r≤z*fee:=
    (show _=C*fee by dsimp only [fee,d];ring).le.trans (mul_le_mul_of_nonneg_right hC hfee)
  have paid:(C*V^d*A^S.card*rimJ (ratioHigh Q.draws Q.paid N m) q r)*T≤z*fee:=
    (show _=(C*T)*fee by dsimp only [fee,d];ring).le.trans (mul_le_mul_of_nonneg_right ht hfee)
  exact ⟨hot,(le_max_left ..).trans cost,hs.1.more more,hs.2.1.trans paid,
    hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.trans paid⟩

end YM.Integration.WilsonIndependentCollarEventQuote

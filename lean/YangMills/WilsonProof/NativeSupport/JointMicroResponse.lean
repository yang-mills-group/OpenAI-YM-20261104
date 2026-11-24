import YangMills.WilsonProof.NativeSupport.JointTerminalParams
import YangMills.WilsonProof.NativeSupport.JointMatchedPath

/-! The actual centered Wilson response, for any physical generating
product, from its shared-vacuum terminal values at real fugacities. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Dated
open Function Finset Lattice RG Wilson RGComparison.Core16 Marker Push.BetaTransport YM.Pressure
open WilsonUniformUnmarkedInletEnergySites WilsonUniformUnmarkedInletBondRemainder
open JointMoments JointShadow Packet TerminalGas
open scoped Classical BigOperators
variable {I:Type} [Fintype I] [DecidableEq I] {G:Gauge} {n c:Side} {t N:ℕ}
local notation "V₀" => Names I t N n
theorem response (d:Descent n c) (ok:d.OK G) (B β v:ℕ→ℝ) (r:ℝ) (V:Config G c) (E:Finset I)
    (F:I → Config G n → ℝ) (ct:∀ i,Continuous (F i)) (sym:∀ i,GaugeInvariant (F i))
    (h:ℝ) (hp:0 ≤ h) (H:Poly (Stock.census V₀)) (quiet:H.part (tag ∅)=0)
    (root:∀ i:V₀,(∑ S:Finset V₀ with i∈S,‖H.part (tag S)‖*2^(S.card-1)) ≤ 1/2) (C:ℝ) (pos:0 < C) :
    let Y:=WilsonUniformUnmarkedInletConnectedShift.temperatures β v r
    let φ:=micro F E h
    let sig (q:sites n d):=if 0 ≤ picture d β v V φ r q then 1 else -1
    (∀ (A:Finset I) (z:ℝ),(C:ℂ)*openAt (params A (z:ℂ)) (Poly.pass H)=
      (d.scalar G B:ℂ)*polynomial (interior d) (moment d Y V (fun q=>h*sig q) (micro F A h)) (z:ℂ)) →
    h*(∑ q∈interior d,|picture d β v V φ r q|) ≤ (3/2:ℝ)^E.card := by
  intro Y φ sig exact_
  let P:=Poly.pass H
  let A:Finset V₀:=other
  let J:Finset V₀:=moving
  let D:Finset V₀:=phys E
  let s (q:sites n d):=if 0 ≤ picture d β v V φ r q then h else -h
  let f (z:ℂ):=polynomial (interior d) (moment d Y V s φ) z/polynomial (interior d) (moment d Y V s 1) z
  let g (z:ℂ):=evaluated J (A∪D) P z/evaluated J A P z
  have factor:(fun q=>h*sig q)=s:=by funext q;dsimp only [s,sig];split <;> ring
  have one:micro F ∅ h=1:=by funext X;simp [micro]
  have noval:phys (t:=t) (N:=N) (n:=n) (∅:Finset I)=∅:=Finset.map_empty _
  have cne:(C:ℂ)≠0:=Complex.ofReal_ne_zero.mpr pos.ne'
  have bne:(d.scalar G B:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (Descent.scalar_pos G d B).ne'
  have same (z:ℝ):f (z:ℂ)=g (z:ℂ):=by
    have withE:=exact_ E z
    have bare:=exact_ ∅ z
    rw [encoded,factor] at withE
    rw [encoded,noval,union_empty,factor,one] at bare
    dsimp only [f,g]
    calc
      _=((d.scalar G B:ℂ)*polynomial (interior d) (moment d Y V s φ) (z:ℂ))/
        ((d.scalar G B:ℂ)*polynomial (interior d) (moment d Y V s 1) (z:ℂ)) :=
          (mul_div_mul_left _ _ bne).symm
      _=((C:ℂ)*evaluated J (A∪D) P (z:ℂ))/((C:ℂ)*evaluated J A P (z:ℂ)) := by
        rw [←bare,←withE]
      _=_ := mul_div_mul_left _ _ cne
  have joined:Continuous φ:=by
    unfold φ micro
    exact continuous_finsetProd _ (fun i _=>continuous_const.add (continuous_const.mul (ct i)))
  have invariant:GaugeInvariant φ:=by
    intro k X;unfold φ micro
    exact prod_congr rfl fun i _=>by rw [sym i k X]
  have orig:=frozen_direction d ok β v r V s joined invariant
  have fd:DifferentiableAt ℂ f 0:=orig.differentiableAt
  have denom:= (disk_quotient H quiet (fun i=>by convert root i using 1; congr 1; ext s; simp) J A D (outside E) (z:=0) (by norm_num)).1
  have gd:DifferentiableAt ℂ g 0:=(all_parameters J _ P).differentiableAt.div (all_parameters J _ P).differentiableAt denom
  have derivEq:=real_derivative fd.hasDerivAt gd.hasDerivAt same
  have abs:=absolute_direction d ok β v r V joined invariant hp
  change ‖deriv f 0‖=_ at abs
  rw [←abs,derivEq]
  have sizeD:D.card=E.card:=by simp [D,phys]
  dsimp only [g,P]
  rw [←sizeD]
  exact direction_estimate H quiet (fun i=>by convert root i using 1; congr 1; ext s; simp) J A D (outside E)

end YM.Integration.InletSusceptibility.Dated

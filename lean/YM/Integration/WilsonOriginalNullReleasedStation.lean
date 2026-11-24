import YM.Integration.WilsonOriginalNullReleasedFrame
import YM.Integration.WilsonOriginalAdjacentMicroscopicPrice
import YM.Integration.WilsonPositionThermometerStationTransport

/-! The full true page of a fixed original cutoff field at a finer reporting
station, beginning from its measured original coordinate at the enrolled station. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullReleasedStation
open Function Filter Finset Lattice RG Wilson Labels Source Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open QuadraticLocal QuadraticLocal.Advent ConnectedActivityE6 Next.Rank.Price
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:ℕ)
local notation "C₀"=>R.family
local notation "Fr"=>R.family.labels.level d
local notation "levels"=>R.family.path.levels

theorem gauge {N p s:ℕ}(live:s ≤ N)(W:Rep G ((C₀).side s p))(tier:W.p=(levels).budget s)
    (beta:W.beta=((C₀).path.rep N p s).beta):
    0 ≤ Coat.gStep W.beta/W.p.threshold ∧ Coat.gStep W.beta/W.p.threshold ≤ 2:=by
  let B:=(levels).clock.hatBeta s
  have bp:0<B:=zero_lt_one.trans_le ((levels).fits.delayed s).le
  have band:B/2 ≤ W.beta:=beta ▸ (R.makes.wilson.represents N p s live).band.1
  have wp:0<W.beta:=lt_of_lt_of_le (half_pos bp) band
  have rt:Real.sqrt B ≤ 2*Real.sqrt W.beta:=by
    nlinarith [Real.sq_sqrt bp.le,Real.sq_sqrt wp.le,Real.sqrt_nonneg B,Real.sqrt_nonneg W.beta]
  have gt:Coat.gStep W.beta ≤ 2*(Real.sqrt B)⁻¹:=by
    change (Real.sqrt W.beta)⁻¹ ≤ 2*(Real.sqrt B)⁻¹
    rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ (Real.sqrt_pos.mpr wp) (Real.sqrt_pos.mpr bp)]
    linarith
  have floor:(Real.sqrt B)⁻¹ ≤ W.p.threshold:=by
    rw [tier]
    exact le_mul_of_one_le_right (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.one_le_exp (sq_nonneg _))
  exact ⟨div_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) W.p.threshold_pos.le,
    (div_le_iff₀ W.p.threshold_pos).mpr (gt.trans (mul_le_mul_of_nonneg_left floor (by norm_num)))⟩

theorem scale {t:ℝ}(pos:0 ≤ t)(bound:t ≤ 2)(x:(Fr).Coeff):
    (Fr).coeffSize ((Fr).scaled t x) ≤ (2:ℝ)^WilsonOriginalAdjacentMicroscopicPrice.height R d*(Fr).coeffSize x:=by
  unfold Frame.coeffSize
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  change ‖((t^((Fr).grades j).2:ℝ):ℂ)*x j‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg pos _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (pow_le_pow_left₀ pos bound _).trans (pow_le_pow_right₀ (by norm_num)
    (Finset.le_sup (f:=fun j:(Fr).Index=>((Fr).grades j).2) (mem_univ j)))

theorem march {k s N p:ℕ}(ref:(C₀).ref d ≤ k)(route:k ≤ s)(live:s ≤ N)(v:(C₀).label d)(ε:ℝ)
    (steps:∀i,k ≤ i→i<s→((levels).params (i+1)).columns ≤ (((C₀).S.block i).val:ℝ)^ε):
    (Fr).coeffSize (columns C₀ d s N p v) ≤ ((C₀).S.a k/(C₀).S.a s)^ε*(Fr).coeffSize (columns C₀ d k N p v):=by
  induction s,route using Nat.le_induction with
  | base => rw [div_self ((C₀).S.a_pos _).ne',Real.one_rpow,one_mul]
  | succ i edge prev =>
    have hp:=prev (Nat.le_trans (Nat.le_succ i) live) (fun j l h=>steps j l (h.trans (Nat.lt_succ_self i)))
    let L:=(((C₀).S.block i).val:ℝ)
    have bl:0<L:=by dsimp only [L];exact_mod_cast ((C₀).S.block i).property
    have back: (Fr).coeffSize (columns C₀ d (i+1) N p v) ≤ ((levels).params (i+1)).columns*
        (Fr).coeffSize (columns C₀ d i N p v):=
      (R.makes.calibrated d N p (ref.trans (edge.trans (Nat.le_trans (Nat.le_succ i) live)))).back i (ref.trans edge)
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) live) (((C₀).factory d N p).terminal.symm v)
    have non:0 ≤ (Fr).coeffSize (columns C₀ d i N p v):=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
    have money:(C₀).S.a k/(C₀).S.a i*L=(C₀).S.a k/(C₀).S.a (i+1):=by
      rw [(C₀).S.a_step,div_div_eq_mul_div];ring
    calc
      _ ≤ L^ε*(Fr).coeffSize (columns C₀ d i N p v):=back.trans (mul_le_mul_of_nonneg_right (steps i edge (Nat.lt_succ_self i)) non)
      _ ≤ L^ε*(((C₀).S.a k/(C₀).S.a i)^ε*(Fr).coeffSize (columns C₀ d k N p v)):=mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg bl.le _)
      _=((C₀).S.a k/(C₀).S.a (i+1))^ε*(Fr).coeffSize (columns C₀ d k N p v):=by
        rw [←money,Real.mul_rpow (div_nonneg ((C₀).S.a_pos _).le ((C₀).S.a_pos _).le) bl.le];ring

theorem original {k s N p:ℕ}(home:Opened C₀ d s p)(ref:(C₀).ref d ≤ k)(route:k ≤ s)(live:s ≤ N)
    (W:Rep G ((C₀).side s p))(tier:W.p=(levels).budget s)(beta:W.beta=((C₀).path.rep N p s).beta)
    (v:(C₀).label d)(ε:ℝ)
    (steps:∀i,k ≤ i→i<s→((levels).params (i+1)).columns ≤ (((C₀).S.block i).val:ℝ)^ε):
    let raw:=((C₀).factory d N p).terminal.symm v
    let y:=fitting (C:=C₀) d N p s R.makes home live raw
    let g:=Coat.gStep W.beta
    (Fr).coeffSize ((Fr).scaled (g/W.p.threshold) y)  ≤ 
      (2:ℝ)^(WilsonOriginalAdjacentMicroscopicPrice.height R d+1)*((C₀).S.a k/(C₀).S.a s)^ε*
        (C₀).S.a k^d*(Fr).coeffSize (awake C₀ d k N p v):=by
  intro raw y g
  have ga:=gauge R live W tier beta
  have big:=scale R d ga.1 ga.2 y
  have fit:(Fr).coeffSize y ≤ 2*(Fr).coeffSize (columns C₀ d s N p v):=(size_gap d N p s R.makes home live raw).1
  have corr:=march R d ref route live (p:=p) v ε steps
  have fix:(C₀).S.a k^d*(Fr).coeffSize (awake C₀ d k N p v)=(Fr).coeffSize (columns C₀ d k N p v):=by
    simp only [awake,Frame.coeffSize,Pi.smul_apply,norm_smul,←Finset.mul_sum,norm_inv,norm_pow,
      Complex.norm_real,Real.norm_of_nonneg ((C₀).S.a_pos _).le]
    field_simp [((C₀).S.a_pos k).ne']
  calc
    _ ≤ (2:ℝ)^WilsonOriginalAdjacentMicroscopicPrice.height R d*(2*(((C₀).S.a k/(C₀).S.a s)^ε*
        (Fr).coeffSize (columns C₀ d k N p v))):=big.trans (mul_le_mul_of_nonneg_left
        (fit.trans (mul_le_mul_of_nonneg_left corr (by norm_num))) (by positivity))
    _ = _:=by rw [pow_succ,←fix];ring

end YM.Integration.WilsonOriginalNullReleasedStation

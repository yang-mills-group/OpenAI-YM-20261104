import YM.Integration.WilsonMaxwellThermometerReflectedUniformFare
import YM.Integration.WilsonMaxwellThermometerReflectedOlder
/-! Issue the finite two-socket normalization on the independent band with
its actual metered inputs decided on the other, physical board. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedEntered
open Filter Function Finset MeasureTheory Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open Source Source.Drops Labels XSpace XSpace.Normalize Maxwell
open WilsonMarkedIndependentNormalizedElection (normalized)
open WilsonMaxwellThermometerIndependentReflection (panel degrees cut posted reading pair)
open WilsonMaxwellThermometerReflectedSources (fields units signs)
open WilsonNeutralCopiedField (point)
open scoped Classical BigOperators Topology
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonMaxwellThermometerReflectedPhysicalColumns (levels)
open WilsonMaxwellThermometerReflectedStation (Name)
open WilsonMaxwellThermometerReflectedScalar (Bits)
open WilsonPositionProgramNormalizedMaster (fee)
open private center from YM.Integration.WilsonMaxwellThermometerReflectedScalar
open private quota from YM.Integration.WilsonMaxwellThermometerReflectedOlder
variable {G:Gauge}{D k u e:ℕ}(R:Run G)(d:Fin 2→ℕ)(fit:∀i,levels i<d i)
local notation "Q" => deck (G:=G) levels d fit
def value (big:0<D)(φ:Wilt Q)(X:Name→Herit Q)(m v₀ N k t:ℕ)(n:Name):ℝ:=
  reading R big φ (X n) m v₀ N k t (point ((primes G).F 0) 0)
def current (big:0<D)(φ:Wilt Q)(X:Name→Herit Q)(m v₀ N k:ℕ)(s:Bool):ℂ:=
  WilsonMaxwellThermometerReflectedCovariance.current (fun n t=>value R d fit big φ X m v₀ N k t n) s

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (big:0<D)(rails:Rails 0 k u e)(he:1 ≤ e)(cap:capP Q ≤ k):
    ∃floor:ℕ,∀(U:XSpace.Run){stage:ℕ}(B:WilsonPositionProgramReporterBand.Band R U stage)
    (φ:Wilt Q)(w:Fin 2→ℝ),(∀ᶠ z:ℝ in atTop,Bough Q φ 1 z w) →
    ∀cost:ℝ,0≤cost → ∃C:ℝ,0≤C ∧ ∃p:ℕ,∀ᶠ t:ℕ in atTop,let m:=B.reporter+t
    ∀v₀:ℕ,floor ≤ v₀ → B.lower t ≤ v₀ → v₀ ≤ m → ∀N:ℕ,m ≤ N →
    ∀X:Name→Herit Q,(∀n i,fee (X n) e i ≤ cost) → ∀s:Bool,
        ‖current R d fit big φ X m v₀ N k s‖ ≤ C*(1+(B.index t:ℝ))^p:=by
  let L:=R.family.path.levels
  obtain ⟨C₀,B₀,cpos,bpos,p,q,main⟩:=WilsonPositionProgramNormalizedAmplitude.original R simple v funded big rails levels d fit cap
  obtain ⟨floor,older⟩:=eventually_atTop.mp main
  refine ⟨floor,?_⟩
  intro U stage B φ w profile allowance allow
  obtain ⟨z₀,lateZ⟩:=eventually_atTop.mp profile
  let E:=|(1+(Real.log 3)⁻¹)*(U.reserve:ℝ)*Real.log U.ratio|
  have hepos:0≤E:=abs_nonneg _
  let M:=1+|z₀|+|Real.log U.ratio|+E
  have one:1 ≤ M:=by dsimp [M]; linarith [abs_nonneg z₀,abs_nonneg (Real.log U.ratio),hepos]
  let gross:ℝ:=C₀*∏i:Fin 2,|w i| *(B₀*allowance)
  let K:=p+q*2
  let F:ℝ:=gross*M^K
  have gpos:0≤gross:=mul_nonneg cpos.le (Finset.prod_nonneg fun i _=>mul_nonneg (abs_nonneg _) (mul_nonneg bpos.le allow))
  have fpos:0 ≤ F:=mul_nonneg gpos (pow_nonneg (zero_le_one.trans one) _)
  refine ⟨(Fintype.card Bits:ℝ)*(F+2*F^2),by positivity,2*(2*K),?_⟩
  filter_upwards [WilsonPositionProgramLowerWindowPrice.original R U simple B,
    WilsonPositionProgramInversionWindowCost.bounds R U simple B] with t bound lower
  intro m v₀ active start vm N top X fundedX s
  let i:ℝ:=B.index t
  let h:ℝ:=(1+i)^2
  let Z:=M*h
  have hi:0 ≤ i:=Nat.cast_nonneg _
  have hh:1 ≤ h:=by dsimp [h]; nlinarith only [hi,sq_nonneg i]
  have hz:0 ≤ Z:=mul_nonneg (zero_le_one.trans one) (zero_le_one.trans hh)
  have Zbig:M ≤ Z:=le_mul_of_one_le_right (zero_le_one.trans one) hh
  have bought:Bough Q φ 1 Z w:=lateZ _ (by
    apply le_trans _ Zbig; dsimp [M];linarith [le_abs_self z₀,abs_nonneg (Real.log U.ratio),hepos])
  have zpos:0 ≤ zz L m:=lower.1
  have inside:zz L m ≤ Z:=by
    calc
      _  ≤  i*Real.log U.ratio:=bound.1
      _  ≤  i*|Real.log U.ratio|:=mul_le_mul_of_nonneg_left (le_abs_self _) hi
      _  ≤  h*M:=mul_le_mul (by dsimp [h];nlinarith only [hi,sq_nonneg i])
        (by dsimp [M];linarith [abs_nonneg z₀,hepos]) (abs_nonneg _) (zero_le_one.trans hh)
      _=Z:=mul_comm ..
  have calendar:Compar L.S (zz L) v₀ m ≤ Z:=(bound.2 v₀ start vm).trans
    (quota U (B.index t) (Z:=M) (by dsimp only [M,E];linarith [abs_nonneg z₀]))
  have paid:=older v₀ active
  let mass(n:Name):=C₀*∏i:Fin 2,w i*(B₀*fee (X n) e i)
  have booked:Bough Q φ (paceT L.S m m) Z w:=by rwa [pace_self]
  have fare (n:Name)(j:ℕ)(hj:j ≤ 1):‖value R d fit big φ X m v₀ N k j n‖ ≤ F*h^K:=by
    have cost:= (paid (X n) m m vm le_rfl φ w Z calendar
      booked j (hj.trans he) (point ((primes G).F 0) 0) N top).1
    change ‖value R d fit big φ X m v₀ N k j n‖ ≤ 
      C₀*Z^p*∏i:Fin 2,w i*((B₀*(zz L m)^q)*WilsonPositionProgramNormalizedMaster.fee (X n) e i) at cost
    have priceEq:C₀*Z^p*(∏i:Fin 2,w i*((B₀*(zz L m)^q)*WilsonPositionProgramNormalizedMaster.fee (X n) e i))=
      mass n*(Z^p*((zz L m)^q)^2):=by simp only [mass,Fin.prod_univ_two];ring
    rw [priceEq] at cost
    have ge:mass n ≤ gross:=by
      apply mul_le_mul_of_nonneg_left _ cpos.le
      apply Finset.prod_le_prod
      · intro i _
        have nn:0≤fee (X n) e i:=by unfold fee;positivity
        exact mul_nonneg (bought.lanes i).1 (mul_nonneg bpos.le nn)
      · intro i _
        have nn:0≤fee (X n) e i:=by unfold fee;positivity
        exact mul_le_mul (le_abs_self _) (mul_le_mul_of_nonneg_left (fundedX n i) bpos.le)
          (mul_nonneg bpos.le nn) (abs_nonneg _)
    have nz:0 ≤ Z^p*((zz L m)^q)^2:=by positivity
    apply cost.trans
    calc
      _  ≤  gross*(Z^p*(Z^q)^2):=
        mul_le_mul ge (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (pow_nonneg zpos _) (pow_le_pow_left₀ zpos inside _) _) (pow_nonneg hz _))
          nz gpos
      _ = F*h^K:=by rw [←pow_mul,←pow_add]; simp only [F,Z,K,mul_pow]; ring
  let A:=F*h^K
  have apos:0 ≤ A:=mul_nonneg fpos (pow_nonneg (zero_le_one.trans hh) _)
  have valid (y:Bits):‖signs y*(pair (fun S j=>value R d fit big φ X m v₀ N k j (s,y,S)):ℂ)‖ ≤  A+2*A^2:=by
    rw [norm_mul,WilsonMaxwellThermometerReflectedSources.price,one_mul,Complex.norm_real]
    exact center _ apos (fun S j hj=>fare (s,y,S) j hj)
  calc
    _ ≤ ∑y:Bits,‖signs y*(pair (fun S j=>value R d fit big φ X m v₀ N k j (s,y,S)):ℂ)‖:=norm_sum_le ..
    _ ≤ (Fintype.card Bits:ℝ)*(A+2*A^2):=by
      calc _ ≤ ∑_y:Bits,(A+2*A^2):=sum_le_sum (fun y _=>valid y)
           _ = _:=by rw [sum_const,card_univ,nsmul_eq_mul]
    _ ≤ (Fintype.card Bits:ℝ)*(F+2*F^2)*h^(2*K):=by
      rw [mul_assoc];apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [mul_comm 2 K,pow_mul,add_mul]
      have tpow:1 ≤ h^K:=one_le_pow₀ hh
      have gain:h^K ≤ (h^K)^2:=by rw [pow_two];exact le_mul_of_one_le_right (zero_le_one.trans tpow) tpow
      dsimp [A];rw [mul_pow];nlinarith only [mul_le_mul_of_nonneg_left gain fpos]
    _ = _:=by dsimp [h,i];rw [←pow_mul]

end YM.Integration.WilsonMaxwellThermometerReflectedEntered
end

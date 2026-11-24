import YM.Integration.WilsonMaxwellThermometerReflectedScalar

/-! Complete reflected original scalar reports through their genuine earlier
infrared stop. The same two source fields and cofactor products retain
all intervening scalar deposits. The fee precedes the auxiliary cutoff. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedOlder
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
variable {G:Gauge} {D k u e:ℕ} (R:Run G)

open WilsonMaxwellThermometerReflectedScalar (Bits Name submitted)
open private center from YM.Integration.WilsonMaxwellThermometerReflectedScalar
variable {l d:ℕ}(h4:4<l)(h6:6<d)(a:Axis)(b:Sec G 6)
def money (big:0<D)(φ:Wilt (panel (G:=G) h4 h6))(m v₀ N k t:ℕ)(n:Name):ℝ:=
  reading R big φ (submitted h4 h6 a b n) m v₀ N k t (point ((primes G).F 0) 0)

theorem lodged (big:0<D)(φ:Wilt (panel (G:=G) h4 h6))(m N k t:ℕ)(n:Name):
    money R h4 h6 a b big φ m m N k t n=WilsonMaxwellThermometerReflectedScalar.money R h4 h6 a b big φ m N k t n:=rfl

def connected (big:0<D)(φ:Wilt (panel (G:=G) h4 h6))(m v₀ N k:ℕ)(s:Bool):ℂ:=
  ∑y:Bits,signs y*(pair (fun S t=>money R h4 h6 a b big φ m v₀ N k t (s,y,S)):ℂ)

private theorem quota (U:XSpace.Run)(n:ℕ){Z:ℝ}(bound:1+|Real.log U.ratio|+
    |(1+(Real.log 3)⁻¹)*(U.reserve:ℝ)*Real.log U.ratio|≤Z):
    WilsonPositionProgramLowerWindowPrice.quota U n ≤ Z*(1+(n:ℝ))^2:=by
  let A:=Real.log U.ratio;let B:=(1+(Real.log 3)⁻¹)*(U.reserve:ℝ)*A
  let j:ℝ:=n
  have hj:0≤j:=Nat.cast_nonneg _
  have hi:j≤(1+j)^2:=by nlinarith only [hj,sq_nonneg j]
  have hi':j*j≤(1+j)^2:=by nlinarith only [hj]
  have h₁:=mul_le_mul (le_abs_self A) hi hj (abs_nonneg A)
  have h₂:=mul_le_mul (le_abs_self B) hi' (mul_nonneg hj hj) (abs_nonneg B)
  have h₃:=mul_le_mul_of_nonneg_right (show |A|+|B|≤Z by linarith only [bound]) (sq_nonneg (1+j))
  calc
    _ = A*j+B*(j*j):=by dsimp [WilsonPositionProgramLowerWindowPrice.quota,A,B,j];ring
    _ ≤ (|A|+|B|)*(1+j)^2:=by rw [add_mul];exact add_le_add h₁ h₂
    _ ≤ _:=h₃

theorem original (U:XSpace.Run){stage:ℕ}(B:WilsonPositionProgramReporterBand.Band R U stage)
    (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (big:0<D)(rails:Rails 0 k u e)(he:1 ≤ e)(cap:capP (panel (G:=G) h4 h6) ≤ k)
    (φ:Wilt (panel (G:=G) h4 h6))(w:Fin 2→ℝ)(profile:∀ᶠ z:ℝ in atTop,Bough _ φ 1 z w):
    ∃floor:ℕ,∃C:ℝ,0 ≤ C ∧ ∃p:ℕ,∀ᶠ t:ℕ in atTop,let m:=B.reporter+t
      ∀v₀:ℕ,floor ≤ v₀ → B.lower t ≤ v₀ → v₀ ≤ m → ∀N:ℕ,m ≤ N → ∀s:Bool,‖connected R h4 h6 a b big φ m v₀ N k s‖ ≤ C*(1+(B.index t:ℝ))^p:=by
  let Q:=panel (G:=G) h4 h6
  let L:=R.family.path.levels
  let X:=submitted h4 h6 a b
  obtain ⟨C₀,B₀,cpos,bpos,p,q,main⟩:=WilsonPositionProgramNormalizedAmplitude.original R simple v funded big rails
    degrees (cut l d) (by intro i;fin_cases i <;> first | exact h4 | exact h6) cap
  obtain ⟨z₀,lateZ⟩:=eventually_atTop.mp profile
  obtain ⟨floor,older⟩:=eventually_atTop.mp main
  let E:=|(1+(Real.log 3)⁻¹)*(U.reserve:ℝ)*Real.log U.ratio|
  have hepos:0≤E:=abs_nonneg _
  let M:=1+|z₀|+|Real.log U.ratio|+E
  have one:1 ≤ M:=by dsimp [M]; linarith [abs_nonneg z₀,abs_nonneg (Real.log U.ratio),hepos]
  let mass (n:Name):=C₀*∏i:Fin 2,w i*(B₀*WilsonPositionProgramNormalizedMaster.fee (X n) e i)
  let K:=p+q*2
  let F:ℝ:=(∑n:Name,‖mass n‖)*M^K
  have fpos:0 ≤ F:=mul_nonneg (sum_nonneg fun _ _=>norm_nonneg _) (pow_nonneg (zero_le_one.trans one) _)
  refine ⟨floor,(Fintype.card Bits:ℝ)*(F+2*F^2),by positivity,2*(2*K),?_⟩
  filter_upwards [WilsonPositionProgramLowerWindowPrice.original R U simple B,
    WilsonPositionProgramInversionWindowCost.bounds R U simple B] with t bound lower
  intro m v₀ active start vm N top s
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
  have booked:Bough Q φ (paceT L.S m m) Z w:=by rwa [pace_self]
  have fare (n:Name)(j:ℕ)(hj:j ≤ 1):‖money R h4 h6 a b big φ m v₀ N k j n‖ ≤ F*h^K:=by
    have cost:= (paid (X n) m m vm le_rfl φ w Z calendar
      booked j (hj.trans he) (point ((primes G).F 0) 0) N top).1
    change ‖money R h4 h6 a b big φ m v₀ N k j n‖ ≤ 
      C₀*Z^p*∏i:Fin 2,w i*((B₀*(zz L m)^q)*WilsonPositionProgramNormalizedMaster.fee (X n) e i) at cost
    have priceEq:C₀*Z^p*(∏i:Fin 2,w i*((B₀*(zz L m)^q)*WilsonPositionProgramNormalizedMaster.fee (X n) e i))=
      mass n*(Z^p*((zz L m)^q)^2):=by simp only [mass,Fin.prod_univ_two];ring
    rw [priceEq] at cost
    have ge:mass n ≤ ∑x:Name,‖mass x‖:=
      (le_abs_self _).trans (single_le_sum (f:=fun x=>‖mass x‖) (fun j _=>norm_nonneg _) (mem_univ n))
    have nz:0 ≤ Z^p*((zz L m)^q)^2:=by positivity
    apply cost.trans
    calc
      _  ≤  (∑x:Name,‖mass x‖)*(Z^p*(Z^q)^2):=
        mul_le_mul ge (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (pow_nonneg zpos _) (pow_le_pow_left₀ zpos inside _) _) (pow_nonneg hz _))
          nz (sum_nonneg fun _ _=>norm_nonneg _)
      _ = F*h^K:=by rw [←pow_mul,←pow_add]; simp only [F,Z,K,mul_pow]; ring
  let A:=F*h^K
  have apos:0 ≤ A:=mul_nonneg fpos (pow_nonneg (zero_le_one.trans hh) _)
  have valid (y:Bits):‖signs y*(pair (fun S j=>money R h4 h6 a b big φ m v₀ N k j (s,y,S)):ℂ)‖ ≤  A+2*A^2:=by
    rw [norm_mul,WilsonMaxwellThermometerReflectedSources.price,one_mul,Complex.norm_real]
    exact center _ apos (fun S j hj=>fare (s,y,S) j hj)
  calc
    _ ≤ ∑y:Bits,‖signs y*(pair (fun S j=>money R h4 h6 a b big φ m v₀ N k j (s,y,S)):ℂ)‖:=norm_sum_le ..
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

end YM.Integration.WilsonMaxwellThermometerReflectedOlder

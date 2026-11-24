import YM.Integration.WilsonMaxwellThermometerReflectedSources
import YM.Integration.WilsonPositionProgramReportedCell
import YM.Integration.WilsonPositionProgramLowerWindowPrice

/-! Finite paid centered reflected first readings of the independently
inverse-normalized original field, with the common h=0 center average and
all four true phases. The cost precedes the finite inversion cutoff. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedScalar
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

abbrev Bits:=Fin 2→Bool
abbrev Masks:=Finset (Fin 2)
abbrev Name:=Bool×Bits×Masks
variable {l d:ℕ} (h4:4<l)(h6:6<d)(a:Axis)(b:Sec G 6)
def submitted (n:Name):Herit (panel (G:=G) h4 h6):=
  posted (fields h4 h6 a b n.1 n.2.1) (units h4 h6) n.2.2

def money (big:0<D)(φ:Wilt (panel (G:=G) h4 h6))(m N k t:ℕ)(n:Name):ℝ:=
  reading R big φ (submitted h4 h6 a b n) m m N k t (point ((primes G).F 0) 0)

theorem earned (big:0<D)(φ:Wilt (panel (G:=G) h4 h6))(m N k t:ℕ)(n:Name):
    let x:=normalized R.family.path.levels R.metals.O (panel (G:=G) h4 h6) (submitted h4 h6 a b n) m N
    money R h4 h6 a b big φ m N k t n=
      ∫o:CellR,(locale o (LodeStar R.family.path.levels R.metals.O φ x m m N 1)).2 t 0 Fin.elim0 ∂dayMeasure:=
  WilsonPositionProgramReportedCell.original R.family.path.levels R.metals.O ((primes G).T 0) big φ
    (normalized _ _ _ (submitted h4 h6 a b n) m N) m N k t (point _ 0)

def connected (big:0<D)(φ:Wilt (panel (G:=G) h4 h6))(m N k:ℕ)(s:Bool):ℂ:=
  ∑y:Bits,signs y*(pair (fun S t=>money R h4 h6 a b big φ m N k t (s,y,S)):ℂ)

private lemma center (J:Masks→ℕ→ℝ){L:ℝ}(pos:0 ≤ L)(w:∀S,∀t ≤ 1,‖J S t‖ ≤ L):
    ‖pair J‖ ≤ L+2*L^2:=by
  have two (s t ℓ q)(hs:s ≤ 1)(ht:t ≤ 1):‖J ℓ s *J q t‖ ≤ L^2:=by
    rw [norm_mul,pow_two];exact mul_le_mul (w _ _ hs) (w _ _ ht) (norm_nonneg _) pos
  change ‖_ - _ - _‖ ≤ _
  calc
    _ ≤ ‖J univ 1-J {0} 1*J {1} 0‖+‖J {0} 0*J {1} 1‖:=norm_sub_le ..
    _ ≤ (L+L^2)+L^2:=add_le_add ((norm_sub_le ..).trans (add_le_add (w _ _ le_rfl)
      (two _ _ _ _ le_rfl (by decide)))) (two _ _ _ _ (by decide) le_rfl)
    _=_:=by ring

theorem original (U:XSpace.Run){stage:ℕ}(B:WilsonPositionProgramReporterBand.Band R U stage)
    (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (big:0<D)(rails:Rails 0 k u e)(he:1 ≤ e)(cap:capP (panel (G:=G) h4 h6) ≤ k)
    (φ:Wilt (panel (G:=G) h4 h6))(w:Fin 2→ℝ)(profile:∀ᶠ z:ℝ in atTop,Bough _ φ 1 z w):
    ∃C:ℝ,0 ≤ C ∧ ∃p:ℕ,∀ᶠ t:ℕ in atTop,let m:=B.reporter+t
      ∀N:ℕ,m ≤ N → ∀s:Bool,‖connected R h4 h6 a b big φ m N k s‖ ≤ C*(1+(B.index t:ℝ))^p:=by
  let Q:=panel (G:=G) h4 h6
  let L:=R.family.path.levels
  let X:=submitted h4 h6 a b
  obtain ⟨C₀,B₀,cpos,bpos,p,q,main⟩:=WilsonPositionProgramNormalizedAmplitude.original R simple v funded big rails
    degrees (cut l d) (by intro i;fin_cases i <;> first | exact h4 | exact h6) cap
  obtain ⟨z₀,lateZ⟩:=eventually_atTop.mp profile
  let M:=1+|z₀|+|Real.log U.ratio|
  have one:1 ≤ M:=by dsimp [M]; linarith [abs_nonneg z₀,abs_nonneg (Real.log U.ratio)]
  let mass (n:Name):=C₀*∏i:Fin 2,w i*(B₀*WilsonPositionProgramNormalizedMaster.fee (X n) e i)
  let K:=p+q*2
  let F:ℝ:=(∑n:Name,‖mass n‖)*M^K
  have fpos:0 ≤ F:=mul_nonneg (sum_nonneg fun _ _=>norm_nonneg _) (pow_nonneg (zero_le_one.trans one) _)
  refine ⟨(Fintype.card Bits:ℝ)*(F+2*F^2),by positivity,2*K,?_⟩
  have dates:Tendsto (fun t:ℕ=>B.reporter+t) atTop atTop:=
    tendsto_atTop_mono (fun t=>Nat.le_add_left t _) tendsto_id
  filter_upwards [dates.eventually main,WilsonPositionProgramLowerWindowPrice.original R U simple B,
    WilsonPositionProgramInversionWindowCost.bounds R U simple B] with t paid bound lower
  intro m N top s
  let i:ℝ:=B.index t
  let h:ℝ:=1+i
  let Z:=M*h
  have hi:0 ≤ i:=Nat.cast_nonneg _
  have hh:1 ≤ h:=by dsimp [h];linarith only [hi]
  have hz:0 ≤ Z:=mul_nonneg (zero_le_one.trans one) (zero_le_one.trans hh)
  have Zbig:M ≤ Z:=le_mul_of_one_le_right (zero_le_one.trans one) hh
  have bought:Bough Q φ 1 Z w:=lateZ _ (by
    apply le_trans _ Zbig; dsimp [M];linarith [le_abs_self z₀,abs_nonneg (Real.log U.ratio)])
  have zpos:0 ≤ zz L m:=lower.1
  have inside:zz L m ≤ Z:=by
    calc
      _  ≤  i*Real.log U.ratio:=bound.1
      _  ≤  i*|Real.log U.ratio|:=mul_le_mul_of_nonneg_left (le_abs_self _) hi
      _  ≤  h*M:=mul_le_mul (by dsimp [h];linarith only [hi])
        (by dsimp [M];linarith [abs_nonneg z₀]) (abs_nonneg _) (zero_le_one.trans hh)
      _=Z:=mul_comm ..
  have booked:Bough Q φ (paceT L.S m m) Z w:=by rwa [pace_self]
  have fare (n:Name)(j:ℕ)(hj:j ≤ 1):‖money R h4 h6 a b big φ m N k j n‖ ≤ F*h^K:=by
    have cost:= (paid (X n) m m le_rfl le_rfl φ w Z (by change Compar L.S (zz L) m m ≤ Z; simpa [Compar] using inside)
      booked j (hj.trans he) (point ((primes G).F 0) 0) N top).1
    change ‖money R h4 h6 a b big φ m N k j n‖ ≤ 
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
  have valid (y:Bits):‖signs y*(pair (fun S j=>money R h4 h6 a b big φ m N k j (s,y,S)):ℂ)‖ ≤  A+2*A^2:=by
    rw [norm_mul,WilsonMaxwellThermometerReflectedSources.price,one_mul,Complex.norm_real]
    exact center _ apos (fun S j hj=>fare (s,y,S) j hj)
  calc
    _ ≤ ∑y:Bits,‖signs y*(pair (fun S j=>money R h4 h6 a b big φ m N k j (s,y,S)):ℂ)‖:=norm_sum_le ..
    _ ≤ (Fintype.card Bits:ℝ)*(A+2*A^2):=by
      calc _ ≤ ∑_y:Bits,(A+2*A^2):=sum_le_sum (fun y _=>valid y)
           _ = _:=by rw [sum_const,card_univ,nsmul_eq_mul]
    _ ≤ (Fintype.card Bits:ℝ)*(F+2*F^2)*h^(2*K):=by
      rw [mul_assoc];apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [mul_comm 2 K,pow_mul,add_mul]
      have tpow:1 ≤ h^K:=one_le_pow₀ hh
      have gain:h^K ≤ (h^K)^2:=by rw [pow_two];exact le_mul_of_one_le_right (zero_le_one.trans tpow) tpow
      dsimp [A];rw [mul_pow];nlinarith only [mul_le_mul_of_nonneg_left gain fpos]

end YM.Integration.WilsonMaxwellThermometerReflectedScalar

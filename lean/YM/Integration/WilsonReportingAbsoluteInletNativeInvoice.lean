import YM.Integration.WilsonReportingAbsoluteInletNativeCoordinates

/-! The actual endpoint, all intermediate physical clock coordinates, and the
selected inlet shape. The required independent finite inverse price is used
in its original normalization, two orders before the desired shift error. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonReportingAbsoluteInletNativeInvoice
open Function Filter Finset Real Lattice RG Wilson
open PhysicalNext.Repeat.Legato Pert.Asymptotics RGComparison.Core16
open WilsonReportingAbsoluteInletNativeDates
open WilsonReportingAbsoluteInletNativeCoordinates
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple) (slow:Pace R)

def InversePrice (p:ℕ) (h:ℕ→ℕ→ℕ→ℝ):Prop :=
  ∀ε>0,∀ᶠ i:ℕ in atTop,∀N per,i≤N→N≤ultraviolet R.family 2 i→
   |regulatorRun R.family N per N/regulatorRun R.family N per i-
     ∏j∈range (N-i),h N per (i+j)| ≤ ε*(regulatorRun R.family N per i)^(p+2)

include simple slow in
theorem paid {c:ℝ} (hc:1<c) (P p:ℕ) (h:ℕ→ℕ→ℕ→ℝ) (bill:InversePrice R p h)
    {ε:ℝ} (ep:0<ε):
    ∀ᶠ k:ℕ in atTop,∀u,ultraviolet R.family c k≤u→
      let t:=inlet R P u
      let N:=u+1
      ∃tu:t≤u, k≤t ∧
        (N-t:ℕ)*log (3:ℝ)≤R.family.S.scale N-R.family.S.scale t ∧
        R.family.S.scale N-R.family.S.scale t≤(Nat.ceil (width P+2):ℝ)*log (R.family.path.levels.clock.hatBeta N) ∧
        ∀per,∀T:Slices R.family.path.levels per,
          let d:=traversal T (tu.trans u.le_succ)
          let x:=shifts R per t N
          let v:=finite R N per t (h N per)
          let g:=regulatorRun R.family N per N
          0<g ∧ g≤1 ∧ Descent.offset v g+(x-v)=line R.family.path per t N ∧ (x-v) d.depth=0 ∧
            ∀l, l≤d.depth→|(x-v) l| ≤ ε*g^p := by
  let W:ℕ:=Nat.ceil (width P+2)
  let η:=ε/3^p
  have η0:0<η:=div_pos ep (by positivity)
  have tiny:0 < min η 1/64:=div_pos (lt_min η0 zero_lt_one) (by norm_num)
  obtain ⟨a,ledger⟩:=eventually_atTop.mp (bill _ tiny)
  obtain ⟨b,paired⟩:=eventually_atTop.mp (clocks R simple W)
  obtain ⟨f,hot⟩:=eventually_atTop.mp ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop 2)
  filter_upwards [eventually_ge_atTop a,eventually_ge_atTop b,eventually_ge_atTop f,
    WilsonReportingAbsoluteInletNativeDates.original R simple slow hc P] with k ak bk fk dates u uk t N
  let A:=R.family.path.levels
  have route:=dates u uk
  have tu:t≤u:=route.2.1.le
  have tN:t≤N:=tu.trans u.le_succ
  have admitted:=route.2.2 t le_rfl tN
  have cost:(width P+2)*log (A.clock.hatBeta u)≤(W:ℝ)*log (A.clock.hatBeta N):=
    (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (log_pos (A.fits.delayed u)).le).trans
      (mul_le_mul_of_nonneg_left (logarithm_monotone A simple u.le_succ) (Nat.cast_nonneg _))
  refine ⟨tu,route.1,admitted.2.1,admitted.2.2.trans cost,?_⟩
  intro per T d x v g
  have lg:=measured R T tN (h N per)
  have hN:0<A.clock.hatBeta N:=zero_lt_one.trans (A.fits.delayed N)
  have BN:0<R.family.path.β N per N:= (half_pos hN).trans_le (R.makes.wilson.represents N per N le_rfl).band.1
  have warm:2≤A.clock.hatBeta N:=hot N (fk.trans (route.1.trans tN))
  have lowerN:A.clock.hatBeta N/2 ≤ R.family.path.β N per N := (R.makes.wilson.represents N per N le_rfl).band.1
  have maxN:1≤R.family.path.β N per N:=by linarith only [warm,lowerN]
  have gN:0<g:=inv_pos.mpr (sqrt_pos.2 BN)
  refine ⟨gN,(inv_le_one₀ (sqrt_pos.2 BN)).2 (by simpa only [sqrt_one] using sqrt_le_sqrt maxN),lg.1,lg.2,?_⟩
  intro l hdepth
  let i:=t+l
  have it:t ≤ i:=Nat.le_add_right _ _
  have iN:i≤N:=by change l≤(traversal T tN).depth at hdepth;rw [traversal_depth] at hdepth;dsimp only [i];omega
  have ki:k≤ i:=route.1.trans it
  have times:=route.2.2 i it iN
  have hotI:2≤A.clock.hatBeta i:=hot i (fk.trans ki)
  have lo: A.clock.hatBeta i/2≤R.family.path.β N per i := (R.makes.wilson.represents N per i iN).band.1
  have hi: R.family.path.β N per N≤2*A.clock.hatBeta N := (R.makes.wilson.represents N per N le_rfl).band.2
  have Bi:0<R.family.path.β N per i:=by linarith only [hotI,lo]
  have rprice:A.clock.hatBeta N≤2*A.clock.hatBeta i:=paired i (bk.trans ki) iN (times.2.2.trans cost)
  have y8:R.family.path.β N per N≤8*R.family.path.β N per i:=by linarith only [hi,rprice,lo]
  have hI:0<A.clock.hatBeta i:=zero_lt_one.trans (A.fits.delayed i)
  have monotone:A.clock.hatBeta i≤A.clock.hatBeta N:=
    (log_le_log_iff hI hN).mp (logarithm_monotone A simple iN)
  have reverse:=comparable warm (R.makes.wilson.represents N per N le_rfl).band.1 Bi
    (R.makes.wilson.represents N per i iN).band.2 (show A.clock.hatBeta i≤2*A.clock.hatBeta N by linarith only [monotone,hN])
  have forward:=comparable hotI lo BN hi rprice
  have square:=squared Bi BN
  let gI:=regulatorRun R.family N per i
  have invFee:=ledger i (ak.trans ki) N per iN times.1
  have paid:=centered_price p η0 BN forward.1.le forward.2.1
    (div_pos reverse.1 forward.1) reverse.2.2.2 square.1 square.2 y8 invFee
  have distance:gI≤3*g:=(div_le_iff₀ gN).mp forward.2.2.2
  have power:gI^p≤3^p*g^p:=by rw [←mul_pow];exact pow_le_pow_left₀ forward.1.le distance p
  change |R.family.path.β N per i-R.family.path.β N per N-
    R.family.path.β N per N*((∏j∈range (N-i),h N per (i+j))^2-1)|≤ε*g^p
  calc _≤η*gI^p:=paid
       _≤η*(3^p*g^p):=mul_le_mul_of_nonneg_left power η0.le
       _=ε*g^p:=by dsimp only [η];field_simp
end YM.Integration.WilsonReportingAbsoluteInletNativeInvoice

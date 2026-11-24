import YangMills.WilsonProof.NativeSupport.JointNativeStep
import YangMills.WilsonProof.NativeSupport.JointMeasuredOpening
import YangMills.WilsonProof.NativeSupport.JointOriginalProfiles
import YangMills.WilsonProof.NativeSupport.JointHistoryWallet
import YangMills.WilsonProof.NativeSupport.FrozenCalendar
import YangMills.WilsonProof.NativeSupport.JointSkyScale
import YangMills.WilsonProof.NativeSupport.JointPhysicalVisit
import YangMills.WilsonProof.NativeSupport.JointBoundary

/-! Propagation on the visited, selected history, with the two actual marks
on each local original kernel. The recorded value retains every prior name. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 130000
noncomputable section
namespace YM.Integration.InletSusceptibility.Dated
open Function Finset Lattice RG Wilson Marker MergeProof MergeProof.Accent Extra.Multi MeasureTheory RGGapR2
open RGComparison.Core16 YM.Pressure Push.BetaTransport PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Legato.Campaign PhysicalNext.JointLoad.Heir FullVolume.Ray Push.PriceCompiler
open JointShadow Painted Packet
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V:Type} [Fintype V] [DecidableEq V]

def recorded (Y:Rep G n) (A:Finset V) (E:Support n → Config G n → Poly (Stock.census V))
    (K:Box n → Config G n → Poly (Stock.census V)) (Z:Config G n):Poly (Stock.census V):=
  play Y (Stock.census V) (exclaim Y.activities (Stock.census V)+clip A K) (fun X=>∑ i,clip A E i X) Z

omit [DecidableEq V] in
theorem unpaint {o:V → Site n} {M:ℕ} (painted:Occupancy (o ∘ (Prod.fst : Ink V → V)) M):Occupancy o M := by
  intro y
  let f (i:V):Ink V:=(i,false,false)
  have below:((univ:Finset V).filter (fun i=>o i=y)).card ≤
      ((univ:Finset (Ink V)).filter (fun i=>o i.1=y)).card := by
    apply card_le_card_of_injOn f
    · intro i hi;exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
    · intro i _ j _ eq;exact congrArg Prod.fst eq
  exact below.trans (painted y)

variable {I:Type} [Fintype I] [DecidableEq I] {R:Run G} {C:Campaign R}
variable {Θ:Luna.Tableau C.width 300} {v:ℕ → ℕ → ℝ} {t N per j:ℕ}
local notation "A" => R.alloy.B.a
local notation "s₀" => R.alloy.B.a.S.side j per
local notation "s₁" => R.alloy.B.a.S.side (j+1) per
local notation "sᵁ" => R.alloy.B.a.S.side N per
local notation "S" => R.alloy.B.a.clock.op j per
local notation "V₀" => Names I t N (R.alloy.B.a.S.side N per)
local notation "J₀" => Sources I j N (R.alloy.B.a.S.side j per)
local notation "p₁" => R.alloy.B.a.budget (j+1)
local notation "p₀" => R.alloy.B.a.budget j
local notation "r₁" => R.T.history N per (j+1)
local notation "r₀" => R.T.history N per j
variable (T:Slices R.alloy.B.a per) (tj:t ≤ j) (jn:j<N)
variable (loc:I → Site (R.alloy.B.a.S.side N per)) (F:I → Config G (R.alloy.B.a.S.side N per) → ℝ)
variable (σ:Bond (R.alloy.B.a.S.side j per)→ℝ) (δ c:ℝ)

def stageWeight (a:Names I t N (R.alloy.B.a.S.side N per)→ℂ) (h:ℝ) (k:(S).Choices) (X:Config G s₁) (Z:Config G s₀):ℂ:=
  ∏ i:J₀,(1+a (address T tj jn i)*(JointPhysical.sample S k (attached T tj jn (address T tj jn i))
    (probe δ h c σ (address T tj jn i)) X Z:ℂ)*value F h c i X)

variable (E:Support (R.alloy.B.a.S.side (j+1) per) → Config G (R.alloy.B.a.S.side (j+1) per) →
  Marker.Poly (Stock.census (Names I t N (R.alloy.B.a.S.side N per))))
variable (K:Box (R.alloy.B.a.S.side (j+1) per) → Config G (R.alloy.B.a.S.side (j+1) per) →
  Marker.Poly (Stock.census (Names I t N (R.alloy.B.a.S.side N per))))
local notation "dates" => (ready (I:=I) (t:=t) (N:=N) (n:=sᵁ))
local notation "Wts" => (fun _:V₀=>(2:ℝ))
local notation "L" => R.alloy.B.a.S.block j

theorem recorded_date [Nonempty I] (sky:Campaign.Sky R C Θ v) (simple:G.Simple)
    (slow:∀ n,((R.alloy.B.a.S.block n).val:ℝ) ≤ Real.log (2+Real.log (R.alloy.B.a.clock.hatBeta n)))
    (radius W:ℕ) (localF:∀ i,LocalOn (halo radius {loc i}) (F i)) (sym:∀ i,GaugeInvariant (F i))
    (ct:∀ i,Continuous (F i)) (unit:∀ i X,|F i X| ≤ 1)
    (cap:1 ≤ c) (allE:linkCap S ≤ c) (direction:∀ b,|σ b| ≤ 1) (large:3 ≤ (L).val)
    (u:ℝ) (proper:Rough.Ledger (place T loc jn) E K (r₁).p.threshold)
    (regular:RootedSheet (r₁).p id E Wts u) (dirty:RootedSheet (r₁).p Prod.fst K Wts u)
    (u0:0 ≤ u) :
    let x:ℝ:=height R N
    let s:ℕ:=(2*radius+1)^4
    let b:=priceDegree W s
    let ν:=tariffDegree Θ.price
    let r:=(x^radiusDegree W s ν)⁻¹
    let h:=r^2
    let upd:=((L).val:ℝ)^ν*u+x^(2*b+1)*(u^2+r^2)
    256 ≤ x → 2*c ≤ x → 64*((Fintype.card I:ℝ)+W+1) ≤ x →
    ((N-t:ℕ):ℝ) ≤ W*x → (scale (traversal T (tj.trans jn.le)):ℝ) ≤ x^W →
    ((p₁).B:ℝ) ≤ 2*x^2 → (A).clock.forcedAllowance (j+1) ≤ 1/x^b →
    Real.sqrt ((A).clock.forcedAllowance j) ≤ 1 → u ≤ r → 2*(|δ| *c) ≤ h →
    ∃ (O:Support s₀ → Config G s₀ → Poly (Stock.census V₀)) (D:Box s₀ → Config G s₀ → Poly (Stock.census V₀)),
      Rough.Ledger (place T loc jn.le) O D (r₀).p.threshold ∧
      RootedSheet (r₀).p id O Wts upd ∧ RootedSheet (r₀).p Prod.fst D Wts upd ∧
      ∀ a:V₀→ℂ,∀ Z,openAt a (recorded r₀ (dates j) O D Z)=
        ∑ k:(S).Choices,∫ X,(Push.SectorMeasure.taggedKernel S (r₁).beta k X Z:ℂ)*
          (openAt a (recorded r₁ (dates (j+1)) E K X)*stageWeight (R:=R) T tj jn F σ δ c a h k X Z) ∂prior G s₁ := by
  intro x s b ν r h upd heat hC mC days span roof quiet stain ur tilt
  let ys:=place (t:=t) T loc jn
  let out:=place (t:=t) T loc jn.le
  let born:=fresh (I:=I) (n:=sᵁ) (t:=t) (N:=N) j
  let bind:=address (I:=I) T tj jn
  let marks:=attached (I:=I) T tj jn
  let st (i:J₀):Support s₁:=halo radius {ys (bind i)}
  let M:=fullMultiplicity (Fintype.card I) (N-t) (scale (traversal T (tj.trans jn.le)))
  let A₁:=oldRadius (x^b) u h
  let D₁:=bornRadius (x^b) h
  let z:=x^(s+1)
  let γ:=(A).clock.forcedAllowance (j+1)
  have top₁:=R.T.choice.represents N per (j+1) jn
  have top₀:=R.T.choice.represents N per j jn.le
  have p1:(r₁).p=p₁:=top₁.vac
  have p0:(r₀).p=p₀:=top₀.vac
  have x1:1 ≤ x:=by linarith
  have xp:=zero_lt_one.trans_le x1
  obtain ⟨hpos,h1,_,_,_,_,_⟩:=calendar_radii W s ν (by linarith : 2 ≤ x) ur
  have M0:0 < M:=by dsimp only [M,fullMultiplicity];have hI:=Fintype.card_pos (α:=I);positivity
  have load:=multiplicity_budget (Fintype.card I) W (N-t) (scale (traversal T (tj.trans jn.le))) x x1 mC days span
  obtain ⟨siteCap,boxCap⟩:=site_budgets x (p₁).B heat roof
  have S0:0 ≤ siteFactor (p₁).B:=by unfold siteFactor;positivity
  have B0:(1:ℝ) ≤ (((p₁).B+(p₁).B+1:ℕ):ℝ)^4:=one_le_pow₀ (by exact_mod_cast (show 1 ≤ (p₁).B+(p₁).B+1 by omega))
  have quiet0:0 ≤ γ:=by change 0 ≤ Real.exp _;exact (Real.exp_pos _).le
  obtain ⟨oa,da,room,cash,err⟩:=funded_date W s ν heat (by exact_mod_cast M0 : 1 ≤ (M:ℝ)) S0 (pow_nonneg xp.le (s+1))
    B0 load siteCap le_rfl boxCap quiet0 quiet u0 ur
  have bills:=sky_stencil sky simple slow jn s
  have supply:fullFare (mountedFare γ (A₁*((M:ℝ)*siteFactor (p₁).B*u)) ((M:ℝ)*siteFactor (p₁).B*(D₁*(h*z)))) ≤
      PhysicalNext.Repeat.Legato.Campaign.Face.creditP (PhysicalNext.Repeat.Legato.Campaign.Face.timeEntry R (j+1))/M :=
    cash.trans (div_le_div_of_nonneg_right bills.2 (Nat.cast_nonneg _))
  have rawStencil (i:J₀):Real.exp ((p₁).supportExponent*coverNumber (p₁).B (st i))*(2*(h*c)) ≤ h*z := by
    have cover:(coverNumber (p₁).B (st i):ℝ) ≤ s:=by exact_mod_cast ball_cover p₁ (ys (bind i)) radius
    have base:Real.exp ((p₁).supportExponent*coverNumber (p₁).B (st i)) ≤ x^s:=by
      apply le_trans (Real.exp_le_exp.mpr _) bills.1
      apply (mul_le_mul_of_nonneg_left cover (p₁).exponent_pos.le).trans
      exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg s)
    calc
      _ = h*(Real.exp ((p₁).supportExponent*coverNumber (p₁).B (st i))*(2*c)) := by ring
      _ ≤ h*(x^s*x) := mul_le_mul_of_nonneg_left (mul_le_mul base hC (by linarith) (pow_nonneg xp.le _)) hpos.le
      _ = h*z := by rw [show z=x^s*x from pow_succ ..]
  let old:=dates (j+1)
  have prev:=clip_ledger r₁ ys E K old proper
  let Ec:=clip old E
  let Kc:=clip old K
  have en:=clip_root old regular
  have kn:=clip_root old dirty
  have parent:(S).ratio.parent ∘ ys=out:=funext (fun i=>(previous_site T jn i (loc:=loc) (t:=t)).symm)
  have occ₁:=occupancy (t:=t) T loc (tj.trans j.le_succ) jn
  have occ₀:=occupancy (t:=t) T loc tj jn.le
  have nativeParent:Occupancy (((S).ratio.parent ∘ ys) ∘ (Prod.fst : Ink V₀ → V₀)) M:=by rw [parent];exact occ₀
  have payload:=native_field T tj jn loc F radius h c hpos.le cap localF sym (fun i=>(ct i).measurable) unit
  let H:=C.L.prim N j per jn
  obtain ⟨f,fin,fout,visit,Y,sector⟩:=physical_joint_visit (per:=per) C (⟨j,jn⟩:Fin N)
  obtain ⟨a,fund⟩:=sky.receives j N per jn
  have fs:f.val.val.val.p=p₁:=fin ▸ p1
  have oldR:Rough.Ledger ys Ec Kc f.val.val.val.p.threshold:=fin.symm ▸ prev.1
  have g4:0 ≤ (p₁).supportExponent-4:=by have bd:=sky.supports (j+1);change 100 ≤ (p₁).supportExponent at bd;linarith
  have lin:=both_sheets Θ L large (γ:=(A).clock.forcedAllowance j) u0 stain err
  have half:1/min D₁ (A₁^2) ≤ 2/min D₁ (A₁^2):=div_le_div_of_nonneg_right (by norm_num) (le_min (zero_le_one.trans da) (sq_nonneg _))
  have outRate:(R.rolls.L ((A).clock.J (j+1)))=L:=(Extra.Iteration.block_eq R.alloy.B.valid j).symm
  have arrival:=BoardAdmission.native_step H Θ ys Wts born bind st (value F h c) (fun _=>h*c) marks (probe δ h c σ)
    f Ec Kc simple visit sector fund oldR (fin.symm ▸ en) (fin.symm ▸ kn)
    (clip_ages old born (date_separate _) E) (clip_ages old born (date_separate _) K)
    u0 oa da (fun _=>by norm_num) (name_fresh T tj jn) (address_injective T tj jn)
    (fun i=>halo_subset radius _ (mem_singleton_self _)) (fun i=>(payload i).1) (fun i=>(payload i).2.1)
    (fun i=>(payload i).2.2.1) (fun _=>mul_nonneg hpos.le (zero_le_one.trans cap)) (fun i=>(payload i).2.2.2)
    M0 (unpaint occ₁) occ₁ nativeParent (mul_nonneg hpos.le (pow_nonneg xp.le _))
    (fs.symm ▸ rawStencil) (fs.symm ▸ g4) (fs.symm ▸ room) (fs.symm ▸ supply)
    (attached_before T tj jn) (fun i b _=>probe_borel δ h c σ i b)
    (fun i b _ _ he=>probe_unit σ tilt hpos h1 (zero_lt_one.trans_le cap) direction he.1 (he.2.trans allE) i b)
    (attached_root T tj jn loc)
  obtain ⟨O,D,ok,re,rk,read⟩:=arrival
  rw [outRate] at re
  refine ⟨O,D,?_,?_,?_,?_⟩
  · simpa only [parent,p0] using ok
  · rw [p0];exact root_mono re ((add_le_add le_rfl half).trans lin.1)
  · rw [p0];exact root_mono rk lin.2
  intro α Z
  have inc:old ⊆ dates j:=fun i hi=>mem_filter.mpr ⟨mem_univ _,Nat.le_trans j.le_succ (mem_filter.mp hi).2⟩
  have free (i:J₀):bind i∉old:=fun hi=>(disjoint_left.mp (date_separate sᵁ) hi (name_fresh T tj jn i)).elim
  have seen (i:J₀):bind i∈dates j:=mem_filter.mpr ⟨mem_univ _,(mem_filter.mp (name_fresh T tj jn i)).2.ge⟩
  have prevC (X:Config G s₁):confined old (recorded r₁ old E K X):=by
    rw [recorded,prev.2 X];exact confined_mask old _
  rw [fin,fout] at read
  have outputL:Rough.Ledger out O D (r₀).p.threshold:=by simpa only [parent,p0] using ok
  rw [recorded,(clip_ledger r₀ out O D (dates j) outputL).2 Z]
  apply measured_dated _ _ (recorded r₁ old E K) _ (value F h c) _ bind (read Z) α old (dates j) inc prevC _ (address_injective T tj jn) free seen
  intro k X i oldI
  have no:i∉born:=fun hf=>disjoint_left.mp (date_separate sᵁ) oldI hf
  simp only [marks,attached_before T tj jn i no,JointPhysical.sample,prod_empty,Complex.ofReal_one]

end YM.Integration.InletSusceptibility.Dated

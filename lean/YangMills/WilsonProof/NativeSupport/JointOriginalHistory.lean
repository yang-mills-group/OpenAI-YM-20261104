import YangMills.WilsonProof.NativeSupport.JointMatchedPath
import YangMills.WilsonProof.NativeSupport.JointUVAdmission
import YangMills.WilsonProof.NativeSupport.JointRecordedDate

/-! The finite physical campaign, down its full growing inlet, for arbitrary
independent microscopic placements and arbitrary signed interior bond tests. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 160000
noncomputable section
namespace YM.Integration.InletSusceptibility.Dated
open Function Finset Filter Lattice RG Wilson Marker MergeProof MergeProof.Accent MeasureTheory RGGapR2
open RGComparison.Core16 YM.Pressure Push.BetaTransport PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Pert.Asymptotics WilsonUniformUnmarkedInletEnergySites
open Packet JointShadow JointMoments
open scoped Classical BigOperators Topology
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] [Nonempty I] {R:Run G} {C:Campaign R}
variable {Θ:Luna.Tableau C.width 300} {v:ℕ→ℕ→ℝ} {t N per:ℕ}
local notation "A₀" => R.alloy.B.a
local notation "nᵁ" => R.alloy.B.a.S.side N per
local notation "V₀" => Names I t N (R.alloy.B.a.S.side N per)
local notation "Rt" => R.T.history N per
local notation "Wts" => (fun _:V₀=>(2:ℝ))
local notation "dates" => (ready (I:=I) (n:=nᵁ) (t:=t) (N:=N))

private theorem zero_record {V:Type} [Fintype V] [DecidableEq V] {n:Side} (Z:Config G n) (Y:Rep G n)
    {a c:ℝ} (vac:Y.activities.Valid Y.p a c) (old:Finset V):
    recorded Y old (fun _ _=>0) (fun _ _=>0) Z=Poly.bead (Stock.census V) (Y.eval Z:ℂ) := by
  have eq:(clip old (fun (_:Box n) (_:Config G n)=>(0:Poly (Stock.census V))))=0 := by
    funext i X;exact map_zero _
  simp only [recorded,eq,add_zero,clip,map_zero,sum_const_zero]
  exact empty_density Y vac Z

theorem history (sky:Campaign.Sky R C Θ v) (simple:G.Simple)
    (slow:∀ n,((R.alloy.B.a.S.block n).val:ℝ) ≤ Real.log (2+Real.log (R.alloy.B.a.clock.hatBeta n)))
    (blocks:∀ j,3 ≤ (R.alloy.B.a.S.block j).val)
    (T:Slices R.alloy.B.a per) (tn:t ≤ N) (loc:I→Site nᵁ) (F:I → Config G nᵁ→ℝ)
    (radius W:ℕ) (c:ℝ) (cap:1 ≤ c) (allE:∀ i,linkCap ((A₀).clock.op i per) ≤ c)
    (localF:∀ i,LocalOn (halo radius {loc i}) (F i)) (sym:∀ i,GaugeInvariant (F i))
    (ct:∀ i,Continuous (F i)) (unit:∀ i X,|F i X| ≤ 1) :
    let x:ℝ:=height R N
    let s:ℕ:=(2*radius+1)^4
    let b:=priceDegree W s
    let ν:=tariffDegree Θ.price
    let r:=(x^radiusDegree W s ν)⁻¹
    let h:=r^2
    let l (j:ℕ):=((R.alloy.B.a.S.block j).val:ℝ)^ν
    let u (j:ℕ):=wallet N l (x^(2*b+1)) r j
    256 ≤ x → 2*c ≤ x → 64*((Fintype.card I:ℝ)+W+1) ≤ x →
    ((N-t:ℕ):ℝ) ≤ W*x → (scale (traversal T tn):ℝ) ≤ x^W →
    (∀ j,t ≤ j → j ≤ N → (A₀).clock.forcedAllowance j ≤ 1/x^b ∧ Real.sqrt ((A₀).clock.forcedAllowance j) ≤ 1) →
    ∀ j,∀ jn:j ≤ N,t ≤ j →
      let d:=traversal T jn
      ∀ (δ:ℕ→ℝ) (σ:sites nᵁ d→ℝ),
      (∀ i,0 < i → i < d.depth → 2*(|δ i| *c) ≤ h) → (∀ q,|σ q| ≤ 1) →
      ∃ (O:Support ((A₀).S.side j per) → Config G ((A₀).S.side j per) → Poly (Stock.census V₀))
        (D:Box ((A₀).S.side j per) → Config G ((A₀).S.side j per) → Poly (Stock.census V₀)),
        Rough.Ledger (place T loc jn) O D ((Rt j).p.threshold) ∧
        RootedSheet (Rt j).p id O Wts (u j) ∧ RootedSheet (Rt j).p Prod.fst D Wts (u j) ∧
        ∀ (E:Finset I) (z:ℝ) (Z:Config G ((A₀).S.side j per)),
          (exposed (A:=A₀) F E h Z:ℂ)*openAt (params E (z:ℂ)) (recorded (Rt j) (dates j) O D Z)=
            (law d (line R.family.path per j N) (micro F E h) δ σ h z Z:ℂ) := by
  intro x s b ν r h l u heat hC mC days span stain j jn
  have width:2*(W:ℝ) ≤ x:=by linarith only [mC,(Nat.cast_nonneg (Fintype.card I):0 ≤ (Fintype.card I:ℝ)),(Nat.cast_nonneg W:0 ≤ (W:ℝ))]
  obtain ⟨un,ur,_⟩:=paid_calendar T tn W s ν heat width days span
  have x0:0 < x:=by linarith
  have hp:0 < h:=sq_pos_of_pos (inv_pos.mpr (pow_pos x0 _))
  induction jn using Nat.decreasingInduction with
  | self=>
    intro _ d
    dsimp only [d]
    rw [traversal_self]
    intro δ σ _ _
    have point:=R.T.choice.represents N per N le_rfl
    have uz:u N=0:=wallet_top ..
    refine ⟨fun _ _=>0,fun _ _=>0,empty_ledger (Rt N) _,?_,?_,?_⟩
    · rw [uz];exact empty_root .. 
    · rw [uz];exact empty_root ..
    intro E z Z
    rw [zero_record Z (Rt N) point.good.labels]
    change _*openAt _ (Poly.send (tag ∅) _) = _
    rw [open_send,prod_empty,one_mul]
    have bareR:(Rt N).eval Z=bare (line R.family.path per N N 0) Z:=congrFun (R.T.choice.starts N per).2 Z
    rw [exposed,dif_pos rfl]
    change (micro F E h Z:ℂ)*((Rt N).eval Z:ℂ)=((bare (line R.family.path per N N 0) Z*micro F E h Z:ℝ):ℂ)
    rw [bareR,Complex.ofReal_mul];ring
  | of_succ j jn ih=>
    intro tj d
    dsimp only [d]
    rw [traversal_push T jn]
    let dj:=traversal T jn
    let S:=(A₀).clock.op j per
    intro δ σ allowed signs
    let left:=if 0 < dj.depth then δ 1 else 0
    let right (b:Bond ((A₀).S.side j per)):=if 0 < dj.depth then σ (.inl b) else 0
    have leftPaid:2*(|left| *c) ≤ h:=by
      dsimp only [left]
      split
      · exact allowed 1 Nat.zero_lt_one (by change 1<dj.depth+1;omega)
      · rw [abs_zero,zero_mul,mul_zero];exact hp.le
    have rightPaid (b:Bond ((A₀).S.side j per)):|right b| ≤ 1:=by
      dsimp only [right];split
      · exact signs _
      · rw [abs_zero];exact zero_le_one
    have tailPaid (i:ℕ) (pos:0 < i) (end_:i < dj.depth):2*(|Descent.upβ δ i| *c) ≤ h:=
      allowed (i+1) (Nat.zero_lt_succ _) (Nat.succ_lt_succ end_)
    obtain ⟨O,D,ok,re,rk,read⟩:=ih (tj.trans j.le_succ) (Descent.upβ δ) (σ ∘ Sum.inr) tailPaid (fun q=>signs (.inr q))
    obtain ⟨O',D',paid,re',rk',mem⟩:=recorded_date (R:=R) T tj jn loc F right left c O D sky simple slow radius W
      localF sym ct unit cap (allE j) rightPaid (blocks j) (u (j+1)) ok re rk (un _) heat hC mC days span (budget_roof R simple jn)
      (stain _ (tj.trans j.le_succ) jn).1 (stain _ tj jn.le).2 (ur _ (tj.trans j.le_succ) jn) leftPaid
    have next:u j=l j*u (j+1)+x^(2*b+1)*(u (j+1)^2+r^2):=wallet_step jn l _ r
    refine ⟨O',D',paid,next.symm ▸ re',next.symm ▸ rk',?_⟩
    intro E z Z
    rw [exposed,dif_neg jn.ne,Complex.ofReal_one,one_mul,mem (params E (z:ℂ)) Z,law_push, next_line]
    have frame:=stage_word (R:=R) T tj jn F E left h c z right hp (zero_lt_one.trans_le cap)
    refine Eq.trans ?_ (scalar_push S (Rt (j+1)).beta (fun b e=>Real.exp (-(left*e))*(1+z*h*right b*e)) _ _ _ (read E z) Z)
    apply sum_congr rfl;intro k _
    apply integral_congr_ae;filter_upwards with X
    exact congrArg (fun w:ℂ=>(Push.SectorMeasure.taggedKernel S (Rt (j+1)).beta k X Z:ℂ)*
      (openAt (params E (z:ℂ)) (recorded (Rt (j+1)) (dates (j+1)) O D X)*w)) (frame k X Z)

end YM.Integration.InletSusceptibility.Dated

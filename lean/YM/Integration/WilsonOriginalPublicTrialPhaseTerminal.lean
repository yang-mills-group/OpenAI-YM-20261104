import YM.Integration.WilsonOriginalPublicTrialPhaseTrace
import YM.Integration.WilsonReplicaTerminalCarrier

/-! A complete replicated trial is born at K on the N-history. The terminal
Haar bill includes the original partition function exactly once. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseTerminal
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Push Marker Extra.Histories
open MergeProof Accent Extra.Multi Cells OPE.Therm PhysicalNext.Repeat.Legato Push.GridApprox
open OPE.Therm.ReplicaChessboard WilsonOriginalPublicTrialPhaseTrace
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {N p K u J:ℕ}
local notation "C" => R.family
local notation "A" => (C).path.levels
local notation "H" => (C).path
local notation "V" => Site ((C).side J p)

def opening (jk:J≤K) (M:Config G ((C).side K p)→ℂ) :=
  birth (Stock.census V) ((H).rep N p K) (fun i=>(tilesAt (C).S p jk).copy i M)

def arrival (jk:J≤K)(uk:u≤K)(M:Config G ((C).side K p)→ℂ) :=
  gust (H) N p K (opening R (N:=N) jk M) u uk

theorem integral (jk:J≤K) (uk:u≤K) (live:K≤N) (M:Config G ((C).side K p)→ℂ)
    (hi:Integrable (opening R (N:=N) jk M) (prior G ((C).side K p))) :
    (∫U,((arrival R (N:=N) jk uk M) U).part (Stock.final V) ∂prior G ((C).side u p)) =
      (partition G ((C).side N p) ((C).beta N p):ℂ)*
        (∫ U,(tilesAt (C).S p jk).fullAt (fun _=>M) U ∂scene (H) N p K) :=by
  let L := (Poly.get (Stock.final V)).restrictScalars ℝ
  have marg:=gust_sum (H) N p K (opening R (N:=N) jk M) hi uk
  have hj:=gust_live (H) N p K _ hi uk
  let T:=tilesAt (C).S p jk
  let D:=partition G ((C).side N p) ((C).beta N p)
  have nz:D≠0:=(partition_pos ((C).beta N p)).ne'
  calc
    _ = L (∫ U,arrival R (N:=N) jk uk M U ∂prior G ((C).side u p)) := L.integral_comp_comm hj
    _ = L (∫ U,opening R (N:=N) jk M U ∂prior G ((C).side K p)) := congr_arg L marg
    _ = ∫ U,(opening R (N:=N) jk M U).part (Stock.final V) ∂prior G ((C).side K p) := (L.integral_comp_comm hi).symm
    _ = _ :=by
      change _ = (D:ℂ)*(∫ U,(T.fullAt (fun _=>M)) U ∂scene (H) N p K)
      erw [account R.makes.wilson live (T.fullAt (fun _=>M))]
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with U
      simp only [opening,birth,Poly.part_smul,Mach,Extra.Trajectories.pass_fire]
      change ((((H).rep N p K).eval U:ℂ)*_)= (D:ℂ)*(((((H).rep N p K).eval U/D:ℝ):ℂ)*_)
      push_cast
      change _ = (D:ℂ) * (((((H).rep N p K).eval U:ℂ) / (D:ℂ)) * ∏i:V,T.copy i M U)
      change (((H).rep N p K).eval U:ℂ)*(∏i:V,T.copy i M U) = _
      field_simp [Complex.ofReal_ne_zero.mpr nz]

theorem original {I:Type} [Fintype I] (d:I→ℕ) (z:I→Site ((C).side K p)) (v:∀i,(C).label (d i))
    (ju:J≤u) (uk:u≤K)(live:K≤N)(r:ℕ)
    (fit:∀i,window (z i) (stencilRadius (C) (d i))⊆window 0 r)
    (space:room (A) J K r) :
    let jK:=ju.trans uk
    let M:=word R (N:=N) d z v
    let a:=actualTransport (C) (N:=N) M uk 1
    let X₀:=fun U=>M U-a
    ∀ (_hi:Integrable (opening R (N:=N) jK X₀) (prior G ((C).side K p)))
      (F₀:V → Config G ((C).side u p)→ℂ)
      (F₁:V→Box ((C).side u p) → Config G ((C).side u p)→ℂ)
      (o:V→Site ((C).side u p)) {w b h f:ℝ},0<w →
      Served ((H).rep N p u) F₀ F₁ (arrival R (N:=N) jK uk X₀) o (fun _=>w) ((A).budget u).supportExponent f →
      Vault (fun _:V=>w) F₀ F₁ b h →
      ‖(∫U,M U ∂scene (H) N p K)-a‖≤
        Real.exp (((C).S.a J/(C).S.a u)^4*Vac.treasury (A) u+b+h+2*f)/w :=by
  intro jK M a X₀ hi F₀ F₁ o w b h f hw served vault
  have en:=uk.trans live
  let P:=(H).rep N p u
  let g:=(A).clock
  let D:=((C).S.a J/(C).S.a u)^4*Vac.treasury (A) u+b+h+2*f
  let Z:=Fintype.card V
  have row:=R.makes.wilson.represents N p u en
  have pos:0<g.hatCoupling u:=inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans ((A).fits.delayed u)))
  have ht:g.hatCoupling u≤P.p.threshold:=by
    rw [show P.p=(A).budget u from row.vac];exact le_mul_of_one_le_right pos.le (Real.one_le_exp (sq_nonneg _))
  have wage:=sail (r:=fun _:V=>w) (fun _=>hw) served row.good (Overlay.beta_positive R.makes.wilson en).le
    vault ((A).budget u).exponent_pos.le (Stock.final V) (gust_live (H) N p K _ hi uk) _ pos ht
    (History.nonnegative (H) R.makes.wilson N p u en)
  have cap:=Vac.suffices_bill (p:=p) R.makes.wilson en Z b h (2*f) 1
  have bound:=wage.trans (Real.exp_monotone cap)
  rw [integral R jK uk live X₀ hi,History.partition_eq (H) R.makes.wilson N p u en,norm_mul,
    Complex.norm_real,Real.norm_of_nonneg (partition_pos _).le,mul_comm (partition ..),
    mul_div_cancel_right₀ _ (partition_pos _).ne'] at bound
  apply (WilsonOriginalPublicTrialPhaseTrace.original R d z v jK live uk r fit space).trans
  apply Stock.spacer _ D w Z (norm_nonneg _) hw Fintype.card_pos
  have fee: Poly.toll (R:=Stock.census V) (fun _=>w) (Stock.final V)=w^Z :=by simp [Poly.toll,Stock.final,Z]
  rw [fee] at bound
  apply bound.trans_eq
  congr 1
  change (Fintype.card (Site ((C).S.side u p)):ℝ)*Vac.treasury (A) u+(Z:ℝ)*(b+h+2*f*1)=(Z:ℝ)*D
  erw [Stock.tallies (C).S J u p]
  unfold Z D
  ring

end YM.Integration.WilsonOriginalPublicTrialPhaseTerminal

import YM.Integration.FVA1Physical.Marked.QuaySpatialSum
import YM.Integration.FVA1Physical.Round2.StencilExteriorTests

/-! Insert a new physical observable directly into any inherited positive
vacuum. Both the single regular term and every failed-mask correction are
funded before blocking. The resulting conditional reading uses that same
incoming vacuum even when the original UV cutoff is strictly finer. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Set Finset MeasureTheory Lattice RG YM.Wilson Source Labels Precision RG.Supply Input Org Extra.Histories
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Bandage.Harmonics PhysicalNext.Repeat.Legato.Round2
open ThroughLaunch Roof Push.PriceCompiler UVNext.CouplingReset Next.Foundations Graces Roost Mallow Coterie
open LocalLTE LocalLTE.Vinca LocalLTE.Concourse MergeProof Planned.GuardedAtom Planned.GuardedAtom.Guard
open Push Push.Local Push.AbsoluteSums RGComparison.Core16.Lam RGComparison.Core16.Catkin
open Further.LogJets
open scoped Classical BigOperators Topology

variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A:Alloy X D} {P:Bolt A} {R:Factor A}
    {rates:ℕ → ℝ} {W:Bid.Worth} {l:ℕ} (crew : Bandage.Harmonics R rates W P l)
    {N n m:ℕ} (hm:m<N)
local notation "H" => Issue.trail P
local notation "In" => (H).rep N n (m+1)
local notation "Out" => (H).rep N n m
local notation "fside" => (H).S.side (m+1) n
local notation "cside" => (H).S.side m n
local notation "δ" => A.B.a.clock.forcedAllowance (m+1)
local notation "F0" => (frames G).level 0
local notation "D0" => localSection G 0
local notation "S" => (H).levels.clock.op m n
local notation "L" => D.L (A.B.a.clock.J (m+1))
local notation "Ψs" => Spool.scaler (X.p.profile (A.B.a.clock.J m)) l L
local notation "κ" => Real.sqrt (A.B.a.clock.forcedAllowance m)

def birthCost {f:Side} (B:BudgetPoint) (S':Support f) (w u e:ℝ) :=
  B.mass S' u + hitWidth B*w*reservedMass B S' e/Real.sqrt w

private theorem fresh_clear {b:Side} (V:Rep G b) (Q:Coefficient ((frames G).level 0) b)
    (Y:Config G b) (good:flags V.p.threshold Y=∅) :
    Q.density 0 (localSection G 0) V Y=(V.eval Y:ℂ)*Q.exponentialEntry 0 (localSection G 0) V Y := by
  have quiet (a:Finset ℕ) : Q.marked V a Y=0 := by
    unfold Coefficient.marked
    split
    next ha =>
        have empty : a=∅ := by
          by_contra h
          obtain ⟨i,hi⟩:=Finset.nonempty_iff_ne_empty.mpr h
          have inclusion: (V.activities.forced i).inventory ⊆ a.biUnion (fun k=>(V.activities.forced k).inventory) :=
            Finset.subset_biUnion_of_mem (fun k=>(V.activities.forced k).inventory) hi
          rw [ha.2,good] at inclusion
          exact (V.activities.forced i).inventory_ne.ne_empty (Finset.subset_empty.mp inclusion)
        subst a
        simp
    next => rfl
  simp only [Coefficient.density,quiet,tsum_zero,mul_zero,add_zero]

include crew hm
theorem fresh_vacuum_source (simple:G.Simple) (hd:3≤A.B.a.clock.J m)
    (hd':3≤A.B.a.clock.J (m+1)) (T:Support fside) (anchored:0∈T)
    (f:Config G fside → ℂ) {u e:ℝ} (shape:(In).p.Regular T f) (jets:(In).p.supBounds 0 T f u)
    (osc:∀ V,‖f V-f 1‖≤e) :
    ∃ Q : Coefficient F0 cside, Q.Format 0 (hol G) Out ∧
      Q.density 0 D0 Out=(S).push (In).beta (fun V=>((In).eval V:ℂ)*f V) ∧
      Q.remBound 0 Out κ ((Ψs) * birthCost (In).p T δ (u+‖f 1‖) e) := by
  let Z:=crew.kube N (m+1) n hm
  let berths:=Z.supply (fun _:ℕ=>T)
  let Y:=Vault.draw F0 In T f berths
  have pos:=Extra.Histories.forcedPos A.B.a (m+1)
  have permit : hitWidth (In).p *Real.sqrt δ ≤ 1 := by
    rw [(P.choice.represents N n (m+1) hm).vac,Blush.glyph_eq]
    exact crew.tag.stamp _ _ (step_paid A.B.a (m+1)) 0 ((Nat.zero_le 3).trans hd') _ (A.B.valid.pays (m+1))|>.2 _ _ (params_eq A.B.valid (m+1)) rfl
  have raw:=Vault.roots F0 In T f berths anchored (P.choice.represents N n (m+1) hm).good pos
    (Dilation.usualPerm permit pos).2 shape (hol G) D0 osc (u+‖f 1‖)
    (bound_sub shape (regular_const (f 1)) jets (bound_const (f 1)))
  obtain ⟨form,_,density,_,tab⟩:=raw
  have rem : Y.remBound 0 In (Real.sqrt δ) (birthCost (In).p T δ (u+‖f 1‖) e) := tab.bound le_rfl
  let M:=Concourse.memo (F0).e0 Y
  obtain ⟨V⟩:=Vinca.proposed H N n m (hol G) (MergeProof.rack_format Z M (memo_format _ form))
    (MergeProof.keeps Z M (memo_cost _ rem))
  obtain ⟨out,idem,budget,_⟩:=crew.epochB hm hd simple Y form rem V
  exact ⟨_,out,idem.trans (congrArg ((S).push (In).beta) (funext density)),budget⟩

theorem fresh_reading_spatial (simple:G.Simple) (hd:3≤A.B.a.clock.J m)
    (hd':3≤A.B.a.clock.J (m+1)) (T:Support fside) (anchored:0∈T)
    (f:Config G fside → ℝ) {u e:ℝ}
    (shape:(In).p.Regular T (fun V=>(f V:ℂ))) (jets:(In).p.supBounds 0 T (fun V=>(f V:ℂ)) u)
    (osc:∀ V,‖(f V:ℂ)-(f 1:ℂ)‖≤e)
    (q s:ℕ) (nq:0<q) (hq:q≤(Out).p.order) {α:ℝ} (a0:0<α)
    (room:((s:ℝ)+1)*α*q*(6*(Out).p.B+2:ℝ)≤(Out).p.supportExponent)
    (U:Config G cside) (alive:U∈Boulevard.sunny (Out).p) :
    (∑ v : Fin q → Operand G cside, (1+(wordRadius 0 (List.ofFn v):ℝ))^s *
       ‖leftDerivs (fun V=>(MSbar.Bulk.expect S In V f : ℂ)) ((List.ofFn v).map compass) U‖) ≤
     (1+α⁻¹)^s*(4*Fintype.card G.ColorIndex*Push.Uniform.countCost α)^q*
       (((Out).p.threshold⁻¹)^q*((Ψs)*birthCost (In).p T δ (u+‖(f 1:ℂ)‖) e)) := by
  obtain ⟨Q,format,dens,budget⟩:=fresh_vacuum_source crew hm simple hd hd' T anchored _ shape jets osc
  have clean : (fun V=>(MSbar.Bulk.expect S In V f : ℂ)) =ᶠ[𝓝 U] Q.exponentialEntry 0 D0 Out := by
    filter_upwards [(Boulevard.sky (Out).p).mem_nhds alive] with V hv
    have hr:=congrFun dens V
    rw [fresh_clear Out Q V (Boulevard.smoky hv)] at hr
    have hmass : (Out).eval V=(S).push (In).beta (In).eval V := congrFun (P.choice.steps N n m hm).1 V
    have push : (S).push (In).beta (fun W=>((In).eval W:ℂ)*(f W:ℂ)) V = (((S).push (In).beta (f*(In).eval) V : ℝ):ℂ) := by
      unfold StepData.push
      simp only [Pi.mul_apply,Complex.real_smul,←Complex.ofReal_mul,smul_eq_mul]
      simp_rw [mul_comm ((In).eval _) (f _)]
      exact integral_complex_ofReal
    rw [push] at hr
    change ((MSbar.Bulk.expect S In V f:ℝ):ℂ)=_
    rw [MSbar.Bulk.expect,←hmass,Complex.ofReal_div,←hr]
    exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (SectorNext.Vacuum.strictly H P.choice N n m hm.le V).ne')
  have nonneg : 0 ≤ (Ψs)*birthCost (In).p T δ (u+‖(f 1:ℂ)‖) e := by
    obtain ⟨a,b,ha,hb,hab,_⟩:=budget
    exact (add_nonneg ha hb).trans hab
  apply polynomial_word_sum 0 q s _ a0 (mul_nonneg (pow_nonneg (inv_nonneg.mpr (Out).p.threshold_pos.le) _) nonneg)
    (fun _=>norm_nonneg _)
  intro v
  rw [(UVNext.PricedKernels.left_congr clean ((List.ofFn v).map compass)).self_of_nhds]
  have ne : List.ofFn v ≠ [] := by intro eq; have h:=congrArg List.length eq; simp only [List.length_ofFn,List.length_nil] at h;omega
  simpa only [List.length_ofFn] using rooted_entry D0 format budget (List.ofFn v) ne (by simpa using hq)
    (α:=((s:ℝ)+1)*α) (mul_nonneg (by positivity) a0.le) (by simpa using room) alive

end YM.Integration.FVA1Physical.Marked

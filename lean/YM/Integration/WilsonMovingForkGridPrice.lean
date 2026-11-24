import YM.Integration.WilsonMovingForkRay
import YM.Integration.WilsonSeparatedGridDesign

/-! Quantitative interpolation on the genuine registered j-grid for the complete
physical product. Its observations have arbitrary diameter and a fixed minimum
physical clearance. The stencil includes the far occupied locations. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonMovingForkGridPrice
open Function Filter Set Metric Extraction Spec Trace Trace.Pilot TraceExtension Climb
open Boundary Boundary.Surface GapsContact GapsContact.Ascent GapsContact.Tunnel EveryPhase
open Contacts.Mat WilsonSeparatedGridDesign WilsonSeparatedGridTree WilsonSeparatedPhysicalRay WilsonSeparatedBranchStencil
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel C.book).Hierarchy}{Z:Trace.Terrace.Arch C}
variable {n:ℕ}{E:Type}[Fintype E]

theorem direction (i:Fin n)(a:Axis):‖Points.direction i a‖≤directions n:=by
  have one:=Finset.single_le_sum (s:=Finset.univ) (f:=fun j:Fin n×Axis=>‖Points.direction j.1 j.2‖)
    (fun j _=>norm_nonneg _) (Finset.mem_univ (i,a))
  dsimp only [directions];linarith only [one]

theorem halo (m:ℕ){η:ℝ}(ep:0<η):
    ∃D:ℝ,0<D ∧ ∀δ:ℝ,0≤δ→δ≤D→∀X:Points n,(∀i j:Fin n,i≠j→η≤dist (X i) (X j))→
      ∀Y:Points n,dist Y X≤radius n m E δ→∀i a,∀v∈Icc 0 (width n m E),
      ∀j k:Fin n,j≠k→η/2≤dist (axisStep Y i a δ v j) (axisStep Y i a δ v k):=by
  let U:=((levels n:ℝ)+1)*span n m E
  have un:0≤U:=mul_nonneg (by positivity) span_nonneg
  have up:0<U+1:=by linarith
  refine ⟨(η/4)/(U+1),div_pos (by positivity) up,?_⟩
  intro δ dp cutoff X clear Y near i a v reach j k neq
  have w:δ*(U+1)≤η/4:=(le_div_iff₀ up).mp cutoff
  have rad:δ*span n m E+radius n m E δ≤η/4:=by
    have lhs:δ*span n m E+radius n m E δ=δ*U:=by unfold U radius;ring
    rw [lhs];rw [mul_add,mul_one] at w;linarith only [w,dp]
  let P:=axisStep Y i a δ v
  have h:dist P X≤η/4:=(dist_triangle _ Y _).trans ((add_le_add (step Y i a dp v reach) near).trans rad)
  have left:dist (X j) (P j)≤η/4:=by rw [dist_comm];exact (PiLp.dist_apply_le P X j).trans h
  have right:dist (P k) (X k)≤η/4:=(PiLp.dist_apply_le P X k).trans h
  linarith only [clear j k neq,dist_triangle (X j) (P j) (X k),dist_triangle (P j) (P k) (X k),left,right]

theorem original (hG:G.Simple)(bliss:Bliss F l Z H)(d:Fin n→ℕ){η:ℝ}(ep:0<η):
    ∃ν∈Ioc (0:ℝ) 1,∃p:ℕ,∀m:ℕ,∃D:ℝ,0<D ∧ ∃A:ℝ,0≤A ∧
    ∀ᶠr in trail,∀δ:ℝ,∀dp:0<δ,δ≤D→∀X:Points n,(∀i j:Fin n,i≠j→η≤dist (X i) (X j))→
      ∀ref:E→E4,∀v:(i:Fin n)→S.Field (d i),let f:=fun z:Points n=>S.classMoment S d (r • z) v
      ‖f X-read (sold m ref dp X) f‖≤ A*δ^(m+1)*(LogV r/ν)^p*∏i,Ascent.cost F (d i) r (v i):=by
  obtain ⟨ρ,rp,ν,hν,K,kp,p,issued⟩:=WilsonMovingForkTubeJets.model F hG bliss d (half_pos ep)
  refine ⟨ν,hν,p,fun m=>?_⟩
  obtain ⟨D,dh,halo⟩:=halo (E:=E) (n:=n) m ep
  let Q:=width n m E
  let L:=directions n
  have lp:0<L:=by dsimp [L,directions];positivity
  have qp:0≤Q:=(clusterRadius_pos (τ:=Fin n⊕E) (n:=m)).le
  let scalar:=((m+1:ℕ):ℝ)*Q^m*((m+1).factorial*K*L^(m+1)/ρ^(m+1)*(Q^(m+1)/(m.factorial:ℝ)))
  let T:=(1+total n m E)^levels n
  have sn:0 ≤ scalar:=by dsimp only [scalar];positivity
  have tn:0≤T:=by dsimp only [T];exact pow_nonneg (by linarith only [WilsonSeparatedGridTree.total_nonneg (n:=n) (m:=m) (E:=E)]) _
  refine ⟨D,dh,scalar*T,mul_nonneg sn tn,?_⟩
  filter_upwards [issued,self_mem_nhdsWithin (a:=0),(ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds]
    with r models hr small δ dp gap X clear ref v
  let f(z:Points n):=S.classMoment S d (r • z) v
  let cash:=(LogV r/ν)^p*∏i,Ascent.cost F (d i) r (v i)
  have cb:0≤cash:=mul_nonneg (pow_nonneg (div_nonneg (Real.log_nonneg ((one_le_inv₀ hr).mpr small)) hν.1.le) _)
    (Finset.prod_nonneg fun _ _=>Ascent.cost_pos ..)
  have paid:=WilsonSeparatedGridDesign.checked m ref dp X
  have localCost(Y:Points n)(reach:dist Y X≤radius n m E δ)(i:Fin n)(a:Axis)(U:Nodes m Q):
      ‖f Y-∑j,bleed U.v j • f (axisStep Y i a δ (U.v j))‖≤ scalar*δ^(m+1)*cash:=by
    let u:=L⁻¹ • Points.direction i a
    let c:=δ*L
    have cp:0<c:=mul_pos dp lp
    have un:‖u‖≤1:=by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr lp.le)]
      exact (inv_mul_le_one₀ lp).mpr (direction i a)
    have input:c • u=δ • Points.direction i a:=by
      dsimp only [c,u];rw [smul_smul,mul_assoc,mul_inv_cancel₀ lp.ne',mul_one]
    let y(t:ℝ):=axisStep Y i a δ t
    have chart(t:ℝ)(ht:t∈Icc 0 Q):∃g:ℂ→ℂ,AnalyticOnNhd ℂ g (closedBall 0 ρ) ∧
        (∀s∈closedBall 0 ρ,‖g s‖≤K*cash) ∧ (fun s=>f (y s))=ᶠ[𝓝 t] fun s=>g ((c*(s-t):ℝ):ℂ):=by
      obtain ⟨g,analytic,gross,same⟩:=models (y t) (halo δ dp.le gap X clear Y reach i a t ht) u un v
      refine ⟨g,analytic,fun z hz=>(gross z hz).trans_eq (by dsimp only [cash];ring),?_⟩
      have tends:Tendsto (fun s:ℝ=>c*(s-t)) (𝓝 t) (𝓝 0):=by
        have cont:Continuous (fun s:ℝ=>c*(s-t)):=by fun_prop
        simpa only [sub_self,mul_zero] using (cont.continuousAt (x:=t)).tendsto
      filter_upwards [tends.eventually same] with s hs
      have eq:y t+(c*(s-t)) • u=y s:=by
        rw [mul_comm c,←smul_smul,input];dsimp only [y,axisStep];rw [add_assoc,←add_smul];congr 2;ring
      simpa only [eq,f] using hs
    have bought:=WilsonMovingForkRay.original rp cp (mul_nonneg kp cb) U (fun t=>f (y t)) chart
    have init:y 0=Y:=by simp [y,axisStep]
    rw [init] at bought
    exact bought.trans_eq (by dsimp only [scalar,c];ring)
  have sale:=paid.2.2 f (scalar*δ^(m+1)*cash) (mul_nonneg (mul_nonneg sn (pow_nonneg dp.le _)) cb) localCost
  exact sale.trans_eq (by dsimp only [cash,T];ring)

end YM.Integration.WilsonMovingForkGridPrice

import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionEditedTransportTail

/-! All centers and all genuine unmasked transport slots are included.
Only one actual clear halo and clearance at the edited bond are required.
The number of original flags and the torus volume never enter the fare. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Finset Lattice RG Wilson Precision Push.Local WilsonStartup
open UVNext.PricedKernels
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

private theorem collar_kept (p:BudgetPoint)(c:Clip)(licensed:Decent c p)(o:Site n)(D:ℕ)
    (U:Fld)(good:Healthy p.threshold (halo (D+p.B) {o}) U)(s:Signed)(z:Site n)
    (inside:separation o (turnSites s 0 z)≤D):PathData.kept c p.threshold z (pull s 0 U):=by
  have turned:Healthy p.threshold (halo p.B {z}) (pull s 0 U):=by
    apply (healthy_pull s 0 p.threshold (halo p.B {z}) U).mp
    apply disjoint_left.mpr
    intro b hb bad
    obtain ⟨a,aa,rfl⟩:=mem_image.mp hb
    obtain ⟨u,uz,dst⟩:=halo_spec.mp aa
    rw [mem_singleton.mp uz] at dst
    have near:separation o (turnSites s 0 a)≤D+p.B:=by
      apply (separation_triangle o (turnSites s 0 z) _).trans
      rw [turn_sep];exact Nat.add_le_add inside dst
    exact disjoint_left.mp good (halo_spec.mpr ⟨o,mem_singleton_self _,near⟩) bad
  intro a
  by_cases far:p.B-2≤separation z a.1
  · exact too_far c p licensed _ _ _ far
  have near:a.1∈halo p.B {z}:=halo_spec.mpr ⟨z,mem_singleton_self _,by omega⟩
  have small:G.chord (faceValue (pull s 0 U) a)≤p.threshold:=
    le_of_not_gt (fun bad=>disjoint_left.mp turned near ((flags_spec ..).mpr ⟨a,anchor_visit a,bad⟩))
  exact small.trans (le_mul_of_one_le_right p.threshold_pos.le (Real.one_le_exp (div_nonneg (Nat.cast_nonneg _) c.radius_pos.le)))

def quadraticMask (P:PathData G)(c:Clip)(p:BudgetPoint)(W:Fld):ℝ:=
  (∑x:Face (Per n),P.baseTerm c p W x)-quadratic c P W

/-- Physical masked versus independent `quadratic`, including the genuine
clipped plaquette and every center on the original period. The estimate
requires no smallness conditions anywhere outside the displayed halo. -/
theorem original_quadratic_mask_price (p:BudgetPoint)(c:Clip)(P:PathData G){σ C Λ:ℝ}
    (pay:P.Bounds c σ C Λ)(licensed:Decent c p)(e:Edge (Site n))(D:ℕ)(U V:Fld)
    (out:∀l:Edge (Site n),l≠e → U l=V l)
    (good:Healthy p.threshold (halo (D+p.B) {e.1}) U)(after:e.1∉flags p.threshold V)(s:Signed):
    |quadraticMask P c p (pull s 0 U)-quadraticMask P c p (pull s 0 V)|≤
      8*C^2*(Fintype.card PlaqAxes:ℝ)*Real.exp (-(σ/2)*(D:ℝ))*basin (σ/2):=by
  let delta:=fun x:Face (Per n)=>(P.baseTerm c p (pull s 0 U) x-uncutBase P c (pull s 0 U) x)-
      (P.baseTerm c p (pull s 0 V) x-uncutBase P c (pull s 0 V) x)
  let fee:=8*C^2*Real.exp (-(σ/2)*(D:ℝ))
  let dist:=fun z:Site n=>separation e.1 (turnSites s 0 z)
  let w:=fun z:Site n=>Real.exp (-(σ/2)*(dist z:ℝ))
  have fn:0≤fee:=by dsimp only [fee];positivity
  have pre:Healthy p.threshold {e.1} U:=disjoint_left.mpr (fun z hz=>disjoint_left.mp good (halo_subset _ _ hz))
  have post:Healthy p.threshold {e.1} V:=disjoint_left.mpr (fun z hz=>mem_singleton.mp hz ▸ after)
  have matching(l:Edge (Site n))(h:l.1∉({e.1}:Support n)):U l=V l:=out l (fun eq=>h (eq ▸ mem_singleton_self _))
  have localPrice(x:Face (Per n)):|delta x|≤fee*w x.1:=by
    change |(P.baseTerm _ _ _ _-uncutBase _ _ _ _)-(P.baseTerm _ _ _ _-uncutBase _ _ _ _)|≤_
    rw [edited_quadratic_gap _ p c P U V matching pre post s x]
    by_cases yes:PathData.kept c p.threshold x.1 (pull s 0 U)
    · rw [if_pos yes,abs_zero];exact mul_nonneg fn (Real.exp_pos _).le
    rw [if_neg yes]
    have d:D<dist x.1:=lt_of_not_ge (fun near=>yes (collar_kept p c licensed e.1 D U good s x.1 near))
    have dd:(D:ℝ)≤(dist x.1:ℝ):=by exact_mod_cast d.le
    have rate:Real.exp (-σ*(dist x.1:ℝ))≤Real.exp (-(σ/2)*(D:ℝ))*w x.1:=by
      dsimp only [w];rw [←Real.exp_add];apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_left dd pay.width.le]
    exact (relocated_square P c pay e U V out s x).trans ((mul_le_mul_of_nonneg_left rate (by positivity : 0≤8*C^2)).trans_eq (by dsimp only [fee];ring))
  have law(W:Fld):quadraticMask P c p W=∑x:Face (Per n),(P.baseTerm c p W x-uncutBase P c W x):=by
    simp only [quadraticMask,uncutBase,quadratic,Finset.sum_sub_distrib]
  have geo:(∑z:Site n,w z)≤basin (σ/2):=by
    refine (Equiv.sum_comp (turnSites s 0) (fun a:Site n=>Real.exp (-(σ/2)*(separation e.1 a:ℝ)))).le.trans ?_
    exact funnel (half_pos pay.width) e.1
  have factor:(∑x:Face (Per n),fee*w x.1)=fee*(Fintype.card PlaqAxes:ℝ)*(∑z:Site n,w z):=by
    rw [Fintype.sum_prod_type]
    simp only [sum_const,card_univ,nsmul_eq_mul]
    simp_rw [←mul_assoc]
    rw [←Finset.mul_sum];ring
  rw [law,law,←Finset.sum_sub_distrib]
  change |∑x:Face (Per n),delta x|≤_
  calc
    _ ≤ ∑x:Face (Per n),|delta x|:=Finset.abs_sum_le_sum_abs .. 
    _ ≤ ∑x:Face (Per n),fee*w x.1:=sum_le_sum (fun x _=>localPrice x)
    _ ≤ _:=by rw [factor];exact (mul_le_mul_of_nonneg_left geo (mul_nonneg fn (Nat.cast_nonneg _))).trans_eq (by dsimp only [fee];ring)

end YM.Integration.FVA1Physical.Exchange.ShieldedAction

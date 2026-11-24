import YM.Integration.OriginalJointCoverSum
import YM.Integration.OriginalMarkedLiftAgreement

/-! The actual strongly priced cover may be presented at one prescribed
active anchor and normed at another. Thin clusters agree by a common
period. Thick clusters retain exponentially small, signed winding. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalCoverReanchoring
open Function Finset Lattice RG Wilson FreeResolvent Gauge Marker
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Motion
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Winding
open Precision WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Soil WilsonCoeffUV.Blue Work.F08
open OriginalRootedPacketLayout OriginalMarkedWindingAllRoots OriginalJointCoverDecay
open IndependentSourcePathFamily OriginalMarkedSourceComet
open scoped BigOperators Classical

variable {V : Type} [DecidableEq V] [Fintype V] {G : Gauge} {D k : V→ℕ} {J : Finset V}
    {n : Side} {e i l m N : ℕ} {A : ℝ} {Q : Realm G (e+1) Credit.leanC} {hm : Q.anchor ≤ m}

def place (base : V→Site n) (v : J) (p : J→Site n) :=
  PeriodicMarkedWinding.roots n (OriginalPhysicalWindingRows.complete J base p) v

omit [Fintype V] in
theorem actual (base : V→Site n) (v : J) (p : J→Site n) (w:J) :
    wrap n (place base v p w)=p w := by
  simp [place,PeriodicMarkedWinding.roots,OriginalPhysicalWindingRows.complete,w.property]

def row (X : FundedMarkedPathSelection.Input Q hm univ k D A) (base : V→Site n) (v : J)
    (L : Pen D J→L[ℝ]ℂ) (i l : ℕ) (p : J→Site n) (z : Fin l→PhysicalWilsonRootedHessian.Label G n) :=
  L (plume ((FundedMarkedPathSelection.output X J N (place base v p)).2 i l) n z)

theorem reanchor (X : FundedMarkedPathSelection.Input Q hm univ k D A)
    (hA : 0≤A) (hN : m<N) (closed : Cloze D k Q Credit.leanC)
    (M : Outerm G D) (well : Wellness k M) (shift : ∀t,ramble t M)
    (cells : V→Site (loose Q.draws m).L)
    (basis : ∀y,X.familyAt y=M (chartIn (loose Q.draws m) y cells))
    (base : V→Site n) (v w holder : J) (u : Site n) (L : Pen D J→L[ℝ]ℂ) (hi : i≤e) :
    let s := Vσ Q m hm
    let C := ‖L‖*(FundedMarkedPathSelection.price Q k D A J m*tiePay (Hooks G) l (s/4))
    account (diameterAt J) (fun p z => ‖row X (N:=N) base w L i l p z-row X (N:=N) base v L i l p z‖)
      (s/8) holder u ≤ (2*C*OriginalJointCoverSum.spatial J (Hooks G) l (s/8))*
        Real.exp (-(s/16)*(n.val:ℝ)) := by
  let s := Vσ Q m hm
  let M₀ := FundedMarkedPathSelection.price Q k D A J m
  let C := ‖L‖*(M₀*tiePay (Hooks G) l (s/4))
  have hs : 0<s := perk hm
  have h0 : 0≤M₀ := mul_nonneg (zero_le_one.trans (Credit.purchase _ (Q.depth m hm))) (pow_nonneg hA _)
  have hC : 0≤C := by
    dsimp [C]
    by_cases h : l=0
    · simpa [h,tiePay] using mul_nonneg L.opNorm_nonneg h0
    · exact mul_nonneg L.opNorm_nonneg (mul_nonneg h0 (pow_nonneg (boardPay_nn (by positivity)) _))
  have each (a : J) (p : J→Site n) (z : Fin l→PhysicalWilsonRootedHessian.Label G n) :
      ‖row X (N:=N) base a L i l p z‖≤ C*Real.exp (-(s/2)*(diameterAt J p z:ℝ)) := by
    apply (L.le_opNorm _).trans
    exact (mul_le_mul_of_nonneg_left (OriginalJointCoverDecay.output J (place base a p) X
      hA hN closed p (actual base a p) a hi z) (norm_nonneg _)).trans_eq (by dsimp only [C,M₀,s];ring)
  have thick (p : J→Site n) (z : Fin l→PhysicalWilsonRootedHessian.Label G n) :
      ‖row X (N:=N) base w L i l p z-row X (N:=N) base v L i l p z‖ ≤
        (2*C*Real.exp (-(s/16)*(n.val:ℝ)))*Real.exp (-(s/4)*(diameterAt J p z:ℝ)) := by
    let d := diameterAt J p z
    by_cases t : 4*d<n.val
    · let full := OriginalPhysicalWindingRows.complete J base p
      let U := univ.image p ∪ univ.image fun i => (z i).1
      have inU (a : V) (ha : a∈J) : full a∈U := mem_union_left _ (mem_image.mpr
        ⟨⟨a,ha⟩,mem_univ _,by simp [full,OriginalPhysicalWindingRows.complete,ha]⟩)
      have length (a : V) (ha : a∈J) (b : V) (hb : b∈J) : separation (full a) (full b)≤d :=
        (le_sup (f:=fun c => separation (full a) c) (inU b hb)).trans
          (le_sup (f:=fun a => U.sup fun b => separation a b) (inU a ha))
      have equal := OriginalMarkedLiftAgreement.thinCover Q.draws Q.paid hN Q.hG Q.green M k well shift n J
        full v w v.property w.property cells length t i l
      have ev : row X (N:=N) base w L i l p z=row X (N:=N) base v L i l p z := by
        simpa only [row,FundedMarkedPathSelection.output,basis,place,full] using congrArg L (congrFun equal z)
      rw [ev,sub_self,norm_zero]
      positivity
    · have hd : (n.val:ℝ)≤4*(d:ℝ) := by exact_mod_cast le_of_not_gt t
      have se : -(s/2)*(d:ℝ)≤ -(s/16)*(n.val:ℝ) + -(s/4)*(d:ℝ) := by
        nlinarith only [mul_le_mul_of_nonneg_left hd hs.le]
      calc
        _ ≤ ‖row X (N:=N) base w L i l p z‖+‖row X (N:=N) base v L i l p z‖ := norm_sub_le ..
        _ ≤ 2*C*Real.exp (-(s/2)*(d:ℝ)) := (add_le_add (each w p z) (each v p z)).trans_eq (by ring)
        _ ≤ _ := by
          have bound := mul_le_mul_of_nonneg_left (Real.exp_monotone se) (show 0 ≤ 2*C by positivity)
          rw [Real.exp_add] at bound
          simpa only [mul_assoc] using bound
  have paid := OriginalJointCoverSum.signed J (s:=s/4) (w:=s/8) (by linarith) holder u _ thick
    (mul_nonneg (by positivity) (Real.exp_pos _).le)
  rw [show s/4-s/8=s/8 by ring] at paid
  exact paid.trans_eq (by ring)

variable {I : V→Type} [∀v,Fintype (I v)] (seeds : ∀v,I v→Seed G (D v))

/-- The independently posted actual finite source has both native
Ward/degree and genuine common-translation covariance before any probe. -/
theorem deposited (degree : ∀ v a,(seeds v a).rank≤k v+(seeds v a).head) :
    Wellness k (independent seeds) ∧ ∀u,ramble u (independent seeds) := by
  refine ⟨⟨empty seeds,fun p => legal seeds p degree,?_⟩,?_⟩
  · exact fun p q J h => OriginalMarkedRootDependence.independent_roots seeds J p q h
  intro u p
  funext S
  by_cases one : ∃v,S={v}
  · obtain ⟨v,rfl⟩ := one
    rw [raised0,IndependentSourcePathFamily.singleton,IndependentSourcePathFamily.singleton,IndependentSourcePathFamily.single,IndependentSourcePathFamily.single,shiftedSum]
    apply sum_congr rfl
    intro a _
    simp only [source,cn,shifted_add,steppedC]
  · have empty (z : V → Cover) : independent seeds z S=0 :=
      sum_eq_zero (fun v _ => dif_neg (fun e => one ⟨v,e.symm⟩))
    rw [raised0,empty,empty]
    rfl

/-- The same law holds after the genuine native iterations which introduce
all nonsingleton source kernels and the complete conditional tree. -/
theorem iterated (A : Levels G) (O : ChartRatio G) (K : V→ℕ) {j b N : ℕ} (hj : j≤b) (hb : b≤N)
    (hG : G.Simple) (hO : LocalRatio O) (degree : ∀ v a,(seeds v a).rank≤k v+(seeds v a).head) :
    let M := Gears A O K k N b j (independent seeds)
    Wellness k M ∧ ∀u,ramble u M :=
  ⟨Cog A O hb (independent seeds) (deposited seeds degree).1 hG hO hj,
    rising (independent seeds) hj hb hG hO (deposited seeds degree).1 (deposited seeds degree).2⟩

end YM.Integration.OriginalCoverReanchoring
end

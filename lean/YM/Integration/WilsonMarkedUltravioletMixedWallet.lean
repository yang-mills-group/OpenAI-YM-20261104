import YM.MergeProof.Endow
import YM.Push.ABSOLUTE_SUMS.Basic

/-! Price every represented mixed support and every allowed marker simultaneously on the
original field. The new sheet and site budget are selected before all held configurations. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedUltravioletMixedWallet
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Marker Push AbsoluteSums
open Extra.Histories Ac MergeProof MergeProof.Accent GridApprox.Nil
open scoped BigOperators Classical Topology
variable {G:Gauge}{n:Side}{V I:Type}[DecidableEq V][Fintype V][Fintype I]{J:Census V}
variable {S:I → Support n}{F:I → Config G n → Poly J}{B D:ℕ}{α σ ρ M:ℝ}{w:V → ℝ}

omit [Fintype V] in
theorem purchase (bank:Towed w S F B α ρ)(wp:∀v,0<w v)(res:0≤σ)(mp:0≤M)
    (weights:∀i U s,(F i U).part s≠0 → 1≤M*Poly.toll w s)
    (spans:∀i U s,(F i U).part s≠0 → D≤coverNumber B (S i)):
    Towed (fun _:V=>(1:ℝ)) S F B (α-σ) ((M*Real.exp (-σ*(D:ℝ)))*ρ):=by
  obtain ⟨wallet,_,hit,atoms⟩:=bank
  let next (i:I):ℝ:=if D≤coverNumber B (S i) then M*wallet i else 0
  have wt (i:I):0≤wallet i:=((atoms i).fares wp).1
  have nn (i:I):0≤next i:=by dsimp only [next];split <;> first | exact mul_nonneg mp (wt i) | exact le_rfl
  refine ⟨next,(hasSum_fintype _).summable,?_,?_⟩
  · intro x
    have origin:=budget_scale (mul_nonneg mp (Real.exp_pos (-σ*(D:ℝ))).le) (hit x)
    apply budget_mono origin
    · intro i
      split <;> first | exact mul_nonneg (nn i) (Real.exp_pos _).le | exact le_rfl
    intro i
    by_cases hx:x∈S i
    · simp only [if_pos hx]
      by_cases long:D≤coverNumber B (S i)
      · rw [show next i=M*wallet i from if_pos long]
        have extent:(D:ℝ)≤(coverNumber B (S i):ℝ):=by exact_mod_cast long
        have exchange:Real.exp ((α-σ)*(coverNumber B (S i):ℝ)) ≤
            Real.exp (-σ*(D:ℝ))*Real.exp (α*(coverNumber B (S i):ℝ)):=by
          rw [←Real.exp_add,Real.exp_le_exp]
          nlinarith only [mul_le_mul_of_nonneg_left extent res]
        calc (M*wallet i)*_ ≤ (M*wallet i)*(Real.exp (-σ*(D:ℝ))*Real.exp (α*(coverNumber B (S i):ℝ))):=
                    mul_le_mul_of_nonneg_left exchange (mul_nonneg mp (wt i))
          _ = _:=by ring
      · rw [show next i=0 from if_neg long,zero_mul]
        exact mul_nonneg (mul_nonneg mp (Real.exp_pos _).le) (mul_nonneg (wt i) (Real.exp_pos _).le)
    · simp only [if_neg hx,mul_zero,le_refl]
  · intro i
    by_cases long:D≤coverNumber B (S i)
    · obtain ⟨a,an,maj,fare⟩:=atoms i
      let actual (s:J.Mode):Prop:=∃U,(F i U).part s≠0
      let c:Sheet J:=fun s=>if actual s then a s else 0
      have cn(s:J.Mode):0≤c s:=by dsimp only [c];split <;> first | exact an s | exact le_rfl
      refine ⟨c,cn,?_,?_⟩
      · intro U s
        by_cases alive:actual s
        · exact (maj U s).trans_eq (if_pos alive).symm
        · have z:(F i U).part s=0:=by by_contra no;exact alive ⟨U,no⟩
          rw [z,norm_zero];exact cn s
      · rw [show next i=M*wallet i from if_pos long]
        apply le_trans _ (mul_le_mul_of_nonneg_left fare mp)
        unfold wordsPrice
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro s _
        simp only [Poly.toll,Finset.prod_const_one,one_mul]
        by_cases alive:actual s
        · obtain ⟨U,live⟩:=alive
          have ratio:=weights i U s live
          rw [show c s=a s from if_pos ⟨U,live⟩]
          calc a s = 1*a s:=by ring
            _ ≤ (M*Poly.toll w s)*a s:=mul_le_mul_of_nonneg_right ratio (an s)
            _ = _:=by simp only [Poly.toll,mul_assoc]
        · rw [show c s=0 from if_neg alive]
          exact mul_nonneg mp (mul_nonneg (Poly.worth wp s).le (an s))
    · refine ⟨0,le_rfl,?_,?_⟩
      · intro U s
        have z:(F i U).part s=0:=by by_contra live;exact long (spans i U s live)
        rw [z,norm_zero];exact le_rfl
      · simp [wordsPrice,next,long]

omit [Fintype V] [Fintype I] in
theorem reach {o:V → Site n}{t:ℝ}(here:∀i,Borne o (S i) (F i) t)
    (far:∀i U s,(F i U).part s≠0 → ∃a∈s.val,∃b∈s.val,D*(4*B+2)+2*B < separation (o a) (o b)):
    ∀i U s,(F i U).part s≠0 → D≤coverNumber B (S i):=by
  intro i U s alive
  obtain ⟨a,ha,b,hb,room⟩:=far i U s alive
  have scope:(s.val:Set V)⊆{v|o v∈S i}:=by by_contra no;exact alive ((here i).scope U s no)
  have hi:=Corona.extent (S i) B (scope ha) (scope hb)
  by_contra! small
  exact (not_le_of_gt room) (hi.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ small.le) _))

end YM.Integration.WilsonMarkedUltravioletMixedWallet

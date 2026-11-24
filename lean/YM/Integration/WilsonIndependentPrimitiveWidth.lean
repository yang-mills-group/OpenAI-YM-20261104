import YM.Integration.WilsonIndependentConditionalFiniteGrant
import YM.Lattice.Box

/-! A local extensive primitive needs only stencil diameter, cell
translation and its finite normalized directional readings. The wage is
uniform in volume, with no factor for the number of root translations. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPrimitiveWidth
open Function Filter Lattice Laurent Bloch WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue
open WilsonCoeffUV.Soil
open scoped Classical BigOperators Topology
variable {α:Type}[Fintype α]{r:ℕ}

private theorem inbox {x:Cover}{D:ℕ}(h:size x≤D):x∈box D:=by
  have bound (i:Axis):(x i).natAbs≤D:=le_trans (Finset.single_le_sum (f:=fun j=>(x j).natAbs)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)) h
  apply box_test.mpr
  constructor<;>intro i<;>have hi:=bound i<;>omega

abbrev Cell (D:ℕ)(α:Type):=↥(box D)×α
private def view {D:ℕ}(u:Fin r→Cell D α):Fin r→Cloth α:=fun i=>((u i).1.val,(u i).2)

theorem original {P:raw α ℝ r}{Q:Ten ℝ (Cloth α) r}(pin:Fin r)(D:ℕ)
    (point:∀x,Tendsto (fun n=>P n (foldUnder n∘x)) atTop (𝓝 (Q x)))
    (moves:∀ᶠ n in atTop,stroll (P n))
    (locality:∀ᶠ n in atTop,∀x,P n x≠0→soar (tor n) x≤D):
    Yields P Q:=by
  have hr:r≠0:=by have h:=pin.isLt;omega
  refine ⟨fun x=>by simpa only [dilute,if_neg hr] using point x,moves,?_⟩
  let A:ℝ:=∑ u:(Fin r→Cell D α),(‖Q (view u)‖+1)
  have pos:0≤A:=Finset.sum_nonneg (fun _ _=>by positivity)
  have invoice:∀ᶠ n:Side in atTop,∀u:Fin r→Cell D α,‖P n (foldUnder n∘view u)‖≤A:=by
    apply eventually_all.mpr;intro u
    have a:= (point (view u)).norm.eventually (gt_mem_nhds (show ‖Q (view u)‖<‖Q (view u)‖+1 by linarith))
    filter_upwards [a] with n hn
    exact (le_of_lt hn).trans (Finset.single_le_sum (f:=fun v:Fin r→Cell D α=>‖Q (view v)‖+1)
      (fun _ _=>by positivity) (Finset.mem_univ u))
  refine ⟨1,A*Real.exp D,one_pos,?_⟩
  filter_upwards [moves,locality,invoice] with n move radius paid
  rw [dilute,if_neg hr]
  refine ⟨mul_nonneg pos (Real.exp_pos _).le,fun x=>?_⟩
  by_cases nz:P n x=0
  · rw [nz,norm_zero];positivity
  let o:Site n:=(x pin).1
  have loc (j):size (lift ((x j).1-o))≤D:=(leg_le (tor n) (Prod.fst∘x) pin j).trans (radius x nz)
  let u:Fin r→Cell D α:=fun j=>(⟨lift ((x j).1-o),inbox (loc j)⟩,(x j).2)
  have atRoot:jog o∘(foldUnder n∘view u)=x:=by
    funext j
    change (o+wrap n (lift ((x j).1-o)),(x j).2)=x j
    apply Prod.ext
    · change o+wrap n (lift ((x j).1-o))=(x j).1
      rw [wrap_lift];abel
    · rfl
  have fee:‖P n x‖≤A:=by rw [←atRoot,move];exact paid u
  apply fee.trans
  rw [neg_one_mul,mul_assoc,←Real.exp_add]
  apply le_mul_of_one_le_right pos
  apply Real.one_le_exp_iff.mpr
  have hx:((soar (tor n) x:ℕ):ℝ)≤D:=by exact_mod_cast radius x nz
  linarith

end YM.Integration.WilsonIndependentPrimitiveWidth

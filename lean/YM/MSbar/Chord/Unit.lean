import YM.MSbar.Chord.Digits
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform
open Precision Gauge MSbar.Wave StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset
variable {G:Gauge}{n:Side}{Q:FaceRail n G}{Z:ℝ}
local notation "S₀"=> Site n
local notation "E"=> Edge (Site n)
local notation "N"=> n.val
local notation "M"=> Moment Q
noncomputable def anchor (n:Side)(Q:FaceRail n G)(e:G.Color):ℝ := Moment Q ((0: Site n),(1:Axis)) 1 e e [0,0]
variable (x:Edge (Site n)) (u v:G.Color) (hG:G.Simple)(h:Ribbon Q)(hQ:Weigh Q Z) (hu:‖u‖=1)(hv:‖v‖=1)
noncomputable def cost (Q:FaceRail n G)(e:G.Color)(Y:ℝ):= |anchor n Q e| +100*tumbler n Y
private lemma target (s:Signed)(b:S₀) : ∃ t:S₀, sendEdge s t x=(b,s.perm x.2) :=by
   by_cases hh:s.flip x.2
   · refine ⟨b+step (s.perm x.2)-s.act x.1,?_⟩; simp [affine,sendEdge,Step.rotate,Step.used,posDir,hh]
   · refine ⟨b-s.act x.1,?_⟩; simp [sendEdge,affine,posDir,Step.rotate,Step.used,hh]
include h hQ hu hv
lemma Prices (i:Axis)(s:Signed)(L:List Axis)(hL:L.length ≤2) (b:S₀):
    |M (b,s.perm x.2) (s.perm i) u v (L.map s.perm) - sign s x.2*sign s i*(bill s L*M x i u v L)| ≤ 17*tumbler n Z:=by
    obtain ⟨t,hT⟩:= target x s b; rw [←hT]; exact axPrice x i u v h hQ hu hv s t L hL
local notation "W"=>tumbler n Z
include x
omit h
lemma fundT : 0 ≤ tumbler n Z:=by
   have hf:= hQ x x.2 u v hu hv; have hh: 0 ≤ Z:= le_trans (Finset.sum_nonneg (fun i _=>mul_nonneg (abs_nonneg _) (by unfold beadPad; positivity))) hf; unfold tumbler; positivity
include h
lemma tick1 (i j: Axis) : |M x i u v [j]| ≤ 17*tumbler n Z:=by
    let s:Signed:= ⟨Equiv.refl _,fun _=>true⟩; have hp:= Prices x u v h hQ hu hv i s [j] (by simp) x.1; let a:=M x i u v [j]; simp only [s,bill,sign,if_true, neg_mul_neg,mul_one,one_mul,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,Equiv.refl_apply] at hp
    have hz:0 ≤ W:=fundT x u v hQ hu hv; have hi : |a- (-1* a)|≤ 17*W :=hp; obtain ⟨h₁,h₂⟩:=abs_le.mp hi; apply abs_le.mpr;change _ ≤ a∧a≤_; constructor<;>linarith
lemma mirrors (i j k a:Axis) (he:sign (Signed.mirror a) x.2 * sign (Signed.mirror a) i * (sign (Signed.mirror a) j * sign (Signed.mirror a) k)= -1): |M x i u v [j,k]|≤ 17*tumbler n Z:=by
    let s:= Signed.mirror a; have hp:=Prices x u v h hQ hu hv i s [j,k] (by simp) x.1; unfold bill at hp; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at hp; let b:= M x i u v [j,k]; have h' : |b - ((sign s x.2*sign s i)*(sign s j *sign s k*b))| ≤ 17*W:=hp; rw [← mul_assoc,show _*(sign s j*sign s k)= -1 from he] at h'; apply abs_le.mpr; have ht:=fundT x u v hQ hu hv; obtain ⟨ha,hb⟩:= abs_le.mp h'; constructor<;>dsimp only [b] at *<;>linarith
variable (e:G.Color)(he: ‖e‖=1)
include hG he
omit hu hv in

lemma fees (i:Axis)(l:List Axis): M x i u v l = ⟪u,v⟫_ℝ * M x i e e l:=by
    unfold Moment; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [blazing Q hG h _ _ e he];ring
lemma fares {j: Axis} (ht : j ≠ x.2) : |M x x.2 u v [j,j]| ≤ cost Q e Z:=by
    obtain ⟨P,h₀,h₁⟩:= extend_two j x.2 ht
    have hp := Prices ((0:S₀),(1:Axis)) e e h hQ he he 1 ({perm:=P,flip:=fun _=>false}: Signed) [0,0] (by decide) x.1; simp only [h₀,h₁,sign,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,bill,Bool.false_eq_true,if_false,mul_one,one_mul] at hp
    have hh : |M x x.2 e e [j,j] - anchor n Q e| ≤ 17*W:= by -- check
        exact hp
    rw [fees x u v hG h hQ e he, abs_mul]
    have he : |inner ℝ u v|≤ 1:= by simpa [hu,hv] using abs_real_inner_le_norm u v
    apply (mul_le_of_le_one_left (abs_nonneg _) he).trans; apply abs_le.2
    have hf:= fundT x u v hQ hu hv; obtain ⟨h₀,h₁⟩:=abs_le.mp hh; unfold cost; have hZ:= abs_le.mp (show |anchor n Q e| ≤ |anchor n Q e| from le_rfl); constructor<;>linarith [hZ.1,hZ.2] -- `W` notation issue
end YM.MSbar.Midpoint

import YM.X.Dial.Polo
/-!
# Signed bare inverse intertwines exactly. Not automatic from sector assumptions on fields.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Dial
open Lattice Wilson Next.Rank Normal MvPolynomial Function Stems Filter MeasureTheory Metric Interval Size Hinge
open Source PertExtension LatticePT Labels Filter Gauss Heat
open scoped Topology ContDiff BigOperators Pointwise Classical
variable {G:Gauge} {d:ℕ} {F:Labels.Frame G d} (S:SectionData F) {H:Hol G} (s:Signed) (h:S.Sound H) (P:Bid.pop S)
local notation "v"=> F.Coeff
local notation "L"=> Label G d
local notation "W"=> Curly G
local notation "Cₚ"=> topMatrix S H h P
local notation "R₀"=> poly (Atom G)
local notation "Q"=> covarianceSymbol G
open PolyFlow
def wool (c:F.Coeff): R₀:=∑ i:F.Index,c i • (Cₚ).basis i
lemma cutboard (c:v): loom (wool S h P c)=boardP S h P 0 c:= by rw [wool,map_sum]; change _ = ∑ i:F.Index,_; simp_rw [map_smul]; exact Finset.sum_congr rfl fun i _=> congr_arg _ (basis_moon i h P)
lemma wool_H (c : v): loom (wool S h P (F.act s.ortho c))= relay s (loom (wool S h P c)):= by rw [cutboard,cutboard,boxS]

lemma wool_V {S : Side}(p : poly (Atom G)): milk (scopedK sale (0:Site S)) (loom p)=loom (milk (via sale (0:Site S)) p):= prepared ..
lemma milk_limit (p :poly (Atom G)) {q:ℕ+}(hq:1<q.val): Limit (fun i=> milk (scopedK sale (0:Site (side q i))) (loom p)) (loom (milk Q p)) atTop:= by
    simp_rw [wool_V]; refine Limit.operator (R:=fun _=> loom.toLinearMap) (T:=loom.toLinearMap) (milk_continuity (f:=fun _=>p) ?_ Limit.const) (fun _=>Limit.const)
    intro a b; let r k:= (via sale (0:Site (side q k))).cov a b; exact tendsto_sub_nhds_zero_iff.mp ((actual_self hq a b).goes hq) -- inspect name
lemma limit_pin {V:Type*}{f:ℕ→poly V}{p q:poly V}(h: Limit f p atTop)(t:Limit f q atTop):p=q:= by ext i; exact tendsto_nhds_unique (h.leaves i) (t.leaves i)
lemma milked_rot {p q:poly (Atom G)}(h:loom p=relay s (loom q)): loom (milk Q p)= relay s (loom (milk Q q)):= by
    let M(i:ℕ):=scopedK (G:=G) sale (0:Site (side 2 i)); refine limit_pin (milk_limit p (q:=2) (by decide)) ?_; apply Limit.replace (Limit.operator (R:=fun i :ℕ=>(relay s).toLinearMap) (T:=(relay s).toLinearMap) (milk_limit q (q:=2) (by decide)) (fun _=> Limit.const)) (Eventually.of_forall ?_); intro i; change relay s (milk (M i) _) = milk (M i) _; rw [h,relay,prepared,show scope _ _= _ from cover_s s]
lemma matrix_H (c:v): (Cₚ).conversion Q (F.act s.ortho c) = F.act s.ortho ((Cₚ).conversion Q c):= by
    let K := wool S h P; have hK (x:v): (F.coords.symm ((Cₚ).conversion Q x)).val = Heat.Ray.clipped d (milk Q (K x)):= by
        let B:= milk Q (K x); have hx : Top.joint F B = (Cₚ).matrix Q x:= by unfold B K wool; change Top.joint F (milk Q _) = ∑ i:F.Index, _; simp only [map_sum,map_smul];rfl
        have Hp:Hue.Fixed B:= by refine Hue.Fixed.heat ?_; intro u y; unfold K wool; simp only [map_sum,map_smul]; exact Finset.sum_congr rfl fun i _=> congr_arg _ ((Vertex.basis_fixed S H h P i) u y)
        change (F.coords.symm ((Cₚ).matrix Q x)).val= _; rw [← hx,Heat.HueTag.shadow_eq B Hp]; rfl
    apply F.coords.symm.injective; rw [show F.coords.symm (F.act s.ortho ((Cₚ).conversion Q c)) = tensor s.ortho (F.coords.symm ((Cₚ).conversion Q c)) from ?_]; swap; · apply F.coords.injective; rw [F.coords.apply_symm_apply, ← F.act_coords,F.coords.apply_symm_apply]
    apply Subtype.ext; change _= rotated s.ortho (_ : Pol G); rw [hK,hK]; unfold Heat.Ray.clipped; rw [printed_v s d _ _ (milked_rot s (wool_H S s h P c)),← Ray.weigh, ← Ray.weigh]; apply Grow.hom_commute (p:=Heat.Ray.print d _) -- may need exact
    intro i; rw [rotated,changed,aeval_X]; apply IsWeightedHomogeneous.sum; intro j _; apply IsWeightedHomogeneous.C_mul; exact isWeightedHomogeneous_X ..
lemma r_spin (c:v): F.act s.ortho ((Cₚ).inverse Q c)= (Cₚ).inverse Q (F.act s.ortho c):= by
   let u:= (Cₚ).conversion Q; apply u.injective; change u (F.act s.ortho (u.symm c))= u (u.symm _); rw [matrix_H S s h P (u.symm c),u.apply_symm_apply,u.apply_symm_apply]
def coarse (n:ℕ): L→ₗ[ℂ] W:= boardP S h P n ∘ₗ ((Cₚ).inverse Q) ∘ₗ F.coords.toLinearMap
lemma coarsen (n:ℕ)(p:L): relay s (coarse S h P n p)= coarse S h P n (tensor s.ortho p):= by unfold coarse;change relay s (boardP _ _ _ _ _)=boardP S h P n ((Cₚ).inverse Q _); rw [boxS S s h P,LinearMap.comp_apply,r_spin S s h P]; congr 2; exact F.act_coords ..
lemma coarse_word (p: Word G)(n:ℕ): coarse p.S p.sound p.chosen n (Grow.labelledP p)= bookMark p n:= by
    let x:=p.axis; let B:= p.F ; let a : B.Coeff:= Pi.single x 1; change (∑ i:B.Index, _)=∑ i:p.F.Index,_; apply Finset.sum_congr rfl; intro i _; change ((topMatrix p.S p.H p.sound p.chosen).inverse Q (B.coords (B.basis x))) i • _= _; rw [B.coords_basis,Vertex.true_coefficients]; rfl
end YM.PositionX.Dial

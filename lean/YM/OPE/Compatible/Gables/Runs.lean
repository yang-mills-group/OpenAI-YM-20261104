import YM.OPE.Compatible.Gables.Feet
/-!
# All trace accounts, ordinary torque identities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)(H:Even c.val)(X: Plot H)
local notation "μ"=> even_both S.ratio H
local notation "X!"=> forest S.ratio he
local notation "W!" => stroll S he H X
local notation "V!" => valley S he H X
local notation "Z!" => AxisChart G X!
local notation "Qµ"=> Blocx S he H
local notation "P!" => Keys G X.Free
local notation "J!" => Keys G (Blocx S he H)
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:ReadyV S he U A D L g)
variable (V:Bor H D b)(Y:Elm A S H t r){P:ChartRatio G}(ht:LocalRatio P)
local notation "LK"=> Keys G (Stand.Free (stroll S he H X))
local notation "Wμ"=> Chart.tangent G Qµ
variable {C:Law (Keys G (Blocx S he H))}(hc:Roomy S he H U C)
-- accounting index and oriented trans
local notation "Q!"=> Active G (forest S.ratio he)
local notation "S!"=> Bid.Dir G c × AxisChart G X!
open Flume.Script Shell
local notation "T!"=> Flume.Script.Tile G S.ratio.count
open Planned.PrimaryIntegral295.Carrier
local notation "U!"=> FUND S he U
local notation "CAX" => actLight S he H G
open JetS ScriptJ Shell Char Libra.Shift
local notation "PL"=> Shift.crossT Wμ C
local notation "PY"=> (Y.L W!)
local notation "H!"=> Chart.tangent G X.Free
open Terp
local notation "TK"=>Keys G (Limb H)
local notation "ZK"=>Keys G X.Stable
local notation "Zμ"=>Chart.tangent G X.Stable
-- reach near gauge from ℓ. visit heights
private def downScale (p:Node H):= (Finset.univ.filter fun i:Node H=> X.flick i<X.flick p).card
lemma size_down (p:↥(({origin H}:Set _)ᶜ)): downScale H X ((Pond H).lastV (X.point p)) < downScale H X p :=by
      have hp:= X.bump p; unfold downScale; apply Finset.card_lt_card; rw [Finset.ssubset_iff_subset_ne]; refine ⟨(fun i hi=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_trans ((Finset.mem_filter.mp hi).2) hp⟩),?_⟩; intro h; let u:=(Pond H).lastV (X.point p); have hx:u∈ Finset.univ.filter fun i:Node H=> X.flick i<X.flick p:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩; rw [←h] at hx; exact lt_irrefl _ ((Finset.mem_filter.mp hx).2)
lemma ctr (x:TK)(y:P!)(t: Keys G (Node H))(h:(Pond H).galaxy G t + X.rollX y=x)(p:Node H):‖t p-t (origin H)‖ ≤ (downScale H X p:ℝ)*‖x‖:=by
      induction hv : downScale H X p using Nat.strong_induction_on generalizing p with
      | _ q ih=>
         by_cases ht:p=origin H
         · rw [ht,sub_self,norm_zero];positivity
         let a: ↥(({origin H}:Set _)ᶜ):=⟨p,ht⟩; let v:= X.point a; let T:=Pond H; let u:= T.lastV v; have hh:u= (Pond H).lastV v:=rfl
         have hz : x v.1=t (T.inn v.1)-t (T.out v.1):=by
              rw [←h]; change _ + X.cite 0 y _= _; erw [X.keptZ 0 y (⟨_,X.purity a⟩ : X.Stable)]; exact add_zero _
         have he: ‖t p-t u‖ ≤ ‖x‖:=by
              apply le_trans (b:=‖x v.1‖) _ (norm_le_pi_norm ..); apply le_of_eq; rw [hz,show p=T.start v from (X.root a).symm]; unfold Score.start u Score.lastV; split; exact norm_sub_rev ..;rfl
         refine le_trans (norm_sub_le_norm_sub_add_norm_sub _ (t u) _) (le_trans (add_le_add he (ih _ ((size_down H X a).trans_eq hv) u rfl)) ?_); rw [show ‖x‖+ ↑(downScale H X u)*‖x‖=(↑(downScale H X u)+1)*‖x‖ from by ring] -- lemma yields? inspect
         gcongr; exact_mod_cast (size_down H X a).trans_eq hv
lemma aimY (x: TK):∃ t: Keys G (Node H), (Pond H).galaxy G t +X.rollX (aimQ H X G x)=x:=by
      let v:=(weep H X G).symm x; obtain ⟨t,ht⟩:= X.normal_arc v; let p:=(Vale H X G) x; have hx:X.slab G v=p.1:=by
           rw [show v=compass H X G p from ((compass H X G).apply_symm_apply v).symm,show compass H X G p= _ from rfl]; exact firstC ..
      rw [hx] at ht; exact ⟨t,ht.trans (show X.dtex G v=x from (weep H X G).apply_symm_apply x)⟩
lemma boulev (x:TK): ‖aimQ H X G x‖ ≤ (1+2*(c.val:ℝ)^4)*‖x‖:=by
      let y:=aimQ H X G x; obtain ⟨t,h⟩:= aimY H X x; apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i; have hh(u): ‖t u-t (origin H)‖≤(c.val:ℝ)^4*‖x‖:=by
           have hx:=ctr H X x y t h u; apply hx.trans; gcongr; have ht: downScale H X u ≤ c.val ^4:= by apply le_trans (Finset.card_le_univ ..); rw [←site_card]; exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
           exact_mod_cast ht
      let p:=(Pond H).inn i.val; let q:= (Pond H).out i.val; have hp:t p -t q + y i=x i.val:=by
           have hv:=congr_fun h i.val;change t p-t q+ X.cite 0 y _=_ at hv; rw [X.kept] at hv; exact hv
      change ‖y i‖≤ _; rw [show y i=x i.val-(t p-t q) from eq_sub_of_add_eq (add_comm .. |>.trans hp)]; apply (norm_sub_le ..).trans; have hy:= norm_sub_le_norm_sub_add_norm_sub (t p) (t (origin H)) (t q); rw [norm_sub_rev (t (origin H))] at hy; apply (add_le_add (norm_le_pi_norm x i.val) (hy.trans (add_le_add (hh p) (hh q)))).trans_eq; ring
end YM.OPE.Cascade.Rill

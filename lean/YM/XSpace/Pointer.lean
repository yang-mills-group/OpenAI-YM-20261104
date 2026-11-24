import YM.XSpace.Tones
/-!
# The actual b,U inputs and their color-diagonal physical stencils

Scalar leading coupons at arbitrary Survey and horizon containing the curvature. Use Fare design on rough estimates.
-/
set_option autoImplicit false
noncomputable section
set_option maxRecDepth 6000
namespace YM.XSpace.Chiral
open Function Set Filter Lattice Chart2 Maxwell Maxwell.Free Normalize Structure1 Source Source.Drops Wilson Bid Work.G05
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge} {d:ℕ} {H:Hol G}
def zeds (S:Snap G d):= expand d S 0
lemma zed_color (g:G.El)(U: Snap G d): zeds (snapColor g U) = Labels.Taylor.paint g (zeds U):= congr_fun (unfold_color ..) 0
def zedsL (d:ℕ): Snap G d→ₗ[ℝ] Labels.Taylor G 0:={toFun:=fun p=>zeds p,map_add':=fun x y=>by unfold zeds expand; split; rfl; simp, map_smul':=fun a x=>by unfold zeds expand; split; rfl; simp}
def wheels (t:Flavor 0): Shell G 0→ₗ[ℝ] G.Color:={ toFun:=fun y=> available y t,map_add' x y := by ext1 i; exact map_add (flavor (G:=G) 0 i t) x y,map_smul' a y:=by ext1 i; exact map_smul (flavor (G:=G) 0 i t) a y }
lemma wheeler (t:Flavor 0)(y:Shell G 0) : wheels t y= available y t:=rfl
def axial (σ:Bool)(p:P)(d:ℕ) : Snap G d →ₗ[ℝ] G.Color:= wheels (Fq σ p) ∘ₗ On.solve G 0 ∘ₗ zedsL d
lemma axials (σ:Bool)(p:P)(U:Snap G d): axial σ p d U=available (On.solve G 0 (zeds U)) (Fq σ p):=by unfold axial; rw [LinearMap.comp_apply,LinearMap.comp_apply,show zedsL d U=zeds U from rfl]; exact wheeler (Fq σ p) (On.solve G 0 (zeds U))
lemma axis_power (σ:Bool)(p:Name G)(U:Snap G d):awaken d (On.lifting (spark σ p)) U= ↑((axial σ p.1 d U) p.2):=by
  simp only [axials, zeds, awaken, On.lifted, light]
lemma axis_color (g:G.El)(U:Snap G d)(σ: Bool)(p:P): axial σ p d (snapColor g U)= G.adjoint g (axial σ p d U):=by
  simp only [axials,zed_color,On.leg_color,shows_hue]
lemma scalar (h:G.Simple)(L:Module.End ℝ G.Color)(he:∀ (g:G.El) x,L (G.adjoint g x)=G.adjoint g (L x)): ∃ t:ℝ, ∀ x,L x=t • x:=by
  let B:= (innerₗ G.Color) ∘ₗ L; obtain ⟨t,h⟩:= invariant_two h B (fun g x y=>by simp only [B,LinearMap.comp_apply,he]; apply Show.shade_price)
  exact ⟨t,fun x=> ext_inner_right ℝ fun y=>((h x y).trans (real_inner_smul_left ..).symm)⟩
variable (h:G.Simple)(S:Survey G H d)(σ:Bool)(p:P)
def agent : GaugePanel G S.size→ₗ[ℝ] G.Color := axial σ p d ∘ₗ S.extract.toLinearMap
def ticket (k:Fin S.size): Module.End ℝ G.Color:= agent S σ p ∘ₗ LinearMap.single ℝ (fun _=>G.Color) k
lemma ticket_value (k:Fin S.size)(x: G.Color): ticket S σ p k x=agent S σ p (Pi.single k x):=by rw [ticket,LinearMap.comp_apply, LinearMap.single_apply]
include h in
lemma ticket_common (k: Fin S.size): ∃ t:ℝ, ∀ x,ticket S σ p k x=t • x:=by
  apply scalar h; intro g x; simp_rw [ticket_value]; rw [show Pi.single k (G.adjoint g x)=rotates g (Pi.single k x) from funext fun j=> by by_cases h:k=j <;> simp [h,rotates,Ne.symm]]; simp only [agent,LinearMap.comp_apply,ContinuousLinearMap.coe_coe]; rw [S.extract_color,axis_color]
def coupon (k:Fin S.size):= (ticket_common h S σ p k).choose
lemma reveal (x:GaugePanel G S.size): axial σ p d (S.extract x)=∑ i:Fin S.size,coupon h S σ p i • x i:=by
  rw [← show agent S σ p x=axial σ p d (S.extract x) by simp only [agent,LinearMap.comp_apply, ContinuousLinearMap.coe_coe]]; conv_lhs=> rw [← Finset.univ_sum_single x,map_sum]; skip
  refine Finset.sum_congr rfl fun i _=>?_ ; rw [← ticket_value]; unfold coupon; rw [(ticket_common h S σ p i).choose_spec]

lemma wedge_eq (u v:PlaqAxes): wedge 1 (six u) (endr u) (six v) (endr v)= if u=v then 1 else 0:=by
  by_cases hx:u=v; · subst u; simp [wedge,Matrix.one_apply,six,endr,v.property.ne, v.property.ne']
  rw [if_neg hx,wedge, Matrix.one_apply,Matrix.one_apply, Matrix.one_apply,Matrix.one_apply]; have he:six u ≠ six v ∨ endr u≠endr v:=by
    by_contra! hc; exact hx (Subtype.ext (Prod.ext hc.1 hc.2))
  have h0 : six u≠endr v ∨ endr u ≠ six v:=by by_contra! H; have hp:six u<endr u:=u.property; have hh:endr v>six v:=v.property; rw [H.1,H.2] at hp; exact lt_asymm hh hp
  rcases he with h|h <;> rcases h0 with he|he <;> simp [*, Ne.symm]
lemma pre_at (u:PlaqAxes)(A:G.Color): available (blade (six u) (endr u) A) (Fq σ p)= q σ p (six u) (endr u) • A:=by
  ext1 i; let L (w:Sheet 0):= (Fq σ p) w; let v:=blade (six u) (endr u) A; change flavor 0 i (Fq σ p) v= _; rw [Fq,map_sum,LinearMap.sum_apply, Finset.sum_eq_single u]; rw [map_smul,LinearMap.smul_apply]; change _ • (v.val _ _ (fun _=>0) i)=_; have hh:=wedge_eq u u; rw [if_pos rfl] at hh; unfold v; rw [blade_eval,hh,one_smul]; rfl
  intro b _ hb; rw [map_smul,LinearMap.smul_apply]; change q σ p (six b) (endr b) • ((blade _ _ A).val _ _ 0 i)= _; rw [blade_eval,wedge_eq,if_neg hb,zero_smul]; simp
  simp
open Next.Rank
lemma sails (A: Shell G 0)(i): Cross.passenger S (Beamer.sweep 0 (gaugeJet A)) i=A.val (six (S.looks i).plaq) (endr (S.looks i).plaq) (fun _=>0):=by
  let t:= S.looks i; have he:= CellsInt.test_top (gaugeJet A) (fun _=>0) (six t.plaq) (endr t.plaq) t.offset; rw [match_leg] at he; ext1 c; change CellsInt.test (gaugeJet A) (six t.plaq) (endr t.plaq) t.offset c=_; change CellsInt.test _ _ _ _ = _ at he; rw [he]; norm_num; rw [show basis∘(fun _:Fin 0=> (0:Axis))=(fun _ => (0:E4)) from Subsingleton.elim ..]
lemma remembrance (he:2≤d)(u:PlaqAxes): ∑ i:Fin S.size, (if (S.looks i).plaq=u then coupon h S σ p i else 0)= q σ p (six u) (endr u):=by
  let i:= coreColor h; let A:= basisC G i; let x : Shell G 0:= blade (six u) (endr u) A
  have hx:= reveal h S σ p (Cross.passenger S (Beamer.sweep 0 (gaugeJet x))); rw [Cross.extracts S (j:=0) he] at hx
  have hm : zeds (Cross.tick (j:=0) he (gaugeJet x))=gaugeJet x:=by rw [zeds,Cross.ticks]; simp
  have hx' : axial σ p d (Cross.tick (j:=0) he (gaugeJet x))= q σ p (six u) (endr u) • A:=by rw [axials,hm,On.on_shell]; apply pre_at
  rw [hx'] at hx; apply smul_left_injective ℝ (norm_pos_iff.mp (show ‖A‖>0 by simp [A])); simp only [Finset.sum_smul]; rw [hx]; apply Finset.sum_congr rfl; intro k _; rw [sails S]; unfold x; rw [blade_eval,wedge_eq]; split_ifs <;> simp
end YM.XSpace.Chiral

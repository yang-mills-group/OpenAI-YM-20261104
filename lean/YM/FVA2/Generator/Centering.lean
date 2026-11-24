import YM.FVA2.Generator.Port
import YM.XSpace.Topaz
/-!
# Pass from the FULL XSpace physical BCH vertex to the resonant cubic with slots ordered
$V3 : ∂_i A_j · [A_i,A_j]$

We can prove the necessary suppression already on the elemental stamp
(`vanishErr`, at any indicated $k≤d$). Thus after
passing to annular increments only the canonical cubic contributes. No Slavnov/Ward
assumption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Center
open Function Set Filter XSpace XSpace.Mu XSpace.Lows XSpace.Trace XSpace.Chart2
open XSpace.Playpen XSpace.Drama XSpace.Sail Lattice Further.FreeCovariance.KP
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{p:Stamp G} {n d e k:ℕ}
open XSpace.Gland XSpace.Chiral
set_option maxHeartbeats 500000 in
lemma extra (x:PlaqAxes): V3 G (tile x)-εglows x G ∈ elemental G 5:= by
    have he(k:ℕ)(x: Line G)(h:x∈cane k G): harp x∈ elemental G (1+k):= read_cut (fun _=>True) (⟨k,x,h⟩) trivial
    have hp:=through3 (i:=1) (j:=1) (k:=0) (elemental G 5) (fun x a y b z c=> productKeen (d:=2+2) (e:=1) (fun _=>True) (productKeen (d:=2) (e:=2) (fun _=>True) (he 1 _ a) (he 1 _ b)) (he 0 _ c))
    exact hp (incurred x)
-- slots
structure Bond (G:Gauge) where
    k : List Axis
    j : Axis
    color : G.ColorIndex

def Bond.fee {G:Gauge} (γ:Bond G) : Fee G:= ⟨γ.k.length, gate γ.k (needle (((0:Cover),γ.j),γ.color)),gated _ _⟩
def Bond.read (γ:Bond G):= harp γ.fee.line
variable (x y z:G.ColorIndex)(i j:Axis)
def axes := [Bond.mk [i] j x, Bond.mk [] i y, Bond.mk [] j z]
def stack := story ((axes x y z i j).map Bond.fee)
lemma standing : debt ((axes x y z i j).map Bond.fee)=4:=rfl
private lemma spark : harp (Bond.fee ⟨[i],j,x⟩).line= hike i (av j x):= by
    rw [march]; apply XSpace.Chart2.same; intro A; let z:=needle (((0:Cover),j),x); rw [leg_test, map_sub]; change (↑(probe (displace (step i) z-z) A):ℂ)=_
    rw [pin]; unfold pit av; simp only [_root_.map_sub,LinearMap.sub_apply, z, probes]; rw [MvPolynomial.aeval_X,MvPolynomial.aeval_X]; simp [radius,numbers]; rfl
lemma assigned : stack x y z i j=hike i (av j x)*(av i y * av j z):=by change _*(_*(_*1))=_; rw [mul_one]; dsimp only; rw [spark]; congr 2; exacts [ harps _, harps _ ]
def shine (G:Gauge)(i j:Axis):= ∑ x:G.ColorIndex,hike i (av j x)*mode i j x
lemma accounted (G:Gauge)(i j:Axis): shine G i j= ∑ x:G.ColorIndex,∑ y:G.ColorIndex,∑ z:G.ColorIndex,(↑(br x y z):ℂ) • stack x y z i j:= by simp_rw [shine,mode,Stk, Finset.mul_sum,mul_smul_comm, assigned]
-- unordered pairs, additive generalization of Wicker order_cost (including group choice)
private lemma order_cost {η:Type*}[AddCommMonoid η] (p:Axis→Axis→η) (h:∀ i,p i i=0) : (∑ j:Axis,∑ i:Axis,p i j)= ∑ o:PlaqAxes, (p o.val.1 o.val.2+p o.val.2 o.val.1):=by
  classical
  let L: Finset (Axis×Axis):= Finset.univ.filter (fun i=>i.1 < i.2)
  let X:Finset (Axis × Axis) := Finset.univ.filter (fun i=> i.2 < i.1)
  let Y:Finset (Axis × Axis) := Finset.univ.filter (fun i=> i.1≠i.2)
  have ht: Y=L ∪ X:= Finset.ext fun i=> by simp [Y,L,X]
  have hp (f: Axis × Axis →η):∑ i∈L,f i=∑ i:PlaqAxes, f i.val := by unfold L PlaqAxes; generalize_proofs hz; exact (Finset.sum_subtype_eq_sum_filter ..).symm
  have hh : Disjoint L X:= Finset.disjoint_left.mpr (by intro i h q; simp [L] at h; simp [X] at q; exact (not_lt_of_gt h) q)
  let F i:= p (i:Axis×Axis).1 i.2; have hv : ∑ i∈X,F i=∑ i∈L,F (Prod.swap i):= by
    have hx : X=L.image Prod.swap:= Finset.ext fun ⟨i,j⟩=> by simp [X,L]
    rw [hx, Finset.sum_image]; intro i _ j _ h; exact (Equiv.prodComm Axis Axis).injective h
  calc _ = ∑ i:Axis×Axis, F i:= (Fintype.sum_prod_type_right ..).symm
       _ = ∑ i∈Y,F i:= Eq.symm (Finset.sum_subset (Finset.subset_univ _) (fun i _ hb=> by simp [Y] at hb; simp [F,hb,h]))
       _ = _ := by rw [ht,Finset.sum_union hh,hv,hp,hp, ← Finset.sum_add_distrib]; rfl
lemma minted (G:Gauge): (∑ p:PlaqAxes, εglows p G)=∑ i:Axis, ∑ j:Axis, shine G i j:=by
    have he(i:Axis)(x:G.ColorIndex): mode i i x=0:=XSpace.Chart2.same fun A=>by rw [mode,Gland.report,Chart2.Drift.ad_same,map_zero]; simp -- fix
    rw [Finset.sum_comm, order_cost _ (fun i=>by simp [shine,he])]; apply Finset.sum_congr rfl; intro z _; unfold shine εglows; rw [←Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro x _; rw [Gland.lit]; unfold six endr; nth_rw 3 [winded]; ring
-- Displacement measure, literal underlying `measure` at two cutoffs.
open Circuits

def δ (χ:Shade.Cut)(s a:ℝ)(v:Hat G d)(k:ℕ) : Module.Dual ℂ (Tile G):= (weigh v k) ∘ₗ (Prelude.send (Shade.outfit χ (s*a)) - Prelude.send (Shade.outfit χ a))
lemma pay (χ:Shade.Cut)(s a:ℝ)(v:Hat G d)(k:ℕ)(p:Tile G): δ χ s a v k p=weigh v k (Shade.measure χ (s*a) p- Shade.measure χ a p):=by rw [δ, LinearMap.comp_apply,LinearMap.sub_apply, Prelude.sends,Prelude.sends]; rfl
private lemma near_cost {a b r:ℝ}(h:0<a)(H:0<b)(hR:0<r)(he:b≤2*a*r): a⁻¹^4*(r^5)⁻¹ ≤ a * (2/b)^5 := by
    have ht : r⁻¹≤(2/b)*a := by rw [inv_le_iff_one_le_mul₀ hR]; field_simp; linarith
    calc _ ≤ a⁻¹^4*((2/b)*a)^5:= by rw [← inv_pow]; gcongr
         _ = _:= by field_simp
variable {ι:Type} {a:ι→ℝ}{L: Filter ι} [L.IsCountablyGenerated] (S:Tendsto a L (𝓝 0))(he:∀ᶠ i in L,0<a i)
variable (χ:Shade.Cut)(s:ℝ)(hs:0<s)
include he S hs
lemma vanishHigher {q:Tile G}(h: Book G n q)(v:Hat G d)(hh: k+4 < n): Tendsto (fun i=> δ χ s (a i) v k q) L (𝓝 0):= by
    obtain ⟨C,hC,T⟩:= steam_row q h v k; let p(x:Cover):= weigh v k (q x); have hp(x:Cover): ‖p x‖≤ C*(area x^5)⁻¹:=by
        have hq := room x; refine (T x).trans ?_; rw [carry_cost,mul_assoc]; gcongr C * ?_; rw [show area x^n = area x^(n-k)*area x^k from (by rw [ ← pow_add ]; congr 1; omega)]; field_simp; gcongr; omega
    have hx(x:Cover): ‖p x‖≤ C*(area x^4)⁻¹:= by refine (hp x).trans ?_; rw [← carry_cost, ← carry_cost]; gcongr C* ?_; exact carry_weight _ (by decide)
    have ht: arrived L a p 0 4:= by
        intro x hx; apply tendsto_zero_iff_norm_tendsto_zero.mpr; let b:=‖x‖/2; have hR:0<b:=half_pos (norm_pos_iff.mpr hx); let y i:=mark (a i) x; let B i:=actual (a i) (y i); let D:=C*(2/b)^5; have hq := (marks x S he).norm.eventually (le_mem_nhds (show b<‖x‖ by unfold b; linarith [norm_pos_iff.mpr hx]))
        apply squeeze_zero' (Eventually.of_forall fun i:ι=> norm_nonneg ((a i:ℂ)⁻¹^4*p (y i))) _ (show Tendsto (fun i=> a i * D) L (𝓝 0) by simpa using S.mul_const D); filter_upwards [he,hq] with i hi hh; change b≤‖B i‖ at hh; change ‖(a i:ℂ)⁻¹^4*p (y i)‖≤ _; rw [norm_mul,norm_pow,norm_inv,Complex.norm_real,Real.norm_of_nonneg hi.le]; calc
          _ ≤ C*((a i)⁻¹^4*(area (y i)^5)⁻¹):= by rw [mul_left_comm C]; gcongr; exact hp _
          _ ≤ C*(a i*(2/b)^5):=mul_le_mul_of_nonneg_left (near_cost hi hR (included (y i)) (hh.trans ((Shade.size_actual hi _).2.trans (by unfold area; gcongr; simp)))) hC
          _ = _ :=mul_left_comm ..
    obtain hp':= perimeter χ s hs S he p (fun _=>0) hC hx ht; simp only [mul_zero, MeasureTheory.integral_zero] at hp'; apply hp'.congr; intro i; rw [pay,map_sub]; simp_rw [Shade.quick_sum,map_sum, map_smul]; rfl
lemma vanishErr {P:Stamp G}(v:Hat G d)(hP:P∈ elemental G d)(u:PlaqAxes)(h:k≤d): Tendsto (fun i=> δ χ s (a i) v k (bounces G P (V3 G (tile u)-εglows u G))) L (𝓝 0):= vanishHigher S he χ s hs (n:=d+5) (earned hP (extra u)) v (by omega)
end YM.FVA2.Generator.Center
